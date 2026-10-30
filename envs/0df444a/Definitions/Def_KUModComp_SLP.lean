-- Prove2me | Definitions.Def_KUModComp_SLP
-- name    : KUModComp_SLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:58:07.485361+00:00
-- url     : https://prove2.me/theorems/9b6820f0-327f-44c6-9850-e77eff64575c
-- title:
--   Straight-line programs over a commutative ring with a multipoint-evaluation oracle
-- statement:
--   The cost model for "ring operations plus one invocation of MULTIVARIATE MULTIPOINT EVALUATION".
--
--   A **straight-line program** is a list of instructions and a list of output registers. Registers are numbered $0,1,2,\dots$; they start as the input list, and each instruction appends its result(s):
--
--   1. `zero`, `one`: the constants $0$ and $1$;
--   2. `add i j`, `mul i j`, `neg i`: $r_i + r_j$, $r_i r_j$, $-r_i$;
--   3. `inv i`: the inverse of $r_i$, through an inversion primitive $\iota : R \to R$ (only its values on units are ever relied on: theorems quantify over every $\iota$ that inverts units);
--   4. `mme d₀ m' N' cs ps`: one invocation of MULTIVARIATE MULTIPOINT EVALUATION with parameters $d_0, m', N'$, on the coefficients held in the registers listed in `cs` and the points held in the registers listed in `ps`; it appends the $N'$ values.
--
--   A register out of range reads $0$. There is no comparison and no branch on ring values. The number of **ring operations** of a program is the number of its instructions other than `mme`; its **oracle-call log** is the list of parameters $(d_0, m', N')$ of its `mme` instructions. Both depend only on the program, not on the ring or the input.
--
--   **Input layout** for MODULAR COMPOSITION: the $d^m$ coefficients of $f$, then the $N$ coefficients of each of $g_0,\dots,g_{m-1}$, then the $n+1$ coefficients of $h$, then the $N'$ points $\beta_0,\dots,\beta_{N'-1}$.
--
--   **Formalization Note** `run ι P input` is the interpreter, `ringOps P` the operation count, `oracleCalls P` the oracle-call log, `layout f g h β` the input list. In `mme`, the coefficient of the exponent vector $e$ is at position `finFunctionFinEquiv e` of `cs`, and coordinate $i$ of point $k$ at position $k m' + i$ of `ps`; missing positions read $0$.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), Theorem 3.1, p. 9 ("ring operations plus one invocation of MULTIVARIATE MULTIPOINT EVALUATION"); Problem 2.1, p. 7; representation of polynomials, p. 8

import Mathlib
import Definitions.Def_KUModComp_mmeSpec

namespace KUModComp

/-- **Instructions of a straight-line program over a commutative ring, with a
MULTIVARIATE MULTIPOINT EVALUATION oracle.** Registers are numbered `0, 1, 2, …`; every
instruction appends its result(s) to the register file.
* `zero`, `one`: the constants `0`, `1`;
* `add i j`, `mul i j`: `r_i + r_j`, `r_i * r_j`; `neg i`: `-r_i`;
* `inv i`: the inverse of `r_i` (meant for a unit `r_i`);
* `mme d₀ m' N' cs ps`: one invocation of MULTIVARIATE MULTIPOINT EVALUATION (Problem 2.1) with
  parameters `d₀, m', N'`: the coefficients are the registers listed in `cs` (exponent vector
  `e : Fin m' → Fin d₀` at position `finFunctionFinEquiv e`), the points the registers listed in
  `ps` (coordinate `i` of point `k` at position `k * m' + i`); it appends the `N'` values. -/
inductive Instr
  | zero
  | one
  | add (i j : ℕ)
  | neg (i : ℕ)
  | mul (i j : ℕ)
  | inv (i : ℕ)
  | mme (d₀ m' N' : ℕ) (cs ps : List ℕ)

/-- A straight-line program: its instruction list and the list of registers it outputs. It
contains no ring element and no branch: it is generated, if at all, from natural-number
parameters. -/
structure SLP where
  code : List Instr
  out : List ℕ

variable {R : Type*} [CommRing R]

/-- The value of register `r` (`0` if out of range). -/
def reg (regs : List R) (r : ℕ) : R := regs.getD r 0

/-- The value of the register named at position `p` of an index list (`0` if the index list is
too short). -/
def regAt (regs : List R) (idx : List ℕ) (p : ℕ) : R :=
  match idx[p]? with
  | some r => reg regs r
  | none => 0

/-- One step of the interpreter. `ι : R → R` is the inversion primitive; the correctness clause of
the theorems quantifies over every `ι` that inverts units, so a program may only rely on inverting
units. -/
def step (ι : R → R) (regs : List R) : Instr → List R
  | .zero => regs ++ [0]
  | .one => regs ++ [1]
  | .add i j => regs ++ [reg regs i + reg regs j]
  | .neg i => regs ++ [-reg regs i]
  | .mul i j => regs ++ [reg regs i * reg regs j]
  | .inv i => regs ++ [ι (reg regs i)]
  | .mme d₀ m' N' cs ps =>
      regs ++ List.ofFn (mmeSpec (d := d₀) (m := m') (N := N')
        (fun e => regAt regs cs (finFunctionFinEquiv e))
        (fun k i => regAt regs ps ((k : ℕ) * m' + i)))

/-- **Run a program** on an input list: the registers start as the input, every instruction is
executed in order, and the output is the list of the values of the registers in `P.out`. -/
def run (ι : R → R) (P : SLP) (input : List R) : List R :=
  let regs := P.code.foldl (step ι) input
  P.out.map (reg regs)

/-- Is the instruction a ring operation (anything but an oracle call)? -/
def Instr.isRingOp : Instr → Bool
  | .mme .. => false
  | _ => true

/-- **Number of ring operations** of a program: every instruction other than `mme` counts one
(`zero`, `one`, `add`, `neg`, `mul`, `inv`). Reading inputs and naming outputs are free. -/
def ringOps (P : SLP) : ℕ := (P.code.filter Instr.isRingOp).length

/-- The parameters `(d₀, m', N')` of an oracle instruction. -/
def Instr.oracleParams : Instr → Option (ℕ × ℕ × ℕ)
  | .mme d₀ m' N' _ _ => some (d₀, m', N')
  | _ => none

/-- **Oracle-call log** of a program: the parameters `(d₀, m', N')` of each invocation of
MULTIVARIATE MULTIPOINT EVALUATION, in program order. -/
def oracleCalls (P : SLP) : List (ℕ × ℕ × ℕ) := P.code.filterMap Instr.oracleParams

/-- **Input layout** of the reduction (Theorem 3.1): the `d^m` coefficients of `f` (exponent vector
`e` at position `finFunctionFinEquiv e`), then the `N` coefficients of `g_0`, …, of `g_{m-1}`
(each low degree first), then the `n + 1` coefficients of `h` (low degree first), then the `N'`
points `β_0, …, β_{N'-1}`. -/
def layout {d m N n N' : ℕ} (f : (Fin m → Fin d) → R) (g : Fin m → Fin N → R)
    (h : Fin (n + 1) → R) (β : Fin N' → R) : List R :=
  List.ofFn (fun k : Fin (d ^ m) => f (finFunctionFinEquiv.symm k)) ++
    (List.ofFn fun i => List.ofFn (g i)).flatten ++ List.ofFn h ++ List.ofFn β

end KUModComp


