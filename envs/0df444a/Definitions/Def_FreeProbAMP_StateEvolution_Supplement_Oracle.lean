-- Prove2me | Definitions.Def_FreeProbAMP_StateEvolution_Supplement_Oracle
-- name    : FreeProbAMP_StateEvolution_Supplement_Oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:57:14.570974+00:00
-- url     : https://prove2.me/theorems/660419f7-4b5f-4c10-b406-e1115aa93219
-- title:
--   Dimension-free oracle programs querying $A$ and $A^*$
-- statement:
--   Fix matrices $A_1,\dots,A_n\in\mathbb R^{d\times d}$ and write $A(x)=n^{-1/2}\sum_i x_iA_i$ for $x\in\mathbb R^n$, with normalized adjoint $A^*(M)_i=\sqrt n\,\mathrm{tr}(A_iM)/d$. An **oracle program** is a finite list of instructions acting on registers that hold real scalars, vectors in $\mathbb R^n$ and $d\times d$ matrices (all initially zero), together with an output vector register. The instructions are:
--
--   1. load a fixed real constant, or the dimension $n$, or the dimension $d$;
--   2. apply a fixed measurable map $f:\mathbb R^k\to\mathbb R$ to $k$ scalar registers, or coordinatewise to $k$ vector registers;
--   3. take the empirical mean $\frac1n\sum_i v_i$ of a vector register;
--   4. form $c\,v+w$ for vectors or $c\,M+N$ for matrices, with $c$ a scalar register;
--   5. call the oracle: $M:=A(v)$ or $v:=A^*(M)$.
--
--   The output is the sign vector $\hat x_i=\mathrm{sign}(v_i)\in\{-1,+1\}$ of the output register, with $\mathrm{sign}(0)=+1$. The same program runs in every dimension. It makes a fixed number of oracle calls, and with unit cost per real operation and per coordinatewise map evaluation it performs $O(n d^2)$ operations. This is the model of "an efficient algorithm which linearly queries $A$ and its adjoint $A^*$" used in Theorems 3.2 and 3.3; it contains the incremental approximate message passing algorithm of §3.2–3.3.
--
--   **Formalization Note.** Registers are indexed by natural numbers and execution is a left fold over the instruction list. `queryCount` counts oracle calls and `cost n d` counts real operations (a call costs $2nd^2$). Programs are deterministic and their maps are fixed in advance, so a map can never read the matrices or call the oracle outside an accounted instruction.
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), p. 7, Theorem 3.2; pp. 9–15, (3.16)–(3.18), (3.30), (3.38)–(3.41)

import Mathlib
import Definitions.Def_FreeProbAMP_StateEvolution_Matrices

open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution.Supplement

open FreeProbAMP.StateEvolution

/-- One instruction of a straight-line program that accesses the matrices `A_1, …, A_n` only
through the linear map `A(x) = n^{-1/2} ∑_i x_i A_i` and its normalized adjoint `A^*`.
Registers are indexed by natural numbers and hold scalars, vectors in `ℝ^n` or `d × d`
matrices; unset registers hold `0`.

* `const r c`: scalar register `r := c` (a fixed real number).
* `loadN r`, `loadD r`: scalar register `r := n`, resp. `r := d`.
* `scalarMap r k f src`: scalar `r := f(s_{src 0}, …, s_{src (k-1)})` for a fixed map
  `f : ℝ^k → ℝ`.
* `pointwise r k f src`: vector `r := (f(v_{src 0, i}, …, v_{src (k-1), i}))_{i ≤ n}`,
  a fixed map `f : ℝ^k → ℝ` applied coordinatewise.
* `mean r src`: scalar `r := (1/n) ∑_i v_{src, i}`.
* `vecComb r c x y`: vector `r := s_c · v_x + v_y`.
* `matComb r c X Y`: matrix `r := s_c · M_X + M_Y`.
* `queryA r src`: matrix `r := A(v_src)` (one call to `A`).
* `queryAdj r src`: vector `r := A^*(M_src)` (one call to `A^*`). -/
inductive Instr : Type
  | const (dst : ℕ) (c : ℝ)
  | loadN (dst : ℕ)
  | loadD (dst : ℕ)
  | scalarMap (dst : ℕ) (k : ℕ) (f : (Fin k → ℝ) → ℝ) (src : Fin k → ℕ)
  | pointwise (dst : ℕ) (k : ℕ) (f : (Fin k → ℝ) → ℝ) (src : Fin k → ℕ)
  | mean (dst src : ℕ)
  | vecComb (dst c x y : ℕ)
  | matComb (dst c x y : ℕ)
  | queryA (dst src : ℕ)
  | queryAdj (dst src : ℕ)

/-- Register contents for dimensions `n` and `d`. -/
structure Store (n d : ℕ) where
  sc : ℕ → ℝ
  vec : ℕ → Fin n → ℝ
  mat : ℕ → RMat d

/-- All registers zero. -/
def Store.init (n d : ℕ) : Store n d := ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩

namespace Instr

/-- Execution of one instruction on the input `A = (A_1, …, A_n)`. -/
def exec {n d : ℕ} (A : Fin n → RMat d) : Instr → Store n d → Store n d
  | .const r c, σ => { σ with sc := Function.update σ.sc r c }
  | .loadN r, σ => { σ with sc := Function.update σ.sc r (n : ℝ) }
  | .loadD r, σ => { σ with sc := Function.update σ.sc r (d : ℝ) }
  | .scalarMap r _ f src, σ => { σ with sc := Function.update σ.sc r (f fun j => σ.sc (src j)) }
  | .pointwise r _ f src, σ =>
      { σ with vec := Function.update σ.vec r (fun i => f fun j => σ.vec (src j) i) }
  | .mean r src, σ => { σ with sc := Function.update σ.sc r (avg n (σ.vec src)) }
  | .vecComb r c x y, σ => { σ with vec := Function.update σ.vec r (σ.sc c • σ.vec x + σ.vec y) }
  | .matComb r c x y, σ => { σ with mat := Function.update σ.mat r (σ.sc c • σ.mat x + σ.mat y) }
  | .queryA r src, σ => { σ with mat := Function.update σ.mat r (applyA A (σ.vec src)) }
  | .queryAdj r src, σ => { σ with vec := Function.update σ.vec r (applyAdj A (σ.mat src)) }

/-- The fixed scalar maps of an instruction are Borel measurable. -/
def MeasurableMaps : Instr → Prop
  | .scalarMap _ _ f _ => Measurable f
  | .pointwise _ _ f _ => Measurable f
  | _ => True

/-- Whether the instruction is a call to `A` or `A^*`. -/
def isQuery : Instr → Bool
  | .queryA _ _ => true
  | .queryAdj _ _ => true
  | _ => false

/-- Real-arithmetic operation count of an instruction in dimensions `n, d`: one operation per
scalar instruction, one evaluation of the fixed map per coordinate, `2n` for a vector combination,
`2d^2` for a matrix combination, and `2nd^2` for a call to `A` or `A^*`. -/
def cost (n d : ℕ) : Instr → ℕ
  | .const _ _ => 1
  | .loadN _ => 1
  | .loadD _ => 1
  | .scalarMap _ _ _ _ => 1
  | .pointwise _ _ _ _ => n
  | .mean _ _ => n
  | .vecComb _ _ _ _ => 2 * n
  | .matComb _ _ _ _ => 2 * d ^ 2
  | .queryA _ _ => 2 * n * d ^ 2
  | .queryAdj _ _ => 2 * n * d ^ 2

end Instr

/-- A deterministic, dimension-free oracle program: a finite list of instructions whose fixed
scalar maps are measurable, and an output vector register. The same program runs for every
`n` and `d`. -/
structure OracleProgram where
  instrs : List Instr
  output : ℕ
  measurable_maps : ∀ ι ∈ instrs, ι.MeasurableMaps

/-- The coordinatewise sign with `sign(0) = +1`. -/
def signVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => if 0 ≤ x i then 1 else -1

namespace OracleProgram

/-- Final register contents after running the program on `A`. -/
def run {n d : ℕ} (P : OracleProgram) (A : Fin n → RMat d) : Store n d :=
  P.instrs.foldl (fun σ ι => ι.exec A σ) (Store.init n d)

/-- The sign vector `x̂ ∈ {-1, +1}^n` output by the program on input `A`. -/
def signing {n d : ℕ} (P : OracleProgram) (A : Fin n → RMat d) : Fin n → ℝ :=
  signVec ((P.run A).vec P.output)

/-- The number of calls to `A` and `A^*` made by the program (the same on every input). -/
def queryCount (P : OracleProgram) : ℕ := (P.instrs.filter Instr.isQuery).length

/-- Total real-arithmetic operation count in dimensions `n, d`, including the final rounding. -/
def cost (P : OracleProgram) (n d : ℕ) : ℕ := (P.instrs.map (Instr.cost n d)).sum + n

end OracleProgram

end FreeProbAMP.StateEvolution.Supplement


