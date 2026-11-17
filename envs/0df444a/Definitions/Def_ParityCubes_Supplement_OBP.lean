-- Prove2me | Definitions.Def_ParityCubes_Supplement_OBP
-- name    : ParityCubes_Supplement_OBP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:09:54.282214+00:00
-- url     : https://prove2.me/theorems/ed350bf7-0644-4b16-b6f0-5011a059006b
-- title:
--   Ordered matrix branching programs over $\mathbb F_2$ and their solution on the word RAM
-- statement:
--   An **ordered matrix branching program** over $\mathbb F_2$ is
--   $$f(x)=u^{\mathsf T}\prod_{i=1}^{n}(A_i+x_iB_i)\,v,$$
--   with dimensions $d_0,\dots,d_n$, $A_i,B_i\in\mathbb F_2^{d_{i-1}\times d_i}$, $u\in\mathbb F_2^{d_0}$, $v\in\mathbb F_2^{d_n}$; the variable $x_i$ appears only in layer $i$.
--
--   A program of the deterministic unit-cost word RAM, started with the entries of the program in memory, **solves** an optimum (such as $\mathrm{cert}(f)$ or $\zeta(f)$) within $t$ steps if it halts within $t$ steps, rejects exactly when the optimum is $+\infty$, and otherwise writes the optimum followed by the indicator vector of a minimizing set after the input.
--
--   **Formalization Note.** The machine is the published `TrulySubcubicAPSP` word RAM (one step per instruction, $W$-bit words); bits are stored as words $0/1$.
-- source:
--   Sheshadri, Smirnov, The Complexity of Choosing Parity Projections, arXiv:2611.00289 (manuscript sha256 95994d2d…), Theorem I.1, p.35 (PDF p.36)

import Mathlib
import Definitions.Def_ParityCubes_cubeSum
import Definitions.Def_TrulySubcubicAPSP_WordRAM

set_option autoImplicit false

namespace ParityCubes.Supplement

open ParityCubes

/-- An **ordered matrix branching program** over `𝔽₂` (Sheshadri–Smirnov, arXiv:2611.00289,
manuscript sha256 95994d2d…, Theorem I.1, p.35 (PDF p.36)):
`f(x) = uᵀ ∏_{i=1}^{n} (A_i + x_i B_i) v`, variable `x_i` appearing only in layer `i`. The dimensions
are `d_0, …, d_n`; `A_i`, `B_i` are `d_{i−1} × d_i` matrices (lists of rows), `u` has length `d_0`
and `v` length `d_n`. -/
structure OBP where
  /-- the number `n` of variables and layers -/
  n : ℕ
  /-- the dimensions `d_0, …, d_n` -/
  dims : List ℕ
  /-- the vector `u` -/
  u : List Bool
  /-- the matrices `A_i` -/
  A : List (List (List Bool))
  /-- the matrices `B_i` -/
  B : List (List (List Bool))
  /-- the vector `v` -/
  v : List Bool

/-- The dimensions are compatible. -/
def OBP.WF (Q : OBP) : Prop :=
  Q.dims.length = Q.n + 1 ∧ Q.A.length = Q.n ∧ Q.B.length = Q.n ∧
    Q.u.length = Q.dims.getD 0 0 ∧ Q.v.length = Q.dims.getD Q.n 0 ∧
    ∀ i < Q.n, (Q.A.getD i []).length = Q.dims.getD i 0 ∧ (Q.B.getD i []).length = Q.dims.getD i 0 ∧
      (∀ row ∈ Q.A.getD i [], row.length = Q.dims.getD (i + 1) 0) ∧
      (∀ row ∈ Q.B.getD i [], row.length = Q.dims.getD (i + 1) 0)

/-- The row vector `p M` over `𝔽₂`, with `cols` columns. -/
def vecMat (p : List Bool) (M : List (List Bool)) (cols : ℕ) : List Bool :=
  List.ofFn (fun j : Fin cols =>
    (List.zipWith (fun a row => a && row.getD j.val false) p M).foldl xor false)

/-- The matrix `A_i + x_i B_i`. -/
def OBP.layer (Q : OBP) (i : ℕ) (b : Bool) : List (List Bool) :=
  if b then List.zipWith (List.zipWith xor) (Q.A.getD i []) (Q.B.getD i []) else Q.A.getD i []

/-- `f(x) = uᵀ ∏_i (A_i + x_i B_i) v`. -/
def OBP.eval (Q : OBP) (x : Fin Q.n → Bool) : Bool :=
  let row := (List.finRange Q.n).foldl
    (fun p i => vecMat p (Q.layer i.val (x i)) (Q.dims.getD (i.val + 1) 0)) Q.u
  (List.zipWith (fun a b => a && b) row Q.v).foldl xor false

/-- The input of `Q` as machine words (bits as `0/1`): `n`, the dimensions, `u`, the entries of all
`A_i` row by row, those of all `B_i`, and `v`. -/
def OBP.words (Q : OBP) : List ℤ :=
  [(Q.n : ℤ)] ++ Q.dims.map (fun d => (d : ℤ)) ++ Q.u.map (fun b => (b.toNat : ℤ)) ++
    (Q.A.flatten.flatten).map (fun b => (b.toNat : ℤ)) ++
    (Q.B.flatten.flatten).map (fun b => (b.toNat : ℤ)) ++ Q.v.map (fun b => (b.toNat : ℤ))

/-- The program `P` of the published deterministic word RAM `TrulySubcubicAPSP` (unit cost, `W`-bit
words), started with the words of `Q` in cells `0, 1, …`, halts within `t` steps; it rejects exactly
when `opt = +∞` ("report infeasibility"), and when it accepts, the cell after the input holds
`opt` and the next `n` cells the indicator of a set `S` with property `good` and `|S| = opt`. -/
def OBPSolves (P : List TrulySubcubicAPSP.Instr) (Q : OBP) (W t : ℕ)
    (good : Finset (Fin Q.n) → Prop) (opt : ℕ∞) : Prop :=
  ∃ (verdict : Bool) (mem : ℤ → BitVec W),
    TrulySubcubicAPSP.exec P t 0 (TrulySubcubicAPSP.loadWords W Q.words) = some (verdict, mem) ∧
    (verdict = false ↔ opt = ⊤) ∧
    (verdict = true → ∃ S : Finset (Fin Q.n), good S ∧ (S.card : ℕ∞) = opt ∧
      (mem (Q.words.length : ℤ)).toInt = S.card ∧
      ∀ i : Fin Q.n, (mem ((Q.words.length + 1 + i.val : ℕ) : ℤ)).toInt = if i ∈ S then 1 else 0)

end ParityCubes.Supplement


