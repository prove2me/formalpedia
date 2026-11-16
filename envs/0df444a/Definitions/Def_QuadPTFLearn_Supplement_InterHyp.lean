-- Prove2me | Definitions.Def_QuadPTFLearn_Supplement_InterHyp
-- name    : QuadPTFLearn_Supplement_InterHyp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:40:21.747209+00:00
-- url     : https://prove2.me/theorems/14ea588d-ac41-4e36-ad00-44174af74225
-- title:
--   Output layout of an intersection of quadratic PTFs $1\{q_j(x)\ge0\ \forall j<m\}$ (Algorithm 1's hypothesis class)
-- statement:
--   Algorithm 1 (RegularLearning) returns a hypothesis from the family $\mathcal H=\{x\mapsto 1\{q_i(x)\ge0\text{ for all }i\in[k]\}\}$ of intersections of quadratic threshold functions. This definition fixes how such a hypothesis is read from the machine's output memory.
--
--   An **intersection of quadratic PTFs** on $\mathbb R^d$ is given by a number $m\in\mathbb N$ and, for each $j<m$, a constant $c_j\in\mathbb R$, a vector $b_j\in\mathbb R^d$ and a matrix $A_j\in\mathbb R^{d\times d}$. Its quadratics and its value are
--   $$q_j(x)=c_j+\langle b_j,x\rangle+x^\top A_jx,\qquad h(x)=1\{q_j(x)\ge0\ \text{for every } j<m\},$$
--   so $m=0$ gives the constant function $1$.
--
--   **Output layout.** When the machine halts, the memory cell at the output base address $p[1]$ holds $m$, which must be a natural number; it is followed by $m$ blocks of $1+d+d^2$ cells, block $j$ holding $c_j$, then the $d$ coordinates of $b_j$, then the entries of $A_j$ in row-major order. This is the block layout of the features of the published PTF decoder `QuadPTFLearn.decode`. If the first cell is not a natural number the output is undecodable, which the statements count as a failure.
--
--   **Formalization Note** The number $m$ of constraints is not bounded and the matrices need not be symmetric; any such output is a $\{0,1\}$-valued hypothesis.
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Theorem 3.10, p.25 (PDF p.27); Algorithm 1 (RegularLearning), steps 6–9, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_QuadPTFLearn_Learner

open MeasureTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

namespace Supplement

/-!
# Output layout of an intersection of quadratic PTFs

I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Theorem 3.10, p.25 (PDF p.27), and Algorithm 1 (RegularLearning), steps 6–9, p.26 (PDF p.28):
the algorithm returns `ĥ ∈ H = {x ↦ 1{q_i(x) ≥ 0 for all i ∈ [k]}}` with every `q_i` of
degree at most two.

**Formalization Note.**
* At `halt`, memory from the cell `p[1]` holds `m` (a natural number), then `m` blocks
  `c_j, b_j (d cells), A_j (d² cells, row-major)`: the same block layout as the features of the
  published `QuadPTFLearn.decode`. The hypothesis is
  `h(x) = 1{c_j + ⟪b_j, x⟫ + xᵀ A_j x ≥ 0 for every j < m}` (for `m = 0` the constant `1`).
* `decodeInter` returns `none` when the first cell is not a natural number; `none` counts as a
  failure in the statements that use it. The number `m` of constraints is not bounded.
-/

/-- An intersection `1{q_j(x) ≥ 0 for all j < m}` of quadratic threshold functions with
`q_j(x) = c_j + ⟪b_j, x⟫ + xᵀ A_j x`. -/
structure InterHyp (d : ℕ) where
  m : ℕ
  c : Fin m → ℝ
  b : Fin m → Pt d
  A : Fin m → Matrix (Fin d) (Fin d) ℝ

/-- The quadratic `q_j(x) = c_j + ⟪b_j, x⟫ + xᵀ A_j x`. -/
noncomputable def InterHyp.quad {d : ℕ} (H : InterHyp d) (j : Fin H.m) (x : Pt d) : ℝ :=
  H.c j + ⟪H.b j, x⟫ + ∑ i, ∑ i', x i * H.A j i i' * x i'

/-- The `{0,1}`-valued hypothesis `1{q_j(x) ≥ 0 for all j < m}`. -/
noncomputable def InterHyp.eval {d : ℕ} (H : InterHyp d) (x : Pt d) : ℝ :=
  if ∀ j, 0 ≤ H.quad j x then 1 else 0

/-- Read an intersection of quadratic PTFs from memory `mem` starting at `base`: a count `m`,
then `m` blocks `(c_j; b_j; A_j row-major)` of `1 + d + d²` cells. -/
noncomputable def decodeInter (d : ℕ) (mem : ℤ → ℝ) (base : ℤ) : Option (InterHyp d) :=
  match natOf (mem base) with
  | none => none
  | some m =>
    let blk : ℕ := 1 + d + d * d
    let cell : ℕ → ℕ → ℝ := fun j o => mem (base + 1 + ((j * blk + o : ℕ) : ℤ))
    some
      { m := m
        c := fun j => cell j 0
        b := fun j => WithLp.toLp 2 (fun i => cell j (1 + i))
        A := fun j i i' => cell j (1 + d + d * i + i') }

end Supplement

end QuadPTFLearn


