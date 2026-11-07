-- Prove2me | Definitions.Def_VertexSampleCSP_weightedFlatten
-- name    : VertexSampleCSP_weightedFlatten
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:56:43.130193+00:00
-- url     : https://prove2.me/theorems/cbea9784-6e1c-4c8d-b8d7-40c6f37b7d4d
-- title:
--   The weighted flattening $B$, the weight $\tau$, the generators $c_{ia}$ and the polytopes $Z_i$
-- statement:
--   Fix positive weights $t_i$ for the relevant variables $i$. Let $W$ be the diagonal matrix with entry $t_i$ at the coordinates of a relevant block $i$ and entry $0$ at the coordinates of the other blocks, and let $W^{-1/2}$ act as $t_i^{-1/2}$ on relevant blocks and as $0$ on the others. The **weighted flattening** is
--
--   $$B=(W^{-1/2}\otimes I^{\otimes(r-2)})\circ M,$$
--
--   and $\tau=\sum_i t_i$ over the relevant variables. For $r=2$ the factor $I^{\otimes0}$ is absent and $B=W^{-1/2}T$. The generators are $c_{ia}=Be_{ia}$ and the polytopes are $Z_i=\mathrm{conv}\{c_{ia}:a\in[q]\}$.
--
--   The image of the feasible region under $B$ is the geometric object in which the two optima are compared.
--
--   **Formalization Note** The weights are a function $t:V\to\mathbb R$ whose values on irrelevant variables are never used. For $r<2$ the index tuple is empty and the definition returns $0$; every statement assumes $r\ge2$.
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix B, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_VertexSampleCSP_Instance
import Definitions.Def_VertexSampleCSP_Instance_Gamma
import Definitions.Def_VertexSampleCSP_tensorEntry
import Definitions.Def_VertexSampleCSP_flatten

namespace VertexSampleCSP

/-- The diagonal entry of `W^{−1/2}` on block `i`: `t_i^{−1/2}` if `i` is relevant (`γ_i(I) > 0`),
and `0` otherwise. -/
noncomputable def wInvSqrt {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ}
    (I : Instance V r q) (t : V → ℝ) (i : V) : ℝ :=
  if 0 < I.gamma i then (Real.sqrt (t i))⁻¹ else 0

/-- The diagonal entry of `W^{1/2}` on block `i`: `t_i^{1/2}` if `i` is relevant, and `0`
otherwise. -/
noncomputable def wSqrt {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ}
    (I : Instance V r q) (t : V → ℝ) (i : V) : ℝ :=
  if 0 < I.gamma i then Real.sqrt (t i) else 0

/-- `W^{1/2} w`: the vector `w` with block `i` multiplied by `wSqrt I t i`. -/
noncomputable def wSqrtVec {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ}
    (I : Instance V r q) (t : V → ℝ) (w : EuclideanSpace ℝ (V × Fin q)) :
    EuclideanSpace ℝ (V × Fin q) :=
  WithLp.toLp 2 (fun p => wSqrt I t p.1 * w p)

/-- `τ = Σ_i t_i` over the relevant variables `i`. -/
noncomputable def tauW {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ}
    (I : Instance V r q) (t : V → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => 0 < I.gamma i), t i

/-- **The weighted flattening `B`.** Chang, *Optimal Vertex Sampling for Constraint Satisfaction
Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix B, p.15 (PDF p.17): "Fix
positive weights ti for the relevant variables i, let W be the diagonal matrix with entry ti at the
coordinates of a relevant block i and entry 0 at the coordinates of the other blocks, and let W^{−1/2}
act as ti^{−1/2} on relevant blocks and as 0 on the others. Define the weighted flattening
B = (W^{−1/2} ⊗ I^{⊗(r−2)}) ◦ M, and put τ = Σi ti over the relevant variables. For r = 2 the factor
I^{⊗0} is absent and B = W^{−1/2}T."

`weightedFlatten I t z` has entry `t_i^{−1/2} (Mz)_{c'}` at an index tuple `c'` whose first coordinate
`c'_1` lies in a relevant block `i`, and entry `0` when that block is irrelevant: `W^{−1/2}` acts on
the first tensor factor of `(ℝ^{V×[q]})^{⊗(r−1)}`, which is the second coordinate of `T`.

**Formalization Note.** The weights are a function `t : V → ℝ`; its values on irrelevant variables
are never used. For `r < 2` the tuple `c'` is empty and the definition returns the junk value `0`;
every statement assumes `r ≥ 2`. -/
noncomputable def weightedFlatten {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ}
    (I : Instance V r q) (t : V → ℝ) (z : EuclideanSpace ℝ (V × Fin q)) :
    EuclideanSpace ℝ (Fin (r - 1) → V × Fin q) :=
  WithLp.toLp 2 (fun c' =>
    (if h : 0 < r - 1 then wInvSqrt I t (c' ⟨0, h⟩).1 else 0) * flatten I z c')

/-- **The generators `c_{ia} = B e_{ia}`.** Chang, STOC 2027 submission (manuscript sha256
1e0edd23…), Appendix B, p.15 (PDF p.17): "Let cia = Beia". -/
noncomputable def genVec {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ}
    (I : Instance V r q) (t : V → ℝ) (i : V) (a : Fin q) :
    EuclideanSpace ℝ (Fin (r - 1) → V × Fin q) :=
  weightedFlatten I t (EuclideanSpace.single (i, a) 1)

/-- **The polytopes `Z_i = conv{c_{ia} : a ∈ [q]}`.** Chang, STOC 2027 submission (manuscript
sha256 1e0edd23…), Appendix B, p.15 (PDF p.17). -/
noncomputable def genPolytope {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ}
    (I : Instance V r q) (t : V → ℝ) (i : V) : Set (EuclideanSpace ℝ (Fin (r - 1) → V × Fin q)) :=
  convexHull ℝ (Set.range (genVec I t i))

end VertexSampleCSP


