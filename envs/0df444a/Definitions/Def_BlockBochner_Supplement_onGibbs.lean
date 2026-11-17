-- Prove2me | Definitions.Def_BlockBochner_Supplement_onGibbs
-- name    : BlockBochner_Supplement_onGibbs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:28:13.136708+00:00
-- url     : https://prove2.me/theorems/e7d917d1-5b2f-4c32-91dd-185efcd58523
-- title:
--   $O(N)$ Gibbs measure $\mu_{J,h}$
-- statement:
--   Let $V$ be a finite set of sites, $N\ge1$, $J=(J_{xy})_{x,y\in V}$ a real matrix and $h=(h_x)_{x\in V}$ external fields $h_x\in\mathbb R^N$. The $O(N)$ Gibbs measure is the probability measure on configurations $\sigma=(\sigma_x)_{x\in V}\in(S^{N-1})^V$ given by
--   $$
--   \mu_{J,h}(d\sigma)\ \propto\ \exp\Big(\tfrac12\sum_{x,y\in V}J_{xy}\,\sigma_x\cdot\sigma_y+\sum_{x\in V}h_x\cdot\sigma_x\Big)\prod_{x\in V}d\omega(\sigma_x),
--   $$
--   where $\omega$ is the uniform probability measure on $S^{N-1}$ and the double sum runs over ordered pairs.
--
--   In the paper $J$ is symmetric with zero diagonal and supported on the edges of a graph; those conditions are hypotheses of the theorems, not part of this definition.
--
--   **Formalization Note** The product measure $\omega^{\otimes V}$ with the displayed (bounded, positive) density, normalized by dividing by its total mass (`cond` on the whole space). The verification file proves that the result is a probability measure for every $J$ and $h$.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228 (sha256 e4bc2683…4a27706), Sec. 1.3, Eq. (1), p.4 (PDF p.5)

import Mathlib
import Definitions.Def_BlockBochner_Supplement_haarSphere

open MeasureTheory ProbabilityTheory

namespace BlockBochner.Supplement

/-- **O(N) Gibbs measure `µ_{J,h}`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 1.3, p.4, Eq. (1):
```
µ_{J,h}(dσ) ∝ exp( ½ Σ_{x,y∈V} J_xy σ_x·σ_y + Σ_{x∈V} h_x·σ_x ) Π_{x∈V} dω(σ_x),
```
for spins `σ_x ∈ S^{N−1}`, a real `V × V` interaction matrix `J` and external fields `h_x ∈ ℝ^N`.

**Formalization Note** The unnormalized measure is the product `ω^{⊗V}` with the density
`exp(½ Σ_{x,y} J_xy ⟨σ_x,σ_y⟩ + Σ_x ⟨h_x,σ_x⟩)`; the double sum runs over ordered pairs, as in (1).
It is normalized by conditioning on the whole space (dividing by its total mass, which is finite
and positive: the density is bounded and positive). Symmetry and the zero diagonal of `J` are
hypotheses of the theorems, not part of this definition. -/
noncomputable def onGibbs (N : ℕ) {V : Type*} [Fintype V] (J : Matrix V V ℝ)
    (h : V → EuclideanSpace ℝ (Fin N)) : Measure (V → GraphNNSphere.Sph N) :=
  ((Measure.pi fun _ : V => haarSphere N).withDensity fun σ =>
    ENNReal.ofReal (Real.exp ((1 / 2 : ℝ) * ∑ x, ∑ y, J x y * inner ℝ (σ x : EuclideanSpace ℝ (Fin N))
      (σ y : EuclideanSpace ℝ (Fin N)) + ∑ x, inner ℝ (h x) (σ x : EuclideanSpace ℝ (Fin N)))))[|Set.univ]

end BlockBochner.Supplement


