-- Prove2me | Definitions.Def_RGGDetect_unifSphere
-- name    : RGGDetect_unifSphere
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:35:53.265569+00:00
-- url     : https://prove2.me/theorems/02ce928e-d00c-48e4-a76c-69f0ef149c8e
-- title:
--   Uniform law on $S^{d-1}$, the product prior, and the cap probability
-- statement:
--   Let $S^{d-1}=\{x\in\mathbb R^d:\|x\|=1\}$ be the unit sphere and $\sigma$ the uniform probability measure on it. For $n$ points $x_1,\dots,x_n\in S^{d-1}$ (a **configuration**), the **product spherical prior** makes $x_1,\dots,x_n$ independent with law $\sigma$. For a threshold $\tau\in\mathbb R$ the **cap probability** is
--
--   $$
--   p(d,\tau)=\mathbb P\{\langle x_1,x_2\rangle\ge\tau\},\qquad x_1,x_2\ \text{independent with law }\sigma .
--   $$
--
--   In the random geometric graph the threshold is chosen so that $p(d,\tau)$ equals the edge density $p$; every object of the mission computes its $p$ from $(d,\tau)$ in this way.
--
--   **Formalization Note** $\sigma$ is Mathlib's cone measure `volume.toSphere` on the unit sphere of `EuclideanSpace ℝ (Fin d)`, divided by its total mass; it is a probability measure for $d\ge1$ (proved in the mission's sanity file) and the zero measure for $d=0$. Vertices are indexed by `Fin n`, i.e. $0,\dots,n-1$.
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), §1, p.1 (PDF p.3); (57), p.18

import Mathlib

open MeasureTheory

namespace RGGDetect

/-- The unit sphere `S^{d-1} ⊂ ℝ^d` (Du, Mao, Sun, Wu, Xu, *Sharp detection thresholds for random
geometric graphs with polynomial average degrees*, arXiv:2610.08517 (held version, sha256 e7bebd4a…),
§1, p.1). -/
abbrev Sph (d : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1

/-- The uniform probability measure `σ` on `S^{d-1}` (arXiv:2610.08517, held version, §1, p.1:
"independent and uniform on the unit sphere"; (57), p.18: "the uniform probability measure σ").

**Formalization Note** It is the cone measure `volume.toSphere` normalised by its total mass. For
`d ≥ 1` the total mass is finite and positive, so this is a probability measure; for `d = 0` the
sphere is empty and the measure is `0`. -/
noncomputable def unifSphere (d : ℕ) : Measure (Sph d) :=
  (volume.toSphere (Set.univ : Set (Sph d)))⁻¹ • volume.toSphere

instance unifSphere.instIsFiniteMeasure (d : ℕ) : IsFiniteMeasure (unifSphere d) := by
  constructor
  unfold unifSphere
  rw [Measure.smul_apply, smul_eq_mul]
  by_cases h : volume.toSphere (Set.univ : Set (Sph d)) = 0
  · simp [h]
  · rw [ENNReal.inv_mul_cancel h (measure_ne_top _ _)]
    exact ENNReal.one_lt_top

/-- The inner product `⟨x, y⟩` of two points of the sphere. -/
noncomputable def ip {d : ℕ} (x y : Sph d) : ℝ :=
  inner ℝ (x : EuclideanSpace ℝ (Fin d)) (y : EuclideanSpace ℝ (Fin d))

/-- A configuration of `n` latent points `x₁, …, x_n ∈ S^{d-1}` (vertices are `Fin n`, the paper's
`[n]` shifted to start at `0`). -/
abbrev Config (n d : ℕ) : Type := Fin n → Sph d

/-- The product spherical prior: `x₁, …, x_n` independent and uniform on `S^{d-1}`. -/
noncomputable def prior (n d : ℕ) : Measure (Config n d) :=
  Measure.pi fun _ : Fin n => unifSphere d

/-- The cap probability `P{⟨x₁, x₂⟩ ≥ τ}` for `x₁, x₂` independent and uniform on `S^{d-1}`
(arXiv:2610.08517, held version, §1, p.1). In the paper `τ = τ(d, p)` is chosen so that this equals
the edge density `p`. -/
noncomputable def capProb (d : ℕ) (τ : ℝ) : ℝ :=
  ((unifSphere d).prod (unifSphere d)).real {q | τ ≤ ip q.1 q.2}

end RGGDetect


