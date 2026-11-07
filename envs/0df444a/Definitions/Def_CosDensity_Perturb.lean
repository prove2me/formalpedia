-- Prove2me | Definitions.Def_CosDensity_Perturb
-- name    : CosDensity_Perturb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:46.071197+00:00
-- url     : https://prove2.me/theorems/b58c7c79-30db-4b25-adfa-a3eaa183b2b3
-- title:
--   The perturbation $\tilde u=(\sqrt{1-\xi^2}\,u,\ \xi)$
-- statement:
--   For $\xi\in\mathbb R$ and a vector $u\in\mathbb R^\iota$, the **perturbed vector** is
--
--   $$\tilde u=\big(\sqrt{1-\xi^2}\,u,\ \xi\big)\in\mathbb R^{\iota}\times\mathbb R .$$
--
--   The paper applies it to every ideal unit vector of the hard instance to make all pairwise similarities strictly positive before rounding to rational vectors.
--
--   **Formalization Note** The new coordinate is the index `none` of `Option ι`.
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.8, p.36

import Mathlib

namespace CosDensity

/-!
# The one-dimensional perturbation of §8.8

Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine Density Moments*, arXiv:2609.06925
(held version, sha256 f4d4df22…), §8.8, p.36 (pdf_page 37): "map every ideal unit vector u ∈ R^{4m}
to ũ = (√(1 − ξ²) u, ξ) ∈ R^{4m+1}".

**Formalization Note.** The source space is `EuclideanSpace ℝ ι` for any finite index type `ι`
(the paper's `ℝ^{4m}`); the new coordinate is the index `none` of `Option ι`.
-/

/-- `ũ = (√(1 − ξ²) u, ξ)`. -/
noncomputable def perturb {ι : Type*} (ξ : ℝ) (u : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ (Option ι) :=
  WithLp.toLp 2 (fun o : Option ι =>
    match o with
    | none => ξ
    | some k => Real.sqrt (1 - ξ ^ 2) * u k)

end CosDensity


