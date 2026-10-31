-- Prove2me | Definitions.Def_ScalarMultiRisk_IsCoherent
-- name    : ScalarMultiRisk_IsCoherent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:56.415+00:00
-- url     : https://prove2.me/theorems/74c7d052-a1a5-49c1-9bbc-e88debfa2a3d
-- title:
--   Definition 3.1 — conditional positive homogeneity
-- statement:
--   A map $\rho_t$ is **conditionally positively homogeneous** if $\rho_t(\lambda X)=\lambda\rho_t(X)$ for every $X\in L^\infty(E)$ and $\lambda\in L^\infty_t(\mathbb R_+)$. A scalarized conditional convex risk measure with this property is **coherent**.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Definition 3.1, p.7

import Mathlib
import Definitions.Def_ScalarMultiRisk_LinftyFull

open MeasureTheory

namespace ScalarMultiRisk

/-- **Conditional positive homogeneity.** arXiv:1807.10694v5, Definition 3.1, p.7:
`ρ_t(λX) = λρ_t(X)` for every `λ ∈ L∞_t(ℝ₊)`. A scalarized conditional convex risk measure with
this property is *coherent*. -/
def IsCoherent {Ω : Type*} [MeasurableSpace Ω] {T : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : FilteredSpace Ω T) (t : Fin (T + 1)) (r : (Ω → E) → Ω → ℝ) : Prop :=
  ∀ X ∈ LinftyFull B (Fin.last T), ∀ l ∈ Linfty B t (fun _ => Set.Ici (0 : ℝ)),
    r (fun ω => l ω • X ω) =ᵐ[B.P] fun ω => l ω * r X ω

end ScalarMultiRisk


