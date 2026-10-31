-- Prove2me | Definitions.Def_InfHorizonVP_gelfandSetIntegral
-- name    : InfHorizonVP_gelfandSetIntegral
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:18:05.044302+00:00
-- url     : https://prove2.me/theorems/0b2a9072-5a6a-4094-97e0-477c3cc6bd9d
-- title:
--   Gelfand integral of a multifunction $\int_A\Phi\,dt$
-- statement:
--   For a multifunction $\Phi:A\rightsquigarrow E^*$, let $\mathcal S^1_\Phi$ be the set of Gelfand integrable selectors of $\Phi$ (functions $f$ with $f(t)\in\Phi(t)$ for a.e. $t\in A$). The **Gelfand integral** of $\Phi$ is
--   $$
--   \int_A\Phi\,dt=\Bigl\{\int_A f\,dt\ \Bigm|\ f\in\mathcal S^1_\Phi\Bigr\}.
--   $$
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §A.2, pp.21–22

import Mathlib
import Definitions.Def_InfHorizonVP_IsGelfandIntegral
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Gelfand integral of a multifunction `∫_A Φ dt`.**
Frankowska, Sagara, arXiv:1801.00400v3, §A.2, p.22: "A function f : I → E* is called a selector
of Φ if f(t) ∈ Φ(t) a.e. t ∈ I. … Denote by S¹_Φ the set of Gelfand integrable selectors of Φ. The
Gelfand integral of Φ is conventionally defined as ∫Φdt := {∫ f dt | f ∈ S¹_Φ}."

`gelfandSetIntegral Φ A` is the set of Gelfand integrals over `A` of the Gelfand integrable
selectors of `Φ` on `A`. -/
def gelfandSetIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : ℝ → Set (E →L[ℝ] ℝ)) (A : Set ℝ) : Set (E →L[ℝ] ℝ) :=
  {z | ∃ f : ℝ → E →L[ℝ] ℝ, (∀ᵐ t ∂(volume.restrict A), f t ∈ Φ t) ∧ IsGelfandIntegral f A z}

end InfHorizonVP


