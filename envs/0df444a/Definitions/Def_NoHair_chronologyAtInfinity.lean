-- Prove2me | Definitions.Def_NoHair_chronologyAtInfinity
-- name    : NoHair_chronologyAtInfinity
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T08:29:58.333233+00:00
-- url     : https://prove2.me/theorems/3fdefb26-29ed-41b6-897d-3268c88ede20
-- title:
--   Timelike communication with arbitrarily distant regions of an asymptotic end
-- statement:
--   Let $A_R$ be decreasing reference regions of a single spatial end and let $R_0$ be an initial cutoff. In an end chart one can take $A_R=\psi(\{\rho>R\})$ for $R\ge R_0$. Define
--   $$
--   P_\infty=\bigcap_{R\ge R_0} I^-(A_R),\quad
--   F_\infty=\bigcap_{R\ge R_0} I^+(A_R),\quad
--   D_\infty=F_\infty\cap P_\infty,\quad H^+_\infty=\partial P_\infty .
--   $$
--   The outward and inward timelike curves may depend on $R$. These definitions formulate an alternative reference region for the end-relative vacuum uniqueness milestone.
-- source:
--   Proposed formulation for the reference-end issue in NoHair.hawking_analytic_nondegenerate_vacuum, https://prove2.me/theorems/d3c7be7a-309a-40fd-b177-28ba5a1b316c . For the classical domain and future horizon of a stationary asymptotic region see P. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Section 2.2, p. 7, equation (2.9) and the following paragraphs, https://arxiv.org/abs/0806.0016 .

import Definitions.Def_NoHair_spacetime

open Set
open scoped ContDiff Manifold

noncomputable section

namespace NoHair

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M]

/-- Points from which a future timelike signal can reach every sufficiently far reference region.
The parameter `R₀` is the first cutoff for the decreasing family `A`. -/
def chronoPastAtInfinity (g : BilinField M) (T : VecField M) (A : ℝ → Set M) (R₀ : ℝ) : Set M :=
  {x | ∀ R, R₀ ≤ R → x ∈ chronoPastSet g T (A R)}

/-- Points that can receive a future timelike signal from every far reference region. -/
def chronoFutureAtInfinity (g : BilinField M) (T : VecField M) (A : ℝ → Set M) (R₀ : ℝ) : Set M :=
  {x | ∀ R, R₀ ≤ R → x ∈ chronoFutureSet g T (A R)}

/-- Two-way communication with arbitrarily far reference regions of one end. -/
def domainOfOuterCommunicationsAtInfinity (g : BilinField M) (T : VecField M)
    (A : ℝ → Set M) (R₀ : ℝ) : Set M :=
  chronoFutureAtInfinity g T A R₀ ∩ chronoPastAtInfinity g T A R₀

/-- The boundary of the set of points that can send timelike signals arbitrarily far out. -/
def futureEventHorizonAtInfinity (g : BilinField M) (T : VecField M)
    (A : ℝ → Set M) (R₀ : ℝ) : Set M :=
  frontier (chronoPastAtInfinity g T A R₀)

end NoHair


