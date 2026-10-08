-- Prove2me | Definitions.Def_ScenarioApproach_Fast_fast
-- name    : ScenarioApproach_Fast_fast
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T04:35:07.944621+00:00
-- url     : https://prove2.me/theorems/3da9e509-09a3-4446-9d88-3d9745dee1cc
-- title:
--   §8.3 — the output (ν*_F, ℓ*_F) of the FAST algorithm
-- statement:
--   FAST works on a sample of $N_1+N_2$ scenarios $\delta_1,\dots,\delta_{N_1+N_2}$, with $N_1\ge 1$.
--
--   1. It solves the scenario program with the first $N_1$ scenarios, obtaining the decision $\nu^*_{N_1}$.
--   2. In the **detuning step** it computes the smallest value $\ell^*_F$ such that $\ell(\nu^*_{N_1},\delta_i)\le\ell^*_F$ for $i=1,\dots,N_1+N_2$, that is,
--   $$
--   \ell^*_F=\max_{i=1,\dots,N_1+N_2}\ \ell(\nu^*_{N_1},\delta_i).
--   $$
--
--   The output of FAST is the pair $(\nu^*_F,\ell^*_F)$ with $\nu^*_F=\nu^*_{N_1}$.
--
--   The detuned cost $\ell^*_F$ is at least the first-stage optimal value $\ell^*_{N_1}$, because the maximum runs over all $N_1+N_2$ scenarios and not only over the $N_2$ new ones.
--
--   **Formalization Note** A sample is `ω : Fin (N₁ + N₂) → Δ`; the first stage uses `ω ∘ Fin.castAdd N₂` (indices $0,\dots,N_1-1$). The first-stage solution is supplied as a map `νstar : (Fin N₁ → Δ) → ℝ^{d-1}`; the theorems require that `νstar ω₁` solve the scenario program for every first-stage sample `ω₁`. The maximum is `Finset.sup'`, nonempty because `NeZero N₁`.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 94, §8.3 (description of FAST, Figure 8.5)

import Mathlib

namespace ScenarioApproach.Fast

/-- The first `N₁` scenarios `δ₁, …, δ_{N₁}` of a sample `ω = (δ₁, …, δ_{N₁+N₂})`. -/
def firstStage {N₁ N₂ : ℕ} {Δ : Type*} (ω : Fin (N₁ + N₂) → Δ) : Fin N₁ → Δ :=
  fun j => ω (Fin.castAdd N₂ j)

/-- The decision returned by FAST (§8.3): `ν*_F = ν*_{N₁}`, the solution `νstar` of the scenario
program with the first `N₁` scenarios. -/
def fastDecision {n N₁ N₂ : ℕ} {Δ : Type*}
    (νstar : (Fin N₁ → Δ) → EuclideanSpace ℝ (Fin n)) (ω : Fin (N₁ + N₂) → Δ) :
    EuclideanSpace ℝ (Fin n) :=
  νstar (firstStage ω)

/-- The detuned cost returned by FAST (§8.3): the smallest `ℓ*_F` with
`ℓ(ν*_{N₁}, δᵢ) ≤ ℓ*_F` for `i = 1, …, N₁ + N₂`, i.e. `max_{i ≤ N₁+N₂} ℓ(ν*_{N₁}, δᵢ)`, taken
over **all** `N₁ + N₂` scenarios. The maximum is over a nonempty set because `N₁ ≠ 0`. -/
noncomputable def fastCost {n N₁ N₂ : ℕ} [NeZero N₁] {Δ : Type*}
    (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ)
    (νstar : (Fin N₁ → Δ) → EuclideanSpace ℝ (Fin n)) (ω : Fin (N₁ + N₂) → Δ) : ℝ :=
  Finset.univ.sup' ⟨Fin.castAdd N₂ 0, Finset.mem_univ _⟩
    (fun i => ℓ (fastDecision νstar ω) (ω i))

end ScenarioApproach.Fast


