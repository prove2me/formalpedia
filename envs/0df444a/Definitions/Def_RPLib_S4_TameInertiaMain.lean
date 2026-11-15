-- Prove2me | Definitions.Def_RPLib_S4_TameInertiaMain
-- name    : RPLib_S4_TameInertiaMain
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:57:49.480739+00:00
-- url     : https://prove2.me/theorems/befd1de6-1604-46de-828d-610a61422c6c
-- title:
--   Tame inertia at a boundary place: $\mathrm{Hom}(I(Q), \mathbb{Z}/N) \cong \mathbb{Z}/N(-1)$
-- statement:
--   At a nonzero prime $Q$ of the pro-chart over a place $x$ where some $a \in A$ has a pole, with $N$ a unit in $A$ and $R_0$ and $\zeta$ a primitive $N$-th root of unity fixed by $I(Q)$, the Kummer character $\theta = \kappa_Z$ is a locally constant homomorphism $I(Q) \to \mathbb{Z}/N$ taking the value $1$, every locally constant homomorphism $\chi : I(Q) \to \mathbb{Z}/N$ is $k\theta$ for a unique $k$, and for $\varphi$ stabilising $Q$ with $\varphi\zeta = \zeta^w$ $$\theta(\sigma) = w\, \theta(\varphi^{-1}\sigma\varphi).$$
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapter IV, Section 2; A. Grothendieck, Revetements etales et groupe fondamental (SGA 1), Lecture Notes in Math. 224, Springer (1971), Expose XIII; A. Grothendieck, J. P. Murre, The Tame Fundamental Group of a Formal Neighbourhood of a Divisor with Normal Crossings on a Scheme, Lecture Notes in Math. 208, Springer (1971)

import Mathlib
import Definitions.Def_RPLib_S4_TameInertiaOnto
import Definitions.Def_RPLib_S4_TameInertiaUp

/-!
# Tame inertia, part Main: `Hom(I_x, ℤ/N) = ℤ/N(-1)` (S4-PD item (2))

At a boundary prime `Q` of the pro-chart (a pole at `x = Q ∩ R0`), with `N` a unit and `ζ` a primitive `N`-th root of
unity fixed by inertia: the Kummer character `θ = kchar ζ Z` of the radical `Z` of `exists_inertia_zeta_mul` is a
locally constant homomorphism `I(Q) → ℤ/N` taking the value `1`, every locally constant homomorphism
`χ : I(Q) → ℤ/N` is `k θ` for a unique `k`, and `θ` is twisted by the cyclotomic character: for `φ ∈ Pi1` stabilising
`Q` with `φ ζ = ζ ^ w`, `θ σ = w θ (φ⁻¹ σ φ)` (`exists_tame_char`). So `Hom(I(Q), ℤ/N) ≅ ℤ/N(-1)` as a module over the
decomposition group.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh Kummer

noncomputable section

theorem epow_one_eq {E : Type} [Field E] {N : ℕ} [NeZero N] {ζ : E} (hζ : IsPrimitiveRoot ζ N) :
    epow ζ (1 : ZMod N) = ζ := by
  rw [epow, ZMod.val_one_eq_one_mod, pow_mod_N hζ, pow_one]

variable {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

/-- **Tame inertia (item (2)).** The tame character `θ : I(Q) → ℤ/N` is a locally constant homomorphism with
`θ σ₀ = 1` for some `σ₀`, every locally constant homomorphism `I(Q) → ℤ/N` is a unique multiple of `θ`, and for
`φ` stabilising `Q` with `φ ζ = ζ ^ w` one has `θ σ = w * θ (φ⁻¹ σ φ)` (the twist by `ℤ/N(-1)`). -/
theorem exists_tame_char {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q)
    [Ring.HasFiniteQuotients R0] {p : ℕ} [Fact p.Prime] [CharP K p] {N : ℕ} [NeZero N]
    (hNA : IsUnit (N : A)) (hNR : IsUnit (N : R0)) {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N)
    (hζI : ∀ σ ∈ Q.inertia (Pi1 A K), σ ζ = ζ)
    (x : IsDedekindDomain.HeightOneSpectrum R0) (hx : x.asIdeal = Q.comap (algebraMap R0 (proChart A K R0)))
    {a : A} (ha : 1 < x.valuation K (algebraMap A K a)) :
    ∃ θ : Q.inertia (Pi1 A K) → ZMod N, IsLocallyConstant θ ∧ (∀ σ τ, θ (σ * τ) = θ σ + θ τ) ∧
      (∃ σ₀, θ σ₀ = 1) ∧ (∀ χ : Q.inertia (Pi1 A K) → ZMod N, IsLocallyConstant χ →
        (∀ σ τ, χ (σ * τ) = χ σ + χ τ) → ∃! k : ZMod N, ∀ σ, χ σ = k * θ σ) ∧
      ∀ φ : Pi1 A K, ∀ hφ : (∀ b : proChart A K R0, φ • b ∈ Q ↔ b ∈ Q), ∀ w : ZMod N, φ ζ = epow ζ w →
        ∀ σ (hσ : σ ∈ Q.inertia (Pi1 A K)), θ ⟨σ, hσ⟩ = w * θ ⟨φ⁻¹ * σ * φ, inertia_conj hφ hσ⟩ := by
  haveI := hQ.1
  obtain ⟨Z, hZ0, hZD, g, hgI, hgZ⟩ :=
    exists_inertia_zeta_mul (p := p) hQ (NeZero.pos N) hNA hζ.pow_eq_one x hx ha
  have hZI : ∀ σ ∈ Q.inertia (Pi1 A K), σ (Z ^ N) = Z ^ N := fun σ hσ => hZD σ (stab_of_mem_inertia hσ)
  let α : (maxUnram A K)ˣ := Units.mk0 Z hZ0
  have hα : α ∈ rad (Q.inertia (Pi1 A K)) N := fun σ hσ => hZI σ hσ
  have h1 : kchar hζ (Γ := Q.inertia (Pi1 A K)) α ⟨g, hgI⟩ = 1 := by
    rw [kchar_eq_iff hζ hα, epow_one_eq hζ]
    exact hgZ
  refine ⟨kchar hζ (Γ := Q.inertia (Pi1 A K)) α, isLocallyConstant_kchar hζ α, kchar_mul hζ hζI hα,
    ⟨⟨g, hgI⟩, h1⟩, fun χ hχc hχ => ?_, fun φ hφ w hw σ hσ => ?_⟩
  · obtain ⟨k, hk⟩ := exists_eq_mul_of_surj (fun χ' hc' h' => exists_ne_eq_of_family hQ hNR hζ hζI χ' hc' h')
      (isLocallyConstant_kchar hζ α) (kchar_mul hζ hζI hα) h1 hχc hχ
    refine ⟨k, hk, fun k' hk' => ?_⟩
    have h2 := (hk' ⟨g, hgI⟩).symm.trans (hk ⟨g, hgI⟩)
    rwa [h1, mul_one, mul_one] at h2
  · -- the twist: `kchar (φ α) = kchar α` since `φ Z / Z` is an `N`-th root of unity, then `kchar_conj`
    have hφΓ : ∀ τ ∈ Q.inertia (Pi1 A K), φ⁻¹ * τ * φ ∈ Q.inertia (Pi1 A K) := fun τ hτ => inertia_conj hφ hτ
    have hφα : Units.map (φ : maxUnram A K →* maxUnram A K) α ∈ rad (Q.inertia (Pi1 A K)) N := by
      intro τ hτ
      show τ ((φ Z) ^ N) = (φ Z) ^ N
      rw [← map_pow, hZD φ hφ]
      exact hZI τ hτ
    have hφZ0 : φ Z ≠ 0 := (map_ne_zero_iff _ φ.injective).2 hZ0
    have hβ1 : (φ Z / Z) ^ N = 1 := by
      rw [div_pow, ← map_pow, hZD φ hφ, div_self (pow_ne_zero _ hZ0)]
    let β : (maxUnram A K)ˣ := Units.mk0 (φ Z / Z) (div_ne_zero hφZ0 hZ0)
    have hβfix : β ∈ fixUnits (Q.inertia (Pi1 A K)) := by
      intro τ hτ
      show τ (φ Z / Z) = φ Z / Z
      rw [← epow_dlog hζ hβ1]
      exact map_epow (hζI τ hτ) _
    have hβα : Units.map (φ : maxUnram A K →* maxUnram A K) α = β * α := by
      apply Units.ext
      show φ Z = φ Z / Z * Z
      rw [div_mul_cancel₀ _ hZ0]
    have key := kchar_conj hζ φ hφΓ hw hα hφα ⟨σ, hσ⟩
    rw [hβα, kchar_mul_left hζ (fixUnits_le_rad _ N hβfix) hα, kchar_of_fix hζ hβfix, zero_add] at key
    exact key

end

end TameInertia
end RamanujanPetersson


