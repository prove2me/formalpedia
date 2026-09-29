-- Prove2me | Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixGenericFibreOpenImmersionDVR
-- name    : AlgebraicGeometry_MazurRapoportAppendixGenericFibreOpenImmersionDVR
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/bcac21df-8b84-54b9-8522-67a71825e668
-- title:
--   Generic fibre inclusion over a DVR: open immersion
-- statement:
--   Throughout, $R$ is a discrete valuation ring (a domain with `IsDiscreteValuationRing`) and $K$ is a field equipped with an $R$-algebra structure making it a fraction field of $R$; `specGenericFibreInclusion R K` denotes the morphism $\operatorname{Spec} K \to \operatorname{Spec} R$ obtained by applying $\operatorname{Spec}$ to $R \to K$.
--
--   On the ring side, `isLocalizationAway_of_irreducible` states that for any irreducible $\varpi \in R$ the fraction field $K$ is a localisation of $R$ away from $\varpi$, i.e. `IsLocalization.Away ϖ K`: inverting a single uniformiser already produces $K$. The proof compares the submonoid of powers of $\varpi$ with the non-zero-divisors of $R$, using that every non-zero element of a discrete valuation ring is associated to a power of a fixed irreducible. Specialisations record this for $\mathbb{Z}_p \subset \mathbb{Q}_p$ with uniformiser $p$ (as an instance, for every prime $p$) and for $p = 3$.
--
--   On the scheme side, `isOpenImmersion_specGenericFibreInclusion` is an instance asserting that `specGenericFibreInclusion R K` is an open immersion, obtained from the localisation description after choosing an irreducible element of $R$; `range_specGenericFibreInclusion_eq_basicOpen` identifies the set-theoretic image of the underlying map, for any irreducible $\varpi$, with the basic open set $D(\varpi) \subseteq \operatorname{Spec} R$. Two further statements record that this morphism is monic and flat. Finally, for each prime $p$ the morphism $\operatorname{Spec}\mathbb{Q}_p \to \operatorname{Spec}\mathbb{Z}_p$ is an open immersion which is not an isomorphism — the failure of invertibility being deduced from the emptiness of the type of sections of the inclusion over $\operatorname{Spec}\mathbb{Z}_p$ — and the conjunction of the two assertions is packaged as a single statement, with the case $p = 3$ also spelled out.
--
--   **Relation to Mathlib.** The notions used are Mathlib's: `IsLocalization.Away`, `AlgebraicGeometry.IsOpenImmersion` (with `IsOpenImmersion.of_isLocalization`), `PrimeSpectrum.basicOpen` and its localisation-away image computation, and the morphism classes `Mono` and `Flat`. Only the abbreviation `specGenericFibreInclusion` for $\operatorname{Spec}$ of the structure map $R \to K$ is the project's own.
--
--   **Where it is used.** This is part of the infrastructure for Néron models over a discrete valuation ring: the open immersion $\operatorname{Spec} K \hookrightarrow \operatorname{Spec} R$ is the base morphism along which generic fibres are formed in the Néron mapping property (`genericFibreRestrict`, `NeronUniqueExtension`), and the strictness statements at $\mathbb{Z}_p$, $\mathbb{Q}_p$ separate the generic fibre from the whole base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_MazurRapoportAppendixGenericFibreOpenImmersionDVR.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronModelInfra

section RingSide

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

theorem isLocalizationAway_of_irreducible {ϖ : R} (hϖ : Irreducible ϖ) :
    IsLocalization.Away ϖ K := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers ϖ)
      (nonZeroDivisors R) ?_ ?_).mpr inferInstance
  · intro x hx
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff x ϖ).mp hx
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hϖ.ne_zero)
  · intro r hr
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (nonZeroDivisors.ne_zero hr) hϖ
    exact ⟨ϖ ^ n, (Submonoid.mem_powers_iff _ ϖ).mpr ⟨n, rfl⟩, hn.dvd⟩

instance isLocalizationAway_uniformizer_zp (p : ℕ) [Fact p.Prime] :
    IsLocalization.Away (p : ℤ_[p]) ℚ_[p] :=
  isLocalizationAway_of_irreducible ℚ_[p] (PadicInt.irreducible_p (p := p))

theorem isLocalizationAway_uniformizer_three :
    IsLocalization.Away (3 : ℤ_[3]) ℚ_[3] := by
  simpa using isLocalizationAway_uniformizer_zp 3

end RingSide

section SchemeSide

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

instance isOpenImmersion_specGenericFibreInclusion :
    IsOpenImmersion (specGenericFibreInclusion R K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : IsLocalization.Away ϖ K := isLocalizationAway_of_irreducible K hϖ
  rw [specGenericFibreInclusion_eq]
  exact AlgebraicGeometry.IsOpenImmersion.of_isLocalization ϖ

theorem range_specGenericFibreInclusion_eq_basicOpen {ϖ : R} (hϖ : Irreducible ϖ) :
    Set.range (specGenericFibreInclusion R K).base =
      (PrimeSpectrum.basicOpen ϖ : Set (PrimeSpectrum R)) := by
  haveI : IsLocalization.Away ϖ K := isLocalizationAway_of_irreducible K hϖ
  have h := PrimeSpectrum.localization_away_comap_range K ϖ
  rw [specGenericFibreInclusion_eq]
  exact h

theorem mono_specGenericFibreInclusion_of_dvr :
    Mono (specGenericFibreInclusion R K) :=
  inferInstance

theorem flat_specGenericFibreInclusion_of_dvr :
    Flat (specGenericFibreInclusion R K) :=
  inferInstance

end SchemeSide

section PadicGates

theorem gate_isOpenImmersion_specGenericFibreInclusion_zp (p : ℕ) [Fact p.Prime] :
    IsOpenImmersion (specGenericFibreInclusion ℤ_[p] ℚ_[p]) :=
  isOpenImmersion_specGenericFibreInclusion ℤ_[p] ℚ_[p]

theorem gate_isOpenImmersion_specGenericFibreInclusion_three :
    IsOpenImmersion (specGenericFibreInclusion ℤ_[3] ℚ_[3]) :=
  gate_isOpenImmersion_specGenericFibreInclusion_zp 3

theorem not_isIso_specGenericFibreInclusion_zp (p : ℕ) [Fact p.Prime] :
    ¬ IsIso (specGenericFibreInclusion ℤ_[p] ℚ_[p]) := by
  intro h
  exact (isEmpty_schemeHomOver_id_specGenericFibreInclusion_zp p).false
    ⟨inv (specGenericFibreInclusion ℤ_[p] ℚ_[p]),
      IsIso.inv_hom_id (specGenericFibreInclusion ℤ_[p] ℚ_[p])⟩

theorem not_isIso_specGenericFibreInclusion_three :
    ¬ IsIso (specGenericFibreInclusion ℤ_[3] ℚ_[3]) :=
  not_isIso_specGenericFibreInclusion_zp 3

theorem gate_strictOpenImmersion_specGenericFibreInclusion_zp (p : ℕ) [Fact p.Prime] :
    IsOpenImmersion (specGenericFibreInclusion ℤ_[p] ℚ_[p]) ∧
      ¬ IsIso (specGenericFibreInclusion ℤ_[p] ℚ_[p]) :=
  ⟨gate_isOpenImmersion_specGenericFibreInclusion_zp p,
    not_isIso_specGenericFibreInclusion_zp p⟩

theorem gate_strictOpenImmersion_specGenericFibreInclusion_three :
    IsOpenImmersion (specGenericFibreInclusion ℤ_[3] ℚ_[3]) ∧
      ¬ IsIso (specGenericFibreInclusion ℤ_[3] ℚ_[3]) :=
  gate_strictOpenImmersion_specGenericFibreInclusion_zp 3

end PadicGates

end NeronModelInfra

/--
info: 'NeronModelInfra.isLocalizationAway_of_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.isLocalizationAway_of_irreducible

/--
info: 'NeronModelInfra.isLocalizationAway_uniformizer_zp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.isLocalizationAway_uniformizer_zp

/--
info: 'NeronModelInfra.isLocalizationAway_uniformizer_three' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.isLocalizationAway_uniformizer_three

/--
info: 'NeronModelInfra.isOpenImmersion_specGenericFibreInclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.isOpenImmersion_specGenericFibreInclusion

/--
info: 'NeronModelInfra.range_specGenericFibreInclusion_eq_basicOpen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.range_specGenericFibreInclusion_eq_basicOpen

/--
info: 'NeronModelInfra.mono_specGenericFibreInclusion_of_dvr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.mono_specGenericFibreInclusion_of_dvr

/--
info: 'NeronModelInfra.flat_specGenericFibreInclusion_of_dvr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.flat_specGenericFibreInclusion_of_dvr

/--
info: 'NeronModelInfra.gate_isOpenImmersion_specGenericFibreInclusion_zp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_isOpenImmersion_specGenericFibreInclusion_zp

/--
info: 'NeronModelInfra.gate_isOpenImmersion_specGenericFibreInclusion_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_isOpenImmersion_specGenericFibreInclusion_three

/--
info: 'NeronModelInfra.not_isIso_specGenericFibreInclusion_zp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.not_isIso_specGenericFibreInclusion_zp

/--
info: 'NeronModelInfra.not_isIso_specGenericFibreInclusion_three' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.not_isIso_specGenericFibreInclusion_three

/--
info: 'NeronModelInfra.gate_strictOpenImmersion_specGenericFibreInclusion_zp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_strictOpenImmersion_specGenericFibreInclusion_zp

/--
info: 'NeronModelInfra.gate_strictOpenImmersion_specGenericFibreInclusion_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_strictOpenImmersion_specGenericFibreInclusion_three

end


