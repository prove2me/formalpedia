-- Prove2me | Definitions.Def_RPLib_S4_CDPack08b
-- name    : RPLib_S4_CDPack08b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:53:26.829881+00:00
-- url     : https://prove2.me/theorems/a4bf0b33-916d-4eb2-9327-179cd9d55dea
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 8b of 71
-- statement:
--   Part 8b of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_Cone_KumAll`: S4-PD (4)/(5), E1 part K: the Kummer-closure property over every `E₀' ⊇ constFieldU`
--   * `Def_RP_Cone_CdSub`: S4-PD (4)/(5), E1: `cd_l ≤ 1` for every CLOSED subgroup of `π₁^geo` (e.g. boundary inertia groups)
--   * `Def_RP_Cone_H3`: S4-PD (4), E4H3: the cone's `H³` vanishes
--   * `Def_RP_Cone_LocNorm`: S4-PD (4), E4L part 4: the normalised tame generator at a finite level
--   * `Def_RP_Cone_ResRad`: S4-PD (4), E4B part 5a: radicands in constant levels, and normalisation along constant extensions
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack08
import Definitions.Def_RPLib_S4_CDPack01
import Definitions.Def_RPLib_S4_CDPack02b
import Definitions.Def_RPLib_S4_KummerFix

/-!
# Curve-duality library package, part 8b of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_Cone_KumAll`: S4-PD (4)/(5), E1 part K: the Kummer-closure property over every `E₀' ⊇ constFieldU`
* `Def_RP_Cone_CdSub`: S4-PD (4)/(5), E1: `cd_l ≤ 1` for every CLOSED subgroup of `π₁^geo` (e.g. boundary inertia groups)
* `Def_RP_Cone_H3`: S4-PD (4), E4H3: the cone's `H³` vanishes
* `Def_RP_Cone_LocNorm`: S4-PD (4), E4L part 4: the normalised tame generator at a finite level
* `Def_RP_Cone_ResRad`: S4-PD (4), E4B part 5a: radicands in constant levels, and normalisation along constant extensions
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Cone_KumAll =====
section

/-!
# S4-PD (4)/(5), E1 part K: the Kummer-closure property over every `E₀' ⊇ constFieldU`

* `constLevel_le_map_of_le`: the constant levels `K(𝔽_{p^m})` lie in every `E` over `E₀' ⊇ constFieldU`;
* `kumClosure_of_picDiv_of_le`: `PicDivU A K p l` gives `KumClosure l E₀' K_U` for every intermediate field
  `E₀' ⊇ constFieldU` of `K_U / K` (e.g. the fixed field of a closed subgroup of `π₁^geo`, such as a boundary inertia
  group). The proof of `kumClosure_of_picDiv` never used finiteness of `E` over the base, only `E ⊇ constFieldU`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open IntermediateField IsDedekindDomain RamanujanPetersson.Kummer RamanujanPetersson.CurveCoh

noncomputable section

variable {K : Type} [Field K] (A : Type) [CommRing A] [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]
  {p : ℕ} [Fact p.Prime] [CharP K p]

/-- `𝔽_{p^m} ⊆ constFieldU ⊆ E₀'`, so the constant level `K(𝔽_{p^m})` lies in every `E ⊇ E₀'`. -/
theorem constLevel_le_map_of_le {e m : ℕ} (hm : 0 < m) {E₀ : IntermediateField K (maxUnram A K)}
    (hE₀ : constFieldU A K (p ^ e) ≤ E₀) (E : IntermediateField E₀ (maxUnram A K)) :
    constLevel K p m ≤ (E.restrictScalars K).map (maxUnram A K).val := by
  have hCU : constLevel K p m ≤ maxUnram A K := by
    rw [maxUnram_eq_sSup]
    exact le_sSup (constLevel_mem_unramSet A (p := p) hm)
  rw [constLevel, IntermediateField.adjoin_le_iff]
  intro x hx
  have hxC : x ∈ constLevel K p m := IntermediateField.subset_adjoin K _ hx
  have hxx : x ^ (p ^ m) = x := by
    rw [Polynomial.mem_rootSet] at hx
    have h2 := hx.2
    simp only [map_sub, map_pow, Polynomial.aeval_X] at h2
    exact sub_eq_zero.1 h2
  have hy : IsConst (p ^ e) (⟨x, hCU hxC⟩ : maxUnram A K) := ⟨m, hm, by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, show (p ^ e) ^ m = (p ^ m) ^ e by rw [← pow_mul, ← pow_mul, mul_comm]]
    exact pow_pow_eq_self hxx e⟩
  have hyE₀ : (⟨x, hCU hxC⟩ : maxUnram A K) ∈ E₀ := hE₀ (IntermediateField.subset_adjoin K _ hy)
  have hyE : (⟨x, hCU hxC⟩ : maxUnram A K) ∈ E := E.algebraMap_mem (⟨_, hyE₀⟩ : E₀)
  rw [IntermediateField.coe_map]
  exact ⟨_, hyE, rfl⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **The Kummer-closure property of `K_U / E₀'` for EVERY `E₀' ⊇ E₀ = constFieldU`** (no finiteness of `E₀'`
over `E₀`), from `Pic(V̄)/l = 0`. Same proof as `kumClosure_of_picDiv`. -/
theorem kumClosure_of_picDiv_of_le (hperf : ∀ (P : Ideal A) [P.IsMaximal], PerfectField P.ResidueField)
    (e : ℕ) (l : ℕ) [NeZero l] (hN : IsUnit (l : A)) (hPic : PicDivU A K p l)
    {E₀ : IntermediateField K (maxUnram A K)} (hE₀ : constFieldU A K (p ^ e) ≤ E₀) :
    KumClosure l E₀ (maxUnram A K) := by
  intro E L _ _ hGal b hb
  haveI := hGal
  have hb' : ∀ σ : L ≃ₐ[E] L, ∃ c : L, σ (b : L) = c ^ l * (b : L) := by
    intro σ
    obtain ⟨c, hc⟩ := hb σ
    refine ⟨(c : L), ?_⟩
    have h1 := congrArg Units.val hc
    rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val] at h1
    change σ (b : L) / (b : L) = (c : L) ^ l at h1
    rw [← h1, div_mul_cancel₀ _ b.ne_zero]
  -- the finite level `ML ∋ b`
  obtain ⟨ML, hML, hβML⟩ := exists_unramSet_of_finite A K {(((b : L) : maxUnram A K) : AlgebraicClosure K)}
    (fun x hx => by rw [Finset.mem_singleton.1 hx]; exact ((b : L) : maxUnram A K).2)
  haveI : FiniteDimensional K ML := hML.1
  haveI : IsGalois K ML := hML.2.1
  have hLU : ML ≤ maxUnram A K := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hML
  obtain ⟨bL, hbL⟩ : ∃ bL : ML, (bL : AlgebraicClosure K) = (((b : L) : maxUnram A K) : AlgebraicClosure K) :=
    ⟨⟨(((b : L) : maxUnram A K) : AlgebraicClosure K), hβML (IntermediateField.subset_adjoin K _ (by simp))⟩, rfl⟩
  -- `ME = ML ∩ E`
  obtain ⟨E', hE'⟩ : ∃ E' : IntermediateField K (AlgebraicClosure K),
      E' = (E.restrictScalars K).map (maxUnram A K).val := ⟨_, rfl⟩
  obtain ⟨ME, hMEd⟩ : ∃ ME : IntermediateField K (AlgebraicClosure K), ME = ML ⊓ E' := ⟨_, rfl⟩
  have hle : ME ≤ ML := by rw [hMEd]; exact inf_le_left
  have hMEE : ME ≤ E' := by rw [hMEd]; exact inf_le_right
  have hME : ∀ x : ML, (x : AlgebraicClosure K) ∈ ME ↔
      ∃ e : E, ((e : maxUnram A K) : AlgebraicClosure K) = x := by
    intro x
    rw [hMEd, IntermediateField.mem_inf]
    constructor
    · rintro ⟨-, h⟩
      rw [hE', ← SetLike.mem_coe, IntermediateField.coe_map] at h
      obtain ⟨y, hy, hyx⟩ := h
      exact ⟨⟨y, hy⟩, hyx⟩
    · rintro ⟨e, he⟩
      refine ⟨x.2, ?_⟩
      rw [hE', ← SetLike.mem_coe, IntermediateField.coe_map]
      exact ⟨(e : maxUnram A K), e.2, he⟩
  haveI : FiniteDimensional K ME := FiniteDimensional.of_injective
    (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion hle).injective
  haveI : Algebra.IsSeparable K ME := Algebra.IsSeparable.of_algHom (F := K) (E' := ML) (IntermediateField.inclusion hle)
  haveI : IsFractionRing (integralClosure A ML) ML := integralClosure.isFractionRing_of_finite_extension (A := A) K ML
  haveI : IsDedekindDomain (integralClosure A ML) := integralClosure.isDedekindDomain (A := A) (K := K) (L := ML)
  haveI : IsFractionRing (integralClosure A ME) ME := integralClosure.isFractionRing_of_finite_extension (A := A) K ME
  haveI : IsDedekindDomain (integralClosure A ME) := integralClosure.isDedekindDomain (A := A) (K := K) (L := ME)
  have hb0 : (b : L) ≠ 0 := b.ne_zero
  -- valuations of `bL` on a fibre over `B_ME` agree mod `l`
  have horb : ∀ w w' : HeightOneSpectrum (integralClosure A ML), underI A hle w = underI A hle w' →
      (l : ℤ) ∣ WithZero.log (w.valuation ML bL) - WithZero.log (w'.valuation ML bL) := fun w w' h =>
    orbit_dvd A E₀ E hLU hle hME (l : ℤ) bL
      (fun τ hτ w => hgrp_dvd A hperf _ E L l hLU hML (b : L) hb0 hb' bL hbL hτ w) w w' h
  -- the divisor `D = v(b)` on `B_ME`
  let w₀ : HeightOneSpectrum (integralClosure A ME) → HeightOneSpectrum (integralClosure A ML) :=
    fun P => Classical.choose (exists_underI_eq A hle P)
  have hw₀ : ∀ P, underI A hle (w₀ P) = P := fun P => Classical.choose_spec (exists_underI_eq A hle P)
  let D : HeightOneSpectrum (integralClosure A ME) → ℤ := fun P => WithZero.log ((w₀ P).valuation ML bL)
  have hfin : (Function.support D).Finite := by
    refine ((finite_log_val_ne_zero (B := integralClosure A ML) bL).image (underI A hle)).subset ?_
    intro P hP
    exact ⟨w₀ P, hP, hw₀ P⟩
  obtain ⟨m, hm, a, ha0, hdivD⟩ := hPic ME inferInstance (hle.trans hLU) D hfin
  -- the level `M = ML ⊔ C_m`
  have hM : ML ⊔ constLevel K p m ∈ unramSet A K := sup_mem_unramSet A K hML (constLevel_mem_unramSet A hm)
  haveI : FiniteDimensional K ↥(ML ⊔ constLevel K p m) := hM.1
  haveI : IsGalois K ↥(ML ⊔ constLevel K p m) := hM.2.1
  have hMC : ME ⊔ constLevel K p m ≤ ML ⊔ constLevel K p m := sup_le_sup_right hle _
  have hLM : ML ≤ ML ⊔ constLevel K p m := le_sup_left
  haveI : FiniteDimensional K ↥(ME ⊔ constLevel K p m) := FiniteDimensional.of_injective
    (IntermediateField.inclusion hMC).toLinearMap (IntermediateField.inclusion hMC).injective
  haveI : Algebra.IsSeparable K ↥(ME ⊔ constLevel K p m) :=
    Algebra.IsSeparable.of_algHom (F := K) (E' := ↥(ML ⊔ constLevel K p m)) (IntermediateField.inclusion hMC)
  haveI : IsFractionRing (integralClosure A ↥(ML ⊔ constLevel K p m)) ↥(ML ⊔ constLevel K p m) :=
    integralClosure.isFractionRing_of_finite_extension (A := A) K _
  haveI : IsDedekindDomain (integralClosure A ↥(ML ⊔ constLevel K p m)) :=
    integralClosure.isDedekindDomain (A := A) (K := K) (L := ↥(ML ⊔ constLevel K p m))
  haveI : IsFractionRing (integralClosure A ↥(ME ⊔ constLevel K p m)) ↥(ME ⊔ constLevel K p m) :=
    integralClosure.isFractionRing_of_finite_extension (A := A) K _
  haveI : IsDedekindDomain (integralClosure A ↥(ME ⊔ constLevel K p m)) :=
    integralClosure.isDedekindDomain (A := A) (K := K) (L := ↥(ME ⊔ constLevel K p m))
  have hbL0 : bL ≠ 0 := by
    intro h
    apply hb0
    have h2 : (((b : L) : maxUnram A K) : AlgebraicClosure K) = 0 := by rw [← hbL, h, ZeroMemClass.coe_zero]
    simpa using h2
  have hbM0 : IntermediateField.inclusion hLM bL ≠ 0 := (map_ne_zero _).2 hbL0
  have ha'0 : IntermediateField.inclusion hMC a ≠ 0 := (map_ne_zero _).2 ha0
  have hdiv : ∀ W : HeightOneSpectrum (integralClosure A ↥(ML ⊔ constLevel K p m)), (l : ℤ) ∣
      WithZero.log (W.valuation (↥(ML ⊔ constLevel K p m))
        (IntermediateField.inclusion hMC a * IntermediateField.inclusion hLM bL)) := by
    intro W
    rw [log_val_mul W ha'0 hbM0, ← val_underI A hMC hM hperf W a, ← val_underI A hLM hM hperf W bL]
    have hP : underI A hle (underI A hLM W) =
        underI A (le_sup_left : ME ≤ ME ⊔ constLevel K p m) (underI A hMC W) := by
      rw [underI_trans, underI_trans]
    have h1 : (l : ℤ) ∣ WithZero.log ((w₀ (underI A (le_sup_left : ME ≤ ME ⊔ constLevel K p m)
        (underI A hMC W))).valuation ML bL) +
        WithZero.log ((underI A hMC W).valuation (↥(ME ⊔ constLevel K p m)) a) := hdivD (underI A hMC W)
    have h2 := horb (underI A hLM W) _ (hP.trans (hw₀ _).symm)
    have h3 := dvd_add h1 h2
    rwa [show ∀ x y z : ℤ, x + y + (z - x) = y + z from fun x y z => by ring] at h3
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq
    (((IntermediateField.inclusion hMC a * IntermediateField.inclusion hLM bL : ↥(ML ⊔ constLevel K p m)) :
      AlgebraicClosure K)) (Nat.pos_of_ne_zero (NeZero.ne l))
  have hγU : γ ∈ maxUnram A K := root_mem_maxUnram_of_dvd A hM hN (mul_ne_zero ha'0 hbM0) hdiv hγ
  -- `a ∈ E`
  have haE' : (a : AlgebraicClosure K) ∈ E' := sup_le hMEE (by rw [hE']; exact constLevel_le_map_of_le A hm hE₀ E) a.2
  rw [← SetLike.mem_coe, hE', IntermediateField.coe_map] at haE'
  obtain ⟨y, hyE, hya⟩ := haE'
  refine ⟨⟨y, hyE⟩, ?_, ⟨γ, hγU⟩, Subtype.ext ?_⟩
  · intro h0
    apply ha0
    apply Subtype.ext
    have hy0 : y = 0 := congrArg Subtype.val h0
    rw [ZeroMemClass.coe_zero, ← hya, hy0, map_zero]
  · simp only [IntermediateField.coe_pow, IntermediateField.coe_mul, IntermediateField.algebraMap_apply]
    rw [hγ, IntermediateField.coe_mul]
    exact congrArg₂ (· * ·) hya.symm hbL

end

end RamanujanPetersson.CdOne

end

-- ===== S4.Def_RP_Cone_CdSub =====
section

/-!
# S4-PD (4)/(5), E1: `cd_l ≤ 1` for every CLOSED subgroup of `π₁^geo` (e.g. boundary inertia groups)

`Δ ≤ π₁^geo` closed. `E₀' := K_U^Δ ⊇ constFieldU`, `Gal(K_U/E₀') ≅ Δ` (closed: infinite Galois correspondence;
homeomorphism: compact to Hausdorff), and `hypL_of_field` applies to `K_U / E₀'`:
* C1: `isC1_subfield` (a subfield of an algebraic extension containing a C1 field is C1) with Tsen
  (`isC1_constFieldU`), giving `allC1_of_le`;
* Kummer closure: `kumClosure_of_picDiv_of_le` (from `PicDivU`).
Results: `hypL_of_closed`, **`h2_closed_eq_zero`** (`H²(Δ, M) = 0` for finite `lⁿ`-torsion `M` with open kernel),
`inertia_isClosed` (the inertia group `Q.inertia (Pi1 A K)` of a prime of the pro-chart is closed) and
`inertia_inf_isClosed` (so `I_s ∩ π₁^geo` is a closed subgroup of `π₁^geo`).
No local ramification theory is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace RamanujanPetersson.CdOne

open IntermediateField RamanujanPetersson.Tsen RamanujanPetersson.Kummer RamanujanPetersson.CurveCoh Topology

/-- A subfield `S` of an algebraic extension `Ω/F` containing the image of a C1 field `F` is C1. -/
theorem isC1_subfield {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    (hF : IsC1 F) (S : Subfield Ω) (hS : ∀ x : F, algebraMap F Ω x ∈ S) : IsC1 S := by
  letI : Algebra F S := ((algebraMap F Ω).codRestrict S hS).toAlgebra
  let f : S →ₐ[F] Ω := { S.subtype with commutes' := fun _ => rfl }
  haveI : Algebra.IsAlgebraic F S := ⟨fun y => by
    obtain ⟨q, hq0, hq⟩ := Algebra.IsAlgebraic.isAlgebraic (R := F) (y : Ω)
    refine ⟨q, hq0, f.toRingHom.injective ?_⟩
    rw [map_zero]
    show f (Polynomial.aeval y q) = 0
    rw [← Polynomial.aeval_algHom_apply]
    exact hq⟩
  exact hF.of_algebraic

section Closed

variable {K : Type} [Field K] (A : Type) [CommRing A] [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]
  {p : ℕ} [Fact p.Prime] [CharP K p]
  (Fq : Type) [Field Fq] [Fintype Fq] [Algebra Fq K] {e : ℕ} (he : 0 < e) (hq : Fintype.card Fq = p ^ e)
  [Algebra (RatFunc Fq) K] [IsScalarTower Fq (RatFunc Fq) K] [Algebra.IsAlgebraic (RatFunc Fq) K]

include he hq in
/-- Every extension of an intermediate field `E₀' ⊇ constFieldU` inside `K_U` is C1 (Tsen). -/
theorem allC1_of_le {E₀ : IntermediateField K (maxUnram A K)} (hE₀ : constFieldU A K (p ^ e) ≤ E₀) :
    AllC1 E₀ (maxUnram A K) := fun E _ => by
  haveI : Algebra.IsAlgebraic (constFieldU A K (p ^ e)) (maxUnram A K) :=
    Algebra.IsAlgebraic.tower_top (K := K) (constFieldU A K (p ^ e))
  exact isC1_subfield (isC1_constFieldU A K Fq he hq) E.toSubfield
    (fun x => E.algebraMap_mem (⟨(x : maxUnram A K), hE₀ x.2⟩ : E₀))

/-- `Δ ≃* Gal(K_U / E₀)` when `Δ` is the fixing subgroup of `E₀`. -/
noncomputable def fixEquiv (E₀ : IntermediateField K (maxUnram A K)) (Δ : Subgroup (Pi1 A K))
    (h : E₀.fixingSubgroup = Δ) : Δ ≃* Gal(maxUnram A K / E₀) :=
  (MulEquiv.subgroupCongr h.symm).trans (fixingSubgroupEquiv E₀)

theorem fixEquiv_apply (E₀ : IntermediateField K (maxUnram A K)) (Δ : Subgroup (Pi1 A K))
    (h : E₀.fixingSubgroup = Δ) (σ : Δ) (x : maxUnram A K) :
    fixEquiv A E₀ Δ h σ x = (σ : Pi1 A K) x := rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem fixEquiv_continuous (E₀ : IntermediateField K (maxUnram A K)) (Δ : Subgroup (Pi1 A K))
    (h : E₀.fixingSubgroup = Δ) : Continuous (fixEquiv A E₀ Δ h) := by
  refine continuous_of_continuousAt_one (fixEquiv A E₀ Δ h) ?_
  intro s hs
  rw [map_one] at hs
  rw [Filter.mem_map]
  obtain ⟨F, hF, hFs⟩ := (krullTopology_mem_nhds_one_iff E₀ (maxUnram A K) s).1 hs
  have := hF
  let b := Module.finBasis E₀ F
  let W : Set Δ := Subtype.val ⁻¹' ⋂ i, (fixElt A K (b i : maxUnram A K) : Set (Pi1 A K))
  have hW : IsOpen W :=
    continuous_subtype_val.isOpen_preimage _ (isOpen_iInter_of_finite fun i => fixElt_isOpen A K _)
  have h1 : (1 : Δ) ∈ W :=
    show ((1 : Δ) : Pi1 A K) ∈ ⋂ i, (fixElt A K (b i : maxUnram A K) : Set (Pi1 A K)) from
      Set.mem_iInter.2 fun i => (fixElt A K _).one_mem
  refine Filter.mem_of_superset (hW.mem_nhds h1) ?_
  intro σ hσ
  have hσ' : ∀ i, (σ : Pi1 A K) (b i : maxUnram A K) = (b i : maxUnram A K) := fun i =>
    (Set.mem_iInter.1 (show (σ : Pi1 A K) ∈ ⋂ i, (fixElt A K (b i : maxUnram A K) : Set (Pi1 A K)) from hσ)) i
  apply hFs
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hlin : (fixEquiv A E₀ Δ h σ).toLinearMap ∘ₗ F.val.toLinearMap = F.val.toLinearMap :=
    b.ext fun i => hσ' i
  exact LinearMap.congr_fun hlin ⟨x, hx⟩

theorem fixEquiv_symm_continuous (E₀ : IntermediateField K (maxUnram A K)) (Δ : Subgroup (Pi1 A K))
    (h : E₀.fixingSubgroup = Δ) [CompactSpace Δ] : Continuous (fixEquiv A E₀ Δ h).symm := by
  have : T2Space Gal(maxUnram A K / E₀) := krullTopology_t2
  exact (Continuous.homeoOfEquivCompactToT2 (f := (fixEquiv A E₀ Δ h).toEquiv)
    (fixEquiv_continuous A E₀ Δ h)).symm.continuous

include he hq in
/-- **`HypL l Δ`** (hence `cd_l(Δ) ≤ 1`) for every closed subgroup `Δ ≤ π₁^geo`, given `Pic(V̄)/l = 0`. -/
theorem hypL_of_closed (hperf : ∀ (P : Ideal A) [P.IsMaximal], PerfectField P.ResidueField)
    (l : ℕ) [Fact l.Prime] (hN : IsUnit (l : A)) (hPic : PicDivU A K p l)
    (Δ : Subgroup (Pi1 A K)) (hΔ : IsClosed (Δ : Set (Pi1 A K))) (hΔg : Δ ≤ pi1geo A K (p ^ e)) :
    HypL l Δ := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hl : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap A K) l]
    exact (hN.map (algebraMap A K)).ne_zero
  haveI : CompactSpace Δ := isCompact_iff_compactSpace.mp hΔ.isCompact
  have hfix : (fixedField Δ).fixingSubgroup = Δ :=
    InfiniteGalois.fixingSubgroup_fixedField (⟨Δ, hΔ⟩ : ClosedSubgroup (Pi1 A K))
  have hE₀ : constFieldU A K (p ^ e) ≤ fixedField Δ :=
    (IntermediateField.le_iff_le Δ _).2 (hΔg.trans (fixingSubgroup_constFieldU A K (p ^ e)).ge)
  obtain ⟨ζ, hζ⟩ := exists_zeta_constFieldU A K he l hl
  have hζ' : IsPrimitiveRoot (IntermediateField.inclusion hE₀ ζ) l :=
    hζ.map_of_injective (IntermediateField.inclusion hE₀).injective
  exact hypL_of_equiv l (fixEquiv A _ Δ hfix) (fixEquiv_continuous A _ Δ hfix)
    (fixEquiv_symm_continuous A _ Δ hfix)
    (hypL_of_field l hζ' (allC1_of_le A Fq he hq hE₀) (kumClosure_of_picDiv_of_le A hperf e l hN hPic hE₀))

include he hq in
/-- **`H²(Δ, M) = 0`** for a closed subgroup `Δ ≤ π₁^geo` and a finite `lⁿ`-torsion `π₁(U)`-module `M` with open
kernel (locally constant cochains on `Δ`), given `Pic(V̄)/l = 0`. -/
theorem h2_closed_eq_zero (hperf : ∀ (P : Ideal A) [P.IsMaximal], PerfectField P.ResidueField)
    (l : ℕ) [Fact l.Prime] (hN : IsUnit (l : A)) (hPic : PicDivU A K p l)
    (Δ : Subgroup (Pi1 A K)) (hΔ : IsClosed (Δ : Set (Pi1 A K))) (hΔg : Δ ≤ pi1geo A K (p ^ e))
    {k : Type*} [CommRing k] {M : Type u} [AddCommGroup M] [Module k M] (ρ : Representation k (Pi1 A K) M)
    (n : ℕ) [Finite M] (hM : ∀ m : M, (l ^ n) • m = 0) (hρ : IsOpen (ρ.ker : Set (Pi1 A K)))
    {f : Δ × Δ → M} (hf : IsLocallyConstant f)
    (hc : ∀ g h j : Δ, f (g * h, j) + f (g, h) = ρ g (f (h, j)) + f (g, h * j)) :
    ∃ b : Δ → M, IsLocallyConstant b ∧ ∀ g h : Δ, f (g, h) = ρ g (b h) - b (g * h) + b g := by
  haveI : CompactSpace Δ := isCompact_iff_compactSpace.mp hΔ.isCompact
  exact h2_eq_zero ρ Δ l (hypL_of_closed A Fq he hq hperf l hN hPic Δ hΔ hΔg) n hM hρ hf hc

end Closed

section Inertia

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
  (R0 : Type) [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]

/-- The orbit map `σ ↦ σ • x` on the pro-chart is locally constant (stabilisers are open). -/
theorem isLocallyConstant_smul_proChart (x : proChart A K R0) :
    IsLocallyConstant fun σ : Pi1 A K => σ • x := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro σ
  have h1 : (fixElt A K (x : maxUnram A K) : Set (Pi1 A K)) ∈ 𝓝 (1 : Pi1 A K) :=
    (fixElt_isOpen A K _).mem_nhds (Subgroup.one_mem _)
  have h2 : Filter.Tendsto (fun τ : Pi1 A K => σ⁻¹ * τ) (𝓝 σ) (𝓝 1) := by
    have := (continuous_mul_left σ⁻¹).tendsto σ
    rwa [inv_mul_cancel] at this
  filter_upwards [h2 h1] with τ hτ
  have hτ' : (σ⁻¹ * τ) (x : maxUnram A K) = x := hτ
  apply Subtype.ext
  show τ (x : maxUnram A K) = σ (x : maxUnram A K)
  calc τ (x : maxUnram A K) = (σ * (σ⁻¹ * τ)) (x : maxUnram A K) := by rw [mul_inv_cancel_left]
    _ = σ (x : maxUnram A K) := by rw [AlgEquiv.mul_apply, hτ']

/-- The inertia group of an ideal of the pro-chart is closed in `π₁(U)`. -/
theorem inertia_isClosed (Q : Ideal (proChart A K R0)) :
    IsClosed ((Q.inertia (Pi1 A K) : Subgroup (Pi1 A K)) : Set (Pi1 A K)) := by
  have h : ((Q.inertia (Pi1 A K) : Subgroup (Pi1 A K)) : Set (Pi1 A K)) =
      ⋂ x : proChart A K R0, (fun σ : Pi1 A K => σ • x) ⁻¹' {y | y - x ∈ Q} := by
    ext σ
    exact ⟨fun h => Set.mem_iInter.2 fun x => h x, fun h x => Set.mem_iInter.1 h x⟩
  rw [h]
  exact isClosed_iInter fun x =>
    ⟨by rw [← Set.preimage_compl]; exact isLocallyConstant_smul_proChart A K R0 x _⟩

/-- `I_Q ∩ π₁^geo` is closed. -/
theorem inertia_inf_isClosed (q : ℕ) (Q : Ideal (proChart A K R0)) :
    IsClosed ((Q.inertia (Pi1 A K) ⊓ pi1geo A K q : Subgroup (Pi1 A K)) : Set (Pi1 A K)) := by
  rw [Subgroup.coe_inf]
  exact (inertia_isClosed A K R0 Q).inter (pi1geo_isClosed A K q)

end Inertia

end RamanujanPetersson.CdOne

end

-- ===== S4.Def_RP_Cone_H3 =====
section

/-!
# S4-PD (4), E4H3: the cone's `H³` vanishes

The cone's `H³` is `Π_s H²(Γ ⊓ I_s, M)`. For `Γ = π₁^geo` and closed `I_s` every factor vanishes by `cd_l ≤ 1` for
closed subgroups of `π₁^geo` (`CdOne.h2_closed_eq_zero`, with `Pic(V̄)/l = 0` as the explicit hypothesis). Stated in the
`H2All` form consumed by `PerfectCx` (`hall`, `hallI` of `ResHyp.h2Equiv`):
* `h2All_closed`, `h2All_geo` (`hall`), `h2All_geo_inf_inertia` (`hallI`, any ideal `Q` of a pro-chart).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open IntermediateField RamanujanPetersson.Kummer RamanujanPetersson.CurveCoh RamanujanPetersson.PerfectCx

section H3

variable {K : Type} [Field K] (A : Type) [CommRing A] [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]
  {p : ℕ} [Fact p.Prime] [CharP K p]
  (Fq : Type) [Field Fq] [Fintype Fq] [Algebra Fq K] {e : ℕ} (he : 0 < e) (hq : Fintype.card Fq = p ^ e)
  [Algebra (RatFunc Fq) K] [IsScalarTower Fq (RatFunc Fq) K] [Algebra.IsAlgebraic (RatFunc Fq) K]

include he hq in
/-- `H²(Δ, -) = 0` (`H2All`) for a closed `Δ ≤ π₁^geo`, given `Pic(V̄)/l = 0`. -/
theorem h2All_closed (hperf : ∀ (P : Ideal A) [P.IsMaximal], PerfectField P.ResidueField)
    (l : ℕ) [Fact l.Prime] (hN : IsUnit (l : A)) (hPic : PicDivU A K p l)
    (Δ : Subgroup (Pi1 A K)) (hΔ : IsClosed (Δ : Set (Pi1 A K))) (hΔg : Δ ≤ pi1geo A K (Fintype.card Fq))
    (Λ : Type) [CommRing Λ] (n : ℕ) : H2All Λ (Pi1 A K) Δ l n := by
  have hΔg' : Δ ≤ pi1geo A K (p ^ e) := by rw [← hq]; exact hΔg
  exact fun _ _ _ ρ _ hM hρ _ hf hc => h2_closed_eq_zero A Fq he hq hperf l hN hPic Δ hΔ hΔg' ρ n hM hρ hf hc

include he hq in
/-- `hall`: `H²(π₁^geo, -) = 0`. -/
theorem h2All_geo (hperf : ∀ (P : Ideal A) [P.IsMaximal], PerfectField P.ResidueField)
    (l : ℕ) [Fact l.Prime] (hN : IsUnit (l : A)) (hPic : PicDivU A K p l) (Λ : Type) [CommRing Λ] (n : ℕ) :
    H2All Λ (Pi1 A K) (pi1geo A K (Fintype.card Fq)) l n :=
  h2All_closed A Fq he hq hperf l hN hPic _ (pi1geo_isClosed A K _) le_rfl Λ n

variable {R0 : Type} [CommRing R0] [Algebra R0 K]

include he hq in
/-- `hallI` (**cone `H³ = 0`**): `H²(π₁^geo ∩ I(Q), -) = 0` for an ideal `Q` of the pro-chart. -/
theorem h2All_geo_inf_inertia (hperf : ∀ (P : Ideal A) [P.IsMaximal], PerfectField P.ResidueField)
    (l : ℕ) [Fact l.Prime] (hN : IsUnit (l : A)) (hPic : PicDivU A K p l) (Q : Ideal (proChart A K R0))
    (Λ : Type) [CommRing Λ] (n : ℕ) :
    H2All Λ (Pi1 A K) (pi1geo A K (Fintype.card Fq) ⊓ Q.inertia (Pi1 A K)) l n := by
  refine h2All_closed A Fq he hq hperf l hN hPic _ ?_ inf_le_left Λ n
  rw [inf_comm]
  exact inertia_inf_isClosed A K R0 _ Q

end H3

end RamanujanPetersson.CdOne

end

-- ===== S4.Def_RP_Cone_LocNorm =====
section

/-!
# S4-PD (4), E4L part 4: the normalised tame generator at a finite level

* `zmod_exists_mul_of_nsmul`, `zmod_exists_unit_mul`: in `ℤ/N`, `ord(c) • g = 0` makes `g` a multiple of `c`, and
  elements of the same additive order differ by a unit.
* `exists_norm_tau` (N): for a boundary prime `Q`, a finite level `M ≤ K_U` with the prime `v = Q ∩ B_M`, and
  `J = I(Q) ∩ Fix(M)` (of finite exponent-index in `I(Q)`), there are `τ ∈ J` and a locally constant character
  `θ : J → ℤ/N` with `θ τ = 1`, invariant under `I(Q)`-conjugation, such that every locally constant character
  `χ : J → ℤ/N` is `χ(τ) • θ`, and `τ` is normalised by valuations: `kchar(α)(τ) = v(α ^ N) mod N` whenever
  `α ^ N ∈ M`. Uses `tame_inertia_le`, the valuation criterion `kchar_eq_of_val_lev` and the ramification converse
  `dvd_val_of_fix_lev`, through the cyclic subgroup of `ℤ/N` of valuations of level-`M` radicands.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh IsDedekindDomain Kummer

noncomputable section

section ZModAux

/-- In `ℤ/N`, an element killed by the additive order of `c` is a multiple of `c`. -/
theorem zmod_exists_mul_of_nsmul {N : ℕ} [NeZero N] (c g : ZMod N) (h : addOrderOf c • g = 0) :
    ∃ x : ZMod N, g = x * c := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hord : addOrderOf c = N / N.gcd c.val := by
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    exact ZMod.addOrderOf_coe _ (NeZero.ne N)
  rw [hord, nsmul_eq_mul, ← ZMod.natCast_zmod_val g, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h
  have hq : 0 < N / N.gcd c.val := Nat.div_pos (Nat.gcd_le_left _ hN) (Nat.gcd_pos_of_pos_left _ hN)
  have hdvd : N.gcd c.val ∣ g.val := by
    refine (Nat.mul_dvd_mul_iff_left hq).1 ?_
    rw [Nat.div_mul_cancel (Nat.gcd_dvd_left N c.val)]
    exact h
  obtain ⟨t, ht⟩ := hdvd
  have hb : ((N.gcd c.val : ℕ) : ZMod N) = c * (N.gcdB c.val : ZMod N) := by
    have h1 := congrArg (fun z : ℤ => (z : ZMod N)) (Nat.gcd_eq_gcd_ab N c.val)
    simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul, ZMod.natCast_self, zero_mul, zero_add,
      ZMod.natCast_zmod_val] at h1
    exact h1
  refine ⟨(N.gcdB c.val : ZMod N) * t, ?_⟩
  rw [← ZMod.natCast_zmod_val g, ht, Nat.cast_mul, hb]
  ring

/-- In `ℤ/N`, elements killing each other's additive orders differ by a unit. -/
theorem zmod_exists_unit_mul {N : ℕ} [NeZero N] {c g : ZMod N} (h1 : addOrderOf c • g = 0)
    (h2 : addOrderOf g • c = 0) : ∃ u : (ZMod N)ˣ, g = u * c := by
  obtain ⟨x, hx⟩ := zmod_exists_mul_of_nsmul c g h1
  obtain ⟨y, hy⟩ := zmod_exists_mul_of_nsmul g c h2
  have hmN : addOrderOf c ∣ N :=
    addOrderOf_dvd_of_nsmul_eq_zero (by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul])
  have : NeZero (addOrderOf c) := ⟨(addOrderOf_pos c).ne'⟩
  have hz : ∀ z : ZMod N, z * c = 0 ↔ ZMod.castHom hmN (ZMod (addOrderOf c)) z = 0 := by
    intro z
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff, addOrderOf_dvd_iff_nsmul_eq_zero,
      nsmul_eq_mul, ZMod.natCast_zmod_val]
  have hxy : ZMod.castHom hmN (ZMod (addOrderOf c)) x * ZMod.castHom hmN (ZMod (addOrderOf c)) y = 1 := by
    have h3 : (x * y - 1) * c = 0 := by linear_combination -hy - y * hx
    have h4 := (hz _).1 h3
    rw [map_sub, map_mul, map_one, sub_eq_zero] at h4
    exact h4
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hmN ⟨_, _, hxy, by rw [mul_comm]; exact hxy⟩
  refine ⟨u, ?_⟩
  have hu' : ZMod.castHom hmN (ZMod (addOrderOf c)) (u : ZMod N) = ZMod.castHom hmN (ZMod (addOrderOf c)) x :=
    congrArg Units.val hu
  have h5 : ((u : ZMod N) - x) * c = 0 := (hz _).2 (by rw [map_sub, hu', sub_self])
  linear_combination hx - h5

end ZModAux

variable {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- (N) The normalised tame generator of `J = I(Q) ∩ Fix(M)`: `θ τ = 1`, every locally constant character is
`χ(τ) • θ`, and `kchar(α)(τ) = v(α ^ N) mod N` for every radical `α` with `α ^ N ∈ M`. -/
theorem exists_norm_tau {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q)
    [Ring.HasFiniteQuotients R0] {p : ℕ} [Fact p.Prime] [CharP K p] {N d : ℕ} [NeZero N] [NeZero d]
    (hNA : IsUnit ((N * d : ℕ) : A)) (hNR : IsUnit ((N * d : ℕ) : R0)) {ζ : maxUnram A K}
    (hζ : IsPrimitiveRoot ζ (N * d)) (hζI : ∀ σ ∈ Q.inertia (Pi1 A K), σ ζ = ζ)
    (x : HeightOneSpectrum R0) (hx : x.asIdeal = Q.comap (algebraMap R0 (proChart A K R0)))
    {a : A} (ha : 1 < x.valuation K (algebraMap A K a))
    {M : IntermediateField K (AlgebraicClosure K)} (hMU : M ≤ maxUnram A K) [FiniteDimensional K M]
    [IsDedekindDomain (integralClosure R0 M)] [IsFractionRing (integralClosure R0 M) M]
    (v : HeightOneSpectrum (integralClosure R0 M)) (hv : v.asIdeal = Q.comap (inclU R0 hMU))
    {J : Subgroup (Pi1 A K)}
    (hJ : ∀ σ, σ ∈ J ↔ σ ∈ Q.inertia (Pi1 A K) ∧
      ∀ y : maxUnram A K, (y : AlgebraicClosure K) ∈ M → σ y = y)
    (k : ℕ) (hd : ∀ σ ∈ Q.inertia (Pi1 A K), σ ^ (p ^ k * d) ∈ J)
    {ζN : maxUnram A K} (hζN : IsPrimitiveRoot ζN N) (hζNJ : ∀ σ ∈ J, σ ζN = ζN) :
    ∃ τ : J, ∃ θ : J → ZMod N, IsLocallyConstant θ ∧ (∀ σ σ', θ (σ * σ') = θ σ + θ σ') ∧ θ τ = 1 ∧
      (∀ g ∈ Q.inertia (Pi1 A K), ∀ σ (hσ : σ ∈ J) (hσ' : g⁻¹ * σ * g ∈ J),
        θ ⟨g⁻¹ * σ * g, hσ'⟩ = θ ⟨σ, hσ⟩) ∧
      (∀ χ : J → ZMod N, IsLocallyConstant χ → (∀ σ σ', χ (σ * σ') = χ σ + χ σ') →
        ∀ σ, χ σ = χ τ * θ σ) ∧
      ∀ (α : (maxUnram A K)ˣ) (b : M), (α : maxUnram A K) ^ N = IntermediateField.inclusion hMU b →
        kchar hζN (Γ := J) α τ = ((WithZero.log (v.valuation M b) : ℤ) : ZMod N) := by
  classical
  have := hQ.1
  have hN : IsUnit (N : R0) := by
    have h := hNR
    rw [Nat.cast_mul] at h
    exact isUnit_of_mul_isUnit_left h
  have hJle : J ≤ Q.inertia (Pi1 A K) := fun σ hσ => ((hJ σ).1 hσ).1
  have hJM : ∀ σ ∈ J, ∀ y : maxUnram A K, (y : AlgebraicClosure K) ∈ M → σ y = y :=
    fun σ hσ => ((hJ σ).1 hσ).2
  obtain ⟨θ, τ₀, hθc, hθm, hθ1, hθconj, hθall⟩ := tame_inertia_le hQ hNA hNR hζ hζI x hx ha hJle k hd
  -- radicals of the level `M`
  have hrad : ∀ (α : (maxUnram A K)ˣ) (b : M), (α : maxUnram A K) ^ N = IntermediateField.inclusion hMU b →
      α ∈ rad J N := by
    intro α b h σ hσ
    rw [h]
    exact hJM σ hσ _ b.2
  have hne : ∀ (α : (maxUnram A K)ˣ) (b : M), (α : maxUnram A K) ^ N = IntermediateField.inclusion hMU b →
      b ≠ 0 := by
    intro α b h hb
    rw [hb, map_zero] at h
    exact pow_ne_zero _ α.ne_zero h
  have hpowγ : ∀ (α : (maxUnram A K)ˣ) (b : M), (α : maxUnram A K) ^ N = IntermediateField.inclusion hMU b →
      ∀ n : ℕ, ((α ^ n : (maxUnram A K)ˣ) : maxUnram A K) ^ N = IntermediateField.inclusion hMU (b ^ n) := by
    intro α b h n
    rw [Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, h, map_pow]
  have hνpow : ∀ (b : M) (n : ℕ), ((WithZero.log (v.valuation M (b ^ n)) : ℤ) : ZMod N) =
      n • ((WithZero.log (v.valuation M b) : ℤ) : ZMod N) := by
    intro b n
    rw [map_pow, WithZero.log_pow, nsmul_eq_mul, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  have hkpow : ∀ α : (maxUnram A K)ˣ, α ∈ rad J N → ∀ (n : ℕ) (σ : J),
      kchar hζN (Γ := J) (α ^ n) σ = n • kchar hζN (Γ := J) α σ := by
    intro α hα n σ
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact kchar_of_fix hζN (fixUnits J).one_mem σ
    | succ n ih => rw [pow_succ, kchar_mul_left hζN ((rad J N).pow_mem hα n) hα σ, ih, succ_nsmul]
  have hθ0 : θ 1 = 0 := by
    have h := hθm 1 1
    rw [mul_one] at h
    linear_combination -h
  have hθpow : ∀ n : ℕ, θ (τ₀ ^ n) = (n : ZMod N) := by
    intro n
    induction n with
    | zero => rw [pow_zero, hθ0, Nat.cast_zero]
    | succ n ih => rw [pow_succ, hθm, ih, hθ1, Nat.cast_succ]
  -- the subgroup `S ≤ ℤ/N` of valuations of level-`M` radicands, and a generator `g = v(b₀)`
  obtain ⟨S, hS⟩ : ∃ S : AddSubgroup (ZMod N), ∀ s, s ∈ S ↔ ∃ (α : (maxUnram A K)ˣ) (b : M),
      (α : maxUnram A K) ^ N = IntermediateField.inclusion hMU b ∧
        ((WithZero.log (v.valuation M b) : ℤ) : ZMod N) = s := by
    refine ⟨{
      carrier := {s | ∃ (α : (maxUnram A K)ˣ) (b : M),
        (α : maxUnram A K) ^ N = IntermediateField.inclusion hMU b ∧
          ((WithZero.log (v.valuation M b) : ℤ) : ZMod N) = s}
      add_mem' := by
        rintro _ _ ⟨α, b, hα, rfl⟩ ⟨β, c, hβ, rfl⟩
        refine ⟨α * β, b * c, by rw [Units.val_mul, mul_pow, hα, hβ, map_mul], ?_⟩
        rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 (hne α b hα))
          ((Valuation.ne_zero_iff _).2 (hne β c hβ)), Int.cast_add]
      zero_mem' := ⟨1, 1, by rw [Units.val_one, one_pow, map_one], by
        rw [map_one, WithZero.log_one, Int.cast_zero]⟩
      neg_mem' := by
        rintro _ ⟨α, b, hα, rfl⟩
        refine ⟨α⁻¹, b⁻¹, by rw [Units.val_inv_eq_inv_val, inv_pow, hα, map_inv₀], ?_⟩
        rw [map_inv₀, WithZero.log_inv, Int.cast_neg] }, fun s => Iff.rfl⟩
  obtain ⟨⟨g, hgS⟩, hgen⟩ := IsAddCyclic.exists_generator (α := S)
  obtain ⟨α₀, b₀, hb₀, hg₀⟩ := (hS g).1 hgS
  have hα₀ := hrad α₀ b₀ hb₀
  obtain ⟨c, hc⟩ := hθall (kchar hζN (Γ := J) α₀) (isLocallyConstant_kchar hζN α₀) (kchar_mul hζN hζNJ hα₀)
  -- `ord(c) • g = 0`, by the ramification converse
  have h1 : addOrderOf c • g = 0 := by
    have hfixU : α₀ ^ addOrderOf c ∈ fixUnits J := by
      refine (kchar_eq_zero_iff hζN ((rad J N).pow_mem hα₀ _)).1 fun σ => ?_
      rw [hkpow α₀ hα₀, hc, ← smul_mul_assoc, addOrderOf_nsmul_eq_zero, zero_mul]
    have hdvd := dvd_val_of_fix_lev hMU v hv (hpowγ α₀ b₀ hb₀ (addOrderOf c))
      (fun σ hσ hσM => hfixU σ ((hJ σ).2 ⟨hσ, hσM⟩))
    rw [← hg₀, ← hνpow]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).2 hdvd
  -- `ord(g) • c = 0`, by the valuation criterion
  have h2 : addOrderOf g • c = 0 := by
    have hval : ((WithZero.log (v.valuation M (b₀ ^ addOrderOf g)) : ℤ) : ZMod N) =
        ((WithZero.log (v.valuation M (1 : M)) : ℤ) : ZMod N) := by
      rw [hνpow, hg₀, addOrderOf_nsmul_eq_zero, map_one, WithZero.log_one, Int.cast_zero]
    have hk := congrFun (kchar_eq_of_val_lev hN hζN hJle hMU v hv hJM ((rad J N).pow_mem hα₀ _)
      (rad J N).one_mem (pow_ne_zero _ (hne α₀ b₀ hb₀)) one_ne_zero (hpowγ α₀ b₀ hb₀ _)
      (by rw [Units.val_one, one_pow, map_one]) hval) τ₀
    rw [hkpow α₀ hα₀, hc, hθ1, mul_one, kchar_of_fix hζN (fixUnits J).one_mem] at hk
    exact hk
  obtain ⟨u, hu⟩ := zmod_exists_unit_mul h1 h2
  let τ : J := τ₀ ^ (u : ZMod N).val
  have hθτ : θ τ = u := by
    show θ (τ₀ ^ (u : ZMod N).val) = u
    rw [hθpow, ZMod.natCast_zmod_val]
  let θ' : J → ZMod N := fun σ => ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * θ σ
  have hθ'm : ∀ σ σ', θ' (σ * σ') = θ' σ + θ' σ' := fun σ σ' => by
    show _ * θ (σ * σ') = _ * θ σ + _ * θ σ'
    rw [hθm, mul_add]
  refine ⟨τ, θ', hθc.comp (fun t : ZMod N => ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * t), hθ'm, ?_, ?_, ?_, ?_⟩
  · show ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * θ τ = 1
    rw [hθτ, Units.inv_mul]
  · intro g' hg' σ hσ hσ'
    show ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * θ _ = ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * θ _
    rw [hθconj g' hg' σ hσ hσ']
  · intro χ hχc hχm σ
    obtain ⟨c', hc'⟩ := hθall χ hχc hχm
    have hu1 : (u : ZMod N) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 := Units.mul_inv u
    show χ σ = χ τ * (((u⁻¹ : (ZMod N)ˣ) : ZMod N) * θ σ)
    rw [hc' σ, hc' τ, hθτ]
    linear_combination (-(c' * θ σ)) * hu1
  · intro α b h
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.1 (hgen ⟨_, (hS _).2 ⟨α, b, h, rfl⟩⟩)
    have hz' : z • g = ((WithZero.log (v.valuation M b) : ℤ) : ZMod N) := congrArg Subtype.val hz
    obtain ⟨m, hmg⟩ : ∃ m : ℕ, m • g = ((WithZero.log (v.valuation M b) : ℤ) : ZMod N) :=
      ⟨(z : ZMod N).val, by rw [← hz', nsmul_eq_mul, zsmul_eq_mul, ZMod.natCast_zmod_val]⟩
    have hval : ((WithZero.log (v.valuation M b) : ℤ) : ZMod N) =
        ((WithZero.log (v.valuation M (b₀ ^ m)) : ℤ) : ZMod N) := by
      rw [hνpow, hg₀, hmg]
    have hk := congrFun (kchar_eq_of_val_lev hN hζN hJle hMU v hv hJM (hrad α b h) ((rad J N).pow_mem hα₀ m)
      (hne α b h) (pow_ne_zero _ (hne α₀ b₀ hb₀)) h (hpowγ α₀ b₀ hb₀ m) hval) τ
    rw [hk, hkpow α₀ hα₀, hc, hθτ, ← hmg, hu, mul_comm c]

end

end TameInertia
end RamanujanPetersson

end

-- ===== S4.Def_RP_Cone_ResRad =====
section

/-!
# S4-PD (4), E4B part 5a: radicands in constant levels, and normalisation along constant extensions

* `exists_sup_constLevel_of_fixed`: an element of `K_U` fixed by `π₁^geo ∩ Gal(K_U/M)` lies in
  `M ⊔ K(𝔽_{p^(e k)})` for some `k > 0` (infinite Galois correspondence on `K_U / K`).
* `log_val_eq_of_inertia_fix`: if `M ≤ M'` are finite levels and every inertia element at `Q` fixing `M` fixes `M'`
  (e.g. `M'` a constant extension of `M`), valuations of elements of `M` agree at `Q ∩ B_M` and `Q ∩ B_M'`.
* `kchar_norm_of_le`: a tame generator normalised by the radicands of `M` is normalised by those of `M'`, once every
  valuation class of an `M'`-radicand is one of an `M`-radicand.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

open CurveCoh GalCover Kummer TameInertia IsDedekindDomain

noncomputable section

section Rad

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- An element of `K_U` fixed by `π₁^geo ∩ Gal(K_U/M)` lies in `M ⊔ K(𝔽_{q^k})` for some `k > 0`. -/
theorem exists_sup_constLevel_of_fixed {e : ℕ} (he : 0 < e)
    {M : IntermediateField K (AlgebraicClosure K)} (hMU : M ≤ maxUnram A K) {x : maxUnram A K}
    (hx : ∀ σ ∈ pi1geo A K (p ^ e), σ ∈ (IntermediateField.restrict hMU).fixingSubgroup → σ x = x) :
    ∃ k, 0 < k ∧ (x : AlgebraicClosure K) ∈ M ⊔ constLevel K p (e * k) := by
  classical
  have hmem : x ∈ IntermediateField.fixedField
      (constFieldU A K (p ^ e) ⊔ IntermediateField.restrict hMU).fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    rw [IntermediateField.fixingSubgroup_sup, fixingSubgroup_constFieldU] at hσ
    exact hx σ (Subgroup.mem_inf.1 hσ).1 (Subgroup.mem_inf.1 hσ).2
  have hsup : constFieldU A K (p ^ e) ⊔ IntermediateField.restrict hMU =
      IntermediateField.adjoin K ({y | IsConst (p ^ e) y} ∪
        (IntermediateField.restrict hMU : Set (maxUnram A K))) := by
    rw [IntermediateField.adjoin_union, IntermediateField.adjoin_self]
    rfl
  rw [InfiniteGalois.fixedField_fixingSubgroup, hsup] at hmem
  obtain ⟨T, hT, hxT⟩ := IntermediateField.exists_finset_of_mem_adjoin hmem
  have hc : ∀ y ∈ T, ∃ n, 0 < n ∧ ((y : AlgebraicClosure K) ∈ M ∨ y ^ (p ^ e) ^ n = y) := by
    intro y hy
    rcases hT hy with hyc | hyM
    · obtain ⟨n, hn, hyn⟩ := hyc
      exact ⟨n, hn, Or.inr hyn⟩
    · exact ⟨1, one_pos, Or.inl ((IntermediateField.mem_restrict hMU _).1 hyM)⟩
  choose! n hn hpow using hc
  refine ⟨∏ y ∈ T, n y, Finset.prod_pos fun y hy => hn y hy, ?_⟩
  have hk : 0 < e * ∏ y ∈ T, n y := Nat.mul_pos he (Finset.prod_pos fun y hy => hn y hy)
  have hle : (IntermediateField.adjoin K (T : Set (maxUnram A K))).map (maxUnram A K).val ≤
      M ⊔ constLevel K p (e * ∏ y ∈ T, n y) := by
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    rcases hpow y hy with hyM | hyc
    · exact le_sup_left (a := M) hyM
    · refine le_sup_right (a := M) (mem_constLevel hk ?_)
      obtain ⟨j, hj⟩ := Finset.dvd_prod_of_mem n hy
      have h1 := pow_pow_mul_eq hyc j
      rw [← hj, ← pow_mul] at h1
      show ((y : AlgebraicClosure K)) ^ p ^ (e * ∏ y ∈ T, n y) = y
      rw [← SubmonoidClass.coe_pow, h1]
  exact hle ⟨x, hxT, rfl⟩

end Rad

section Val

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- Valuations agree along an extension of finite levels `M ≤ M'` in which inertia at `Q` fixing `M` fixes `M'`. -/
theorem log_val_eq_of_inertia_fix [Ring.HasFiniteQuotients R0] {Q : Ideal (proChart A K R0)} [Q.IsPrime]
    {M M' : IntermediateField K (AlgebraicClosure K)} (hMM : M ≤ M') (hMU : M ≤ maxUnram A K)
    (hMU' : M' ≤ maxUnram A K) [FiniteDimensional K M']
    [IsDedekindDomain (integralClosure R0 M)] [IsFractionRing (integralClosure R0 M) M]
    [IsDedekindDomain (integralClosure R0 M')] [IsFractionRing (integralClosure R0 M') M']
    (v : HeightOneSpectrum (integralClosure R0 M)) (hv : v.asIdeal = Q.comap (inclU R0 hMU))
    (v' : HeightOneSpectrum (integralClosure R0 M')) (hv' : v'.asIdeal = Q.comap (inclU R0 hMU'))
    (hfix : ∀ σ ∈ Q.inertia (Pi1 A K), (∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M → σ x = x) →
      ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M' → σ x = x)
    (b : M) :
    WithZero.log (v'.valuation M' (IntermediateField.inclusion hMM b)) = WithZero.log (v.valuation M b) := by
  classical
  obtain ⟨t, ht⟩ : M'.FG := by
    have : Module.Finite K M'.toSubalgebra.toSubmodule := inferInstanceAs (Module.Finite K M')
    exact IntermediateField.fg_of_fg_toSubalgebra M' (Subalgebra.fg_of_fg_toSubmodule Submodule.FG.of_finite)
  obtain ⟨L, hL, hle⟩ := exists_unramSet_of_finite A K t (fun x hx =>
    hMU' (by rw [← ht]; exact IntermediateField.subset_adjoin K _ (Finset.mem_coe.2 hx)))
  have : FiniteDimensional K L := hL.1
  have : IsGalois K L := hL.2.1
  have hLU : L ≤ maxUnram A K := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hL
  have hM'L : M' ≤ L := by
    rw [← ht]
    exact hle
  have hML : M ≤ L := hMM.trans hM'L
  have : IsFractionRing (integralClosure R0 L) L :=
    integralClosure.isFractionRing_of_finite_extension (A := R0) K L
  have : IsDedekindDomain (integralClosure R0 L) := integralClosure.isDedekindDomain (A := R0) (K := K) (L := L)
  have hcomp : ∀ y : integralClosure R0 M, inclU R0 hLU (incl R0 K hML y) = inclU R0 hMU y :=
    fun y => Subtype.ext (Subtype.ext rfl)
  have hcomp' : ∀ y : integralClosure R0 M', inclU R0 hLU (incl R0 K hM'L y) = inclU R0 hMU' y :=
    fun y => Subtype.ext (Subtype.ext rfl)
  obtain ⟨y0, hy0v, hy00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  let w : HeightOneSpectrum (integralClosure R0 L) := ⟨Q.comap (inclU R0 hLU), Ideal.IsPrime.comap _, by
    refine (Submodule.ne_bot_iff _).2 ⟨incl R0 K hML y0, ?_, ?_⟩
    · rw [Ideal.mem_comap, hcomp, ← Ideal.mem_comap, ← hv]
      exact hy0v
    · intro h
      exact hy00 (Subtype.ext (Subtype.ext
        (congrArg (fun z : integralClosure R0 L => ((z : L) : AlgebraicClosure K)) h)))⟩
  have hvw : v.asIdeal = w.asIdeal.comap (incl R0 K hML) := by
    ext y
    show y ∈ v.asIdeal ↔ inclU R0 hLU (incl R0 K hML y) ∈ Q
    rw [hcomp, hv, Ideal.mem_comap]
  have hv'w : v'.asIdeal = w.asIdeal.comap (incl R0 K hM'L) := by
    ext y
    show y ∈ v'.asIdeal ↔ inclU R0 hLU (incl R0 K hM'L y) ∈ Q
    rw [hcomp', hv', Ideal.mem_comap]
  have hIeq : w.asIdeal.inertia (L ≃ₐ[K] L) ⊓ (IntermediateField.restrict hML).fixingSubgroup =
      w.asIdeal.inertia (L ≃ₐ[K] L) ⊓ (IntermediateField.restrict hM'L).fixingSubgroup := by
    apply le_antisymm
    · intro τ hτ
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hτ).1, ?_⟩
      obtain ⟨g, hgI, hg⟩ := TameInertia.exists_inertia_lift (R0 := R0) hLU (Q := Q) (Subgroup.mem_inf.1 hτ).1
      have hgM : ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M → g x = x := by
        intro x hx
        have h1 := hg ⟨x, hML hx⟩
        have h2 : τ ⟨x, hML hx⟩ = ⟨x, hML hx⟩ :=
          (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Subgroup.mem_inf.1 hτ).2 _
            ((IntermediateField.mem_restrict hML _).2 hx)
        rw [h2] at h1
        exact h1
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have h3 := hfix g hgI hgM (IntermediateField.inclusion hLU y) ((IntermediateField.mem_restrict hM'L _).1 hy)
      rw [hg y] at h3
      exact (IntermediateField.inclusion hLU).injective h3
    · intro τ hτ
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hτ).1, ?_⟩
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Subgroup.mem_inf.1 hτ).2 y
        ((IntermediateField.mem_restrict hM'L _).2 (hMM ((IntermediateField.mem_restrict hML _).1 hy)))
  have h1 := log_val_eq_card_mul (R0 := R0) hML w v hvw b
  have h2 := log_val_eq_card_mul (R0 := R0) hM'L w v' hv'w (IntermediateField.inclusion hMM b)
  have hpos : (0 : ℤ) < (Nat.card ↥(w.asIdeal.inertia (L ≃ₐ[K] L) ⊓
      (IntermediateField.restrict hM'L).fixingSubgroup) : ℤ) := by
    exact_mod_cast Nat.card_pos
  rw [hIeq] at h1
  have h12 : IntermediateField.inclusion hM'L (IntermediateField.inclusion hMM b) =
      IntermediateField.inclusion hML b := rfl
  rw [h12, h1] at h2
  exact (mul_left_cancel₀ hpos.ne' h2).symm

set_option synthInstance.maxHeartbeats 400000 in
/-- Normalisation propagates from `M` to `M' ⊇ M` when the valuation classes of `M'`-radicands come from `M`. -/
theorem kchar_norm_of_le {Q : Ideal (proChart A K R0)} [Q.IsPrime] {N : ℕ} [NeZero N] (hN : IsUnit (N : R0))
    {ζN : maxUnram A K} (hζN : IsPrimitiveRoot ζN N) {J : Subgroup (Pi1 A K)} (hJ : J ≤ Q.inertia (Pi1 A K))
    {M M' : IntermediateField K (AlgebraicClosure K)} (hMM : M ≤ M') (hMU : M ≤ maxUnram A K)
    (hMU' : M' ≤ maxUnram A K)
    [IsDedekindDomain (integralClosure R0 M)] [IsFractionRing (integralClosure R0 M) M]
    [IsDedekindDomain (integralClosure R0 M')] [IsFractionRing (integralClosure R0 M') M']
    (v : HeightOneSpectrum (integralClosure R0 M)) (v' : HeightOneSpectrum (integralClosure R0 M'))
    (hv' : v'.asIdeal = Q.comap (inclU R0 hMU'))
    (hJM' : ∀ σ ∈ J, ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M' → σ x = x)
    (hval : ∀ b : M, WithZero.log (v'.valuation M' (IntermediateField.inclusion hMM b)) =
      WithZero.log (v.valuation M b))
    (hS : ∀ (α : (maxUnram A K)ˣ) (b : M'), (α : maxUnram A K) ^ N = IntermediateField.inclusion hMU' b →
      ∃ (β : (maxUnram A K)ˣ) (c : M), (β : maxUnram A K) ^ N = IntermediateField.inclusion hMU c ∧
        ((WithZero.log (v.valuation M c) : ℤ) : ZMod N) = ((WithZero.log (v'.valuation M' b) : ℤ) : ZMod N))
    {τ : J} (hτ : ∀ (β : (maxUnram A K)ˣ) (c : M), (β : maxUnram A K) ^ N = IntermediateField.inclusion hMU c →
      kchar hζN (Γ := J) β τ = ((WithZero.log (v.valuation M c) : ℤ) : ZMod N))
    (α : (maxUnram A K)ˣ) (b : M') (hα : (α : maxUnram A K) ^ N = IntermediateField.inclusion hMU' b) :
    kchar hζN (Γ := J) α τ = ((WithZero.log (v'.valuation M' b) : ℤ) : ZMod N) := by
  obtain ⟨β, c, hβ, hc⟩ := hS α b hα
  have hrad : ∀ (γ : (maxUnram A K)ˣ) (a : M'), (γ : maxUnram A K) ^ N = IntermediateField.inclusion hMU' a →
      γ ∈ rad J N := by
    intro γ a h σ hσ
    rw [h]
    exact hJM' σ hσ _ a.2
  have hne : ∀ (γ : (maxUnram A K)ˣ) (a : M'), (γ : maxUnram A K) ^ N = IntermediateField.inclusion hMU' a →
      a ≠ 0 := by
    intro γ a h ha
    rw [ha, map_zero] at h
    exact pow_ne_zero _ γ.ne_zero h
  have hβ' : (β : maxUnram A K) ^ N = IntermediateField.inclusion hMU' (IntermediateField.inclusion hMM c) := hβ
  have heq := kchar_eq_of_val_lev hN hζN hJ hMU' v' hv' hJM' (hrad α b hα) (hrad β _ hβ')
    (hne α b hα) (hne β _ hβ') hα hβ' (by rw [hval, hc])
  rw [heq, hτ β c hβ, hc]

end Val

end

end Residue
end RamanujanPetersson

end


