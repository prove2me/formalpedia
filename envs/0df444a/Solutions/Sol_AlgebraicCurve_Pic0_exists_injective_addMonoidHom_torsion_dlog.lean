-- Prove2me | solution 1 for AlgebraicCurve.Pic0.exists_injective_addMonoidHom_torsion_dlog
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/f5127c10-0f53-5c27-84fc-dc3967291576

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicGeometry_KwPthPowerKerDExpansionEngine
import Definitions.Def_ModularCurve_KwNo6HspecCartierDlogCampaignFrame
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_KwPke_kw_pke_hsep_of_isSeparable_adjoin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_exists_injective_addMonoidHom_torsion_dlog
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve KaehlerDifferential

namespace P2mWs11R4

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem dlog_algebraMap (a : K) : kw_hwcd_dlog K (algebraMap K F a) = 0 := by
  rw [kw_hwcd_dlog, Derivation.map_algebraMap, smul_zero]

theorem dlog_eq_zero_iff {f : F} (hf : f ≠ 0) : kw_hwcd_dlog K f = 0 ↔ D K F f = 0 := by
  rw [kw_hwcd_dlog, smul_eq_zero, or_iff_right (inv_ne_zero hf)]

theorem dlog_eq_of_forall_ord_eq [IsAlgClosed K] (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
    {f f' : F} (hf : f ≠ 0) (hf' : f' ≠ 0) (h : ∀ v : Place K F, v.ord f = v.ord f') :
    kw_hwcd_dlog K f = kw_hwcd_dlog K f' := by
  have hq : ∀ v : Place K F, v.ord (f' * f⁻¹) = 0 := fun v => by
    rw [v.ord_mul hf' (inv_ne_zero hf), v.ord_inv, h v, add_neg_cancel]
  obtain ⟨a, ha⟩ := Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed t ht hq
  have ha0 : algebraMap K F a ≠ 0 := by rw [ha]; exact mul_ne_zero hf' (inv_ne_zero hf)
  have hf'eq : f' = algebraMap K F a * f := by rw [ha, inv_mul_cancel_right₀ hf]
  rw [hf'eq, kw_hwcd_dlog_mul ha0 hf, dlog_algebraMap, zero_add]

theorem dlog_mul_pow_char (p : ℕ) [CharP F p] {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    kw_hwcd_dlog K (f * g ^ p) = kw_hwcd_dlog K f := by
  rw [kw_hwcd_dlog_mul hf (pow_ne_zero _ hg), kw_hwcd_dlog_pow_char p hg, add_zero]

section Witness

variable (p : ℕ)

theorem exists_witness (c : Pic0.torsion K F p) :
    ∃ (Dv : Divisor.degZero (K := K) (F := F)) (f : F), Pic0.mk Dv = (c : Pic0 K F) ∧ f ≠ 0 ∧
      ∀ v : Place K F, v.ord f = (p : ℤ) * (Dv : Divisor K F) v := by
  obtain ⟨Dv, hDv⟩ := Pic0.mk_surjective (c : Pic0 K F)
  have hc : ((p : ℕ) : ℤ) • (c : Pic0 K F) = 0 := Pic0.mem_torsion.mp c.2
  rw [← hDv, Pic0.mk, ← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf, Divisor.mem_principal] at hc
  obtain ⟨f, hf, hfD⟩ := hc
  refine ⟨Dv, f, hDv, hf, fun v => ?_⟩
  rw [← hfD v, AddSubgroupClass.coe_zsmul, Finsupp.smul_apply, smul_eq_mul]

noncomputable def repr (c : Pic0.torsion K F p) : Divisor.degZero (K := K) (F := F) :=
  (exists_witness p c).choose

noncomputable def fn (c : Pic0.torsion K F p) : F :=
  (exists_witness p c).choose_spec.choose

theorem mk_repr (c : Pic0.torsion K F p) : Pic0.mk (repr p c) = (c : Pic0 K F) :=
  (exists_witness p c).choose_spec.choose_spec.1

theorem fn_ne_zero (c : Pic0.torsion K F p) : fn p c ≠ 0 :=
  (exists_witness p c).choose_spec.choose_spec.2.1

theorem ord_fn (c : Pic0.torsion K F p) (v : Place K F) :
    v.ord (fn p c) = (p : ℤ) * (repr p c : Divisor K F) v :=
  (exists_witness p c).choose_spec.choose_spec.2.2 v

end Witness

section Map

variable [IsAlgClosed K]

theorem dlog_eq_of_mk_eq (p : ℕ) [CharP F p] (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
    {D₁ D₂ : Divisor.degZero (K := K) (F := F)} {f₁ f₂ : F}
    (hmk : Pic0.mk D₁ = Pic0.mk D₂) (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0)
    (h₁ : ∀ v : Place K F, v.ord f₁ = (p : ℤ) * (D₁ : Divisor K F) v)
    (h₂ : ∀ v : Place K F, v.ord f₂ = (p : ℤ) * (D₂ : Divisor K F) v) :
    kw_hwcd_dlog K f₁ = kw_hwcd_dlog K f₂ := by

  have hsub : Pic0.mk (D₁ - D₂) = 0 := by
    rw [Pic0.mk, QuotientAddGroup.mk_sub]
    exact sub_eq_zero.mpr hmk
  rw [Pic0.mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, Divisor.mem_principal] at hsub
  obtain ⟨g, hg, hgD⟩ := hsub

  have hord : ∀ v : Place K F, v.ord f₁ = v.ord (f₂ * g ^ p) := fun v => by
    rw [v.ord_mul hf₂ (pow_ne_zero _ hg), ← zpow_natCast, v.ord_zpow, h₁ v, h₂ v, ← hgD v,
      AddSubgroupClass.coe_sub, Finsupp.sub_apply]
    ring
  rw [dlog_eq_of_forall_ord_eq t ht hf₁ (mul_ne_zero hf₂ (pow_ne_zero _ hg)) hord,
    dlog_mul_pow_char p hf₂ hg]

noncomputable def dlogFun (p : ℕ) (c : Pic0.torsion K F p) : Ω[F⁄K] := kw_hwcd_dlog K (fn p c)

theorem dlogFun_eq (p : ℕ) [CharP F p] (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
    (c : Pic0.torsion K F p) {Dv : Divisor.degZero (K := K) (F := F)} {f : F}
    (hmk : Pic0.mk Dv = (c : Pic0 K F)) (hf : f ≠ 0)
    (h : ∀ v : Place K F, v.ord f = (p : ℤ) * (Dv : Divisor K F) v) :
    dlogFun p c = kw_hwcd_dlog K f :=
  dlog_eq_of_mk_eq p t ht ((mk_repr p c).trans hmk.symm) (fn_ne_zero p c) hf (ord_fn p c) h

theorem dlogFun_add (p : ℕ) [CharP F p] (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F] (c₁ c₂ : Pic0.torsion K F p) :
    dlogFun p (c₁ + c₂) = dlogFun p c₁ + dlogFun p c₂ := by
  have hmk : Pic0.mk (repr p c₁ + repr p c₂) = ((c₁ + c₂ : Pic0.torsion K F p) : Pic0 K F) := by
    rw [Pic0.mk_add, mk_repr, mk_repr, AddSubgroup.coe_add]
  have hf : fn p c₁ * fn p c₂ ≠ 0 := mul_ne_zero (fn_ne_zero p c₁) (fn_ne_zero p c₂)
  have hord : ∀ v : Place K F, v.ord (fn p c₁ * fn p c₂) =
      (p : ℤ) * ((repr p c₁ + repr p c₂ : Divisor.degZero (K := K) (F := F)) : Divisor K F) v := fun v => by
    rw [v.ord_mul (fn_ne_zero p c₁) (fn_ne_zero p c₂), ord_fn, ord_fn, AddSubgroup.coe_add,
      Finsupp.add_apply, mul_add]
  rw [dlogFun_eq p t ht (c₁ + c₂) hmk hf hord, kw_hwcd_dlog_mul (fn_ne_zero p c₁) (fn_ne_zero p c₂)]
  rfl

noncomputable def dlogHom (p : ℕ) [CharP F p] (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F] : Pic0.torsion K F p →+ Ω[F⁄K] :=
  AddMonoidHom.mk' (dlogFun p) (dlogFun_add p t ht)

theorem dlogHom_apply (p : ℕ) [CharP F p] (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F] (c : Pic0.torsion K F p) :
    dlogHom p t ht c = kw_hwcd_dlog K (fn p c) := rfl

theorem dlogHom_injective (p : ℕ) [Fact p.Prime] [CharP F p] (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
    (hsepK : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F)
    (hdt : KaehlerDifferential.D K F t ≠ 0) :
    Function.Injective (dlogHom (K := K) (F := F) p t ht) := by
  haveI : PerfectField K := inferInstance
  have hsep := KwPke.kw_pke_hsep_of_isSeparable_adjoin (ℓ := p) t hsepK
  rw [injective_iff_map_eq_zero]
  intro c hc
  rw [dlogHom_apply, dlog_eq_zero_iff (fn_ne_zero p c)] at hc
  obtain ⟨g, hg⟩ := KwPke.kw_pke_ker_d_pthPower (K := K) (ℓ := p) t hsep hdt hc
  have hg0 : g ≠ 0 := by
    intro h0
    exact fn_ne_zero p c (by rw [hg, h0, zero_pow (Fact.out : p.Prime).ne_zero])
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

  have hD : ∀ v : Place K F, (repr p c : Divisor K F) v = v.ord g := fun v => by
    have := ord_fn p c v
    rw [hg, ← zpow_natCast, v.ord_zpow] at this
    exact (mul_left_cancel₀ hp0 this).symm
  have hmk : Pic0.mk (repr p c) = 0 := by
    rw [Pic0.mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, Divisor.mem_principal]
    exact ⟨g, hg0, hD⟩
  apply Subtype.ext
  rw [← mk_repr p c, hmk]
  rfl

end Map

end P2mWs11R4

open P2mWs11R4 in
theorem solution
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (t : F) (ht : Transcendental K t) [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
    (hsepK : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F)
    (hdt : KaehlerDifferential.D K F t ≠ 0) :
    ∃ φ : AlgebraicCurve.Pic0.torsion K F p →+ Ω[F⁄K], Function.Injective φ ∧
      ∀ c, ∃ f : F, f ≠ 0 ∧ (∀ v : AlgebraicCurve.Place K F, (p : ℤ) ∣ v.ord f) ∧
        φ c = f⁻¹ • KaehlerDifferential.D K F f := by
  haveI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  refine ⟨dlogHom p t ht, dlogHom_injective p t ht hsepK hdt, fun c => ⟨fn p c, fn_ne_zero p c,
    fun v => ⟨_, ord_fn p c v⟩, rfl⟩⟩

end S_AlgebraicCurve_Pic0_exists_injective_addMonoidHom_torsion_dlog
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_exists_injective_addMonoidHom_torsion_dlog (solution)
