-- Prove2me | solution 1 for AutomorphicForm.continuous_finprod_localFactor_and_exists_fractionalIdeal_norm_finprod_le_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ee382ab8-9d0a-5d10-988a-8cf48f9b54a3

import Mathlib
import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_continuous_finprod_localFactor_and_exists_fractionalIdeal_norm_finprod_le_of_isCompact
p2m_attr_erase "instance" "NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion"

set_option autoImplicit false

open NumberField IsDedekindDomain Filter Topology

namespace HFfin

variable (F : Type) [Field F] [NumberField F]

private theorem snd_apply_mul_inv_snd_apply (u : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (u : AdeleRing (𝓞 F) F).2 v * ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 := by
  have h := congrArg (fun x : AdeleRing (𝓞 F) F => x.2 v) u.mul_inv
  exact h

private theorem valued_algebraMap_mul_apply (s : 𝓞 F) (y : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s * y) v) = v.intValuation s * Valued.v (y v) := by
  have h : (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s * y) v
      = ((algebraMap (𝓞 F) F s : F) : v.adicCompletion F) * y v := rfl
  rw [h, map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]

private theorem exists_finite_support_valuation_bounds_of_isCompact (U : Set (AdeleRing (𝓞 F) F)ˣ) (hU : IsCompact U) :
    ∃ L : HeightOneSpectrum (𝓞 F) → ℤ, (Function.support L).Finite ∧ (∀ v, 0 ≤ L v) ∧
      ∀ u ∈ U, ∀ v : HeightOneSpectrum (𝓞 F),
        WithZero.exp (-(L v)) ≤ Valued.v ((u : AdeleRing (𝓞 F) F).2 v) ∧
        Valued.v ((u : AdeleRing (𝓞 F) F).2 v) ≤ WithZero.exp (L v) := by

  have hC : IsCompact ((fun u : (AdeleRing (𝓞 F) F)ˣ => (u : AdeleRing (𝓞 F) F).2) '' U) :=
    hU.image (continuous_snd.comp Units.continuous_val)
  have hC' : IsCompact ((fun u : (AdeleRing (𝓞 F) F)ˣ => ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) '' U) :=
    hU.image (continuous_snd.comp Units.continuous_coe_inv)
  obtain ⟨s, hs0, hs⟩ :=
    IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact (𝓞 F) F hC
  obtain ⟨s', hs'0, hs'⟩ :=
    IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact (𝓞 F) F hC'

  set n : HeightOneSpectrum (𝓞 F) → ℕ := fun v =>
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {s} : Ideal (𝓞 F))).factors with hn
  set n' : HeightOneSpectrum (𝓞 F) → ℕ := fun v =>
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {s'} : Ideal (𝓞 F))).factors with hn'
  have hns : ∀ v : HeightOneSpectrum (𝓞 F), v.intValuation s = WithZero.exp (-(n v : ℤ)) :=
    fun v => v.intValuation_if_neg hs0
  have hns' : ∀ v : HeightOneSpectrum (𝓞 F), v.intValuation s' = WithZero.exp (-(n' v : ℤ)) :=
    fun v => v.intValuation_if_neg hs'0

  have hvan : ∀ (r : 𝓞 F) (hr : r ≠ 0) (m : HeightOneSpectrum (𝓞 F) → ℕ),
      (∀ v : HeightOneSpectrum (𝓞 F), v.intValuation r = WithZero.exp (-(m v : ℤ))) →
      ∀ v, m v ≠ 0 → v.asIdeal ∣ Ideal.span {r} := by
    intro r hr m hm v hv
    rw [← HeightOneSpectrum.intValuation_lt_one_iff_dvd, hm v, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  refine ⟨fun v => (n v : ℤ) + (n' v : ℤ), ?_, fun v => by positivity, ?_⟩
  · have hfin := (Ideal.finite_factors (I := Ideal.span {s}) (by simpa using hs0)).union
      (Ideal.finite_factors (I := Ideal.span {s'}) (by simpa using hs'0))
    refine hfin.subset ?_
    intro v hv
    simp only [Function.mem_support, ne_eq] at hv
    by_cases h1 : n v = 0
    · right
      exact hvan s' hs'0 n' hns' v (by omega)
    · left
      exact hvan s hs0 n hns v h1
  · intro u hu v
    have hup : ∀ (r : 𝓞 F) (m : ℕ) (y : FiniteAdeleRing (𝓞 F) F),
        v.intValuation r = WithZero.exp (-(m : ℤ)) →
        (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r * y) v ∈ HeightOneSpectrum.adicCompletionIntegers F v →
        Valued.v (y v) ≤ WithZero.exp (m : ℤ) := by
      intro r m y hr hint
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap_mul_apply, hr] at hint
      calc Valued.v (y v) = WithZero.exp (m : ℤ) * (WithZero.exp (-(m : ℤ)) * Valued.v (y v)) := by
            rw [← mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, one_mul]
        _ ≤ WithZero.exp (m : ℤ) * 1 := mul_le_mul_right hint _
        _ = WithZero.exp (m : ℤ) := mul_one _
    have h1 : Valued.v ((u : AdeleRing (𝓞 F) F).2 v) ≤ WithZero.exp (n v : ℤ) :=
      hup s (n v) _ (hns v) (hs _ ⟨u, hu, rfl⟩ v)
    have h2 : Valued.v (((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) ≤ WithZero.exp (n' v : ℤ) :=
      hup s' (n' v) _ (hns' v) (hs' _ ⟨u, hu, rfl⟩ v)
    have hmul : Valued.v ((u : AdeleRing (𝓞 F) F).2 v) *
        Valued.v (((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) = 1 := by
      rw [← map_mul, snd_apply_mul_inv_snd_apply, map_one]
    constructor
    · calc WithZero.exp (-((n v : ℤ) + (n' v : ℤ)))
          ≤ WithZero.exp (-(n' v : ℤ)) := by
            rw [WithZero.exp_le_exp]
            omega
        _ = Valued.v ((u : AdeleRing (𝓞 F) F).2 v) *
              (WithZero.exp (-(n' v : ℤ)) * Valued.v (((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v)) := by
            rw [mul_left_comm, hmul, mul_one]
        _ ≤ Valued.v ((u : AdeleRing (𝓞 F) F).2 v) * 1 := by
            refine mul_le_mul_right ?_ _
            calc WithZero.exp (-(n' v : ℤ)) * Valued.v (((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v)
                ≤ WithZero.exp (-(n' v : ℤ)) * WithZero.exp (n' v : ℤ) := mul_le_mul_right h2 _
              _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
        _ = Valued.v ((u : AdeleRing (𝓞 F) F).2 v) := mul_one _
    · calc Valued.v ((u : AdeleRing (𝓞 F) F).2 v) ≤ WithZero.exp (n v : ℤ) := h1
        _ ≤ WithZero.exp ((n v : ℤ) + (n' v : ℤ)) := by
            rw [WithZero.exp_le_exp]
            omega

end HFfin

section FinCont

open IsDedekindDomain NumberField Filter Topology

private theorem T1F2_finite_setOf_valued_ne_one (F : Type) [Field F] [NumberField F] (U : (AdeleRing (𝓞 F) F)ˣ) :
    {v : HeightOneSpectrum (𝓞 F) | Valued.v (((U : AdeleRing (𝓞 F) F).2) v) ≠ 1}.Finite := by
  have hmul : (U : AdeleRing (𝓞 F) F).2 * ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 :=
    congrArg Prod.snd (Units.mul_inv U)
  have hmul' : ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 * (U : AdeleRing (𝓞 F) F).2 = 1 :=
    congrArg Prod.snd (Units.inv_mul U)
  have hu : IsUnit ((U : AdeleRing (𝓞 F) F).2) := ⟨⟨_, _, hmul, hmul'⟩, rfl⟩
  exact Filter.eventually_cofinite.mp (FiniteAdeleRing.isUnit_iff.mp hu).2

private theorem T1F2_valued_eq_one_of_mul_eq_one (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (a b : v.adicCompletion F) (hab : a * b = 1) (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ 1) :
    Valued.v a = 1 := by
  by_contra h
  have hlt : Valued.v a < 1 := lt_of_le_of_ne ha h
  have h1 : Valued.v a * Valued.v b = 1 := by rw [← map_mul, hab, map_one]
  have h2 : Valued.v a * Valued.v b ≤ Valued.v a * 1 := mul_le_mul_right hb _
  rw [h1, mul_one] at h2
  exact absurd (lt_of_le_of_lt h2 hlt) (lt_irrefl _)

private theorem T1F2_isOpen_setOf_forall_mem_integers (F : Type) [Field F] [NumberField F] :
    IsOpen {u : (AdeleRing (𝓞 F) F)ˣ |
      (∀ v : HeightOneSpectrum (𝓞 F), ((u : AdeleRing (𝓞 F) F).2) v ∈ v.adicCompletionIntegers F) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) v ∈ v.adicCompletionIntegers F} := by
  have hO : IsOpen {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)
  have h1 : Continuous fun u : (AdeleRing (𝓞 F) F)ˣ => (u : AdeleRing (𝓞 F) F).2 :=
    continuous_snd.comp Units.continuous_val
  have h2 : Continuous fun u : (AdeleRing (𝓞 F) F)ˣ => ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 :=
    continuous_snd.comp Units.continuous_coe_inv
  exact (hO.preimage h1).inter (hO.preimage h2)

private theorem T1F2_setOf_valued_eq_one_and_valued_sub_le_mem_nhds (F : Type) [Field F] [NumberField F]
    (y₀ : (AdeleRing (𝓞 F) F)ˣ) (T : Finset (HeightOneSpectrum (𝓞 F))) (δ : HeightOneSpectrum (𝓞 F) → ℤ) :
    {y : (AdeleRing (𝓞 F) F)ˣ |
      (∀ v : HeightOneSpectrum (𝓞 F),
        Valued.v ((((y * y₀⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) v) = 1) ∧
      ∀ v ∈ T, Valued.v (((y : AdeleRing (𝓞 F) F).2) v - ((y₀ : AdeleRing (𝓞 F) F).2) v) ≤ WithZero.exp (δ v)}
      ∈ 𝓝 y₀ := by

  have hW := T1F2_isOpen_setOf_forall_mem_integers F
  have hm : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => y * y₀⁻¹ := continuous_id.mul continuous_const
  have hA : {y : (AdeleRing (𝓞 F) F)ˣ | ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v ((((y * y₀⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) v) = 1} ∈ 𝓝 y₀ := by
    refine Filter.mem_of_superset ((hW.preimage hm).mem_nhds ?_) ?_
    · simp only [Set.mem_preimage, mul_inv_cancel, Set.mem_setOf_eq, inv_one, Units.val_one]
      exact ⟨fun v => (v.adicCompletionIntegers F).one_mem, fun v => (v.adicCompletionIntegers F).one_mem⟩
    · rintro y ⟨h1, h2⟩ v
      refine T1F2_valued_eq_one_of_mul_eq_one F v _ ((((y * y₀⁻¹)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v)
        ?_ (h1 v) (h2 v)
      have := congrArg Prod.snd (Units.mul_inv (y * y₀⁻¹))
      exact congrFun (congrArg DFunLike.coe this) v

  have hev : ∀ v : HeightOneSpectrum (𝓞 F), Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((y : AdeleRing (𝓞 F) F).2) v :=
    fun v => (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp Units.continuous_val)
  have hB : ∀ v : HeightOneSpectrum (𝓞 F), {y : (AdeleRing (𝓞 F) F)ˣ |
      Valued.v (((y : AdeleRing (𝓞 F) F).2) v - ((y₀ : AdeleRing (𝓞 F) F).2) v) ≤ WithZero.exp (δ v)} ∈ 𝓝 y₀ := by
    intro v
    obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (δ v))
    have hc0 : Valued.v c ≠ 0 := by rw [hc]; exact WithZero.exp_ne_zero
    have hcne : c ≠ 0 := by rintro rfl; exact hc0 (map_zero _)
    have hc0' : Valued.v.restrict c ≠ 0 := by simp [hcne]
    have hs : {a : v.adicCompletion F | Valued.v (a - ((y₀ : AdeleRing (𝓞 F) F).2) v) ≤ WithZero.exp (δ v)}
        ∈ 𝓝 (((y₀ : AdeleRing (𝓞 F) F).2) v) := by
      rw [Valued.mem_nhds]
      refine ⟨Units.mk0 _ hc0', fun a ha => ?_⟩
      rw [Units.val_mk0] at ha
      have ha' := (Valuation.restrict_lt_iff _).mp ha
      rw [hc] at ha'
      exact le_of_lt ha'
    exact (hev v).continuousAt.preimage_mem_nhds hs
  have hB' : (⋂ v ∈ T, {y : (AdeleRing (𝓞 F) F)ˣ |
      Valued.v (((y : AdeleRing (𝓞 F) F).2) v - ((y₀ : AdeleRing (𝓞 F) F).2) v) ≤ WithZero.exp (δ v)}) ∈ 𝓝 y₀ :=
    (Filter.biInter_finset_mem T).mpr fun v _ => hB v
  refine Filter.mem_of_superset (Filter.inter_mem hA hB') ?_
  rintro y ⟨h1, h2⟩
  refine ⟨h1, fun v hv => ?_⟩
  exact (Set.mem_iInter₂.mp h2) v hv

private theorem T1F4_snd_mul_apply (F : Type) [Field F] [NumberField F] (x y : AdeleRing (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) : (x * y).2 v = x.2 v * y.2 v := rfl

private theorem T1F4_snd_apply_ne_zero (F : Type) [Field F] [NumberField F] (U : (AdeleRing (𝓞 F) F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) : (U : AdeleRing (𝓞 F) F).2 v ≠ 0 := by
  have h : (U : AdeleRing (𝓞 F) F).2 v * ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 := by
    have := congrArg Prod.snd (Units.mul_inv U)
    exact congrFun (congrArg DFunLike.coe this) v
  exact left_ne_zero_of_mul_eq_one h

private theorem T1F4_continuous_finprod (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ)
    (thr : HeightOneSpectrum (𝓞 F) → ℤ)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (hΦd : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w : v.adicCompletion F), Differentiable ℂ (Φ j v w))
    (hΦ1 : ∀ (j : Fin n), ∀ v ∉ S, ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v w = 1 → Φ j v w s = 1)
    (hΦlc : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w₀ : v.adicCompletion F), w₀ ≠ 0 → ∃ δ : ℤ,
      ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v (w - w₀) ≤ WithZero.exp δ → Φ j v w s = Φ j v w₀ s)
    (x₀ : (AdeleRing (𝓞 F) F)ˣ) (j : Fin n) :
    Continuous fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      Φ j v (((x₀ : AdeleRing (𝓞 F) F) * (p.2 : AdeleRing (𝓞 F) F)).2 v) p.1 := by
  classical
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨s₀, y₀⟩ := p₀

  set U₀ : (AdeleRing (𝓞 F) F)ˣ := x₀ * y₀ with hU₀
  set w₀ : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F := fun v => (U₀ : AdeleRing (𝓞 F) F).2 v with hw₀
  have hw₀v : ∀ v, w₀ v = (x₀ : AdeleRing (𝓞 F) F).2 v * (y₀ : AdeleRing (𝓞 F) F).2 v := by
    intro v
    simp only [hw₀, hU₀, Units.val_mul]
    rfl
  have hw₀ne : ∀ v, w₀ v ≠ 0 := fun v => T1F4_snd_apply_ne_zero F U₀ v

  have hfin := T1F2_finite_setOf_valued_ne_one F U₀
  set T : Finset (HeightOneSpectrum (𝓞 F)) := S ∪ hfin.toFinset with hT
  have hT1 : ∀ v ∉ T, v ∉ S ∧ Valued.v (w₀ v) = 1 := by
    intro v hv
    rw [hT, Finset.mem_union, not_or] at hv
    refine ⟨hv.1, ?_⟩
    by_contra h
    exact hv.2 (hfin.mem_toFinset.2 h)

  choose δ hδ using fun v => hΦlc j v (w₀ v) (hw₀ne v)
  set c : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F :=
    fun v => (x₀ : AdeleRing (𝓞 F) F).2 v with hc
  have hcne : ∀ v, Valued.v (c v) ≠ 0 := fun v =>
    (Valuation.ne_zero_iff _).2 (T1F4_snd_apply_ne_zero F x₀ v)
  set δ' : HeightOneSpectrum (𝓞 F) → ℤ := fun v => δ v - WithZero.log (Valued.v (c v)) with hδ'

  have hN := T1F2_setOf_valued_eq_one_and_valued_sub_le_mem_nhds F y₀ T δ'
  have hgc : Continuous fun s : ℂ => ∏ v ∈ T, Φ j v (w₀ v) s :=
    continuous_finsetProd T fun v _ => (hΦd j v (w₀ v)).continuous
  refine ((hgc.comp continuous_fst).continuousAt (x := (s₀, y₀))).congr_of_eventuallyEq ?_
  refine Filter.mem_of_superset (prod_mem_nhds Filter.univ_mem hN) ?_
  rintro ⟨s, y⟩ ⟨-, hy1, hy2⟩
  show (∏ᶠ v : HeightOneSpectrum (𝓞 F), Φ j v (((x₀ : AdeleRing (𝓞 F) F) * (y : AdeleRing (𝓞 F) F)).2 v) s)
    = ∏ v ∈ T, Φ j v (w₀ v) s

  have hy : (y : AdeleRing (𝓞 F) F) = ((y * y₀⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * (y₀ : AdeleRing (𝓞 F) F) := by
    rw [← Units.val_mul, inv_mul_cancel_right]
  have hW : ∀ v, (((x₀ : AdeleRing (𝓞 F) F) * (y : AdeleRing (𝓞 F) F)).2 v)
      = ((y * y₀⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v * w₀ v := by
    intro v
    rw [T1F4_snd_mul_apply, hw₀v, hy, T1F4_snd_mul_apply]
    ring
  have hWsub : ∀ v, (((x₀ : AdeleRing (𝓞 F) F) * (y : AdeleRing (𝓞 F) F)).2 v) - w₀ v
      = c v * ((y : AdeleRing (𝓞 F) F).2 v - (y₀ : AdeleRing (𝓞 F) F).2 v) := by
    intro v
    rw [T1F4_snd_mul_apply, hw₀v]
    simp only [hc]
    ring
  have hpt : ∀ v, Φ j v (((x₀ : AdeleRing (𝓞 F) F) * (y : AdeleRing (𝓞 F) F)).2 v) s = Φ j v (w₀ v) s := by
    intro v
    by_cases hv : v ∈ T
    · refine hδ v _ s ?_
      rw [hWsub, map_mul]
      calc Valued.v (c v) * Valued.v ((y : AdeleRing (𝓞 F) F).2 v - (y₀ : AdeleRing (𝓞 F) F).2 v)
          ≤ Valued.v (c v) * WithZero.exp (δ' v) := mul_le_mul_right (hy2 v hv) _
        _ = WithZero.exp (δ v) := by
            conv_lhs => rw [← WithZero.exp_log (hcne v)]
            rw [← WithZero.exp_add, hδ']
            simp
    · obtain ⟨hvS, hv1⟩ := hT1 v hv
      have hval : Valued.v (((x₀ : AdeleRing (𝓞 F) F) * (y : AdeleRing (𝓞 F) F)).2 v) = 1 := by
        rw [hW, map_mul, hy1 v, one_mul, hv1]
      rw [hΦ1 j v hvS _ s hval, hΦ1 j v hvS _ s hv1]
  rw [finprod_congr hpt]
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
  by_contra hvT
  obtain ⟨hvS, hv1⟩ := hT1 v hvT
  exact hv (hΦ1 j v hvS _ s hv1)

end FinCont

section FinBound

open IsDedekindDomain NumberField Filter

private theorem T1F3_finite_setOf_valued_ne_one (F : Type) [Field F] [NumberField F] (U : (AdeleRing (𝓞 F) F)ˣ) :
    {v : HeightOneSpectrum (𝓞 F) | Valued.v (((U : AdeleRing (𝓞 F) F).2) v) ≠ 1}.Finite := by
  have hmul : (U : AdeleRing (𝓞 F) F).2 * ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 :=
    congrArg Prod.snd (Units.mul_inv U)
  have hmul' : ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 * (U : AdeleRing (𝓞 F) F).2 = 1 :=
    congrArg Prod.snd (Units.inv_mul U)
  have hu : IsUnit ((U : AdeleRing (𝓞 F) F).2) := ⟨⟨_, _, hmul, hmul'⟩, rfl⟩
  exact Filter.eventually_cofinite.mp (FiniteAdeleRing.isUnit_iff.mp hu).2

private theorem T1F3_exists_fractionalIdeal_ne_zero_mem_of_forall_valued_le (F : Type) [Field F] [NumberField F]
    (N : HeightOneSpectrum (𝓞 F) → ℤ) (hN : (Function.support N).Finite) :
    ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F, I ≠ 0 ∧ ∀ ξ : F,
      (∀ v : HeightOneSpectrum (𝓞 F), v.valuation F ξ ≤ WithZero.exp (N v)) → ξ ∈ I := by
  have hJ : (∏ v ∈ hN.toFinset, v.asIdeal ^ (N v).toNat) ≠ ⊥ :=
    Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ v.ne_bot
  obtain ⟨d, hdJ, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hdF : algebraMap (𝓞 F) F d ≠ 0 := NumberField.RingOfIntegers.coe_ne_zero_iff.mpr hd0
  refine ⟨FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (algebraMap (𝓞 F) F d)⁻¹,
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero hdF), fun ξ hξ => ?_⟩
  have hdvd : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ^ (N v).toNat ∣ Ideal.span {d} := by
    intro v
    by_cases hv : v ∈ hN.toFinset
    · exact (Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal ^ (N v).toNat) hv).trans
        (Ideal.dvd_span_singleton.mpr hdJ)
    · have h0 : N v = 0 := by
        by_contra h
        exact hv (hN.mem_toFinset.mpr (Function.mem_support.mpr h))
      rw [h0, Int.toNat_zero, pow_zero]
      exact one_dvd _
  have hint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (algebraMap (𝓞 F) F d * ξ) ≤ 1 := by
    intro v
    have h1 : v.valuation F (algebraMap (𝓞 F) F d) = v.intValuation d := v.valuation_of_algebraMap d
    have h2 : v.intValuation d ≤ WithZero.exp (-((N v).toNat : ℤ)) :=
      (v.intValuation_le_pow_iff_dvd d _).mpr (hdvd v)
    calc v.valuation F (algebraMap (𝓞 F) F d * ξ)
        = v.intValuation d * v.valuation F ξ := by rw [Valuation.map_mul, h1]
      _ ≤ WithZero.exp (-((N v).toNat : ℤ)) * WithZero.exp (N v) := mul_le_mul' h2 (hξ v)
      _ = WithZero.exp (-((N v).toNat : ℤ) + N v) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp (0 : ℤ) := WithZero.exp_le_exp.mpr (by omega)
      _ = 1 := WithZero.exp_zero
  obtain ⟨z, hz⟩ := RingHom.mem_range.mp
    (IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hint)
  refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨z, ?_⟩
  rw [Algebra.smul_def, hz, mul_comm (algebraMap (𝓞 F) F d) ξ, mul_inv_cancel_right₀ hdF]

private theorem T1F3_exists_pos_finprod_absNorm_pow_toNat_neg_le_mul_abs_norm (F : Type) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ξ : F, ξ ∈ I → ξ ≠ 0 → ∀ e : HeightOneSpectrum (𝓞 F) → ℤ,
      (∀ v : HeightOneSpectrum (𝓞 F), v.valuation F ξ = WithZero.exp (e v)) →
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(e v)).toNat
        ≤ c₀ * ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) := by
  obtain ⟨a, aI, ha, hI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have haF : algebraMap (𝓞 F) F a ≠ 0 := NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ha
  have hNa : (0 : ℚ) < |Algebra.norm ℚ (algebraMap (𝓞 F) F a)| :=
    abs_pos.mpr (Algebra.norm_ne_zero_iff.mpr haF)
  refine ⟨((|Algebra.norm ℚ (algebraMap (𝓞 F) F a)| : ℚ) : ℝ), Rat.cast_pos.mpr hNa,
    fun ξ hξ hξ0 e he => ?_⟩
  rw [hI, FractionalIdeal.mem_singleton_mul] at hξ
  obtain ⟨y, hy, hξy⟩ := hξ
  obtain ⟨b, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
  have hab : algebraMap (𝓞 F) F a * ξ = algebraMap (𝓞 F) F b := by
    rw [hξy, mul_inv_cancel_left₀ haF]
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    exact mul_ne_zero haF hξ0 hab
  have hdvd : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ^ (-(e v)).toNat ∣ Ideal.span {b} := by
    intro v
    by_cases hv : 0 ≤ e v
    · rw [Int.toNat_eq_zero.mpr (by omega), pow_zero]
      exact one_dvd _
    · have h1 : v.valuation F (algebraMap (𝓞 F) F b) = v.intValuation b := v.valuation_of_algebraMap b
      have h2 : v.valuation F (algebraMap (𝓞 F) F a) = v.intValuation a := v.valuation_of_algebraMap a
      have h3 : v.intValuation b ≤ WithZero.exp (e v) := by
        rw [← h1, ← hab, Valuation.map_mul, h2, he v]
        exact mul_le_of_le_one_left' (v.intValuation_le_one a)
      refine (v.intValuation_le_pow_iff_dvd b _).mp ?_
      rwa [Int.toNat_of_nonneg (by omega), neg_neg]
  have hNb : Algebra.norm ℚ (algebraMap (𝓞 F) F b) = ((Algebra.norm ℤ b : ℤ) : ℚ) :=
    (Algebra.coe_norm_int b).symm
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 F)),
      ∏ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(e v)).toNat
        ≤ ((|Algebra.norm ℚ (algebraMap (𝓞 F) F a)| : ℚ) : ℝ) * ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) := by
    intro T
    have hT : (∏ v ∈ T, v.asIdeal ^ (-(e v)).toNat) ∣ Ideal.span {b} :=
      Finset.prod_dvd_of_coprime
        (fun v _ w _ hvw => IsDedekindDomain.HeightOneSpectrum.isCoprime_pow_of_ne v w hvw _ _)
        (fun v _ => hdvd v)
    have hT' := map_dvd (Ideal.absNorm (S := 𝓞 F)) hT
    simp only [map_prod, map_pow, Ideal.absNorm_span_singleton] at hT'
    have hle : (∏ v ∈ T, Ideal.absNorm v.asIdeal ^ (-(e v)).toNat) ≤ (Algebra.norm ℤ b).natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr (Algebra.norm_ne_zero_iff.mpr hb0)) hT'
    have hcast : (∏ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(e v)).toNat)
        = ((∏ v ∈ T, Ideal.absNorm v.asIdeal ^ (-(e v)).toNat : ℕ) : ℝ) := by
      simp only [Nat.cast_prod, Nat.cast_pow]
    have hR : (((Algebra.norm ℤ b).natAbs : ℕ) : ℝ)
        = ((|Algebra.norm ℚ (algebraMap (𝓞 F) F a)| : ℚ) : ℝ) * ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) := by
      rw [Nat.cast_natAbs, ← Rat.cast_intCast, Int.cast_abs, ← hNb, ← hab, map_mul, abs_mul, Rat.cast_mul]
    rw [hcast, ← hR]
    exact Nat.cast_le.mpr hle
  by_cases hfin : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(e v)).toNat
  · rw [finprod_eq_prod _ hfin]
    exact key _
  · rw [finprod_of_infinite_mulSupport hfin]
    have h := key ∅
    rwa [Finset.prod_empty] at h

private theorem T1F3_prod_le_finprod {ι : Type} (g : ι → ℝ) (hg1 : ∀ i, 1 ≤ g i)
    (hfin : (Function.mulSupport g).Finite) (T : Finset ι) :
    ∏ i ∈ T, g i ≤ ∏ᶠ i, g i := by
  classical
  rw [finprod_eq_prod_of_mulSupport_subset g (s := T ∪ hfin.toFinset)
    (fun i hi => by simp only [Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inr hi)]
  rw [← Finset.union_sdiff_self_eq_union, Finset.prod_union Finset.disjoint_sdiff]
  have h1 : (1 : ℝ) ≤ ∏ i ∈ hfin.toFinset \ T, g i := by
    rw [← Finset.prod_const_one (s := hfin.toFinset \ T)]
    exact Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ => hg1 i
  have h0 : 0 ≤ ∏ i ∈ T, g i := Finset.prod_nonneg fun i _ => zero_le_one.trans (hg1 i)
  exact le_mul_of_one_le_right h0 h1

private theorem T1F3_one_le_absNorm (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 := fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr h

private theorem T1F3_valued_freq (F : Type) [Field F] [NumberField F] (ξ : F) (uf : (AdeleRing (𝓞 F) F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((algebraMap F (AdeleRing (𝓞 F) F) ξ * (uf : AdeleRing (𝓞 F) F)).2 v)
      = v.valuation F ξ * Valued.v ((uf : AdeleRing (𝓞 F) F).2 v) := by
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ξ, ← map_mul]
  rfl

open scoped Classical in

private theorem T1F3_finBound (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ)
    (thr : HeightOneSpectrum (𝓞 F) → ℤ)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (hthr : ∀ v ∉ S, thr v = 0)
    (hΦ1 : ∀ (j : Fin n), ∀ v ∉ S, ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v w = 1 → Φ j v w s = 1)
    (hΦ0 : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w : v.adicCompletion F) (s : ℂ),
      w ≠ 0 → WithZero.exp (thr v) < Valued.v w → Φ j v w s = 0)
    (hΦb : ∀ R : ℝ, ∃ (M : ℝ) (κ : ℕ), 0 ≤ M ∧ ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F))
      (w : v.adicCompletion F) (e : ℤ) (s : ℂ), ‖s‖ ≤ R → Valued.v w = WithZero.exp e →
      ‖Φ j v w s‖ ≤ (if v ∈ S then M else 1) * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat) ^ κ)
    (L : HeightOneSpectrum (𝓞 F) → ℤ) (hLfin : (Function.support L).Finite) (hL0 : ∀ v, 0 ≤ L v) (R : ℝ) :
    ∃ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (c : ℝ), 0 ≤ c ∧
      ∀ (j : Fin n) (s : ℂ), ‖s‖ ≤ R → ∀ (uf : (AdeleRing (𝓞 F) F)ˣ),
        (∀ v : HeightOneSpectrum (𝓞 F), WithZero.exp (-(L v)) ≤ Valued.v ((uf : AdeleRing (𝓞 F) F).2 v) ∧
          Valued.v ((uf : AdeleRing (𝓞 F) F).2 v) ≤ WithZero.exp (L v)) →
        ∀ (ξ : {ξ : F // ξ ≠ 0}),
          ((ξ : F) ∉ I → ∏ᶠ v : HeightOneSpectrum (𝓞 F),
            Φ j v ((algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (uf : AdeleRing (𝓞 F) F)).2 v) s = 0) ∧
          ‖∏ᶠ v : HeightOneSpectrum (𝓞 F),
            Φ j v ((algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (uf : AdeleRing (𝓞 F) F)).2 v) s‖
            ≤ c * (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k := by

  set Nf : HeightOneSpectrum (𝓞 F) → ℤ := fun v => thr v + L v with hNf
  have hNfin : (Function.support Nf).Finite := by
    refine (S.finite_toSet.union hLfin).subset fun v hv => ?_
    by_contra hv'
    simp only [Set.mem_union, Finset.mem_coe, Function.mem_support, not_or, not_not] at hv'
    exact hv (by simp only [hNf, hthr v hv'.1, hv'.2, add_zero])
  obtain ⟨I, -, hI⟩ := T1F3_exists_fractionalIdeal_ne_zero_mem_of_forall_valued_le F Nf hNfin
  obtain ⟨c₀, hc₀, hc₀I⟩ := T1F3_exists_pos_finprod_absNorm_pow_toNat_neg_le_mul_abs_norm F I
  obtain ⟨M, κ, hM, hb⟩ := hΦb R

  set CL : ℝ := ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (L v).toNat with hCL
  have hN1 := T1F3_one_le_absNorm F
  have hCL0 : 0 ≤ CL := finprod_nonneg fun v => by positivity
  refine ⟨κ, I, M ^ S.card * (c₀ * CL) ^ κ, by positivity, fun j s hs uf huf ξ => ?_⟩

  set x : FiniteAdeleRing (𝓞 F) F := (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (uf : AdeleRing (𝓞 F) F)).2
    with hx
  have hvalξ0 : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (ξ : F) ≠ 0 :=
    fun v => (Valuation.ne_zero_iff _).mpr ξ.2
  have hvalu0 : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((uf : AdeleRing (𝓞 F) F).2 v) ≠ 0 := by
    intro v h0
    have := (huf v).1
    rw [h0] at this
    exact WithZero.exp_ne_zero (le_zero_iff.mp this)
  set eξ : HeightOneSpectrum (𝓞 F) → ℤ := fun v => WithZero.log (v.valuation F (ξ : F)) with heξ
  set eu : HeightOneSpectrum (𝓞 F) → ℤ := fun v => WithZero.log (Valued.v ((uf : AdeleRing (𝓞 F) F).2 v)) with heu
  have hvalξ : ∀ v, v.valuation F (ξ : F) = WithZero.exp (eξ v) := fun v => (WithZero.exp_log (hvalξ0 v)).symm
  have hvalu : ∀ v, Valued.v ((uf : AdeleRing (𝓞 F) F).2 v) = WithZero.exp (eu v) :=
    fun v => (WithZero.exp_log (hvalu0 v)).symm
  have hvalx : ∀ v, Valued.v (x v) = WithZero.exp (eξ v + eu v) := by
    intro v
    rw [hx, T1F3_valued_freq, hvalξ, hvalu, WithZero.exp_add]
  have hx0 : ∀ v, x v ≠ 0 := by
    intro v h0
    have := hvalx v
    rw [h0, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  have heuL : ∀ v, -(L v) ≤ eu v := fun v => WithZero.exp_le_exp.mp (by rw [← hvalu]; exact (huf v).1)

  have hfinx : {v : HeightOneSpectrum (𝓞 F) | Valued.v (x v) ≠ 1}.Finite := by
    have h := T1F3_finite_setOf_valued_ne_one F
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 (ξ : F) ξ.2) * uf)
    have hx' : (((Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 (ξ : F) ξ.2) * uf :
        (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 = x := by
      simp [hx, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_mk0]
    rwa [hx'] at h
  set T : Finset (HeightOneSpectrum (𝓞 F)) := S ∪ hfinx.toFinset with hT
  have hsupp : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => Φ j v (x v) s) ⊆ (T : Set _) := by
    intro v hv
    rw [hT, Finset.coe_union, Set.mem_union, Finset.mem_coe, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    by_contra h
    simp only [not_or, not_not] at h
    exact hv (hΦ1 j v h.1 (x v) s h.2)
  have hprod : ∏ᶠ v : HeightOneSpectrum (𝓞 F), Φ j v (x v) s = ∏ v ∈ T, Φ j v (x v) s :=
    finprod_eq_prod_of_mulSupport_subset _ hsupp

  have hvan : (ξ : F) ∉ I → ∏ᶠ v : HeightOneSpectrum (𝓞 F), Φ j v (x v) s = 0 := by
    intro hξI
    obtain ⟨v₀, hv₀⟩ : ∃ v₀ : HeightOneSpectrum (𝓞 F), ¬ v₀.valuation F (ξ : F) ≤ WithZero.exp (Nf v₀) :=
      not_forall.mp fun hall => hξI (hI (ξ : F) hall)
    rw [not_le, hvalξ, WithZero.exp_lt_exp] at hv₀
    have hlt : WithZero.exp (thr v₀) < Valued.v (x v₀) := by
      rw [hvalx, WithZero.exp_lt_exp]
      have := heuL v₀
      simp only [hNf] at hv₀
      omega
    have hzero : Φ j v₀ (x v₀) s = 0 := hΦ0 j v₀ (x v₀) s (hx0 v₀) hlt
    have hv₀T : v₀ ∈ T := by
      by_contra h
      have h1 : Φ j v₀ (x v₀) s = 1 := by
        by_contra h1
        exact h (hsupp h1)
      rw [hzero] at h1
      exact zero_ne_one h1
    rw [hprod]
    exact Finset.prod_eq_zero hv₀T hzero
  refine ⟨hvan, ?_⟩

  by_cases hξI : (ξ : F) ∈ I
  swap
  · rw [hvan hξI, norm_zero]
    positivity

  have hplace : ∀ v ∈ T, ‖Φ j v (x v) s‖ ≤ (if v ∈ S then M else 1)
      * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(eξ v)).toNat * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (L v).toNat) ^ κ := by
    intro v _
    refine (hb j v (x v) (eξ v + eu v) s hs (hvalx v)).trans ?_
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ κ) ?_
    · rw [← pow_add]
      refine pow_le_pow_right₀ (hN1 v) ?_
      have := heuL v
      omega
    · split_ifs
      · exact hM
      · exact zero_le_one

  have hST : S ⊆ T := Finset.subset_union_left
  have hMprod : ∏ v ∈ T, (if v ∈ S then M else (1 : ℝ)) = M ^ S.card := by
    rw [← Finset.prod_subset hST (fun v _ hvS => if_neg hvS)]
    rw [Finset.prod_congr rfl (fun v hv => if_pos hv), Finset.prod_const]

  have hfin1 : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(eξ v)).toNat).Finite := by
    have h := T1F3_finite_setOf_valued_ne_one F
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 (ξ : F) ξ.2))
    refine h.subset fun v hv => ?_
    rw [Set.mem_setOf_eq]
    intro h1
    apply hv
    have h1' : v.valuation F (ξ : F) = 1 := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (ξ : F)]
      simpa [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_mk0] using h1
    show ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(eξ v)).toNat = 1
    rw [heξ]
    simp only [h1', WithZero.log_one, neg_zero, Int.toNat_zero, pow_zero]
  have hfin2 : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (L v).toNat).Finite := by
    refine hLfin.subset fun v hv => ?_
    rw [Function.mem_support]
    intro h0
    apply hv
    show ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (L v).toNat = 1
    rw [h0, Int.toNat_zero, pow_zero]
  have hle1 : ∏ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(eξ v)).toNat
      ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(eξ v)).toNat :=
    T1F3_prod_le_finprod _ (fun v => one_le_pow₀ (hN1 v)) hfin1 T
  have hle2 : ∏ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (L v).toNat ≤ CL :=
    T1F3_prod_le_finprod _ (fun v => one_le_pow₀ (hN1 v)) hfin2 T
  have hc₀' := hc₀I (ξ : F) hξI ξ.2 eξ hvalξ
  have hNξ0 : 0 ≤ ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ) := by exact_mod_cast abs_nonneg _

  rw [hprod]
  calc ‖∏ v ∈ T, Φ j v (x v) s‖ = ∏ v ∈ T, ‖Φ j v (x v) s‖ := norm_prod _ _
    _ ≤ ∏ v ∈ T, ((if v ∈ S then M else 1)
        * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(eξ v)).toNat * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (L v).toNat) ^ κ) :=
        Finset.prod_le_prod (fun v _ => norm_nonneg _) hplace
    _ = M ^ S.card * ((∏ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(eξ v)).toNat)
        * ∏ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (L v).toNat) ^ κ := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_mul_distrib, hMprod]
    _ ≤ M ^ S.card * ((c₀ * ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) * CL) ^ κ := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ κ) (by positivity)
        exact mul_le_mul (hle1.trans hc₀') hle2 (Finset.prod_nonneg fun v _ => by positivity) (by positivity)
    _ ≤ M ^ S.card * ((c₀ * CL) * max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ κ := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ κ) (by positivity)
        calc c₀ * ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ) * CL = (c₀ * CL) * ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ) := by
              ring
          _ ≤ (c₀ * CL) * max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ) :=
              mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
    _ = M ^ S.card * (c₀ * CL) ^ κ * (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ κ := by
        rw [mul_pow]; ring

end FinBound

section HFMain

open IsDedekindDomain NumberField

private theorem HF_exists_pos_le_abs_norm_of_mem (F : Type) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ξ : F, ξ ∈ I → ξ ≠ 0 → c₀ ≤ ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) := by
  obtain ⟨a, aI, ha, hI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have haF : algebraMap (𝓞 F) F a ≠ 0 := NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ha
  have hNa : (0 : ℚ) < |Algebra.norm ℚ (algebraMap (𝓞 F) F a)| :=
    abs_pos.mpr (Algebra.norm_ne_zero_iff.mpr haF)
  have hNaR : (0 : ℝ) < ((|Algebra.norm ℚ (algebraMap (𝓞 F) F a)| : ℚ) : ℝ) := Rat.cast_pos.mpr hNa
  refine ⟨(((|Algebra.norm ℚ (algebraMap (𝓞 F) F a)| : ℚ) : ℝ))⁻¹, inv_pos.mpr hNaR, fun ξ hξ hξ0 => ?_⟩
  rw [hI, FractionalIdeal.mem_singleton_mul] at hξ
  obtain ⟨y, hy, hξy⟩ := hξ
  obtain ⟨b, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
  have hab : algebraMap (𝓞 F) F a * ξ = algebraMap (𝓞 F) F b := by
    rw [hξy, mul_inv_cancel_left₀ haF]
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    exact mul_ne_zero haF hξ0 hab
  have hNb : Algebra.norm ℚ (algebraMap (𝓞 F) F b) = ((Algebra.norm ℤ b : ℤ) : ℚ) :=
    (Algebra.coe_norm_int b).symm
  have h1 : (1 : ℚ) ≤ |Algebra.norm ℚ (algebraMap (𝓞 F) F b)| := by
    rw [hNb, ← Int.cast_abs, ← Int.cast_one, Int.cast_le]
    exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr hb0)
  have h2 : |Algebra.norm ℚ (algebraMap (𝓞 F) F a)| * |Algebra.norm ℚ ξ|
      = |Algebra.norm ℚ (algebraMap (𝓞 F) F b)| := by
    rw [← abs_mul, ← map_mul, hab]
  rw [inv_le_iff_one_le_mul₀ hNaR, ← Rat.cast_mul, mul_comm, h2]
  exact_mod_cast h1

open scoped Classical in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) (thr : HeightOneSpectrum (𝓞 F) → ℤ)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (_hthr : ∀ v ∉ S, thr v = 0)
    (_hΦd : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w : v.adicCompletion F), Differentiable ℂ (Φ j v w))
    (_hΦ1 : ∀ (j : Fin n), ∀ v ∉ S, ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v w = 1 → Φ j v w s = 1)
    (_hΦ0 : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w : v.adicCompletion F) (s : ℂ), w ≠ 0 →
      WithZero.exp (thr v) < Valued.v w → Φ j v w s = 0)
    (_hΦb : ∀ R : ℝ, ∃ (M : ℝ) (κ : ℕ), 0 ≤ M ∧ ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F))
      (w : v.adicCompletion F) (e : ℤ) (s : ℂ), ‖s‖ ≤ R → Valued.v w = WithZero.exp e →
        ‖Φ j v w s‖ ≤ (if v ∈ S then M else 1) * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat) ^ κ)
    (_hΦlc : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w₀ : v.adicCompletion F), w₀ ≠ 0 → ∃ δ : ℤ,
      ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v (w - w₀) ≤ WithZero.exp δ → Φ j v w s = Φ j v w₀ s) :
    (∀ (x₀ : (AdeleRing (𝓞 F) F)ˣ) (j : Fin n),
      Continuous fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        Φ j v (((x₀ : AdeleRing (𝓞 F) F) * (p.2 : AdeleRing (𝓞 F) F)).2 v) p.1) ∧
    (∀ (U : Set (AdeleRing (𝓞 F) F)ˣ), IsCompact U → ∀ R : ℝ,
      ∃ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (c₀ c : ℝ), 0 < c₀ ∧ 0 ≤ c ∧
        (∀ ξ : F, ξ ∈ I → ξ ≠ 0 → c₀ ≤ ((|Algebra.norm ℚ ξ| : ℚ) : ℝ)) ∧
        ∀ (j : Fin n) (s : ℂ), ‖s‖ ≤ R → ∀ u ∈ U, ∀ ξ : F, ξ ≠ 0 →
          (ξ ∉ I → ∏ᶠ v : HeightOneSpectrum (𝓞 F),
              Φ j v ((algebraMap F (AdeleRing (𝓞 F) F) ξ * (u : AdeleRing (𝓞 F) F)).2 v) s = 0) ∧
          ‖∏ᶠ v : HeightOneSpectrum (𝓞 F),
              Φ j v ((algebraMap F (AdeleRing (𝓞 F) F) ξ * (u : AdeleRing (𝓞 F) F)).2 v) s‖
            ≤ c * (max 1 ((|Algebra.norm ℚ ξ| : ℚ) : ℝ)) ^ k) := by
  refine ⟨fun x₀ j => T1F4_continuous_finprod F S n thr Φ _hΦd _hΦ1 _hΦlc x₀ j, fun U hU R => ?_⟩
  obtain ⟨L, hLfin, hL0, hL⟩ := HFfin.exists_finite_support_valuation_bounds_of_isCompact F U hU
  obtain ⟨k, I, c, hc0, hF⟩ := T1F3_finBound F S n thr Φ _hthr _hΦ1 _hΦ0 _hΦb L hLfin hL0 R
  obtain ⟨c₀, hc₀, hc₀I⟩ := HF_exists_pos_le_abs_norm_of_mem F I
  refine ⟨k, I, c₀, c, hc₀, hc0, hc₀I, fun j s hs u hu ξ hξ => ?_⟩
  exact hF j s hs u (hL u hu) ⟨ξ, hξ⟩

end HFMain

end S_AutomorphicForm_continuous_finprod_localFactor_and_exists_fractionalIdeal_norm_finprod_le_of_isCompact
end P2MW
export P2MW.S_AutomorphicForm_continuous_finprod_localFactor_and_exists_fractionalIdeal_norm_finprod_le_of_isCompact (solution)
