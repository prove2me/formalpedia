-- Prove2me | solution 1 for AutomorphicForm.exists_mul_sigmaTensor_eq_includeRight_inv_mul_of_forall_ne_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/6736490e-54a1-5a3c-b543-f701e92af675

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_GroupCohomology_TateCohomology
import Theorems.Thm_NumberField_PlaceDecomp_card_tateH0_units_eq_card_and_subsingleton_tateHneg1
import Theorems.Thm_NumberField_PlaceDecomp_card_over_mul_card_decomp_above
import Theorems.Thm_NumberField_PlaceDecomp_smul_algebraMap
import Theorems.Thm_NumberField_PlaceDecomp_forall_smul_eq_iff_mem_range_adicCompletionSemialgHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_mul_sigmaTensor_eq_includeRight_inv_mul_of_forall_ne_of_finrank_eq_two

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions NumberField.PlaceDecomp

namespace AutomorphicForm
p2m_export "AutomorphicForm" "sigmaTensor"
namespace LocalNormIndexTwo
p2m_open "AutomorphicForm"

section PartA

variable {K L : Type} [Field K] [Field L] [Algebra K L] {A : Type} [CommRing A] [Algebra K A]

theorem sigmaTensor_tmul (σ : L ≃ₐ[K] L) (a : L) (x : A) :
    sigmaTensor K L A σ (a ⊗ₜ[K] x) = σ a ⊗ₜ[K] x := by
  simp [sigmaTensor]

theorem sigmaTensor_includeRight (σ : L ≃ₐ[K] L) (x : A) :
    sigmaTensor K L A σ ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) x) =
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) x := by
  rw [Algebra.TensorProduct.includeRight_apply, sigmaTensor_tmul, map_one]

theorem sigmaTensor_symm_sigmaTensor (σ : L ≃ₐ[K] L) (e : L ⊗[K] A) :
    sigmaTensor K L A σ.symm (sigmaTensor K L A σ e) = e := by
  induction e using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [sigmaTensor_tmul, sigmaTensor_tmul, AlgEquiv.symm_apply_apply]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem sigmaTensor_injective (σ : L ≃ₐ[K] L) : Function.Injective (sigmaTensor K L A σ) :=
  Function.LeftInverse.injective (sigmaTensor_symm_sigmaTensor σ)

end PartA

section PartB

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

noncomputable abbrev psi (v : HeightOneSpectrum (𝓞 K)) :
    L ⊗[K] v.adicCompletion K ≃ₐ[L] Π w : v.Extension (𝓞 L), w.1.adicCompletion L :=
  HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v

variable {K L}

theorem psi_tmul (v : HeightOneSpectrum (𝓞 K)) (a : L) (x : v.adicCompletion K)
    (w : v.Extension (𝓞 L)) :
    psi K L v (a ⊗ₜ[K] x) w =
      algebraMap L (w.1.adicCompletion L) a *
        algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x := by
  rw [psi, HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv, AlgEquiv.coe_ofBijective]
  exact HeightOneSpectrum.adicCompletion.baseChange_tmul_apply K L (𝓞 L) v a x w

theorem psi_includeRight (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K)
    (w : v.Extension (𝓞 L)) :
    psi K L v ((Algebra.TensorProduct.includeRight :
        v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) x) w =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x := by
  rw [Algebra.TensorProduct.includeRight_apply, psi_tmul, map_one, one_mul]

abbrev w0 (K : Type) [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    (w₁ : HeightOneSpectrum (𝓞 L)) : (HeightOneSpectrum.under (𝓞 K) w₁).Extension (𝓞 L) :=
  ⟨w₁, rfl⟩

noncomputable abbrev iota (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L]
    [Algebra K L] (w₁ : HeightOneSpectrum (𝓞 L)) :
    (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K →ₛₐ[algebraMap K L]
      (w0 K w₁).1.adicCompletion L :=
  HeightOneSpectrum.Extension.adicCompletionSemialgHom K L (w0 K w₁)

theorem psi_tmul_w0 (w₁ : HeightOneSpectrum (𝓞 L)) (a : L)
    (x : (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K) :
    psi K L (HeightOneSpectrum.under (𝓞 K) w₁) (a ⊗ₜ[K] x) (w0 K w₁) =
      algebraMap L (w₁.adicCompletion L) a * iota K L w₁ x :=
  psi_tmul _ a x _

theorem psi_includeRight_w0 (w₁ : HeightOneSpectrum (𝓞 L))
    (x : (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K) :
    psi K L (HeightOneSpectrum.under (𝓞 K) w₁) ((Algebra.TensorProduct.includeRight :
        _ →ₐ[K] L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K) x) (w0 K w₁) =
      iota K L w₁ x :=
  psi_includeRight _ x _

theorem smul_iota (w₁ : HeightOneSpectrum (𝓞 L)) [IsGalois K L]
    (τ : PlaceDecomp.decomp K L w₁) (x : (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K) :
    τ • iota K L w₁ x = iota K L w₁ x :=
  (NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom K L w₁
    (iota K L w₁ x)).2 ⟨x, rfl⟩ τ

theorem psi_sigmaTensor (w₁ : HeightOneSpectrum (𝓞 L)) [IsGalois K L]
    (τ : PlaceDecomp.decomp K L w₁)
    (e : L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K) :
    psi K L (HeightOneSpectrum.under (𝓞 K) w₁)
        (sigmaTensor K L ((HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K)
          (τ : L ≃ₐ[K] L) e) (w0 K w₁) =
      τ • psi K L (HeightOneSpectrum.under (𝓞 K) w₁) e (w0 K w₁) := by
  induction e using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, Pi.zero_apply, smul_zero]
  | tmul a x =>
      rw [sigmaTensor_tmul, psi_tmul_w0, psi_tmul_w0, smul_mul', smul_iota,
        NumberField.PlaceDecomp.smul_algebraMap]
  | add a b ha hb => rw [map_add, map_add, Pi.add_apply, ha, hb, map_add, Pi.add_apply, smul_add]

end PartB

section PartC

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem eq_of_card_eq_two {A : Type*} [AddGroup A] (h : Nat.card A = 2) {a b : A}
    (ha : a ≠ 0) (hb : b ≠ 0) : a = b := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : A)).1 h
  exact (hy a ha).trans (hy b hb).symm

theorem psi_w0_injective (w₁ : HeightOneSpectrum (𝓞 L))
    (hone : ∀ w : (HeightOneSpectrum.under (𝓞 K) w₁).Extension (𝓞 L), w.1 = w₁)
    {e e' : L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K}
    (h : psi K L (HeightOneSpectrum.under (𝓞 K) w₁) e (w0 K w₁) =
      psi K L (HeightOneSpectrum.under (𝓞 K) w₁) e' (w0 K w₁)) : e = e' := by
  apply (psi K L (HeightOneSpectrum.under (𝓞 K) w₁)).injective
  funext w
  obtain ⟨w, hw⟩ := w
  obtain rfl : w = w₁ := hone ⟨w, hw⟩
  exact h

theorem psi_w0_surjective (w₁ : HeightOneSpectrum (𝓞 L)) (y : w₁.adicCompletion L) :
    ∃ e : L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K,
      psi K L (HeightOneSpectrum.under (𝓞 K) w₁) e (w0 K w₁) = y := by
  obtain ⟨g, hg⟩ := Function.surjective_eval
    (β := fun w : (HeightOneSpectrum.under (𝓞 K) w₁).Extension (𝓞 L) => w.1.adicCompletion L)
    (w0 K w₁) y
  obtain ⟨e, he⟩ := (psi K L (HeightOneSpectrum.under (𝓞 K) w₁)).surjective g
  exact ⟨e, by rw [he]; exact hg⟩

noncomputable abbrev unitIota (K : Type) [Field K] [NumberField K] (L : Type) [Field L]
    [NumberField L] [Algebra K L] (w₁ : HeightOneSpectrum (𝓞 L))
    (s : ((HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K)ˣ) : (w₁.adicCompletion L)ˣ :=
  Units.map (iota K L w₁).toRingHom.toMonoidHom s

theorem coe_unitIota (w₁ : HeightOneSpectrum (𝓞 L))
    (s : ((HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K)ˣ) :
    (unitIota K L w₁ s : w₁.adicCompletion L) = iota K L w₁ (s : _) := rfl

theorem unitIota_mem_invariants [IsGalois K L] (w₁ : HeightOneSpectrum (𝓞 L))
    (s : ((HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K)ˣ) :
    Additive.ofMul (unitIota K L w₁ s) ∈
      (Rep.ofMulDistribMulAction (PlaceDecomp.decomp K L w₁)
        (w₁.adicCompletion L)ˣ).ρ.invariants := by
  intro τ
  change Additive.ofMul (τ • unitIota K L w₁ s) = Additive.ofMul (unitIota K L w₁ s)
  congr 1
  ext
  rw [PlaceDecomp.coe_smul_units, coe_unitIota, smul_iota]

noncomputable def cls [IsGalois K L] (w₁ : HeightOneSpectrum (𝓞 L))
    [Fintype (PlaceDecomp.decomp K L w₁)]
    (s : ((HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K)ˣ) :
    (Rep.ofMulDistribMulAction (PlaceDecomp.decomp K L w₁) (w₁.adicCompletion L)ˣ).tateH0 :=
  Submodule.Quotient.mk ⟨Additive.ofMul (unitIota K L w₁ s), unitIota_mem_invariants w₁ s⟩

theorem cls_inv_mul [IsGalois K L] (w₁ : HeightOneSpectrum (𝓞 L))
    [Fintype (PlaceDecomp.decomp K L w₁)]
    (s s' : ((HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K)ˣ) :
    cls w₁ (s⁻¹ * s') = cls w₁ s' - cls w₁ s := by
  rw [cls, cls, cls, ← Submodule.Quotient.mk_sub]
  congr 1
  apply Subtype.ext
  change Additive.ofMul (unitIota K L w₁ (s⁻¹ * s')) =
    Additive.ofMul (unitIota K L w₁ s') - Additive.ofMul (unitIota K L w₁ s)
  rw [unitIota, map_mul, map_inv, ofMul_mul, ofMul_inv, neg_add_eq_sub]

theorem exists_prod_smul_eq_of_cls_eq_zero [IsGalois K L] (w₁ : HeightOneSpectrum (𝓞 L))
    [Fintype (PlaceDecomp.decomp K L w₁)]
    (s : ((HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K)ˣ) (h : cls w₁ s = 0) :
    ∃ y : (w₁.adicCompletion L)ˣ, ∏ τ : PlaceDecomp.decomp K L w₁, τ • y = unitIota K L w₁ s := by
  obtain ⟨c, hc⟩ := (Submodule.Quotient.mk_eq_zero _).1 h
  obtain ⟨y, rfl⟩ := Representation.Coinvariants.mk_surjective _ c
  refine ⟨Additive.toMul y, ?_⟩
  have h1 := congrArg Subtype.val hc
  rw [Representation.normBar_mk, Representation.coe_normToInvariants_apply] at h1
  rw [← Representation.norm_ofMulDistribMulAction_eq]
  exact congrArg Additive.toMul h1

theorem nonsplit [Algebra.IsQuadraticExtension K L] (w₁ : HeightOneSpectrum (𝓞 L))
    (σ' : PlaceDecomp.decomp K L w₁) (h1 : (1 : PlaceDecomp.decomp K L w₁) ≠ σ')
    (huniv : ∀ τ : PlaceDecomp.decomp K L w₁, τ = 1 ∨ τ = σ')
    (hone : ∀ w : (HeightOneSpectrum.under (𝓞 K) w₁).Extension (𝓞 L), w.1 = w₁)
    (s s' : ((HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K)ˣ)
    (hs : ∀ e : L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K,
      e * sigmaTensor K L ((HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K)
          (σ' : L ≃ₐ[K] L) e ≠
        (Algebra.TensorProduct.includeRight :
          (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K →ₐ[K]
            L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K) s)
    (hs' : ∀ e : L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K,
      e * sigmaTensor K L ((HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K)
          (σ' : L ≃ₐ[K] L) e ≠
        (Algebra.TensorProduct.includeRight :
          (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K →ₐ[K]
            L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K) s') :
    ∃ e : L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K,
      e * sigmaTensor K L ((HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K)
          (σ' : L ≃ₐ[K] L) e =
        (Algebra.TensorProduct.includeRight :
          (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K →ₐ[K]
            L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K)
          ((s⁻¹ * s' : ((HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K)ˣ) :
            (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K) := by
  classical
  haveI : Fintype (PlaceDecomp.decomp K L w₁) := Fintype.ofFinite _

  have hcard : Nat.card (PlaceDecomp.decomp K L w₁) = 2 :=
    (Nat.card_eq_two_iff' (1 : PlaceDecomp.decomp K L w₁)).2
      ⟨σ', h1.symm, fun τ hτ => (huniv τ).resolve_left hτ⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclic (PlaceDecomp.decomp K L w₁) := isCyclic_of_prime_card (p := 2) hcard
  have huniv' : (Finset.univ : Finset (PlaceDecomp.decomp K L w₁)) = {1, σ'} := by
    ext τ
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact huniv τ

  have hH : Nat.card (Rep.ofMulDistribMulAction (PlaceDecomp.decomp K L w₁)
      (w₁.adicCompletion L)ˣ).tateH0 = 2 :=
    (NumberField.PlaceDecomp.card_tateH0_units_eq_card_and_subsingleton_tateHneg1 K L w₁).1.trans
      hcard

  have key : ∀ t : ((HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K)ˣ, cls w₁ t = 0 →
      ∃ e : L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K,
        e * sigmaTensor K L ((HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K)
            (σ' : L ≃ₐ[K] L) e =
          (Algebra.TensorProduct.includeRight :
            (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K →ₐ[K]
              L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K) (t : _) := by
    intro t ht
    obtain ⟨y, hy⟩ := exists_prod_smul_eq_of_cls_eq_zero w₁ t ht
    rw [huniv', Finset.prod_pair h1, one_smul] at hy
    have hyv := congrArg (fun u : (w₁.adicCompletion L)ˣ => (u : w₁.adicCompletion L)) hy
    simp only [Units.val_mul, PlaceDecomp.coe_smul_units, coe_unitIota] at hyv
    obtain ⟨e, he⟩ := psi_w0_surjective (K := K) w₁ (y : w₁.adicCompletion L)
    refine ⟨e, psi_w0_injective w₁ hone ?_⟩
    rw [map_mul, Pi.mul_apply, psi_sigmaTensor, he, psi_includeRight_w0]
    exact hyv
  have hcs : cls w₁ s ≠ 0 := fun h => by obtain ⟨e, he⟩ := key s h; exact hs e he
  have hcs' : cls w₁ s' ≠ 0 := fun h => by obtain ⟨e, he⟩ := key s' h; exact hs' e he
  have h0 : cls w₁ (s⁻¹ * s') = 0 := by
    rw [cls_inv_mul, eq_of_card_eq_two hH hcs hcs', sub_self]
  exact key _ h0

end PartC

section PartD

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem eq_zero_or_eq_one_of_mul_self {F : Type*} [Field F] {p : F} (h : p * p = p) :
    p = 0 ∨ p = 1 := by
  have h' : p * (p - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.1 h' with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.1 h1)

theorem split [Algebra.IsQuadraticExtension K L] (σ : L ≃ₐ[K] L) (hσ : ∃ a : L, σ a ≠ a)
    (w₁ : HeightOneSpectrum (𝓞 L)) (hbot : PlaceDecomp.decomp K L w₁ = ⊥)
    (htwo : Nat.card ((HeightOneSpectrum.under (𝓞 K) w₁).Extension (𝓞 L)) = 2)
    (s : (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K) :
    ∃ e : L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K,
      e * sigmaTensor K L ((HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K) σ e =
        (Algebra.TensorProduct.includeRight :
          (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K →ₐ[K]
            L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K) s := by
  classical

  have hsurj : ∀ y : w₁.adicCompletion L, ∃ x, iota K L w₁ x = y := fun y =>
    (NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom K L w₁ y).1
      fun τ => by
        have hτ : τ = 1 := Subtype.ext (Subgroup.mem_bot.1 ((le_of_eq hbot) τ.2))
        rw [hτ, one_smul]

  obtain ⟨w₂, hne, huniq⟩ := (Nat.card_eq_two_iff' (w0 K w₁)).1 htwo
  have hw : ∀ w : (HeightOneSpectrum.under (𝓞 K) w₁).Extension (𝓞 L), w = w0 K w₁ ∨ w = w₂ :=
    fun w => or_iff_not_imp_left.2 (huniq w)
  have hfun : ∀ g g' : (Π w : (HeightOneSpectrum.under (𝓞 K) w₁).Extension (𝓞 L),
      w.1.adicCompletion L), g (w0 K w₁) = g' (w0 K w₁) → g w₂ = g' w₂ → g = g' :=
    fun g g' ha hb => funext fun w => by rcases hw w with rfl | rfl <;> assumption

  set ψ := psi K L (HeightOneSpectrum.under (𝓞 K) w₁) with hψ
  let T : (Π w : (HeightOneSpectrum.under (𝓞 K) w₁).Extension (𝓞 L), w.1.adicCompletion L) →+*
      (Π w : (HeightOneSpectrum.under (𝓞 K) w₁).Extension (𝓞 L), w.1.adicCompletion L) :=
    ψ.toRingEquiv.toRingHom.comp
      ((sigmaTensor K L ((HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K) σ).comp
        ψ.symm.toRingEquiv.toRingHom)
  have hT : ∀ e, T (ψ e) =
      ψ (sigmaTensor K L ((HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K) σ e) := by
    intro e
    change ψ (sigmaTensor K L _ σ (ψ.symm (ψ e))) = _
    rw [AlgEquiv.symm_apply_apply]
  have hTinj : Function.Injective T := by
    intro g g' h
    have h' : sigmaTensor K L _ σ (ψ.symm g) = sigmaTensor K L _ σ (ψ.symm g') := ψ.injective h
    exact ψ.symm.injective (sigmaTensor_injective σ h')
  have hTc : ∀ x, T (ψ ((Algebra.TensorProduct.includeRight :
      (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K →ₐ[K]
        L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K) x)) =
      ψ ((Algebra.TensorProduct.includeRight :
      (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K →ₐ[K]
        L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K) x) := by
    intro x
    rw [hT, sigmaTensor_includeRight]

  set δ : (Π w : (HeightOneSpectrum.under (𝓞 K) w₁).Extension (𝓞 L), w.1.adicCompletion L) :=
    Pi.single (w0 K w₁) 1 with hδ
  have hδ0 : δ (w0 K w₁) = 1 := Pi.single_eq_same _ _
  have hδ2 : δ w₂ = 0 := Pi.single_eq_of_ne hne _
  have hδδ : δ * δ = δ := by rw [hδ, ← Pi.single_mul, mul_one]
  have hTδ : ∀ w, T δ w * T δ w = T δ w := fun w => by rw [← Pi.mul_apply, ← map_mul, hδδ]
  rcases eq_zero_or_eq_one_of_mul_self (hTδ (w0 K w₁)) with ha | ha <;>
    rcases eq_zero_or_eq_one_of_mul_self (hTδ w₂) with hb | hb
  ·
    exfalso
    have h0 : T δ = 0 := hfun _ _ (by rw [ha, Pi.zero_apply]) (by rw [hb, Pi.zero_apply])
    have : δ = 0 := hTinj (by rw [h0, map_zero])
    have := congrFun this (w0 K w₁)
    rw [hδ0, Pi.zero_apply] at this
    exact one_ne_zero this
  ·
    have hT1 : T δ = 1 - δ :=
      hfun _ _ (by rw [ha, Pi.sub_apply, Pi.one_apply, hδ0, sub_self])
        (by rw [hb, Pi.sub_apply, Pi.one_apply, hδ2, sub_zero])
    set c := ψ ((Algebra.TensorProduct.includeRight :
      (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K →ₐ[K]
        L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K) s) with hc
    refine ⟨ψ.symm (c * δ + (1 - δ)), ψ.injective ?_⟩
    rw [map_mul, ← hT, AlgEquiv.apply_symm_apply, map_add, map_mul, map_sub, map_one, hTc, ← hc,
      hT1]
    linear_combination (-(c - 1) ^ 2) * hδδ
  ·
    exfalso
    have hT1 : T δ = δ := hfun _ _ (by rw [ha, hδ0]) (by rw [hb, hδ2])
    obtain ⟨a, haσ⟩ := hσ
    obtain ⟨x, hx⟩ := hsurj (ψ (a ⊗ₜ[K] 1) (w0 K w₁))
    have hcmp : δ * ψ (a ⊗ₜ[K] 1) = δ * ψ ((Algebra.TensorProduct.includeRight :
        (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K →ₐ[K]
          L ⊗[K] (HeightOneSpectrum.under (𝓞 K) w₁).adicCompletion K) x) :=
      hfun _ _ (by rw [Pi.mul_apply, Pi.mul_apply, psi_includeRight_w0, hx])
        (by rw [Pi.mul_apply, Pi.mul_apply, hδ2, zero_mul, zero_mul])
    have h2 := congrArg T hcmp
    rw [map_mul, map_mul, hT1, hTc, ← hcmp, hT, sigmaTensor_tmul] at h2
    have h3 := congrFun h2 (w0 K w₁)
    rw [Pi.mul_apply, Pi.mul_apply, hδ0, one_mul, one_mul, psi_tmul_w0, psi_tmul_w0, map_one,
      mul_one, mul_one] at h3
    exact haσ ((algebraMap L (w₁.adicCompletion L)).injective h3)
  ·
    exfalso
    have h1 : T δ = 1 := hfun _ _ (by rw [ha, Pi.one_apply]) (by rw [hb, Pi.one_apply])
    have : δ = 1 := hTinj (by rw [h1, map_one])
    have := congrFun this w₂
    rw [hδ2, Pi.one_apply] at this
    exact zero_ne_one this

end PartD

section PartE

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem dichotomy [Algebra.IsQuadraticExtension K L] (σ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 K)) :
    (∃ w₁ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₁ = v ∧
        σ ∈ PlaceDecomp.decomp K L w₁ ∧ ∀ w : v.Extension (𝓞 L), w.1 = w₁) ∨
      (∃ w₁ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₁ = v ∧
        PlaceDecomp.decomp K L w₁ = ⊥ ∧ Nat.card (v.Extension (𝓞 L)) = 2) := by
  have hG2 : Nat.card (L ≃ₐ[K] L) = 2 :=
    (IsGalois.card_aut_eq_finrank K L).trans (Algebra.IsQuadraticExtension.finrank_eq_two K L)
  set w₁ := PlaceAbove.above K L v with hw₁def
  have hw₁ : HeightOneSpectrum.under (𝓞 K) w₁ = v :=
    HeightOneSpectrum.ext (PlaceAbove.comap_above K L v)
  haveI : Finite (v.Extension (𝓞 L)) := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  have hcard := NumberField.PlaceDecomp.card_over_mul_card_decomp_above K L v
  change Nat.card (v.Extension (𝓞 L)) * Nat.card (PlaceDecomp.decomp K L w₁) = _ at hcard
  rw [hG2] at hcard
  have hn : Nat.card (v.Extension (𝓞 L)) ∣ 2 := ⟨_, hcard.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).1 hn with h1 | h2
  · left
    rw [h1, one_mul] at hcard
    have htop : PlaceDecomp.decomp K L w₁ = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hcard, hG2])
    refine ⟨w₁, hw₁, by rw [htop]; exact Subgroup.mem_top σ, fun w => ?_⟩
    haveI := (Nat.card_eq_one_iff_unique.1 h1).1
    exact congrArg Subtype.val (Subsingleton.elim w ⟨w₁, hw₁⟩)
  · right
    rw [h2] at hcard
    have hd : Nat.card (PlaceDecomp.decomp K L w₁) = 1 := by omega
    exact ⟨w₁, hw₁, Subgroup.eq_bot_of_card_eq _ hd, h2⟩

theorem main (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (s s' : (v.adicCompletion K)ˣ)
    (hs : ∀ e : L ⊗[K] v.adicCompletion K,
      e * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ e ≠
        (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) s)
    (hs' : ∀ e : L ⊗[K] v.adicCompletion K,
      e * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ e ≠
        (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) s') :
    ∃ e : L ⊗[K] v.adicCompletion K,
      e * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ e =
        (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K)
          ((s⁻¹ * s' : (v.adicCompletion K)ˣ) : v.adicCompletion K) := by
  haveI : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  have hG2 : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans h2

  have hσ1 : σ ≠ 1 := by
    intro h
    have hall : ∀ τ : L ≃ₐ[K] L, τ = 1 := fun τ => by
      have := hgen τ
      rwa [h, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
    have h1 : Nat.card (L ≃ₐ[K] L) = 1 :=
      Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
    omega

  have hGal : ∀ τ : L ≃ₐ[K] L, τ = 1 ∨ τ = σ := by
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[K] L)).1 hG2
    intro τ
    by_cases hτ : τ = 1
    · exact Or.inl hτ
    · exact Or.inr ((huniq τ hτ).trans (huniq σ hσ1).symm)
  have hmove : ∃ a : L, σ a ≠ a := not_forall.1 fun h => hσ1 (AlgEquiv.ext h)
  rcases dichotomy σ v with ⟨w₁, hw₁, hD, hone⟩ | ⟨w₁, hw₁, hbot, htwo⟩
  ·
    subst hw₁
    have h1 : (1 : PlaceDecomp.decomp K L w₁) ≠ ⟨σ, hD⟩ := fun h =>
      hσ1 (congrArg Subtype.val h).symm
    have huniv : ∀ τ : PlaceDecomp.decomp K L w₁, τ = 1 ∨ τ = ⟨σ, hD⟩ := fun τ =>
      (hGal τ).imp (fun h => Subtype.ext h) (fun h => Subtype.ext h)
    exact nonsplit w₁ ⟨σ, hD⟩ h1 huniv hone s s' hs hs'
  ·
    subst hw₁
    obtain ⟨e, he⟩ := split σ hmove w₁ hbot htwo (s : _)
    exact (hs e he).elim

end PartE

end AutomorphicForm.LocalNormIndexTwo

open scoped TensorProduct TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (s s' : (v.adicCompletion K)ˣ)
    (hs : ∀ e : L ⊗[K] v.adicCompletion K,
      e * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ e ≠
        (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) s)
    (hs' : ∀ e : L ⊗[K] v.adicCompletion K,
      e * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ e ≠
        (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) s') :
    ∃ e : L ⊗[K] v.adicCompletion K,
      e * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ e =
        (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K)
          ((s⁻¹ * s' : (v.adicCompletion K)ˣ) : v.adicCompletion K) :=
  AutomorphicForm.LocalNormIndexTwo.main K L h2 σ hgen v s s' hs hs'

end S_AutomorphicForm_exists_mul_sigmaTensor_eq_includeRight_inv_mul_of_forall_ne_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_exists_mul_sigmaTensor_eq_includeRight_inv_mul_of_forall_ne_of_finrank_eq_two (solution)
