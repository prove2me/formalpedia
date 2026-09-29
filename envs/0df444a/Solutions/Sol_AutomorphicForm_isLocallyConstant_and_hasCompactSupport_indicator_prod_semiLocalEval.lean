-- Prove2me | solution 1 for AutomorphicForm.isLocallyConstant_and_hasCompactSupport_indicator_prod_semiLocalEval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/cf83c9df-c625-5621-be53-ea363f43e80c

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isLocallyConstant_and_hasCompactSupport_indicator_prod_semiLocalEval

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace Filter Topology
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace SlL4

section SemiLocal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem semiLocalHomeomorph_apply (x : L ⊗[K] v.adicCompletion K) :
    AutomorphicForm.semiLocalHomeomorph K L v x =
      HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x :=
  rfl

theorem semiLocalEval_apply (a : FiniteAdeleRing (𝓞 L) L) :
    AutomorphicForm.semiLocalEval K L v a =
      (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (fun w : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w.1 a) :=
  rfl

theorem semiLocalHomeomorph_semiLocalEval (a : FiniteAdeleRing (𝓞 L) L) (w : v.Extension (𝓞 L)) :
    AutomorphicForm.semiLocalHomeomorph K L v (AutomorphicForm.semiLocalEval K L v a) w = a w.1 := by
  rw [semiLocalHomeomorph_apply, semiLocalEval_apply, AlgEquiv.apply_symm_apply]
  rfl

theorem semiLocalEval_mem_semiLocalIntegers_iff (a : FiniteAdeleRing (𝓞 L) L) :
    AutomorphicForm.semiLocalEval K L v a ∈ AutomorphicForm.semiLocalIntegers K L v ↔
      ∀ w : v.Extension (𝓞 L), a w.1 ∈ w.1.adicCompletionIntegers L := by
  rw [AutomorphicForm.semiLocalIntegers_eq_preimage, Set.mem_preimage, AutomorphicForm.piIntegers, Set.mem_univ_pi]
  refine forall_congr' fun w => ?_
  rw [semiLocalHomeomorph_semiLocalEval, SetLike.mem_coe]

theorem semiLocalComponent_apply (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (i j : Fin 2) :
    (AutomorphicForm.semiLocalComponent K L v h : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j =
      AutomorphicForm.semiLocalEval K L v ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) :=
  rfl

theorem semiLocalComponent_mem_iff (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    AutomorphicForm.semiLocalComponent K L v h ∈ AutomorphicForm.semiLocalIntegralSet K L v ↔
      ∀ w : v.Extension (𝓞 L), AdelicLevel.finComponent (𝓞 L) L w.1 h ∈ AutomorphicForm.localIntegralSet L w.1 := by
  rw [AutomorphicForm.semiLocalIntegralSet, AutomorphicForm.mem_integralUnitsSet]
  simp only [← map_inv, semiLocalComponent_apply, semiLocalEval_mem_semiLocalIntegers_iff,
    AutomorphicForm.mem_localIntegralSet, AdelicLevel.finComponent_apply]
  constructor
  · rintro ⟨h1, h2⟩ w
    exact ⟨fun i j => h1 i j w, fun i j => h2 i j w⟩
  · intro hw
    exact ⟨fun i j w => (hw w).1 i j, fun i j w => (hw w).2 i j⟩

theorem continuous_semiLocalEval : Continuous (AutomorphicForm.semiLocalEval K L v) := by
  have h1 : Continuous fun a : FiniteAdeleRing (𝓞 L) L =>
      (fun w : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w.1 a) :=
    continuous_pi fun w => AdelicLevel.continuous_finAdeleEval (𝓞 L) L w.1
  have h2 : Continuous (AutomorphicForm.semiLocalHomeomorph K L v).symm :=
    (AutomorphicForm.semiLocalHomeomorph K L v).symm.continuous
  have key : ∀ a : FiniteAdeleRing (𝓞 L) L, AutomorphicForm.semiLocalEval K L v a =
      (AutomorphicForm.semiLocalHomeomorph K L v).symm
        (fun w : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w.1 a) := by
    intro a
    apply (AutomorphicForm.semiLocalHomeomorph K L v).injective
    rw [Homeomorph.apply_symm_apply]
    funext w
    exact semiLocalHomeomorph_semiLocalEval K L v a w
  have heq : (fun a : FiniteAdeleRing (𝓞 L) L => AutomorphicForm.semiLocalEval K L v a) =
      fun a => (AutomorphicForm.semiLocalHomeomorph K L v).symm
        (fun w : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w.1 a) := funext key
  show Continuous fun a : FiniteAdeleRing (𝓞 L) L => AutomorphicForm.semiLocalEval K L v a
  rw [heq]
  exact h2.comp h1

end SemiLocal

section FiniteFactor

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 K)))

def above : Finset (HeightOneSpectrum (𝓞 L)) :=
  HeightOneSpectrum.preimageComapFinset (𝓞 K) K L (𝓞 L) S

variable {K L S}

theorem mem_above_iff {w : HeightOneSpectrum (𝓞 L)} : w ∈ above K L S ↔ w.under (𝓞 K) ∈ S := by
  rw [above, HeightOneSpectrum.preimageComapFinset, Set.Finite.mem_toFinset, Set.mem_preimage, Finset.mem_coe]

variable (K L S)

def intOutside : Subring (FiniteAdeleRing (𝓞 L) L) where
  carrier := {x | ∀ w, w ∉ above K L S → x w ∈ w.adicCompletionIntegers L}
  mul_mem' ha hb w hw := by rw [AdelicLevel.coe_mul_apply]; exact mul_mem (ha w hw) (hb w hw)
  one_mem' w _ := by rw [AdelicLevel.coe_one_apply]; exact one_mem _
  add_mem' ha hb w hw := by rw [AdelicLevel.coe_add_apply]; exact add_mem (ha w hw) (hb w hw)
  zero_mem' w _ := by rw [AdelicLevel.coe_zero_apply]; exact zero_mem _
  neg_mem' ha w hw := by rw [AdelicLevel.coe_neg_apply]; exact neg_mem (ha w hw)

theorem mem_intOutside {x : FiniteAdeleRing (𝓞 L) L} :
    x ∈ intOutside K L S ↔ ∀ w, w ∉ above K L S → x w ∈ w.adicCompletionIntegers L := Iff.rfl

theorem isOpen_intOutside : IsOpen (intOutside K L S : Set (FiniteAdeleRing (𝓞 L) L)) :=
  RestrictedProduct.isOpen_forall_imp_mem
    (R := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
    (A := fun w : HeightOneSpectrum (𝓞 L) => (w.adicCompletionIntegers L : Set (w.adicCompletion L)))
    Fact.out (p := fun w => w ∉ above K L S)

theorem isClosed_intOutside : IsClosed (intOutside K L S : Set (FiniteAdeleRing (𝓞 L) L)) := by
  have : (intOutside K L S : Set (FiniteAdeleRing (𝓞 L) L)) = ⋂ w ∈ ((↑(above K L S) : Set (HeightOneSpectrum (𝓞 L)))ᶜ),
      (fun x : FiniteAdeleRing (𝓞 L) L => x w) ⁻¹' (w.adicCompletionIntegers L : Set (w.adicCompletion L)) := by
    ext x
    simp only [SetLike.mem_coe, mem_intOutside, Set.mem_iInter, Set.mem_compl_iff, Set.mem_preimage,
      Finset.mem_coe]
  rw [this]
  exact isClosed_biInter fun w _ =>
    (AdelicLevel.isClosed_adicCompletionIntegers w).preimage (AdelicLevel.continuous_finAdeleEval (𝓞 L) L w)

theorem isLocallyConstant_finset_prod {X : Type*} [TopologicalSpace X] {ι : Type*} (s : Finset ι)
    (F : ι → X → ℂ) (hF : ∀ i ∈ s, IsLocallyConstant (F i)) :
    IsLocallyConstant fun x => ∏ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact IsLocallyConstant.const 1
  | insert a s ha ih =>
    have h1 : IsLocallyConstant (F a) := hF a (Finset.mem_insert_self a s)
    have h2 : IsLocallyConstant fun x => ∏ i ∈ s, F i x := ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have := h1.mul h2
    simp only [Finset.prod_insert ha]
    exact this

theorem isCompact_box (D : ∀ w : HeightOneSpectrum (𝓞 L), Set (w.adicCompletion L))
    (hD : ∀ w ∈ above K L S, IsCompact (D w))
    (hD' : ∀ w, w ∉ above K L S → D w = (w.adicCompletionIntegers L : Set (w.adicCompletion L))) :
    IsCompact {x : FiniteAdeleRing (𝓞 L) L | ∀ w, x w ∈ D w} := by
  set T : Set (HeightOneSpectrum (𝓞 L)) := (↑(above K L S) : Set (HeightOneSpectrum (𝓞 L)))ᶜ with hT
  have hTc : Filter.cofinite ≤ 𝓟 T := by
    rw [Filter.le_principal_iff, hT]
    exact (above K L S).finite_toSet.compl_mem_cofinite
  let RR : HeightOneSpectrum (𝓞 L) → Type := fun w => w.adicCompletion L
  let AA : ∀ w : HeightOneSpectrum (𝓞 L), Set (RR w) := fun w =>
    (w.adicCompletionIntegers L : Set (w.adicCompletion L))
  let ι := RestrictedProduct.inclusion RR AA hTc
  set B' : Set (RestrictedProduct RR AA (𝓟 T)) := {y | ∀ w, y w ∈ D w} with hB'
  have hDall : ∀ w, IsCompact (D w) := by
    intro w
    by_cases hw : w ∈ above K L S
    · exact hD w hw
    · rw [hD' w hw]
      exact isCompact_iff_compactSpace.2 (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 L) L w)
  have hB'c : IsCompact B' := by
    rw [(RestrictedProduct.isEmbedding_coe_of_principal (R := RR) (A := AA) (S := T)).isCompact_iff]
    have heq : (DFunLike.coe '' B' : Set (∀ w, RR w)) = Set.pi Set.univ D := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩ w -
        exact hy w
      · intro hx
        have hx' : ∀ᶠ w in 𝓟 T, x w ∈ AA w := by
          rw [Filter.eventually_principal]
          intro w hw
          have hwS : w ∉ above K L S := hw
          have := hx w (Set.mem_univ w)
          rwa [hD' w hwS] at this
        exact ⟨⟨x, hx'⟩, fun w => hx w (Set.mem_univ w), rfl⟩
    rw [heq]
    exact isCompact_univ_pi hDall
  have himage : ι '' B' = {x : FiniteAdeleRing (𝓞 L) L | ∀ w, x w ∈ D w} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ w
      exact hy w
    · intro hx
      have hx' : ∀ᶠ w in 𝓟 T, (x : ∀ w, RR w) w ∈ AA w := by
        rw [Filter.eventually_principal]
        intro w hw
        have hwS : w ∉ above K L S := hw
        have := hx w
        rwa [hD' w hwS] at this
      refine ⟨⟨(x : ∀ w, RR w), hx'⟩, fun w => hx w, ?_⟩
      exact RestrictedProduct.ext _ _ fun w => rfl
  rw [← himage]
  exact hB'c.image (RestrictedProduct.continuous_inclusion hTc)

variable {K L S}

theorem setOf_forall_semiLocalEval_mem_eq :
    {xf : FiniteAdeleRing (𝓞 L) L | ∀ v ∉ S,
        AutomorphicForm.semiLocalEval K L v xf ∈ AutomorphicForm.semiLocalIntegers K L v} =
      (intOutside K L S : Set (FiniteAdeleRing (𝓞 L) L)) := by
  ext x
  rw [Set.mem_setOf_eq, SetLike.mem_coe, mem_intOutside]
  constructor
  · intro h w hw
    have hv : w.under (𝓞 K) ∉ S := fun h' => hw (mem_above_iff.mpr h')
    have := (semiLocalEval_mem_semiLocalIntegers_iff K L (w.under (𝓞 K)) x).mp (h _ hv) ⟨w, rfl⟩
    exact this
  · intro h v hv
    rw [semiLocalEval_mem_semiLocalIntegers_iff]
    intro w
    apply h
    rw [mem_above_iff, w.2]
    exact hv

variable (K L S)

theorem main
    (Fv : (v : HeightOneSpectrum (𝓞 K)) → L ⊗[K] v.adicCompletion K → ℂ)
    (hFv : ∀ v ∈ S, IsLocallyConstant (Fv v) ∧ HasCompactSupport (Fv v)) :
    IsLocallyConstant (fun xf : FiniteAdeleRing (𝓞 L) L =>
        {xf : FiniteAdeleRing (𝓞 L) L | ∀ v ∉ S,
            AutomorphicForm.semiLocalEval K L v xf ∈ AutomorphicForm.semiLocalIntegers K L v}.indicator
          (fun xf => ∏ v ∈ S, Fv v (AutomorphicForm.semiLocalEval K L v xf)) xf) ∧
      HasCompactSupport (fun xf : FiniteAdeleRing (𝓞 L) L =>
        {xf : FiniteAdeleRing (𝓞 L) L | ∀ v ∉ S,
            AutomorphicForm.semiLocalEval K L v xf ∈ AutomorphicForm.semiLocalIntegers K L v}.indicator
          (fun xf => ∏ v ∈ S, Fv v (AutomorphicForm.semiLocalEval K L v xf)) xf) := by
  classical
  rw [setOf_forall_semiLocalEval_mem_eq]
  refine ⟨?_, ?_⟩
  ·
    have hprod : IsLocallyConstant fun xf : FiniteAdeleRing (𝓞 L) L =>
        ∏ v ∈ S, Fv v (AutomorphicForm.semiLocalEval K L v xf) :=
      isLocallyConstant_finset_prod S (fun v xf => Fv v (AutomorphicForm.semiLocalEval K L v xf)) fun v hv =>
        (hFv v hv).1.comp_continuous (continuous_semiLocalEval K L v)
    have hind : IsLocallyConstant ((intOutside K L S : Set (FiniteAdeleRing (𝓞 L) L)).indicator
        fun _ => (1 : ℂ)) :=
      AutomorphicForm.isLocallyConstant_indicator_one (isOpen_intOutside K L S) (isClosed_intOutside K L S)
    have := hind.mul hprod
    convert this using 1
    funext xf
    simp only [Pi.mul_apply]
    by_cases hx : xf ∈ (intOutside K L S : Set (FiniteAdeleRing (𝓞 L) L))
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  ·
    let D : ∀ w : HeightOneSpectrum (𝓞 L), Set (w.adicCompletion L) := fun w =>
      if w ∈ above K L S then
        (fun x : L ⊗[K] (w.under (𝓞 K)).adicCompletion K =>
            AutomorphicForm.semiLocalHomeomorph K L (w.under (𝓞 K)) x ⟨w, rfl⟩) '' tsupport (Fv (w.under (𝓞 K)))
      else (w.adicCompletionIntegers L : Set (w.adicCompletion L))
    have hD : ∀ w ∈ above K L S, IsCompact (D w) := by
      intro w hw
      simp only [D, if_pos hw]
      have hev : Continuous fun x : L ⊗[K] (w.under (𝓞 K)).adicCompletion K =>
          AutomorphicForm.semiLocalHomeomorph K L (w.under (𝓞 K)) x ⟨w, rfl⟩ :=
        (continuous_apply _).comp (AutomorphicForm.semiLocalHomeomorph K L (w.under (𝓞 K))).continuous
      exact (hFv _ (mem_above_iff.mp hw)).2.image hev
    have hD' : ∀ w, w ∉ above K L S → D w = (w.adicCompletionIntegers L : Set (w.adicCompletion L)) := by
      intro w hw
      simp only [D, if_neg hw]
    have hbox := isCompact_box K L S D hD hD'
    refine HasCompactSupport.intro hbox fun x hx => ?_
    by_contra hne
    apply hx
    have hmem : x ∈ (intOutside K L S : Set (FiniteAdeleRing (𝓞 L) L)) := by
      by_contra hnot
      exact hne (Set.indicator_of_notMem hnot _)
    rw [Set.indicator_of_mem hmem] at hne
    have hfac : ∀ v ∈ S, Fv v (AutomorphicForm.semiLocalEval K L v x) ≠ 0 := fun v hv h0 =>
      hne (Finset.prod_eq_zero hv h0)
    have hsupp : ∀ v ∈ S, AutomorphicForm.semiLocalEval K L v x ∈ tsupport (Fv v) := fun v hv =>
      subset_tsupport _ (Function.mem_support.mpr (hfac v hv))
    rw [SetLike.mem_coe, mem_intOutside] at hmem
    intro w
    by_cases hw : w ∈ above K L S
    · simp only [D, if_pos hw]
      exact ⟨_, hsupp _ (mem_above_iff.mp hw), semiLocalHomeomorph_semiLocalEval K L (w.under (𝓞 K)) x ⟨w, rfl⟩⟩
    · simp only [D, if_neg hw]
      exact hmem w hw

end FiniteFactor

end SlL4

end

open NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Sx : Finset (HeightOneSpectrum (𝓞 K)))
    (Fv : (v : HeightOneSpectrum (𝓞 K)) → L ⊗[K] v.adicCompletion K → ℂ)
    (hFv : ∀ v ∈ Sx, IsLocallyConstant (Fv v) ∧ HasCompactSupport (Fv v)) :
    IsLocallyConstant (fun xf : FiniteAdeleRing (𝓞 L) L =>
        {xf : FiniteAdeleRing (𝓞 L) L | ∀ v ∉ Sx,
            AutomorphicForm.semiLocalEval K L v xf ∈ AutomorphicForm.semiLocalIntegers K L v}.indicator
          (fun xf => ∏ v ∈ Sx, Fv v (AutomorphicForm.semiLocalEval K L v xf)) xf) ∧
      HasCompactSupport (fun xf : FiniteAdeleRing (𝓞 L) L =>
        {xf : FiniteAdeleRing (𝓞 L) L | ∀ v ∉ Sx,
            AutomorphicForm.semiLocalEval K L v xf ∈ AutomorphicForm.semiLocalIntegers K L v}.indicator
          (fun xf => ∏ v ∈ Sx, Fv v (AutomorphicForm.semiLocalEval K L v xf)) xf) :=
  SlL4.main K L Sx Fv hFv

end S_AutomorphicForm_isLocallyConstant_and_hasCompactSupport_indicator_prod_semiLocalEval
end P2MW
export P2MW.S_AutomorphicForm_isLocallyConstant_and_hasCompactSupport_indicator_prod_semiLocalEval (solution)
