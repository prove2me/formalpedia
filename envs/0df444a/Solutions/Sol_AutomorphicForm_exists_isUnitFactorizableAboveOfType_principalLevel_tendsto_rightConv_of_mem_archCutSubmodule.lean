-- Prove2me | solution 1 for AutomorphicForm.exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_mem_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/bba78778-1ffa-590b-b278-7fa7067a1d37

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Theorems.Thm_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_mem_archCutSubmodule

set_option autoImplicit false

section

open AutomorphicForm

open NumberField IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions
open AutomorphicForm

noncomputable section

namespace Q09AIDock
namespace LevelFiniteFactor

section Local

variable (L : Type) [Field L] [NumberField L]

private def IsLocalLevelOne (N : Ideal (𝓞 L)) (w : HeightOneSpectrum (𝓞 L))
    (m : Fin 2 → Fin 2 → w.adicCompletion L) : Prop :=
  (∀ i j, m i j ∈ w.adicCompletionIntegers L) ∧
    Valued.v (m 1 0) ≤ AdelicLevel.idealBound (𝓞 L) N w ∧
      Valued.v (m 1 1 - 1) ≤ AdelicLevel.idealBound (𝓞 L) N w

variable {L}

private theorem isLocalLevelOne_of_integral {N : Ideal (𝓞 L)} {w : HeightOneSpectrum (𝓞 L)}
    (hb : AdelicLevel.idealBound (𝓞 L) N w = 1) {m : Fin 2 → Fin 2 → w.adicCompletion L}
    (hm : ∀ i j, m i j ∈ w.adicCompletionIntegers L) : IsLocalLevelOne L N w m := by
  refine ⟨hm, ?_, ?_⟩
  · rw [hb]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hm 1 0)
  · rw [hb]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (sub_mem (hm 1 1) (one_mem _))

private theorem isLevelOneMatrix_iff_forall {N : Ideal (𝓞 L)}
    (M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    AdelicLevel.IsLevelOneMatrix (𝓞 L) L N M ↔
      ∀ w : HeightOneSpectrum (𝓞 L),
        IsLocalLevelOne L N w fun i j => AdelicLevel.finAdeleEval (𝓞 L) L w (M i j) := by
  constructor
  · intro h w
    exact ⟨fun i j => h.integral i j w, h.lowerLeft w, h.lowerRight w⟩
  · intro h
    exact
      { integral := fun i j w => (h w).1 i j
        lowerLeft := fun w => (h w).2.1
        lowerRight := fun w => (h w).2.2 }

private theorem mem_finiteLevelOne_iff_forall {N : Ideal (𝓞 L)} (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    h ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N ↔
      ∀ w : HeightOneSpectrum (𝓞 L),
        (IsLocalLevelOne L N w fun i j => AdelicLevel.finAdeleEval (𝓞 L) L w (h.val i j)) ∧
          IsLocalLevelOne L N w fun i j => AdelicLevel.finAdeleEval (𝓞 L) L w ((h⁻¹).val i j) := by
  rw [AdelicLevel.mem_finiteLevelOne_iff, isLevelOneMatrix_iff_forall, isLevelOneMatrix_iff_forall]
  exact forall_and.symm

private theorem isOpen_setOf_isLocalLevelOne {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) {X : Type} [TopologicalSpace X]
    {w : HeightOneSpectrum (𝓞 L)} (m : X → Fin 2 → Fin 2 → w.adicCompletion L)
    (hm : ∀ i j, Continuous fun x => m x i j) : IsOpen {x | IsLocalLevelOne L N w (m x)} := by
  have h1 : IsOpen {x | ∀ i j, m x i j ∈ w.adicCompletionIntegers L} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      ((AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 L) L).out w).preimage (hm i j)
  have h2 : IsOpen {x | Valued.v (m x 1 0) ≤ AdelicLevel.idealBound (𝓞 L) N w} :=
    (AdelicLevel.isOpen_setOf_valued_le_idealBound (K := L) w hN).preimage (hm 1 0)
  have h3 : IsOpen {x | Valued.v (m x 1 1 - 1) ≤ AdelicLevel.idealBound (𝓞 L) N w} :=
    (AdelicLevel.isOpen_setOf_valued_le_idealBound (K := L) w hN).preimage
      ((hm 1 1).sub continuous_const)
  exact h1.inter (h2.inter h3)

private theorem isClosed_setOf_isLocalLevelOne (N : Ideal (𝓞 L)) {X : Type} [TopologicalSpace X]
    {w : HeightOneSpectrum (𝓞 L)} (m : X → Fin 2 → Fin 2 → w.adicCompletion L)
    (hm : ∀ i j, Continuous fun x => m x i j) : IsClosed {x | IsLocalLevelOne L N w (m x)} := by
  have h1 : IsClosed {x | ∀ i j, m x i j ∈ w.adicCompletionIntegers L} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      (AdelicLevel.isClosed_adicCompletionIntegers (K := L) w).preimage (hm i j)
  have h2 : IsClosed {x | Valued.v (m x 1 0) ≤ AdelicLevel.idealBound (𝓞 L) N w} :=
    (AdelicLevel.isClosed_setOf_valued_le_idealBound (K := L) w N).preimage (hm 1 0)
  have h3 : IsClosed {x | Valued.v (m x 1 1 - 1) ≤ AdelicLevel.idealBound (𝓞 L) N w} :=
    (AdelicLevel.isClosed_setOf_valued_le_idealBound (K := L) w N).preimage
      ((hm 1 1).sub continuous_const)
  exact h1.inter (h2.inter h3)

private theorem isOpen_setOf_forall_isLocalLevelOne {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) {X : Type} [TopologicalSpace X]
    {ι : Type} [Finite ι] (w : ι → HeightOneSpectrum (𝓞 L))
    (m m' : X → (i : ι) → Fin 2 → Fin 2 → (w i).adicCompletion L)
    (hm : ∀ i a b, Continuous fun x => m x i a b) (hm' : ∀ i a b, Continuous fun x => m' x i a b) :
    IsOpen {x | ∀ i, IsLocalLevelOne L N (w i) (m x i) ∧ IsLocalLevelOne L N (w i) (m' x i)} := by
  simp only [Set.setOf_forall, Set.setOf_and]
  exact isOpen_iInter_of_finite fun i =>
    (isOpen_setOf_isLocalLevelOne hN (fun x => m x i) (hm i)).inter
      (isOpen_setOf_isLocalLevelOne hN (fun x => m' x i) (hm' i))

private theorem isClosed_setOf_forall_isLocalLevelOne (N : Ideal (𝓞 L)) {X : Type} [TopologicalSpace X]
    {ι : Type} (w : ι → HeightOneSpectrum (𝓞 L))
    (m m' : X → (i : ι) → Fin 2 → Fin 2 → (w i).adicCompletion L)
    (hm : ∀ i a b, Continuous fun x => m x i a b) (hm' : ∀ i a b, Continuous fun x => m' x i a b) :
    IsClosed {x | ∀ i, IsLocalLevelOne L N (w i) (m x i) ∧ IsLocalLevelOne L N (w i) (m' x i)} := by
  simp only [Set.setOf_forall, Set.setOf_and]
  exact isClosed_iInter fun i =>
    (isClosed_setOf_isLocalLevelOne N (fun x => m x i) (hm i)).inter
      (isClosed_setOf_isLocalLevelOne N (fun x => m' x i) (hm' i))

variable (L) in
private def IsLocalPrincipal (N : Ideal (𝓞 L)) (w : HeightOneSpectrum (𝓞 L))
    (m : Fin 2 → Fin 2 → w.adicCompletion L) : Prop :=
  IsLocalLevelOne L N w m ∧ IsLocalLevelOne L N w fun i j => m i.rev j.rev

private theorem isLocalPrincipal_of_integral {N : Ideal (𝓞 L)} {w : HeightOneSpectrum (𝓞 L)}
    (hb : AdelicLevel.idealBound (𝓞 L) N w = 1) {m : Fin 2 → Fin 2 → w.adicCompletion L}
    (hm : ∀ i j, m i j ∈ w.adicCompletionIntegers L) : IsLocalPrincipal L N w m :=
  ⟨isLocalLevelOne_of_integral hb hm, isLocalLevelOne_of_integral hb fun i j => hm i.rev j.rev⟩

private theorem isOpen_setOf_forall_isLocalPrincipal {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) {X : Type} [TopologicalSpace X]
    {ι : Type} [Finite ι] (w : ι → HeightOneSpectrum (𝓞 L))
    (m m' : X → (i : ι) → Fin 2 → Fin 2 → (w i).adicCompletion L)
    (hm : ∀ i a b, Continuous fun x => m x i a b) (hm' : ∀ i a b, Continuous fun x => m' x i a b) :
    IsOpen {x | ∀ i, IsLocalPrincipal L N (w i) (m x i) ∧ IsLocalPrincipal L N (w i) (m' x i)} := by
  have h1 := isOpen_setOf_forall_isLocalLevelOne hN w m m' hm hm'
  have h2 := isOpen_setOf_forall_isLocalLevelOne hN w (fun x i a b => m x i a.rev b.rev)
    (fun x i a b => m' x i a.rev b.rev) (fun i a b => hm i _ _) (fun i a b => hm' i _ _)
  have : {x | ∀ i, IsLocalPrincipal L N (w i) (m x i) ∧ IsLocalPrincipal L N (w i) (m' x i)} =
      {x | ∀ i, IsLocalLevelOne L N (w i) (m x i) ∧ IsLocalLevelOne L N (w i) (m' x i)} ∩
      {x | ∀ i, (IsLocalLevelOne L N (w i) fun a b => m x i a.rev b.rev) ∧
        IsLocalLevelOne L N (w i) fun a b => m' x i a.rev b.rev} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, IsLocalPrincipal]
    exact ⟨fun h => ⟨fun i => ⟨(h i).1.1, (h i).2.1⟩, fun i => ⟨(h i).1.2, (h i).2.2⟩⟩,
      fun h i => ⟨⟨(h.1 i).1, (h.2 i).1⟩, ⟨(h.1 i).2, (h.2 i).2⟩⟩⟩
  rw [this]
  exact h1.inter h2

private theorem isClosed_setOf_forall_isLocalPrincipal (N : Ideal (𝓞 L)) {X : Type} [TopologicalSpace X]
    {ι : Type} (w : ι → HeightOneSpectrum (𝓞 L))
    (m m' : X → (i : ι) → Fin 2 → Fin 2 → (w i).adicCompletion L)
    (hm : ∀ i a b, Continuous fun x => m x i a b) (hm' : ∀ i a b, Continuous fun x => m' x i a b) :
    IsClosed {x | ∀ i, IsLocalPrincipal L N (w i) (m x i) ∧ IsLocalPrincipal L N (w i) (m' x i)} := by
  have h1 := isClosed_setOf_forall_isLocalLevelOne N w m m' hm hm'
  have h2 := isClosed_setOf_forall_isLocalLevelOne N w (fun x i a b => m x i a.rev b.rev)
    (fun x i a b => m' x i a.rev b.rev) (fun i a b => hm i _ _) (fun i a b => hm' i _ _)
  have : {x | ∀ i, IsLocalPrincipal L N (w i) (m x i) ∧ IsLocalPrincipal L N (w i) (m' x i)} =
      {x | ∀ i, IsLocalLevelOne L N (w i) (m x i) ∧ IsLocalLevelOne L N (w i) (m' x i)} ∩
      {x | ∀ i, (IsLocalLevelOne L N (w i) fun a b => m x i a.rev b.rev) ∧
        IsLocalLevelOne L N (w i) fun a b => m' x i a.rev b.rev} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, IsLocalPrincipal]
    exact ⟨fun h => ⟨fun i => ⟨(h i).1.1, (h i).2.1⟩, fun i => ⟨(h i).1.2, (h i).2.2⟩⟩,
      fun h i => ⟨⟨(h.1 i).1, (h.2 i).1⟩, ⟨(h.1 i).2, (h.2 i).2⟩⟩⟩
  rw [this]
  exact h1.inter h2

variable (L) in

private def weylFin : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) := AdelicLevel.glFin (𝓞 L) L (AdelicLevel.weyl (𝓞 L) L)

variable (L) in
private theorem weylFin_apply (i j : Fin 2) :
    ((weylFin L : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j =
      if i = j then 0 else 1 := by
  show AdelicLevel.adeleFin (𝓞 L) L ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) = _
  fin_cases i <;> fin_cases j <;> simp

variable (L) in
private theorem weylFin_mul_self : weylFin L * weylFin L = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, weylFin_apply, weylFin_apply, weylFin_apply,
    weylFin_apply, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp

variable (L) in
private theorem weylFin_inv : (weylFin L)⁻¹ = weylFin L :=
  inv_eq_of_mul_eq_one_right (weylFin_mul_self L)

variable (L) in

private theorem weylFin_conj_val (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (i j : Fin 2) :
    ((weylFin L)⁻¹ * h * weylFin L).val i j = h.val i.rev j.rev := by
  rw [weylFin_inv]
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, weylFin_apply]
  fin_cases i <;> fin_cases j <;> simp [Fin.rev]

variable (L) in

private def finitePrincipalLevel (N : Ideal (𝓞 L)) : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :=
  AdelicLevel.finiteLevelOne (𝓞 L) L N ⊓
    (AdelicLevel.finiteLevelOne (𝓞 L) L N).map (MulAut.conj (weylFin L)).toMonoidHom

variable (L) in
private theorem finitePrincipalLevel_le (N : Ideal (𝓞 L)) :
    finitePrincipalLevel L N ≤ AdelicLevel.finiteLevelOne (𝓞 L) L N := inf_le_left

private theorem mem_map_conj_iff {G : Type*} [Group G] (H : Subgroup G) (w g : G) :
    g ∈ H.map (MulAut.conj w).toMonoidHom ↔ w⁻¹ * g * w ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

private theorem mem_finitePrincipalLevel_iff_forall {N : Ideal (𝓞 L)} (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    h ∈ finitePrincipalLevel L N ↔
      ∀ w : HeightOneSpectrum (𝓞 L),
        (IsLocalPrincipal L N w fun i j => AdelicLevel.finAdeleEval (𝓞 L) L w (h.val i j)) ∧
          IsLocalPrincipal L N w fun i j => AdelicLevel.finAdeleEval (𝓞 L) L w ((h⁻¹).val i j) := by
  unfold finitePrincipalLevel
  rw [Subgroup.mem_inf, mem_map_conj_iff, mem_finiteLevelOne_iff_forall, mem_finiteLevelOne_iff_forall]
  have hc : ∀ i j, ((weylFin L)⁻¹ * h * weylFin L).val i j = h.val i.rev j.rev := weylFin_conj_val L h
  have hci : ∀ i j, (((weylFin L)⁻¹ * h * weylFin L)⁻¹).val i j = (h⁻¹).val i.rev j.rev := by
    intro i j
    rw [show ((weylFin L)⁻¹ * h * weylFin L)⁻¹ = (weylFin L)⁻¹ * h⁻¹ * weylFin L by
      rw [weylFin_inv, mul_inv_rev, mul_inv_rev, weylFin_inv, mul_assoc]]
    exact weylFin_conj_val L h⁻¹ i j
  simp only [hc, hci, IsLocalPrincipal]
  exact ⟨fun H w => ⟨⟨(H.1 w).1, (H.2 w).1⟩, ⟨(H.1 w).2, (H.2 w).2⟩⟩,
    fun H => ⟨fun w => ⟨(H w).1.1, (H w).2.1⟩, fun w => ⟨(H w).1.2, (H w).2.2⟩⟩⟩

variable (L) in

private theorem mem_principalLevel_iff_glFin {N : Ideal (𝓞 L)} (g : GL (Fin 2) (AdeleRing (𝓞 L) L)) :
    g ∈ AdelicLevel.principalLevel (𝓞 L) L N ↔ AdelicLevel.glFin (𝓞 L) L g ∈ finitePrincipalLevel L N := by
  unfold finitePrincipalLevel
  rw [AdelicLevel.mem_principalLevel_iff, Subgroup.mem_inf, mem_map_conj_iff, mem_map_conj_iff,
    AdelicLevel.mem_levelOne_iff, AdelicLevel.mem_levelOne_iff, map_mul, map_mul, map_inv]
  rfl

variable (L) in
private theorem isOpen_finitePrincipalLevel {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) :
    IsOpen (finitePrincipalLevel L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) := by
  have h1 := AdelicLevel.isOpen_finiteLevelOne (𝓞 L) L (N := N) hN
  have h2 : IsOpen ((fun g => (weylFin L)⁻¹ * g * weylFin L) ⁻¹'
      (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))) :=
    h1.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  convert h1.inter h2 using 1
  ext g
  simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
  unfold finitePrincipalLevel
  rw [Subgroup.mem_inf, mem_map_conj_iff]

variable (L) in
private theorem isClosed_finitePrincipalLevel (N : Ideal (𝓞 L)) :
    IsClosed (finitePrincipalLevel L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) := by
  have h1 := AdelicLevel.isClosed_finiteLevelOne (𝓞 L) L N
  have h2 : IsClosed ((fun g => (weylFin L)⁻¹ * g * weylFin L) ⁻¹'
      (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))) :=
    h1.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  convert h1.inter h2 using 1
  ext g
  simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
  unfold finitePrincipalLevel
  rw [Subgroup.mem_inf, mem_map_conj_iff]

variable (L) in
private theorem isCompact_finitePrincipalLevel (N : Ideal (𝓞 L)) :
    IsCompact (finitePrincipalLevel L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) :=
  (AdelicLevel.isCompact_finiteLevelOne (𝓞 L) L N).of_isClosed_subset (isClosed_finitePrincipalLevel L N)
    (finitePrincipalLevel_le L N)

private def plevelIndicator (N : Ideal (𝓞 L)) : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ :=
  (finitePrincipalLevel L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))).indicator fun _ => 1

private theorem isFinTestFactor_plevelIndicator {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) :
    IsFinTestFactor L (plevelIndicator (L := L) N) :=
  ⟨isLocallyConstant_indicator_one (isOpen_finitePrincipalLevel L hN) (isClosed_finitePrincipalLevel L N),
    HasCompactSupport.intro (isCompact_finitePrincipalLevel L N) fun _ hg => Set.indicator_of_notMem hg _⟩

end Local

section SemiLocal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))

private theorem semiLocalHomeomorph_semiLocalEval (a : FiniteAdeleRing (𝓞 L) L) (w : v.Extension (𝓞 L)) :
    semiLocalHomeomorph K L v (semiLocalEval K L v a) w = AdelicLevel.finAdeleEval (𝓞 L) L w.1 a := by
  show HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
      ((HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (fun w' : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w'.1 a)) w =
    AdelicLevel.finAdeleEval (𝓞 L) L w.1 a
  rw [AlgEquiv.apply_symm_apply]

private def componentEntries (m : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) (w : v.Extension (𝓞 L)) :
    Fin 2 → Fin 2 → w.1.adicCompletion L :=
  fun i j => semiLocalHomeomorph K L v (m i j) w

private theorem componentEntries_semiLocalComponent (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    (w : v.Extension (𝓞 L)) :
    componentEntries K L v (semiLocalComponent K L v h).val w =
      fun i j => AdelicLevel.finAdeleEval (𝓞 L) L w.1 (h.val i j) := by
  funext i j
  exact semiLocalHomeomorph_semiLocalEval K L v (h.val i j) w

private theorem continuous_componentEntries_val (w : v.Extension (𝓞 L)) (i j : Fin 2) :
    Continuous fun γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => componentEntries K L v γ.val w i j :=
  (continuous_apply w).comp
    ((semiLocalHomeomorph K L v).continuous.comp (Units.continuous_val.matrix_elem i j))

private theorem continuous_componentEntries_inv (w : v.Extension (𝓞 L)) (i j : Fin 2) :
    Continuous fun γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      componentEntries K L v (γ⁻¹).val w i j :=
  (continuous_apply w).comp
    ((semiLocalHomeomorph K L v).continuous.comp (Units.continuous_coe_inv.matrix_elem i j))

private def semiLocalLevelSet (N : Ideal (𝓞 L)) : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
  {γ | ∀ w : v.Extension (𝓞 L),
    IsLocalPrincipal L N w.1 (componentEntries K L v γ.val w) ∧
      IsLocalPrincipal L N w.1 (componentEntries K L v (γ⁻¹).val w)}

private theorem semiLocalComponent_mem_semiLocalLevelSet_iff (N : Ideal (𝓞 L))
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    semiLocalComponent K L v h ∈ semiLocalLevelSet K L v N ↔
      ∀ w : v.Extension (𝓞 L),
        (IsLocalPrincipal L N w.1 fun i j => AdelicLevel.finAdeleEval (𝓞 L) L w.1 (h.val i j)) ∧
          IsLocalPrincipal L N w.1 fun i j => AdelicLevel.finAdeleEval (𝓞 L) L w.1 ((h⁻¹).val i j) := by
  rw [semiLocalLevelSet, Set.mem_setOf_eq, ← map_inv]
  refine forall_congr' fun w => ?_
  rw [componentEntries_semiLocalComponent, componentEntries_semiLocalComponent]

private theorem isOpen_semiLocalLevelSet {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) : IsOpen (semiLocalLevelSet K L v N) := by
  haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  exact isOpen_setOf_forall_isLocalPrincipal hN (fun w : v.Extension (𝓞 L) => w.1)
    (fun (γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) w => componentEntries K L v γ.val w)
    (fun (γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) w => componentEntries K L v (γ⁻¹).val w)
    (fun w => continuous_componentEntries_val K L v w) (fun w => continuous_componentEntries_inv K L v w)

private theorem isClosed_semiLocalLevelSet (N : Ideal (𝓞 L)) : IsClosed (semiLocalLevelSet K L v N) :=
  isClosed_setOf_forall_isLocalPrincipal N (fun w : v.Extension (𝓞 L) => w.1)
    (fun (γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) w => componentEntries K L v γ.val w)
    (fun (γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) w => componentEntries K L v (γ⁻¹).val w)
    (fun w => continuous_componentEntries_val K L v w) (fun w => continuous_componentEntries_inv K L v w)

private theorem mem_semiLocalIntegers_of_forall (t : L ⊗[K] v.adicCompletion K)
    (ht : ∀ w : v.Extension (𝓞 L), semiLocalHomeomorph K L v t w ∈ w.1.adicCompletionIntegers L) :
    t ∈ semiLocalIntegers K L v := by
  rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, piIntegers, Set.mem_univ_pi]
  exact ht

private theorem forall_of_mem_semiLocalIntegers (t : L ⊗[K] v.adicCompletion K) (ht : t ∈ semiLocalIntegers K L v)
    (w : v.Extension (𝓞 L)) : semiLocalHomeomorph K L v t w ∈ w.1.adicCompletionIntegers L := by
  rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, piIntegers, Set.mem_univ_pi] at ht
  exact ht w

private theorem semiLocalLevelSet_subset (N : Ideal (𝓞 L)) :
    semiLocalLevelSet K L v N ⊆ semiLocalIntegralSet K L v := by
  intro γ hγ
  show γ ∈ integralUnitsSet (semiLocalIntegers K L v)
  refine mem_integralUnitsSet.2 ⟨fun i j => ?_, fun i j => ?_⟩
  · exact mem_semiLocalIntegers_of_forall K L v _ fun w => (hγ w).1.1.1 i j
  · exact mem_semiLocalIntegers_of_forall K L v _ fun w => (hγ w).2.1.1 i j

private theorem isCompact_semiLocalLevelSet (N : Ideal (𝓞 L)) : IsCompact (semiLocalLevelSet K L v N) :=
  (isCompact_semiLocalIntegralSet K L v).of_isClosed_subset (isClosed_semiLocalLevelSet K L v N)
    (semiLocalLevelSet_subset K L v N)

private theorem isSemiLocalTestFn_indicator_semiLocalLevelSet {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) :
    IsSemiLocalTestFn K L v ((semiLocalLevelSet K L v N).indicator fun _ => (1 : ℂ)) := by
  haveI := t2Space_tensorGL K L (v.adicCompletion K)
  haveI : R1Space (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := T2Space.r1Space
  exact ⟨isLocallyConstant_indicator_one (isOpen_semiLocalLevelSet K L v hN)
      (isClosed_semiLocalLevelSet K L v N),
    HasCompactSupport.intro (isCompact_semiLocalLevelSet K L v N) fun _ hg => Set.indicator_of_notMem hg _⟩

end SemiLocal

section Level

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
private theorem map_algebraMap_ne_bot {NK : Ideal (𝓞 K)} (hNK : NK ≠ ⊥) :
    Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK ≠ ⊥ :=
  fun h => hNK ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective K L)).1 h)

private theorem idealBound_map_eq_one_of_not_dvd {NK : Ideal (𝓞 K)} (hNK : NK ≠ ⊥) {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ NK) (w : HeightOneSpectrum (𝓞 L)) (hw : w.under (𝓞 K) = v) :
    AdelicLevel.idealBound (𝓞 L) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) w = 1 := by
  refine AdelicLevel.idealBound_eq_one_of_not_dvd (map_algebraMap_ne_bot (L := L) hNK) fun hdvd => ?_
  have hcount := HeightOneSpectrum.mk_count_factors_map (𝓞 K) (𝓞 L)
    (RingOfIntegers.algebraMap.injective K L) w NK
  rw [hw] at hcount
  have h0 : (Associates.mk v.asIdeal).count (Associates.mk NK).factors = 0 := by
    by_contra hne
    exact hv ((Associates.count_ne_zero_iff_dvd (show NK ≠ 0 from hNK) v.irreducible).1 hne)
  rw [h0, mul_zero] at hcount
  exact (Associates.count_ne_zero_iff_dvd (show Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK ≠ 0 from
    map_algebraMap_ne_bot (L := L) hNK) w.irreducible).2 hdvd hcount

private theorem mem_finitePrincipalLevel_iff_of_integral {NK : Ideal (𝓞 K)} (hNK : NK ≠ ⊥)
    {SK : Finset (HeightOneSpectrum (𝓞 K))} (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    {h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hint : ∀ v ∉ SK, semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v) :
    h ∈ finitePrincipalLevel L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ↔
      ∀ v ∈ SK,
        semiLocalComponent K L v h ∈ semiLocalLevelSet K L v (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) := by
  rw [mem_finitePrincipalLevel_iff_forall]
  constructor
  · intro H v _
    rw [semiLocalComponent_mem_semiLocalLevelSet_iff]
    intro w
    exact H w.1
  · intro H w
    by_cases hv : w.under (𝓞 K) ∈ SK
    · exact (semiLocalComponent_mem_semiLocalLevelSet_iff K L _ _ h).1 (H _ hv) ⟨w, rfl⟩
    · have hnd : ¬ (w.under (𝓞 K)).asIdeal ∣ NK := fun hd => hv (hNS _ hd)
      have hb := idealBound_map_eq_one_of_not_dvd hNK hnd w rfl
      have hI : semiLocalComponent K L (w.under (𝓞 K)) h ∈
          integralUnitsSet (semiLocalIntegers K L (w.under (𝓞 K))) := hint _ hv
      obtain ⟨h1, h2⟩ := mem_integralUnitsSet.1 hI
      have loc : ∀ t : FiniteAdeleRing (𝓞 L) L,
          semiLocalEval K L (w.under (𝓞 K)) t ∈ semiLocalIntegers K L (w.under (𝓞 K)) →
            AdelicLevel.finAdeleEval (𝓞 L) L w t ∈ w.adicCompletionIntegers L := by
        intro t ht
        have := forall_of_mem_semiLocalIntegers K L _ _ ht ⟨w, rfl⟩
        rwa [semiLocalHomeomorph_semiLocalEval] at this
      exact ⟨isLocalPrincipal_of_integral hb fun i j => loc (h.val i j) (h1 i j),
        isLocalPrincipal_of_integral hb fun i j => loc ((h⁻¹).val i j) (h2 i j)⟩

private theorem semiLocalComponent_mem_semiLocalIntegralSet_of_mem_finitePrincipalLevel {N : Ideal (𝓞 L)}
    {h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hh : h ∈ finitePrincipalLevel L N)
    (v : HeightOneSpectrum (𝓞 K)) : semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v := by
  rw [mem_finitePrincipalLevel_iff_forall] at hh
  show semiLocalComponent K L v h ∈ integralUnitsSet (semiLocalIntegers K L v)
  refine mem_integralUnitsSet.2 ⟨fun i j => ?_, fun i j => ?_⟩
  · refine mem_semiLocalIntegers_of_forall K L v (semiLocalEval K L v (h.val i j)) fun w => ?_
    rw [semiLocalHomeomorph_semiLocalEval]
    exact (hh w.1).1.1.1 i j
  · refine mem_semiLocalIntegers_of_forall K L v (semiLocalEval K L v ((h⁻¹).val i j)) fun w => ?_
    rw [semiLocalHomeomorph_semiLocalEval]
    exact (hh w.1).2.1.1 i j

private theorem levelIndicator_mul_left {N : Ideal (𝓞 L)} {u : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hu : u ∈ finitePrincipalLevel L N) (x : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    plevelIndicator N (u * x) = plevelIndicator N x := by
  unfold plevelIndicator
  by_cases hx : x ∈ finitePrincipalLevel L N
  · have hx' : x ∈ (finitePrincipalLevel L N : Set _) := hx
    have hux : u * x ∈ (finitePrincipalLevel L N : Set _) := Subgroup.mul_mem _ hu hx
    rw [Set.indicator_of_mem hx', Set.indicator_of_mem hux]
  · have hx' : x ∉ (finitePrincipalLevel L N : Set _) := hx
    have hux : u * x ∉ (finitePrincipalLevel L N : Set _) := fun hux =>
      hx (by simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hux)
    rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hux]

private theorem levelIndicator_mul_right {N : Ideal (𝓞 L)} {u : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hu : u ∈ finitePrincipalLevel L N) (x : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    plevelIndicator N (x * u) = plevelIndicator N x := by
  unfold plevelIndicator
  by_cases hx : x ∈ finitePrincipalLevel L N
  · have hx' : x ∈ (finitePrincipalLevel L N : Set _) := hx
    have hxu : x * u ∈ (finitePrincipalLevel L N : Set _) := Subgroup.mul_mem _ hx hu
    rw [Set.indicator_of_mem hx', Set.indicator_of_mem hxu]
  · have hx' : x ∉ (finitePrincipalLevel L N : Set _) := hx
    have hxu : x * u ∉ (finitePrincipalLevel L N : Set _) := fun hxu =>
      hx (by simpa using Subgroup.mul_mem _ hxu (Subgroup.inv_mem _ hu))
    rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hxu]

private theorem isBiInvariantUnder_glArch_mul_plevelIndicator (N : Ideal (𝓞 L))
    (fa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) :
    IsBiInvariantUnder L (AdelicLevel.principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L)
      fun g => fa (AdelicLevel.glArch (𝓞 L) L g) * plevelIndicator N (AdelicLevel.glFin (𝓞 L) L g) := by
  intro u hu g
  obtain ⟨hlev, harch⟩ := Subgroup.mem_inf.1 hu
  rw [mem_finiteAdelicGL2Subgroup_iff] at harch
  rw [mem_principalLevel_iff_glFin] at hlev
  constructor
  · dsimp only
    rw [map_mul, map_mul, harch, one_mul, levelIndicator_mul_left hlev]
  · dsimp only
    rw [map_mul, map_mul, harch, mul_one, levelIndicator_mul_right hlev]

variable (K L)

private theorem isSemiLocalFactorization_plevelIndicator {NK : Ideal (𝓞 K)} (hNK : NK ≠ ⊥)
    {SK : Finset (HeightOneSpectrum (𝓞 K))} (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    {fa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ} (hfa : IsArchTestFactor L fa) :
    IsSemiLocalFactorization K L SK
      (fun g => fa (AdelicLevel.glArch (𝓞 L) L g) *
        plevelIndicator (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) (AdelicLevel.glFin (𝓞 L) L g))
      fa (plevelIndicator (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK))
      (fun v => (semiLocalLevelSet K L v (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)).indicator
        fun _ => 1) := by
  have hN := map_algebraMap_ne_bot (L := L) hNK
  refine ⟨hfa, isFinTestFactor_plevelIndicator hN,
    fun v _ => isSemiLocalTestFn_indicator_semiLocalLevelSet K L v hN, fun h hint => ?_,
    fun h hex => ?_, fun _ => rfl⟩
  · unfold plevelIndicator
    by_cases hh : h ∈ finitePrincipalLevel L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
    · have hh' : h ∈ (finitePrincipalLevel L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) :
          Set _) := hh
      have hall := (mem_finitePrincipalLevel_iff_of_integral hNK hNS hint).1 hh
      rw [Set.indicator_of_mem hh']
      exact (Finset.prod_eq_one fun v hv => Set.indicator_of_mem (hall v hv) _).symm
    · have hh' : h ∉ (finitePrincipalLevel L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) :
          Set _) := hh
      rw [Set.indicator_of_notMem hh']
      have hnot : ¬ ∀ v ∈ SK, semiLocalComponent K L v h ∈
          semiLocalLevelSet K L v (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) :=
        fun hall => hh ((mem_finitePrincipalLevel_iff_of_integral hNK hNS hint).2 hall)
      obtain ⟨v, hvS, hv⟩ : ∃ v ∈ SK, semiLocalComponent K L v h ∉
          semiLocalLevelSet K L v (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) := by
        by_contra hcon
        exact hnot fun v hvS => Classical.byContradiction fun hv => hcon ⟨v, hvS, hv⟩
      exact (Finset.prod_eq_zero hvS (Set.indicator_of_notMem hv _)).symm
  · obtain ⟨v, -, hv⟩ := hex
    have hh : h ∉ (finitePrincipalLevel L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) :
        Set _) :=
      fun hh => hv (semiLocalComponent_mem_semiLocalIntegralSet_of_mem_finitePrincipalLevel hh v)
    exact Set.indicator_of_notMem hh _

private theorem isUnitFactorizableAboveOfType_glArch_mul_plevelIndicator {NK : Ideal (𝓞 K)} (hNK : NK ≠ ⊥)
    {SK : Finset (HeightOneSpectrum (𝓞 K))} (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L) {fa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ} (hfa : IsArchTestFactor L fa)
    (hfin : IsArchFactorBiFinite L tys fa) :
    IsUnitFactorizableAboveOfType K L tys
      (AdelicLevel.principalLevel (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L)
      SK fun g => fa (AdelicLevel.glArch (𝓞 L) L g) *
        plevelIndicator (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) (AdelicLevel.glFin (𝓞 L) L g) :=
  ⟨⟨isBiInvariantUnder_glArch_mul_plevelIndicator _ fa, _, _, _,
      isSemiLocalFactorization_plevelIndicator K L hNK hNS hfa⟩,
    IsArchBiFinite.of_factorization L (fun _ => rfl) hfin⟩

end Level

end Q09AIDock.LevelFiniteFactor

end

end

section

open AutomorphicForm

open NumberField NumberField.AdelicLevel
open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Q09AIDock
namespace ArchFinSplit

section Inclusions

variable (F : Type) [Field F] [NumberField F]

private def adelicFinGLIncl : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) →* AdelicGL2 (𝓞 F) F :=
  (Units.mapEquiv (adelicMatrixProdEquiv F).symm.toMulEquiv).toMonoidHom.comp <|
    (MulEquiv.prodUnits.symm : _ ≃* (_ × _)ˣ).toMonoidHom.comp <|
      MonoidHom.prod (1 : _ →* GL (Fin 2) (InfiniteAdeleRing F)) (MonoidHom.id _)

private theorem glArch_adelicFinGLIncl (k : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
    glArch (𝓞 F) F (adelicFinGLIncl F k) = 1 := by
  ext i j
  rfl

private theorem glFin_adelicFinGLIncl (k : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
    glFin (𝓞 F) F (adelicFinGLIncl F k) = k := by
  ext i j
  rfl

private def adelicProdMulEquiv :
    AdelicGL2 (𝓞 F) F ≃*
      GL (Fin 2) (InfiniteAdeleRing F) × GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) :=
  (Units.mapEquiv (adelicMatrixProdEquiv F).toMulEquiv).trans MulEquiv.prodUnits

private theorem adelicProdMulEquiv_apply (x : AdelicGL2 (𝓞 F) F) :
    adelicProdMulEquiv F x = (glArch (𝓞 F) F x, glFin (𝓞 F) F x) :=
  Prod.ext (by ext i j; rfl) (by ext i j; rfl)

private theorem adelicArchGLIncl_eq (a : GL (Fin 2) (InfiniteAdeleRing F)) :
    adelicArchGLIncl F a = (adelicProdMulEquiv F).symm (a, 1) := by
  ext i j
  rfl

private theorem adelicFinGLIncl_eq (b : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
    adelicFinGLIncl F b = (adelicProdMulEquiv F).symm (1, b) := by
  ext i j
  rfl

private theorem adelicArchGLIncl_glArch_mul_adelicFinGLIncl_glFin (x : AdelicGL2 (𝓞 F) F) :
    adelicArchGLIncl F (glArch (𝓞 F) F x) * adelicFinGLIncl F (glFin (𝓞 F) F x) = x := by
  have h := (adelicProdMulEquiv F).symm_apply_apply x
  rw [adelicProdMulEquiv_apply] at h
  rw [adelicArchGLIncl_eq, adelicFinGLIncl_eq, ← map_mul (adelicProdMulEquiv F).symm, Prod.mk_mul_mk,
    mul_one, one_mul]
  exact h

private theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl F) := by
  have hval : Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      ((adelicArchGLIncl F g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      (((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) :
          InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

private theorem continuous_adelicFinGLIncl : Continuous (adelicFinGLIncl F) := by
  have hval : Continuous fun k : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) =>
      ((adelicFinGLIncl F k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun k : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) =>
      (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (k : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) :
          InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
    exact continuous_const.prodMk (Units.continuous_val.matrix_elem i j)
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

end Inclusions

section Measures

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in
private theorem t2Space_archGL : T2Space (GL (Fin 2) (InfiniteAdeleRing F)) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing F))
  exact Units.isClosedEmbedding_embedProduct.toIsEmbedding.t2Space

private theorem locallyCompactSpace_archGL : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing F)) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing F))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing F))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

private theorem isHaarMeasure_archHaarK :
    @Measure.IsHaarMeasure (GL (Fin 2) (InfiniteAdeleRing F)) _ _ (glBorelOf (InfiniteAdeleRing F))
      (archHaarK F) := by
  letI := glBorelOf (InfiniteAdeleRing F)
  haveI := borelSpace_glBorelOf (InfiniteAdeleRing F)
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing F))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing F))
  haveI : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing F)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  exact Measure.isHaarMeasure_haarMeasure _

private def archProjMeasure (U : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))) :
    @Measure (GL (Fin 2) (InfiniteAdeleRing F)) (glBorelOf (InfiniteAdeleRing F)) :=
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  letI := glBorelOf (InfiniteAdeleRing F)
  Measure.map (glArch (𝓞 F) F)
    ((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).restrict (glFin (𝓞 F) F ⁻¹' U))

private theorem exists_forall_rightConv_eq_smul_integral
    {U : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))} (hUo : IsOpen U)
    (hUc : IsCompact U) (hUne : U.Nonempty) :
    ∃ c : ℝ, 0 < c ∧
      ∀ f : AdelicGL2 (𝓞 F) F → ℂ, Continuous f →
        (∀ g, ∀ k ∈ U, f (g * adelicFinGLIncl F k) = f g) →
        ∀ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, Continuous fa → HasCompactSupport fa →
        ∀ g, rightConv F f
            (fun x => fa (glArch (𝓞 F) F x) * U.indicator (fun _ => (1 : ℂ)) (glFin (𝓞 F) F x)) g =
          c • (letI := glBorelOf (InfiniteAdeleRing F)
            ∫ y, f (g * adelicArchGLIncl F y) * fa y ∂(archHaarK F)) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  letI : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F)) := glBorelOf (InfiniteAdeleRing F)
  haveI := borelSpace_glBorelOf (InfiniteAdeleRing F)
  haveI := t2Space_archGL F
  haveI := locallyCompactSpace_archGL F
  haveI := isHaarMeasure_archHaarK F
  have hS : MeasurableSet (glFin (𝓞 F) F ⁻¹' U) :=
    (hUo.preimage (continuous_glFin (𝓞 F) F)).measurableSet
  have hglArch : Measurable (glArch (𝓞 F) F) := (continuous_glArch (𝓞 F) F).measurable
  have hdecomp := adelicArchGLIncl_glArch_mul_adelicFinGLIncl_glFin F
  have hν : ∀ {A : Set (GL (Fin 2) (InfiniteAdeleRing F))}, MeasurableSet A →
      archProjMeasure F U A =
        AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F (glArch (𝓞 F) F ⁻¹' A ∩ glFin (𝓞 F) F ⁻¹' U) := by
    intro A hA
    show Measure.map (glArch (𝓞 F) F)
      ((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).restrict (glFin (𝓞 F) F ⁻¹' U)) A = _
    rw [Measure.map_apply hglArch hA, Measure.restrict_apply (hglArch hA)]
  haveI hinv : (archProjMeasure F U).IsMulLeftInvariant := by
    refine (forall_measure_preimage_mul_iff _).1 fun h A hA => ?_
    rw [hν (measurable_const_mul h hA), hν hA]
    have hset : glArch (𝓞 F) F ⁻¹' ((fun x => h * x) ⁻¹' A) ∩ glFin (𝓞 F) F ⁻¹' U =
        (fun x => adelicArchGLIncl F h * x) ⁻¹' (glArch (𝓞 F) F ⁻¹' A ∩ glFin (𝓞 F) F ⁻¹' U) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, map_mul, glArch_adelicArchGLIncl,
        glFin_adelicArchGLIncl, one_mul]
    rw [hset, measure_preimage_mul]
  haveI hfin : IsFiniteMeasureOnCompacts (archProjMeasure F U) := by
    refine ⟨fun C hC => ?_⟩
    rw [hν hC.measurableSet]
    have himg : glArch (𝓞 F) F ⁻¹' C ∩ glFin (𝓞 F) F ⁻¹' U ⊆
        (fun p : GL (Fin 2) (InfiniteAdeleRing F) ×
            GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) =>
          adelicArchGLIncl F p.1 * adelicFinGLIncl F p.2) '' (C ×ˢ U) :=
      fun x hx => ⟨(glArch (𝓞 F) F x, glFin (𝓞 F) F x), ⟨hx.1, hx.2⟩, hdecomp x⟩
    have hcpt : IsCompact ((fun p : GL (Fin 2) (InfiniteAdeleRing F) ×
            GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) =>
          adelicArchGLIncl F p.1 * adelicFinGLIncl F p.2) '' (C ×ˢ U)) :=
      (hC.prod hUc).image (((continuous_adelicArchGLIncl F).comp continuous_fst).mul
        ((continuous_adelicFinGLIncl F).comp continuous_snd))
    exact lt_of_le_of_lt (measure_mono himg) hcpt.measure_lt_top
  obtain ⟨k₀, hk₀⟩ := hUne
  haveI hpos : (archProjMeasure F U).IsOpenPosMeasure := by
    refine ⟨fun V hV hVne => ?_⟩
    rw [hν hV.measurableSet]
    obtain ⟨u, hu⟩ := hVne
    have hmem : adelicArchGLIncl F u * adelicFinGLIncl F k₀ ∈
        glArch (𝓞 F) F ⁻¹' V ∩ glFin (𝓞 F) F ⁻¹' U := by
      simp only [Set.mem_inter_iff, Set.mem_preimage, map_mul, glArch_adelicArchGLIncl,
        glFin_adelicArchGLIncl, glArch_adelicFinGLIncl, glFin_adelicFinGLIncl, mul_one, one_mul]
      exact ⟨hu, hk₀⟩
    exact (((hV.preimage (continuous_glArch (𝓞 F) F)).inter
      (hUo.preimage (continuous_glFin (𝓞 F) F))).measure_pos _ ⟨_, hmem⟩).ne'
  haveI hHaar : (archProjMeasure F U).IsHaarMeasure := {}
  refine ⟨(Measure.haarScalarFactor (archProjMeasure F U) (archHaarK F) : ℝ),
    NNReal.coe_pos.2 (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _), ?_⟩
  intro f hf hlev fa hfa hfac g
  have hH : Continuous fun y => f (g * adelicArchGLIncl F y) * fa y :=
    (hf.comp (continuous_const.mul (continuous_adelicArchGLIncl F))).mul hfa
  have hHc : HasCompactSupport fun y => f (g * adelicArchGLIncl F y) * fa y := hfac.mul_left
  have hind : (fun x => f (g * x) *
        (fa (glArch (𝓞 F) F x) * U.indicator (fun _ => (1 : ℂ)) (glFin (𝓞 F) F x))) =
      fun x => (glFin (𝓞 F) F ⁻¹' U).indicator (fun x => f (g * x) * fa (glArch (𝓞 F) F x)) x := by
    funext x
    by_cases hx : glFin (𝓞 F) F x ∈ U
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ glFin (𝓞 F) F ⁻¹' U from hx),
        mul_one]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ glFin (𝓞 F) F ⁻¹' U from hx),
        mul_zero, mul_zero]
  have hcongr : ∫ x in glFin (𝓞 F) F ⁻¹' U, f (g * x) * fa (glArch (𝓞 F) F x)
        ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ x in glFin (𝓞 F) F ⁻¹' U, f (g * adelicArchGLIncl F (glArch (𝓞 F) F x)) * fa (glArch (𝓞 F) F x)
        ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    refine setIntegral_congr_fun hS fun x hx => ?_
    show f (g * x) * fa (glArch (𝓞 F) F x) =
      f (g * adelicArchGLIncl F (glArch (𝓞 F) F x)) * fa (glArch (𝓞 F) F x)
    rw [← hlev (g * adelicArchGLIncl F (glArch (𝓞 F) F x)) (glFin (𝓞 F) F x) hx, mul_assoc, hdecomp x]
  have hmap : ∫ y, f (g * adelicArchGLIncl F y) * fa y ∂(archProjMeasure F U) =
      ∫ x in glFin (𝓞 F) F ⁻¹' U, f (g * adelicArchGLIncl F (glArch (𝓞 F) F x)) * fa (glArch (𝓞 F) F x)
        ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    have hm : AEStronglyMeasurable (fun y => f (g * adelicArchGLIncl F y) * fa y)
        (Measure.map (glArch (𝓞 F) F)
          ((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).restrict (glFin (𝓞 F) F ⁻¹' U))) :=
      hH.aestronglyMeasurable
    exact integral_map hglArch.aemeasurable hm
  have hKc : IsCompact (tsupport fun y => f (g * adelicArchGLIncl F y) * fa y) := hHc
  have hrestrict : (archProjMeasure F U).restrict
        (tsupport fun y => f (g * adelicArchGLIncl F y) * fa y) =
      (((Measure.haarScalarFactor (archProjMeasure F U) (archHaarK F) : ℝ≥0) : ℝ≥0∞) • archHaarK F).restrict
        (tsupport fun y => f (g * adelicArchGLIncl F y) * fa y) := by
    ext A hA
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA, Measure.smul_apply, smul_eq_mul,
      Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure (archProjMeasure F U) (archHaarK F)
        (hKc.of_isClosed_subset isClosed_closure
          (closure_minimal Set.inter_subset_right (isClosed_tsupport _))),
      ENNReal.smul_def, smul_eq_mul]
  have hzero : ∀ y, y ∉ tsupport (fun y => f (g * adelicArchGLIncl F y) * fa y) →
      f (g * adelicArchGLIncl F y) * fa y = 0 :=
    fun y hy => (image_eq_zero_of_notMem_tsupport hy :)
  have huniq : ∫ y, f (g * adelicArchGLIncl F y) * fa y ∂(archProjMeasure F U) =
      (Measure.haarScalarFactor (archProjMeasure F U) (archHaarK F) : ℝ) •
        ∫ y, f (g * adelicArchGLIncl F y) * fa y ∂(archHaarK F) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, hrestrict,
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_smul_measure, ENNReal.coe_toReal]
  rw [rightConv_apply, hind, integral_indicator hS, hcongr, ← hmap]
  exact huniq

end Measures

end Q09AIDock.ArchFinSplit

end

end

section

open AutomorphicForm

open NumberField IsDedekindDomain

noncomputable section

namespace Q09AIDock

namespace LevelFiniteFactor

variable {K : Type} [Field K] [NumberField K]

private theorem exists_heightOneSpectrum_comap_eq_span (p : ℕ) (hp : p.Prime) :
    ∃ P : HeightOneSpectrum (𝓞 K),
      Ideal.comap (algebraMap ℤ (𝓞 K)) P.asIdeal = Ideal.span {(p : ℤ)} := by
  have hinj : Function.Injective (algebraMap ℤ (𝓞 K)) := RingHom.injective_int _
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hp0).2 (Nat.prime_iff_prime_int.1 hp)
  obtain ⟨Q, -, hQprime, hQcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (Ideal.span {(p : ℤ)}) (⊥ : Ideal (𝓞 K)) (Ideal.comap_bot_le_of_injective _ hinj)
  refine ⟨⟨Q, hQprime, fun hQ => ?_⟩, hQcomap⟩
  rw [hQ, Ideal.comap_bot_of_injective _ hinj] at hQcomap
  exact hp0 (Ideal.span_singleton_eq_bot.1 hQcomap.symm)

private theorem ne_bot_of_forall_dvd_mem {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ N → p ∈ S) : N ≠ ⊥ := by
  rintro rfl
  have hall : ∀ p : HeightOneSpectrum (𝓞 K), p ∈ S := fun p =>
    hNS p (by rw [← Ideal.zero_eq_bot]; exact dvd_zero _)
  choose P hP using fun q : {p : ℕ | Nat.Prime p} =>
    exists_heightOneSpectrum_comap_eq_span (K := K) q.1 q.2
  haveI : Infinite {p : ℕ | Nat.Prime p} := Set.infinite_coe_iff.2 Nat.infinite_setOf_prime
  refine not_injective_infinite_finite (fun q : {p : ℕ | Nat.Prime p} => (⟨P q, hall (P q)⟩ : S))
    fun q₁ q₂ h => ?_
  have h' : P q₁ = P q₂ := congrArg Subtype.val h
  have hspan : Ideal.span {((q₁ : ℕ) : ℤ)} = Ideal.span {((q₂ : ℕ) : ℤ)} := by
    rw [← hP q₁, ← hP q₂, h']
  have hq := Int.eq_of_associated_of_nonneg (Ideal.span_singleton_eq_span_singleton.1 hspan)
    (by positivity) (by positivity)
  exact Subtype.ext (by exact_mod_cast hq)

end LevelFiniteFactor

namespace ArchFactor

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in
private theorem continuous_archEntries : Continuous (archEntries F) :=
  continuous_pi fun i => continuous_pi fun j =>
    (AdelicBox.continuous_ringEquiv_mixedSpace (K := F)).comp (Units.continuous_val.matrix_elem i j)

variable {F}

open scoped Classical in
private theorem continuous_of_isArchTestFactor {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (h : IsArchTestFactor F fa) : Continuous fa := by
  obtain ⟨⟨Φ, hΦ, hrepr⟩, -⟩ := h
  have hfa : fa = Φ ∘ archEntries F := funext hrepr
  rw [hfa]
  exact hΦ.continuous.comp (continuous_archEntries F)

open scoped Classical in
private theorem isArchTestFactor_const_smul {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (h : IsArchTestFactor F fa) (z : ℂ) : IsArchTestFactor F (z • fa) := by
  obtain ⟨⟨Φ, hΦ, hrepr⟩, hsupp⟩ := h
  refine ⟨⟨fun y => z • Φ y, hΦ.const_smul z, fun g => ?_⟩, ?_⟩
  · show z • fa g = z • Φ (archEntries F g)
    rw [hrepr g]
  · exact hsupp.comp_left (g := fun x => z • x) (smul_zero z)

omit [NumberField F] in
private theorem isArchFactorBiFinite_const_smul {tys : ArchTypeFamily F}
    {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : IsArchFactorBiFinite F tys fa) (z : ℂ) :
    IsArchFactorBiFinite F tys (z • fa) :=
  ⟨(archFactorCutSubmodule F tys).smul_mem z h.1, (archFactorDualCutSubmodule F tys).smul_mem z h.2⟩

end ArchFactor

end Q09AIDock

end

end

section

open AutomorphicForm

open NumberField NumberField.AdelicLevel IsDedekindDomain MeasureTheory

noncomputable section

namespace Q09AIDock
namespace AIDock

open LevelFiniteFactor ArchFinSplit ArchFactor

private theorem exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_arch
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L) (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f)
    (hlev : ∀ g : AdelicGL2 (𝓞 L) L,
      ∀ k ∈ principalLevel (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L,
        f (g * k) = f g)
    (hAI : ∃ fa : ℕ → (GL (Fin 2) (InfiniteAdeleRing L) → ℂ),
      (∀ n, IsArchTestFactor L (fa n) ∧ IsArchFactorBiFinite L tys (fa n)) ∧
      ∀ g, Filter.Tendsto
        (fun n => letI := glBorelOf (InfiniteAdeleRing L)
          ∫ y, f (g * adelicArchGLIncl L y) * fa n y ∂(archHaarK L))
        Filter.atTop (nhds (f g))) :
    ∃ φ : ℕ → (AdelicGL2 (𝓞 L) L → ℂ),
      (∀ n, IsUnitFactorizableAboveOfType K L tys
        (principalLevel (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK (φ n)) ∧
      ∀ g, Filter.Tendsto (fun n => rightConv L f (φ n) g) Filter.atTop (nhds (f g)) := by
  letI : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing L)) := glBorelOf (InfiniteAdeleRing L)
  obtain ⟨fa, hfa, hlim⟩ := hAI
  have hNK : NK ≠ ⊥ := ne_bot_of_forall_dvd_mem hNS
  have hN' : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK ≠ ⊥ := map_algebraMap_ne_bot hNK
  obtain ⟨c, hc, hsplit⟩ := exists_forall_rightConv_eq_smul_integral L
    (isOpen_finitePrincipalLevel L hN')
    (isCompact_finitePrincipalLevel L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK))
    ⟨1, (finitePrincipalLevel L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)).one_mem⟩
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hinv : ∀ g, ∀ k ∈ (finitePrincipalLevel L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) :
      Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))), f (g * adelicFinGLIncl L k) = f g := by
    intro g k hk
    refine hlev g _ ?_
    rw [Subgroup.mem_inf, mem_principalLevel_iff_glFin, mem_finiteAdelicGL2Subgroup_iff, glFin_adelicFinGLIncl,
      glArch_adelicFinGLIncl]
    exact ⟨hk, rfl⟩
  refine ⟨fun n => fun x => ((c : ℂ)⁻¹ • fa n) (glArch (𝓞 L) L x) *
      plevelIndicator (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) (glFin (𝓞 L) L x), fun n => ?_, fun g => ?_⟩
  · exact isUnitFactorizableAboveOfType_glArch_mul_plevelIndicator K L hNK hNS tys
      (isArchTestFactor_const_smul (hfa n).1 (c : ℂ)⁻¹) (isArchFactorBiFinite_const_smul (hfa n).2 (c : ℂ)⁻¹)
  · refine (hlim g).congr fun n => ?_
    have hfa' : IsArchTestFactor L ((c : ℂ)⁻¹ • fa n) := isArchTestFactor_const_smul (hfa n).1 (c : ℂ)⁻¹
    have hs : rightConv L f (fun x => ((c : ℂ)⁻¹ • fa n) (glArch (𝓞 L) L x) *
          plevelIndicator (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) (glFin (𝓞 L) L x)) g =
        c • ∫ y, f (g * adelicArchGLIncl L y) * ((c : ℂ)⁻¹ • fa n) y ∂(archHaarK L) :=
      hsplit f hf hinv ((c : ℂ)⁻¹ • fa n) (continuous_of_isArchTestFactor hfa') hfa'.2 g
    have hfun : (fun y => f (g * adelicArchGLIncl L y) * ((c : ℂ)⁻¹ • fa n) y) =
        fun y => (c : ℂ)⁻¹ * (f (g * adelicArchGLIncl L y) * fa n y) :=
      funext fun y => by rw [Pi.smul_apply, smul_eq_mul]; ring
    have hpull : (∫ y, (c : ℂ)⁻¹ * (f (g * adelicArchGLIncl L y) * fa n y) ∂(archHaarK L)) =
        (c : ℂ)⁻¹ * ∫ y, f (g * adelicArchGLIncl L y) * fa n y ∂(archHaarK L) :=
      integral_const_mul _ _
    show (∫ y, f (g * adelicArchGLIncl L y) * fa n y ∂(archHaarK L)) =
      rightConv L f (fun x => ((c : ℂ)⁻¹ • fa n) (glArch (𝓞 L) L x) *
        plevelIndicator (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) (glFin (𝓞 L) L x)) g
    rw [hs, hfun, hpull, Complex.real_smul, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

end Q09AIDock.AIDock

end

end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm

open NumberField NumberField.AdelicLevel IsDedekindDomain in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L) (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f)
    (hlev : ∀ g : AdelicGL2 (𝓞 L) L,
      ∀ k ∈ principalLevel (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L,
        f (g * k) = f g)
    (harch : f ∈ archCutSubmodule L tys) :
    ∃ φ : ℕ → (AdelicGL2 (𝓞 L) L → ℂ),
      (∀ n, IsUnitFactorizableAboveOfType K L tys
        (principalLevel (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK (φ n)) ∧
      ∀ g, Filter.Tendsto (fun n => rightConv L f (φ n) g) Filter.atTop (nhds (f g)) :=
  Q09AIDock.AIDock.exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_arch
    K L NK SK hNS tys f hf hlev
    (AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule
      L tys f hf harch)

end
end S_AutomorphicForm_exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_mem_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_mem_archCutSubmodule (solution)
