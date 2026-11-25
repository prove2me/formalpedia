-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Rational
-- name    : GroundTheory_GlobalFields_IdeleGroups_Rational
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:39:18.110007+00:00
-- url     : https://prove2.me/theorems/b064e40a-e0c1-4d9d-ae10-5b80cbd3c38d
-- title:
--   Rational
-- statement:
--   Definitions and structural lemmas for Rational, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/Rational.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_StandardOpenEquiv
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_standardOpenSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_toInfinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_diagonal_injective
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isOpen_standardOpenSubgroup
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_continuous_equiv_symm_of_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_standardOpenSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_snd


set_option autoImplicit false
namespace GroundTheory.Global
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing
noncomputable section
local instance _p2m_local_instance_d54fe1196b_11 (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩
namespace RationalIdeles
open IdeleGroup
theorem isReal_infinitePlace (w : InfinitePlace ℚ) : w.IsReal := by
  rw [Subsingleton.elim w Rat.infinitePlace]
  exact Rat.isReal_infinitePlace
def realEquiv : InfiniteAdeleRing ℚ ≃+* ℝ :=
  (RingEquiv.piUnique fun w : InfinitePlace ℚ ↦ w.Completion).trans
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_infinitePlace default))
theorem continuous_realEquiv : Continuous realEquiv :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous.comp
    (continuous_apply _)
theorem continuous_realEquiv_symm : Continuous realEquiv.symm := by
  exact continuous_equiv_symm_of_eq realEquiv.toEquiv
    ((Homeomorph.piUnique fun w : InfinitePlace ℚ ↦ w.Completion).trans
      (InfinitePlace.Completion.isometryEquivRealOfIsReal
        (isReal_infinitePlace default)).toHomeomorph)
    fun _ ↦ rfl
def realUnitsEquiv : (InfiniteAdeleRing ℚ)ˣ ≃ₜ* ℝˣ :=
  unitsContinuousMulEquiv realEquiv.toMulEquiv continuous_realEquiv continuous_realEquiv_symm
def realPart : IdeleGroup ℚ →* ℝˣ :=
  realUnitsEquiv.toMulEquiv.toMonoidHom.comp (toInfinite ℚ)
theorem coe_realPart (x : IdeleGroup ℚ) : (realPart x : ℝ) = realEquiv (x : 𝔸[ℚ]).1 :=
  rfl
theorem continuous_realPart : Continuous realPart :=
  realUnitsEquiv.continuous.comp (continuous_toInfinite ℚ)
@[simp]
theorem realPart_diagonal (a : ℚˣ) : (realPart (diagonal ℚ a) : ℝ) = a := by
  rw [coe_realPart, coe_diagonal]
  exact eq_ratCast (realEquiv.toRingHom.comp (algebraMap ℚ (InfiniteAdeleRing ℚ))) a
theorem realPart_ofIntegerUnits (a : (InfiniteAdeleRing ℚ)ˣ)
    (u : Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) :
    realPart (ofIntegerUnits a u) = realUnitsEquiv a :=
  rfl
def positiveSubgroup : Subgroup (IdeleGroup ℚ) :=
  standardOpenSubgroup ℚ ⊓ (Units.posSubgroup ℝ).comap realPart
theorem mem_positiveSubgroup {x : IdeleGroup ℚ} :
    x ∈ positiveSubgroup ↔ x ∈ standardOpenSubgroup ℚ ∧ 0 < (realPart x : ℝ) := by
  rw [positiveSubgroup, Subgroup.mem_inf, Subgroup.mem_comap, Units.mem_posSubgroup]
theorem isOpen_positiveSubgroup : IsOpen (positiveSubgroup : Set (IdeleGroup ℚ)) := by
  have h : (positiveSubgroup : Set (IdeleGroup ℚ)) =
      (standardOpenSubgroup ℚ : Set (IdeleGroup ℚ)) ∩ {x | 0 < (realPart x : ℝ)} := by
    ext x
    exact mem_positiveSubgroup
  rw [h]
  exact (isOpen_standardOpenSubgroup ℚ).inter
    (isOpen_lt continuous_const (Units.continuous_val.comp continuous_realPart))
theorem diagonal_mem_standardOpenSubgroup_iff (a : ℚˣ) :
    diagonal ℚ a ∈ standardOpenSubgroup ℚ ↔ (a : ℚ) = 1 ∨ (a : ℚ) = -1 := by
  rw [← ker_toFractionalIdeal, MonoidHom.mem_ker, toFractionalIdeal_diagonal,
    toPrincipalIdeal_eq_iff, Units.val_one, ← FractionalIdeal.spanSingleton_one,
    FractionalIdeal.spanSingleton_eq_spanSingleton]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : ((z : 𝓞 ℚ) : ℚ) * a = 1 := by
      rw [Units.smul_def, Algebra.smul_def] at hz
      exact hz
    rcases Rat.RingOfIntegers.isUnit_iff.1 z.isUnit with h | h
    · left
      rwa [h, one_mul] at hz'
    · right
      rwa [h, neg_one_mul, neg_eq_iff_eq_neg] at hz'
  · rintro (h | h)
    · exact ⟨1, by rw [one_smul, h]⟩
    · exact ⟨-1, by rw [Units.neg_smul, one_smul, h, neg_neg]⟩
theorem positiveSubgroup_inf_diagonal_range : positiveSubgroup ⊓ (diagonal ℚ).range = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, a, rfl⟩
  obtain ⟨h1, h2⟩ := mem_positiveSubgroup.1 hx
  rw [realPart_diagonal] at h2
  rw [Subgroup.mem_bot]
  rcases (diagonal_mem_standardOpenSubgroup_iff a).1 h1 with h | h
  · rw [show a = 1 from Units.ext h, map_one]
  · rw [h] at h2
    norm_num at h2
theorem subsingleton_classGroup : Subsingleton (ClassGroup (𝓞 ℚ)) := by
  have h := Rat.classNumber_eq
  rw [NumberField.classNumber] at h
  exact Fintype.card_le_one_iff_subsingleton.1 h.le
theorem positiveSubgroup_sup_diagonal_range : positiveSubgroup ⊔ (diagonal ℚ).range = ⊤ := by
  have htop : (diagonal ℚ).range ⊔ standardOpenSubgroup ℚ = ⊤ := by
    rw [← IdeleGroup.ker_toClassGroup, eq_top_iff]
    intro x _
    have := subsingleton_classGroup
    exact Subsingleton.elim _ _
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ (diagonal ℚ).range ⊔ standardOpenSubgroup ℚ := htop ▸ Subgroup.mem_top x
  obtain ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩ := Subgroup.mem_sup.1 hx
  rcases lt_or_gt_of_ne (realPart u).ne_zero with hneg | hpos
  · have hm : diagonal ℚ (-1) ∈ standardOpenSubgroup ℚ :=
      (diagonal_mem_standardOpenSubgroup_iff (-1)).2 (Or.inr (by simp))
    have hp : diagonal ℚ (-1) * u ∈ positiveSubgroup := by
      refine mem_positiveSubgroup.2 ⟨mul_mem hm hu, ?_⟩
      rw [map_mul, Units.val_mul, realPart_diagonal]
      push_cast
      linarith
    refine Subgroup.mem_sup.2 ⟨_, hp, diagonal ℚ (-a), ⟨-a, rfl⟩, ?_⟩
    rw [mul_right_comm, ← map_mul, neg_one_mul, neg_neg]
  · exact Subgroup.mem_sup.2 ⟨u, mem_positiveSubgroup.2 ⟨hu, hpos⟩, diagonal ℚ a, ⟨a, rfl⟩,
      mul_comm _ _⟩
def positiveSubgroupEquivIdeleClassGroup : positiveSubgroup ≃ₜ* IdeleClassGroup ℚ :=
  openSubgroupEquivQuotient _ _ isOpen_positiveSubgroup positiveSubgroup_inf_diagonal_range
    positiveSubgroup_sup_diagonal_range
@[simp]
theorem positiveSubgroupEquivIdeleClassGroup_apply (x : positiveSubgroup) :
    positiveSubgroupEquivIdeleClassGroup x = IdeleClassGroup.mk ℚ x :=
  rfl
def positiveSubgroupEquiv : positiveSubgroup ≃ₜ* Units.posSubgroup ℝ ×
    Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ where
  toFun x := (⟨realPart x, (Units.mem_posSubgroup _).2 (mem_positiveSubgroup.1 x.2).2⟩,
    (standardOpenSubgroupEquiv ℚ ⟨x, (mem_positiveSubgroup.1 x.2).1⟩).2)
  invFun p := ⟨ofIntegerUnits (realUnitsEquiv.symm p.1) p.2, mem_positiveSubgroup.2
    ⟨ofIntegerUnits_mem _ _, by
      rw [realPart_ofIntegerUnits, ContinuousMulEquiv.apply_symm_apply]
      exact (Units.mem_posSubgroup _).1 p.1.2⟩⟩
  left_inv x := by
    have h : realUnitsEquiv.symm (realPart x) = toInfinite ℚ x :=
      realUnitsEquiv.symm_apply_apply _
    apply Subtype.ext
    change ofIntegerUnits (realUnitsEquiv.symm (realPart x)) _ = (x : IdeleGroup ℚ)
    rw [h]
    exact Units.ext (Prod.ext rfl (Subtype.ext (funext fun _ ↦ rfl)))
  right_inv p := Prod.ext (Subtype.ext (realUnitsEquiv.apply_symm_apply _))
    (funext fun _ ↦ Units.ext (Subtype.ext rfl))
  map_mul' x y := Prod.ext (Subtype.ext (map_mul realPart (x : IdeleGroup ℚ) y))
    (funext fun _ ↦ Units.ext (Subtype.ext rfl))
  continuous_toFun := by
    exact ((continuous_realPart.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp ((standardOpenSubgroupEquiv ℚ).continuous.comp
        (continuous_subtype_val.subtype_mk _)))
  continuous_invFun := by
    exact (continuous_subtype_val.comp ((standardOpenSubgroupEquiv ℚ).symm.continuous.comp
      ((realUnitsEquiv.symm.continuous.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        continuous_snd))).subtype_mk _
@[simp]
theorem coe_positiveSubgroupEquiv_apply_fst (x : positiveSubgroup) :
    ((positiveSubgroupEquiv x).1 : ℝˣ) = realPart x :=
  rfl
@[simp]
theorem coe_positiveSubgroupEquiv_apply_snd (x : positiveSubgroup) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (((positiveSubgroupEquiv x).2 v : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) =
      ((x : IdeleGroup ℚ) : 𝔸[ℚ]).2 v :=
  rfl
@[simp]
theorem realPart_positiveSubgroupEquiv_symm_apply (p : Units.posSubgroup ℝ ×
    Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) :
    realPart (positiveSubgroupEquiv.symm p : IdeleGroup ℚ) = p.1 :=
  congrArg (fun q ↦ (q.1 : ℝˣ)) (positiveSubgroupEquiv.apply_symm_apply p)
@[simp]
theorem coe_positiveSubgroupEquiv_symm_apply_snd (p : Units.posSubgroup ℝ ×
    Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((positiveSubgroupEquiv.symm p : IdeleGroup ℚ) : 𝔸[ℚ]).2 v =
      ((p.2 v : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) :=
  rfl
def integersRingEquiv :
    (Π v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ) ≃+* Π p : Nat.Primes, ℤ_[p] :=
  (RingEquiv.piCongrRight fun v ↦
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv).trans
    (RingEquiv.piCongrLeft (fun p : Nat.Primes ↦ ℤ_[p]) Rat.HeightOneSpectrum.primesEquiv)
def integersHomeomorph :
    (Π v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ) ≃ₜ Π p : Nat.Primes, ℤ_[p] :=
  (Homeomorph.piCongrRight fun v ↦
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph).trans
    (Homeomorph.piCongrLeft (Y := fun p : Nat.Primes ↦ ℤ_[p]) Rat.HeightOneSpectrum.primesEquiv)
theorem integersRingEquiv_eq_integersHomeomorph (x : Π v : HeightOneSpectrum (𝓞 ℚ),
    v.adicCompletionIntegers ℚ) : integersRingEquiv x = integersHomeomorph x :=
  rfl
theorem continuous_integersRingEquiv : Continuous integersRingEquiv :=
  integersHomeomorph.continuous.congr fun x ↦ (integersRingEquiv_eq_integersHomeomorph x).symm
theorem continuous_integersRingEquiv_symm : Continuous integersRingEquiv.symm := by
  exact continuous_equiv_symm_of_eq integersRingEquiv.toEquiv integersHomeomorph
    integersRingEquiv_eq_integersHomeomorph
def integerUnitsEquiv :
    (Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) ≃ₜ*
      (Π p : Nat.Primes, ℤ_[p])ˣ :=
  ContinuousMulEquiv.piUnits.symm.trans
    (unitsContinuousMulEquiv integersRingEquiv.toMulEquiv continuous_integersRingEquiv
      continuous_integersRingEquiv_symm)
def integerUnitsEquivPi :
    (Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) ≃ₜ*
      Π p : Nat.Primes, ℤ_[p]ˣ :=
  integerUnitsEquiv.trans ContinuousMulEquiv.piUnits
def mulMap : ℚˣ × positiveSubgroup →* IdeleGroup ℚ :=
  (diagonal ℚ).coprod positiveSubgroup.subtype
theorem mulMap_bijective : Function.Bijective mulMap := by
  constructor
  · rw [injective_iff_map_eq_one]
    rintro ⟨a, u⟩ h
    have h' : diagonal ℚ a * (u : IdeleGroup ℚ) = 1 := h
    have hu : (u : IdeleGroup ℚ)⁻¹ ∈ positiveSubgroup ⊓ (diagonal ℚ).range :=
      ⟨positiveSubgroup.inv_mem u.2, a, eq_inv_of_mul_eq_one_left h'⟩
    rw [positiveSubgroup_inf_diagonal_range, Subgroup.mem_bot, inv_eq_one] at hu
    have ha : diagonal ℚ a = 1 := by rwa [hu, mul_one] at h'
    exact Prod.ext (diagonal_injective ℚ (ha.trans (map_one _).symm)) (Subtype.ext hu)
  · intro x
    have hx : x ∈ positiveSubgroup ⊔ (diagonal ℚ).range :=
      positiveSubgroup_sup_diagonal_range ▸ Subgroup.mem_top x
    obtain ⟨u, hu, _, ⟨a, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hx
    exact ⟨(a, ⟨u, hu⟩), mul_comm _ _⟩
def ideleEquiv : IdeleGroup ℚ ≃* ℚˣ × Units.posSubgroup ℝ × Π p : Nat.Primes, ℤ_[p]ˣ :=
  (MulEquiv.ofBijective mulMap mulMap_bijective).symm.trans
    (MulEquiv.prodCongr (MulEquiv.refl _) (positiveSubgroupEquiv.toMulEquiv.trans
      (MulEquiv.prodCongr (MulEquiv.refl _) integerUnitsEquivPi.toMulEquiv)))
def ideleClassGroupEquiv : IdeleClassGroup ℚ ≃ₜ* Units.posSubgroup ℝ × (Π p : Nat.Primes, ℤ_[p])ˣ :=
  positiveSubgroupEquivIdeleClassGroup.symm.trans (positiveSubgroupEquiv.trans
    (continuousMulEquivProdCongr (ContinuousMulEquiv.refl _) integerUnitsEquiv))
def ideleClassGroupEquivPi : IdeleClassGroup ℚ ≃ₜ* Units.posSubgroup ℝ × Π p : Nat.Primes, ℤ_[p]ˣ :=
  positiveSubgroupEquivIdeleClassGroup.symm.trans (positiveSubgroupEquiv.trans
    (continuousMulEquivProdCongr (ContinuousMulEquiv.refl _) integerUnitsEquivPi))
end RationalIdeles
end
end GroundTheory.Global


