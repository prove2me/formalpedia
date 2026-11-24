-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
-- name    : Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T21:36:31.72669+00:00
-- url     : https://prove2.me/theorems/4c28ae90-709b-4126-9c3f-bb520b5facb2
-- title:
--   Standard Order Extended Basis Apply Low Block
-- statement:
--   Definitions and structural lemmas for Standard Order Extended Basis Apply Low Block, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Theorems.Thm_GlobalTheory_RootEx_Model_conj_mem
import Theorems.Thm_GlobalTheory_SplitWeil_Model_KOne_le_KO
import Theorems.Thm_GlobalTheory_SplitWeil_Model_isOpen_int
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_int
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_IntM_mul_maxM
import Theorems.Thm_GlobalTheory_StepData_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_MaxM_add
import Theorems.Thm_GlobalTheory_StepData_MaxM_mul_intM
import Theorems.Thm_GlobalTheory_StepData_blocks_inv
import Theorems.Thm_GlobalTheory_StepData_exists_diag_blocks
import Theorems.Thm_GlobalTheory_StepData_exists_mul_KOne
import Theorems.Thm_GlobalTheory_StepData_intM_of_mem_KO
import Theorems.Thm_GlobalTheory_StepData_intM_zero
import Theorems.Thm_GlobalTheory_StepData_inv_mul_mem_KOne
import Theorems.Thm_GlobalTheory_StepData_maxM_zero
import Theorems.Thm_GlobalTheory_StepData_mem_KO
import Theorems.Thm_GlobalTheory_StepData_mem_KOne
import Theorems.Thm_GlobalTheory_StepData_tame_det_of_mem_KOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
namespace GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
structure Level (G : Type*) [Group G] where

  J : Subgroup G

  lam : J →* ℂˣ
def Level.map {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') (P : Level G) : Level G' where
  J := P.J.comap φ.symm.toMonoidHom
  lam := P.lam.comp (φ.symm.toMonoidHom.subgroupComap P.J)
section Plain
variable {k : Type*} [Field k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
open Classical in

def extZ (J : Subgroup (GL a k)) (ρ : J →* ℂˣ) (M : Matrix a a k) : ℂ :=
  if h : ∃ g : J, (g : GL a k).val = M then (ρ h.choose : ℂ) else 0
theorem extZ_coe (J : Subgroup (GL a k)) (ρ : J →* ℂˣ) (g : J) : extZ J ρ (g : GL a k).val = ρ g := by
  have h : ∃ g' : J, (g' : GL a k).val = (g : GL a k).val := ⟨g, rfl⟩
  rw [extZ, dif_pos h, show h.choose = g from Subtype.ext (Units.ext h.choose_spec)]
theorem extZ_of_not (J : Subgroup (GL a k)) (ρ : J →* ℂˣ) {M : Matrix a a k}
    (h : ¬ ∃ g ∈ J, g.val = M) : extZ J ρ M = 0 :=
  dif_neg fun ⟨g, hg⟩ => h ⟨g, g.2, hg⟩
theorem extZ_ne_zero_iff (J : Subgroup (GL a k)) (ρ : J →* ℂˣ) {M : Matrix a a k} :
    extZ J ρ M ≠ 0 ↔ ∃ g ∈ J, g.val = M := by
  refine ⟨fun h => by_contra fun h' => h (extZ_of_not J ρ h'), ?_⟩
  rintro ⟨g, hg, rfl⟩
  rw [extZ_coe J ρ ⟨g, hg⟩]; exact Units.ne_zero _
def reGL (e : a ≃ b) : GL a k ≃* GL b k := Units.mapEquiv (Matrix.reindexRingEquiv k e).toMulEquiv
theorem reGL_symm_val (e : a ≃ b) (g : GL b k) : ((reGL e).symm g).val = g.val.submatrix e e := rfl
def embTop (t : Type*) [Fintype t] [DecidableEq t] : GL a k →* GL (a ⊕ t) k :=
  Units.map
    { toFun := fun g : Matrix a a k => (fromBlocks g 0 0 1 : Matrix (a ⊕ t) (a ⊕ t) k)
      map_one' := fromBlocks_one
      map_mul' := fun g h => by simp [fromBlocks_multiply] }
omit [DecidableEq a] [DecidableEq t] in
theorem mul_toBlocks₁₁ (M M' : Matrix (a ⊕ t) (a ⊕ t) k) :
    (M * M').toBlocks₁₁ = M.toBlocks₁₁ * M'.toBlocks₁₁ + M.toBlocks₁₂ * M'.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks M', fromBlocks_multiply, toBlocks_fromBlocks₁₁]
omit [DecidableEq a] [DecidableEq t] in
theorem mul_toBlocks₂₁ (M M' : Matrix (a ⊕ t) (a ⊕ t) k) :
    (M * M').toBlocks₂₁ = M.toBlocks₂₁ * M'.toBlocks₁₁ + M.toBlocks₂₂ * M'.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks M', fromBlocks_multiply, toBlocks_fromBlocks₂₁]
end Plain
abbrev Ix (r t : Type*) (j : ℕ) : Type _ := r ⊕ (Fin j × t)
def Ix.blk {r t : Type*} {j : ℕ} : Ix r t j → ℕ := Sum.elim (fun _ => 0) (fun p => p.1.val + 1)
def Ix.diagonalBlockOfMatrix {r t k : Type*} {j : ℕ} (M : Matrix (Ix r t j) (Ix r t j) k) (i : Fin j) : Matrix t t k :=
  M.submatrix (fun s => Sum.inr (i, s)) (fun s => Sum.inr (i, s))
def ixZero (r t : Type*) : r ≃ Ix r t 0 := (Equiv.sumEmpty r (Fin 0 × t)).symm
def ixSucc (r t : Type*) (j : ℕ) : Ix r t j ⊕ t ≃ Ix r t (j + 1) where
  toFun := Sum.elim (Sum.map id fun p => (p.1.castSucc, p.2)) fun s => Sum.inr (Fin.last j, s)
  invFun := Sum.elim (fun i => Sum.inl (Sum.inl i))
    fun p => Fin.lastCases (Sum.inr p.2) (fun i => Sum.inl (Sum.inr (i, p.2))) p.1
  left_inv := by rintro ((i | ⟨i, s⟩) | s) <;> simp
  right_inv := by
    rintro (i | ⟨i, s⟩)
    · simp
    · induction i using Fin.lastCases <;> simp
section Local
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
variable (k a) in

structure TypeDatum extends Level (GL a k) where
  KOne_le : KOne k a ≤ J
  le_KO : J ≤ KO k a
  lam_eq_one : ∀ g : J, (g : GL a k) ∈ KOne k a → lam g = 1
namespace TypeDatum
variable (k a) in

def full : TypeDatum k a := ⟨⟨KO k a, 1⟩, StepData.KOne_le_KO, le_rfl, fun _ _ => rfl⟩
variable (k a) in

def principal : TypeDatum k a := ⟨⟨KOne k a, 1⟩, le_rfl, StepData.KOne_le_KO, fun _ _ => rfl⟩
def ofResidue (H : Subgroup (GL a 𝓀[k])) (χ : H →* ℂˣ) : TypeDatum k a where
  J := (H.comap (Matrix.GeneralLinearGroup.map (n := a) (IsLocalRing.residue 𝒪[k]))).map
    (Matrix.GeneralLinearGroup.map (n := a) (algebraMap 𝒪[k] k))
  lam := (χ.comp ((Matrix.GeneralLinearGroup.map (n := a) (IsLocalRing.residue 𝒪[k])).subgroupComap H)).comp
    (Subgroup.equivMapOfInjective _ _ (Units.map_injective
      (Matrix.map_injective (FaithfulSMul.algebraMap_injective 𝒪[k] k)))).symm.toMonoidHom
  KOne_le := Subgroup.map_mono fun g hg => by
    rw [Subgroup.mem_comap, show _ = (1 : GL a 𝓀[k]) from hg]; exact H.one_mem
  le_KO := Subgroup.map_le_range _ _
  lam_eq_one := by
    rintro ⟨_, u, hu, rfl⟩ ⟨u', hu', e⟩
    have inj : Function.Injective (Matrix.GeneralLinearGroup.map (n := a) (algebraMap 𝒪[k] k)) :=
      Units.map_injective (Matrix.map_injective (FaithfulSMul.algebraMap_injective 𝒪[k] k))
    obtain rfl : u' = u := inj e
    have h1 : (Subgroup.equivMapOfInjective _ _ inj).symm ⟨_, u', hu, rfl⟩ = ⟨u', hu⟩ :=
      (MulEquiv.symm_apply_eq _).2 rfl
    change χ ((Matrix.GeneralLinearGroup.map (n := a) (IsLocalRing.residue 𝒪[k])).subgroupComap H
      ((Subgroup.equivMapOfInjective _ _ inj).symm ⟨_, u', hu, rfl⟩)) = 1
    rw [h1, ← map_one χ]
    exact congrArg χ (Subtype.ext hu')
variable (P : TypeDatum k a)
theorem exists_of_congr {g : GL a k} (hg : g ∈ P.J) {M : Matrix a a k} (h : MaxM (M - g.val)) :
    ∃ g' ∈ P.J, g'.val = M := by
  obtain ⟨u, hu, hu'⟩ := exists_mul_KOne (P.le_KO hg) h
  exact ⟨g * u, P.J.mul_mem hg (P.KOne_le hu), hu'⟩
def reindex (e : a ≃ b) : TypeDatum k b where
  toLevel := P.toLevel.map (reGL e)
  KOne_le := fun g hg => P.KOne_le (mem_KOne.2 fun i j => by
    simpa [reGL_symm_val, Matrix.one_apply] using mem_KOne.1 hg (e i) (e j))
  le_KO := fun g hg => by
    obtain ⟨h1, h2⟩ := mem_KO.1 (P.le_KO hg)
    exact mem_KO.2 ⟨fun i j => by simpa [reGL_symm_val] using h1 (e.symm i) (e.symm j),
      fun i j => by
        have := h2 (e.symm i) (e.symm j)
        rw [← map_inv] at this
        simpa [reGL_symm_val] using this⟩
  lam_eq_one := fun g hg => P.lam_eq_one ⟨(reGL e).symm g, g.2⟩ (mem_KOne.2 fun i j => by
    simpa [reGL_symm_val, Matrix.one_apply] using mem_KOne.1 hg (e i) (e j))
def rho (μ : kˣ →* ℂˣ) : P.J →* ℂˣ :=
  P.lam * (μ.comp (Matrix.GeneralLinearGroup.det.comp P.J.subtype))⁻¹
theorem rho_apply (μ : kˣ →* ℂˣ) (g : P.J) :
    P.rho μ g = P.lam g * (μ (Matrix.GeneralLinearGroup.det (g : GL a k)))⁻¹ := rfl
theorem rho_congr {μ : kˣ →* ℂˣ} (hμ : IsTame μ) {g g' : P.J} (h : MaxM ((g' : GL a k).val - (g : GL a k).val)) :
    P.rho μ g' = P.rho μ g := by
  have hu := inv_mul_mem_KOne (P.le_KO g.2) h
  have : P.rho μ (g⁻¹ * g') = 1 := by
    rw [rho_apply, P.lam_eq_one _ hu, show ((g⁻¹ * g' : P.J) : GL a k) = (g : GL a k)⁻¹ * g' from rfl,
      tame_det_of_mem_KOne hμ hu]; simp
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this.symm
variable (t) in

def stepJ : Subgroup (GL (a ⊕ t) k) where
  carrier := {h | h ∈ KO k (a ⊕ t) ∧ (∃ g ∈ P.J, g.val = h.val.toBlocks₁₁) ∧ IntM h.val.toBlocks₁₂ ∧
    MaxM h.val.toBlocks₂₁ ∧ ∃ D ∈ KO k t, D.val = h.val.toBlocks₂₂}
  one_mem' := ⟨one_mem _, ⟨1, one_mem _, by simp [← fromBlocks_one]⟩, by simpa [← fromBlocks_one] using intM_zero,
    by simpa [← fromBlocks_one] using maxM_zero, 1, one_mem _, by simp [← fromBlocks_one]⟩
  mul_mem' := by
    rintro h h' ⟨h0, ⟨g, hg, eg⟩, hB, hC, D, hD, eD⟩ ⟨h0', ⟨g', hg', eg'⟩, hB', hC', -⟩
    have hC'' : MaxM (h * h').val.toBlocks₂₁ := by
      rw [Units.val_mul, mul_toBlocks₂₁, ← eg', ← eD]
      exact (hC.mul_intM (intM_of_mem_KO (P.le_KO hg'))).add ((intM_of_mem_KO hD).mul_maxM hC')
    refine ⟨mul_mem h0 h0', P.exists_of_congr (P.J.mul_mem hg hg') ?_,
      fun i j => intM_of_mem_KO (mul_mem h0 h0') _ _, hC'', (exists_diag_blocks (mul_mem h0 h0') hC'').2⟩
    rw [Units.val_mul, mul_toBlocks₁₁, Units.val_mul, eg, eg']
    simpa using hB.mul_maxM hC'
  inv_mem' := by
    rintro h ⟨h0, ⟨g, hg, eg⟩, -, hC, -⟩
    obtain ⟨m1, -, m3⟩ := blocks_inv h0 hC
    refine ⟨inv_mem h0, P.exists_of_congr (P.J.inv_mem hg) ?_, fun i j => intM_of_mem_KO (inv_mem h0) _ _, m3,
      (exists_diag_blocks (inv_mem h0) m3).2⟩
    have := (mem_KO.1 (P.le_KO hg)).2.mul_maxM m1
    rwa [← eg, Matrix.mul_sub, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_one] at this
theorem mem_stepJ_iff {h : GL (a ⊕ t) k} : h ∈ P.stepJ t ↔
    h ∈ KO k (a ⊕ t) ∧ (∃ g ∈ P.J, g.val = h.val.toBlocks₁₁) ∧ MaxM h.val.toBlocks₂₁ :=
  ⟨fun H => ⟨H.1, H.2.1, H.2.2.2.1⟩, fun H => ⟨H.1, H.2.1, fun _ _ => intM_of_mem_KO H.1 _ _, H.2.2,
    (exists_diag_blocks H.1 H.2.2).2⟩⟩
def corner (h : P.stepJ t) : P.J := ⟨h.2.2.1.choose, h.2.2.1.choose_spec.1⟩
theorem corner_val (h : P.stepJ t) : (P.corner h : GL a k).val = (h : GL (a ⊕ t) k).val.toBlocks₁₁ :=
  h.2.2.1.choose_spec.2
theorem corner_mul (h h' : P.stepJ t) :
    MaxM ((P.corner (h * h') : GL a k).val - ((P.corner h * P.corner h' : P.J) : GL a k).val) := by
  rw [corner_val, Subgroup.coe_mul, Units.val_mul, mul_toBlocks₁₁, Subgroup.coe_mul, Units.val_mul, corner_val, corner_val]
  simpa using h.2.2.2.1.mul_maxM h'.2.2.2.2.1
variable (t) in

def stepLam (μ : kˣ →* ℂˣ) (hμ : IsTame μ) : P.stepJ t →* ℂˣ :=
  MonoidHom.mk' (fun h => P.lam (P.corner h) * (μ (Matrix.GeneralLinearGroup.det (P.corner h : GL a k)))⁻¹ *
      μ (Matrix.GeneralLinearGroup.det (h : GL (a ⊕ t) k))) fun h h' => by
    simp only [← rho_apply]
    rw [P.rho_congr hμ (P.corner_mul h h'), map_mul, Subgroup.coe_mul, map_mul, map_mul, mul_mul_mul_comm]
variable (t) in

def step (μ : kˣ →* ℂˣ) (hμ : IsTame μ) : TypeDatum k (a ⊕ t) where
  J := P.stepJ t
  lam := P.stepLam t μ hμ
  KOne_le := fun h hh => by
    have m := mem_KOne.1 hh
    refine P.mem_stepJ_iff.2 ⟨StepData.KOne_le_KO hh, P.exists_of_congr P.J.one_mem fun i j => ?_, fun i j => ?_⟩
    · simpa [Matrix.one_apply, toBlocks₁₁] using m (.inl i) (.inl j)
    · simpa [Matrix.one_apply, toBlocks₂₁] using m (.inr i) (.inl j)
  le_KO := fun _ hh => hh.1
  lam_eq_one := fun h hh => by
    have m := mem_KOne.1 hh
    have hc : (P.corner h : GL a k) ∈ KOne k a := mem_KOne.2 fun i j => by
      rw [corner_val]; simpa [Matrix.one_apply, toBlocks₁₁] using m (.inl i) (.inl j)
    change P.lam (P.corner h) * (μ (Matrix.GeneralLinearGroup.det (P.corner h : GL a k)))⁻¹ *
      μ (Matrix.GeneralLinearGroup.det (h : GL (a ⊕ t) k)) = 1
    rw [P.lam_eq_one _ hc, tame_det_of_mem_KOne hμ hc, tame_det_of_mem_KOne hμ hh]; simp
open Classical in
variable (t) in

def Phi (μ : kˣ →* ℂˣ) : Matrix (a ⊕ t) a k → ℂ := fun x =>
  if MaxM x.toRows₂ then extZ P.J (P.rho μ) x.toRows₁ else 0
omit [Fintype t] [DecidableEq t] in
theorem Phi_of_mem (μ : kˣ →* ℂˣ) {x : Matrix (a ⊕ t) a k} (g : P.J) (hg : (g : GL a k).val = x.toRows₁)
    (hx : MaxM x.toRows₂) :
    P.Phi t μ x = (P.lam g : ℂ) * ((μ (Matrix.GeneralLinearGroup.det (g : GL a k)))⁻¹ : ℂˣ) := by
  rw [Phi, if_pos hx, ← hg, extZ_coe, rho_apply, Units.val_mul]
omit [Fintype t] [DecidableEq t] in
theorem Phi_ne_zero_iff (μ : kˣ →* ℂˣ) {x : Matrix (a ⊕ t) a k} :
    P.Phi t μ x ≠ 0 ↔ (∃ g ∈ P.J, g.val = x.toRows₁) ∧ MaxM x.toRows₂ := by
  unfold Phi
  split_ifs with h <;> simp [h, extZ_ne_zero_iff]
end TypeDatum
section Iter
variable {r : Type*} [Fintype r] [DecidableEq r]
variable (t) in

def TypeDatum.iter (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) :
    TypeDatum k (Ix r t j) :=
  Nat.rec (motive := fun j => TypeDatum k (Ix r t j)) (P.reindex (ixZero r t))
    (fun j Q => (Q.step t (μ (j + 1)) (hμ _)).reindex (ixSucc r t j)) j
variable (t) in

def TypeDatum.iterPhi (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) :
    Matrix (Ix r t (j + 1)) (Ix r t j) k → ℂ := fun x =>
  (P.iter t μ hμ j).Phi t (μ (j + 1)) (x.submatrix (ixSucc r t j) id)
end Iter
section Parahoric
variable {r s s' : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
variable (r s) in

def parahoric (δ : kˣ →* ℂˣ) (hδ : IsTame δ) : TypeDatum k (r ⊕ s) := (TypeDatum.full k r).step s δ hδ
open Classical in

def parPhi (δ : kˣ →* ℂˣ) : Matrix (r ⊕ s) (r ⊕ s') k → ℂ := fun x =>
  if MaxM x.toBlocks₂₁ ∧ IntM x.toBlocks₁₂ ∧ IntM x.toBlocks₂₂ then
    extZ (KO k r) (δ.comp (Matrix.GeneralLinearGroup.det.comp (KO k r).subtype))⁻¹ x.toBlocks₁₁ else 0
end Parahoric
example (P : TypeDatum k a) (μ : kˣ →* ℂˣ) : P.Phi t μ (fromRows 1 0) = 1 := by
  rw [P.Phi_of_mem μ 1 (by simp) (by simpa using maxM_zero)]; simp
example [Nonempty a] (P : TypeDatum k a) (μ : kˣ →* ℂˣ) : P.Phi t μ 0 = 0 := by
  by_contra h
  obtain ⟨⟨g, -, e⟩, -⟩ := (P.Phi_ne_zero_iff μ).1 h
  exact g.ne_zero (e.trans (by ext; simp))
example (μ : kˣ →* ℂˣ) (u : GL a k) (hu : u ∈ KO k a) :
    (TypeDatum.full k a).Phi t μ (fromRows u.val 0) = ((μ (Matrix.GeneralLinearGroup.det u))⁻¹ : ℂˣ) := by
  rw [TypeDatum.Phi_of_mem _ μ ⟨u, hu⟩ (by simp) (by simpa using maxM_zero)]; exact one_mul _
end Local
section Frames
variable {k : Type*} [Field k]
variable {ι ι' Y Y' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
variable (k ι Y) in

structure LatFrame where

  ord : ι ≃ Y

  bas : GL Y k
namespace LatFrame
variable (k ι) in

def refl : LatFrame k ι ι := ⟨Equiv.refl ι, 1⟩
def conj (F : LatFrame k ι Y) : GL ι k ≃* GL Y k := (reGL F.ord).trans (MulAut.conj F.bas)
def coords (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') (x : Matrix Y Y' k) : Matrix ι ι' k :=
  ((F.bas⁻¹).val * x * F'.bas.val).submatrix F.ord F'.ord
def transport (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') (Φ : Matrix ι ι' k → ℂ) : Matrix Y Y' k → ℂ :=
  fun x => Φ (F.coords F' x)
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end LatFrame
variable [ValuativeRel k]
def latOf (g : GL Y k) : Submodule 𝒪[k] (Y → k) where
  carrier := {y | ∀ i, ((g⁻¹).val *ᵥ y) i ∈ 𝒪[k]}
  add_mem' := fun hy hz i => by rw [mulVec_add]; exact add_mem (hy i) (hz i)
  zero_mem' := fun i => by simp
  smul_mem' := fun c y hy i => by
    rw [show c • y = (c : k) • y from rfl, mulVec_smul]; exact mul_mem c.2 (hy i)
def box (n : Type*) (c : kˣ) : Submodule 𝒪[k] (n → k) where
  carrier := {y | ∀ i, valuation k (y i) ≤ valuation k (c : k)}
  add_mem' := fun hy hz i => Valuation.map_add_le _ (hy i) (hz i)
  zero_mem' := fun i => by simp
  smul_mem' := fun x y hy i => by
    rw [show (x • y) i = (x : k) * y i from rfl, map_mul]
    exact mul_le_of_le_one_of_le x.2 (hy i)
theorem mem_box {n : Type*} {c : kˣ} {y : n → k} : y ∈ box n c ↔ ∀ i, valuation k (y i) ≤ valuation k (c : k) :=
  Iff.rfl
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def stabLat (g : GL Y k) : Subgroup (GL Y k) := (KO k Y).comap (MulAut.conj g⁻¹).toMonoidHom
end Frames
section StdFrames
variable {k : Type*} [Field k] {ι n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
def typeFrame (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) : LatFrame k ι (n ⊕ Fin c) :=
  ⟨ord, embA n (SplitFlip.diagGL fun i => ϖ ^ (i.val + 1))⟩
def plainFrame (ord : ι ≃ n ⊕ Fin c) : LatFrame k ι (n ⊕ Fin c) := ⟨ord, 1⟩
def normalBasis (ϖ : kˣ) (e : Fin c → ℤ) (z : n → k) : GL (n ⊕ Fin c) k :=
  colE c 1 z * embA n (SplitFlip.diagGL fun i => ϖ ^ e i)
end StdFrames
abbrev XIx (κ t : Type*) (j : ℕ) : Type _ := (κ ⊕ Fin j) ⊕ (Fin j × t)
def stdOrd (κ t : Type*) {l : ℕ} (j c : ℕ) (h : j + c = l) : Ix (κ ⊕ Fin l) t j ≃ XIx κ t j ⊕ Fin c :=
  ((((Equiv.refl κ).sumCongr ((finCongr (by omega : l = c + j)).trans
      (finSumFinEquiv.symm.trans (Equiv.sumComm _ _)))).trans (Equiv.sumAssoc _ _ _).symm).sumCongr
    (Equiv.refl _)).trans
  ((Equiv.sumAssoc _ _ _).trans (((Equiv.refl _).sumCongr (Equiv.sumComm _ _)).trans (Equiv.sumAssoc _ _ _).symm))
section Groups
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
def Cgrp (J : Subgroup (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k) : Subgroup (GL (n ⊕ Fin c) k) :=
  R k n c 1 ⊓ J.comap (MulAut.conj h⁻¹).toMonoidHom
def prX (C : Subgroup (GL (n ⊕ Fin c) k)) : Subgroup (GL n k) where
  carrier := {g | ∃ u ∈ N k n c 1, u * embX c g ∈ C}
  one_mem' := ⟨1, one_mem _, by simp⟩
  mul_mem' := by
    rintro g g' ⟨u, hu, h⟩ ⟨u', hu', h'⟩
    refine ⟨u * ((embX c g⁻¹)⁻¹ * u' * embX c g⁻¹), mul_mem hu (RootEx.Model.conj_mem hu' g⁻¹), ?_⟩
    convert C.mul_mem h h' using 1
    simp [mul_assoc]
  inv_mem' := by
    rintro g ⟨u, hu, h⟩
    refine ⟨(embX c g)⁻¹ * u⁻¹ * embX c g, RootEx.Model.conj_mem (inv_mem hu) g, ?_⟩
    convert C.inv_mem h using 1
    simp [mul_assoc]
def IsColChar (ψ : AddChar k Circle) (P : Level (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k)
    (χ : prX (Cgrp P.J h) →* ℂˣ) : Prop :=
  ∀ (g : prX (Cgrp P.J h)), ∀ u ∈ N k n c 1, ∀ hm : h⁻¹ * (u * embX c (g : GL n k)) * h ∈ P.J,
    (χ g : ℂ) = (ψ (simpleSum u) : ℂ) * ((P.lam ⟨_, hm⟩)⁻¹ : ℂˣ)
end Groups
section Unfold
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ)
  (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
def flat (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k) : Matrix n n' k → ℂ := opE ψ ν 1 (om μ h' h Φ)
def idxAt (J : Subgroup (GL (n ⊕ Fin c) k)) (h' : GL (n' ⊕ Fin (c + 1)) k) :
    Set (DoubleCoset.Quotient (R k n c 1 : Set (GL (n ⊕ Fin c) k)) J) :=
  {β | ∃ h, DoubleCoset.mk (R k n c 1) J h = β ∧ flat ψ ν μ Φ h' h ≠ 0}
def volNat (b : GL (n ⊕ Fin c) k) (S : Subgroup (GL (n ⊕ Fin c) k)) : ℝ :=
  (volN ν n c 1 (S.subgroupOf (N k n c 1))).toReal / (volN ν n c 1 ((stabLat b).subgroupOf (N k n c 1))).toReal
def xi (J : Subgroup (GL (n ⊕ Fin c) k)) (b : GL (n ⊕ Fin c) k) (h' : GL (n' ⊕ Fin (c + 1)) k)
    (h : GL (n ⊕ Fin c) k) : Matrix n n' k → ℂ := fun x₀ =>
  (((volNat ν b (Cgrp J h))⁻¹ : ℝ) : ℂ) * flat ψ ν μ Φ h' h x₀
end Unfold
section Couple
variable {k : Type*} [Field k] {n n' : Type*}
def withCol (x₀ : Matrix n n' k) (y : n → k) : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k :=
  fromBlocks x₀ (Matrix.of fun r _ => y r) 0 0
variable [ValuativeRel k]
def cosetInd (M : Submodule 𝒪[k] (n → k)) (yb : (n → k) ⧸ M) : (n → k) → ℂ :=
  Set.indicator {y | Submodule.Quotient.mk y = yb} fun _ => 1
variable [Fintype n] [MeasurableSpace k] (ψ : AddChar k Circle) (ν : Measure k) (ε : k)
omit [ValuativeRel k] in

def hat (f : (n → k) → ℂ) (η : n → k) : ℂ := ∫ y, f y * (ψ (ε * (η ⬝ᵥ y)) : ℂ) ∂(Measure.pi fun _ => ν)
omit [ValuativeRel k] in

def hatCol (Ψ : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ) (x₀ : Matrix n n' k) (η : n → k) : ℂ :=
  hat ψ ν ε (fun y => Ψ (withCol x₀ y)) η
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k] [BorelSpace k]
example (hν : IsUnitVol ν) : hat ψ ν ε (cosetInd (box n 1) 0) 0 = 1 := by
  have := hν.1
  have := secondCountable k
  have e : {y : n → k | Submodule.Quotient.mk (p := box n 1) y = 0} = Set.pi Set.univ fun _ => (𝒪[k] : Set k) := by
    ext y; simp [mem_box, Valuation.mem_integer_iff]
  simp only [hat, cosetInd, e, zero_dotProduct, mul_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
  rw [integral_indicator_const _ (MeasurableSet.univ_pi fun _ => (isOpen_int k).measurableSet), Measure.real,
    Measure.pi_pi]
  simp [hν.2]
end Couple
section Chains
structure Chain (k : Type*) [Field k] (s : ℕ) (X : ℕ → Type*) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (Z : Type*) [Fintype Z] [DecidableEq Z] where

  lev : ∀ j c, j + c = s + 1 → Level (GL (X j ⊕ Fin c) k)

  bas : ∀ j c, j + c = s + 1 → GL (X j ⊕ Fin c) k

  levTop : Level (GL Z k)

  mu : ℕ → kˣ →* ℂˣ

  Phi : ∀ j c, j + c = s → Matrix (X (j + 1) ⊕ Fin c) (X j ⊕ Fin (c + 1)) k → ℂ

  PhiTop : Matrix Z (X (s + 1) ⊕ Fin 0) k → ℂ
abbrev RepFam (k : Type*) [Field k] (s : ℕ) (X : ℕ → Type*) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] :=
  ∀ j c, j + c = s → Set (GL (X j ⊕ Fin (c + 1)) k)
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s : ℕ} {X : ℕ → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type*} [Fintype Z] [DecidableEq Z]
def HasTypes {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (P' : Level (GL a k)) (P : Level (GL b k)) (Φ : Matrix b a k → ℂ) : Prop :=
  (∀ g : P'.J, om μ (g : GL a k) 1 Φ = (P'.lam g : ℂ) • Φ) ∧
    ∀ h : P.J, om μ 1 (h : GL b k) Φ = (((P.lam h)⁻¹ : ℂˣ) : ℂ) • Φ
namespace Chain
variable (T : Chain k s X Z)
def Laws : Prop :=
  (∀ j c (h : j + c = s), HasTypes (T.mu (j + 1)) (T.lev j (c + 1) (by omega)) (T.lev (j + 1) c (by omega))
    (T.Phi j c h)) ∧ HasTypes (T.mu (s + 2)) (T.lev (s + 1) 0 rfl) T.levTop T.PhiTop
def Regular : Prop :=
  (∀ j c h, T.Phi j c h ∈ SB _) ∧ T.PhiTop ∈ SB _ ∧
    ∀ j c h, IsOpen ((T.lev j c h).J : Set (GL (X j ⊕ Fin c) k)) ∧
      IsCompact ((T.lev j c h).J : Set (GL (X j ⊕ Fin c) k)) ∧ (T.lev j c h).J ≤ stabLat (T.bas j c h)
def Psi (h : GL (X s ⊕ Fin (0 + 1)) k) (x₀ : Matrix (X (s + 1)) (X s) k) (y : X (s + 1) → k) : ℂ :=
  om (T.mu (s + 1)) h 1 (T.Phi s 0 rfl) (withCol x₀ y)
variable (A : RepFam k s X)
def RepsInStab : Prop := ∀ j c h, ∀ g ∈ A j c h, g ∈ stabLat (T.bas j (c + 1) (by omega))
def RepsMeet : Prop := ∀ j c h, ∀ g ∈ A j c h, ∀ y : X j → k,
  Sum.elim y 0 ∈ latOf (g * T.bas j (c + 1) (by omega)) ↔ ∀ i, y i ∈ 𝒪[k]
def RepsNormal (ϖ : kˣ) : Prop := ∀ j c h, ∀ g ∈ A j c h, ∃ (e : Fin (c + 1) → ℤ) (z : X j → k),
  (∀ i, -(j : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (∀ i, z i ∈ 𝒪[k]) ∧
    latOf (g * T.bas j (c + 1) (by omega)) = latOf (normalBasis ϖ e z)
def RepsOne : Prop := ∀ j c h, ∀ g ∈ A j c h,
  DoubleCoset.mk (R k (X j) (c + 1) 1) (T.lev j (c + 1) (by omega)).J g =
    DoubleCoset.mk (R k (X j) (c + 1) 1) (T.lev j (c + 1) (by omega)).J 1 → g = 1
variable (S M : Submodule 𝒪[k] (X (s + 1) → k))
def Adapted : Prop := ∀ g ∈ A s 0 rfl, ∀ x₀ y,
  (T.Psi g x₀ y ≠ 0 → y ∈ S) ∧ ∀ z ∈ M, T.Psi g x₀ (y + z) = T.Psi g x₀ y
def coupIdx : Set ((X (s + 1) → k) ⧸ M) :=
  {yb | ∃ y ∈ S, Submodule.Quotient.mk y = yb ∧ ∃ g ∈ A s 0 rfl, ∃ x₀, T.Psi g x₀ y ≠ 0}
def xiPen (h : GL (X s ⊕ Fin (0 + 1)) k) (yb : (X (s + 1) → k) ⧸ M) : Matrix (X (s + 1)) (X s) k → ℂ :=
  fun x₀ => T.Psi h x₀ (Quotient.out yb)
variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)
def xiTop (ε : k) (yb : (X (s + 1) → k) ⧸ M) : Matrix (Z ⊕ Unit) (X (s + 1)) k → ℂ := fun x =>
  T.PhiTop (fromCols x.toRows₁ 0) * hat ψ ν ε (cosetInd M yb) (x (Sum.inr ()))
def idx (j c : ℕ) (h : j + 1 + c = s) (g : GL (X j ⊕ Fin (c + 1 + 1)) k) :
    Set (DoubleCoset.Quotient (R k (X (j + 1)) (c + 1) 1 : Set (GL (X (j + 1) ⊕ Fin (c + 1)) k))
      (T.lev (j + 1) (c + 1) (by omega)).J) :=
  idxAt ψ ν (T.mu (j + 1)) (T.Phi j (c + 1) (by omega)) (T.lev (j + 1) (c + 1) (by omega)).J g
def entry (j c : ℕ) (h : j + 1 + c = s) (g : GL (X j ⊕ Fin (c + 1 + 1)) k) (g' : GL (X (j + 1) ⊕ Fin (c + 1)) k) :
    Matrix (X (j + 1)) (X j) k → ℂ :=
  xi ψ ν (T.mu (j + 1)) (T.Phi j (c + 1) (by omega)) (T.lev (j + 1) (c + 1) (by omega)).J
    (T.bas (j + 1) (c + 1) (by omega)) g g'
structure IsRepSystem : Prop where
  zero : ∀ c h, A 0 c h = {1}
  bij : ∀ j c (h : j + 1 + c = s),
    Set.BijOn (DoubleCoset.mk (R k (X (j + 1)) (c + 1) 1) (T.lev (j + 1) (c + 1) (by omega)).J) (A (j + 1) c h)
      (⋃ g ∈ A j (c + 1) (by omega), T.idx ψ ν j c h g)
def someReps : RepFam k s X := fun j =>
  Nat.rec (motive := fun j => ∀ c, j + c = s → Set (GL (X j ⊕ Fin (c + 1)) k)) (fun _ _ => {1})
    (fun j B c h => Quotient.out '' ⋃ g ∈ B (c + 1) (by omega), T.idx ψ ν j c h g) j
end Chain
variable {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]
def Chain.ofType (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (F : ∀ j c, j + c = s + 1 → LatFrame k (Ix r t j) (X j ⊕ Fin c)) (Ftop : LatFrame k (Ix r t (s + 2)) Z) :
    Chain k s X Z where
  lev j c h := (P.iter t μ hμ j).toLevel.map (F j c h).conj
  bas j c h := (F j c h).bas
  levTop := (P.iter t μ hμ (s + 2)).toLevel.map Ftop.conj
  mu := μ
  Phi j c h := (F (j + 1) c (by omega)).transport (F j (c + 1) (by omega)) (P.iterPhi t μ hμ j)
  PhiTop := Ftop.transport (F (s + 1) 0 rfl) (P.iterPhi t μ hμ (s + 1))
def Chain.ofTwist (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (ν : ℕ → kˣ →* ℂˣ)
    (F : ∀ j c, j + c = s + 1 → LatFrame k (Ix r t j) (X j ⊕ Fin c)) (Ftop : LatFrame k (Ix r t (s + 2)) Z) :
    Chain k s X Z where
  lev j c h := (parahoric r (Fin j × t) δ hδ).toLevel.map (F j c h).conj
  bas j c h := (F j c h).bas
  levTop := (parahoric r (Fin (s + 2) × t) δ hδ).toLevel.map Ftop.conj
  mu j := ν j * δ
  Phi j c h := (F (j + 1) c (by omega)).transport (F j (c + 1) (by omega)) (parPhi δ)
  PhiTop := Ftop.transport (F (s + 1) 0 rfl) (parPhi δ)
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable (t) in

def typeChain (ϖ : kˣ) (P : TypeDatum k (κ ⊕ Fin (s + 1))) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) :
    Chain k s (XIx κ t) (Ix (κ ⊕ Fin (s + 1)) t (s + 2)) :=
  Chain.ofType P μ hμ (fun j c h => typeFrame ϖ (stdOrd κ t j c h)) (LatFrame.refl k _)
variable (κ t s) in

def twistChain (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (ν : ℕ → kˣ →* ℂˣ) :
    Chain k s (XIx κ t) (Ix (κ ⊕ Fin (s + 1)) t (s + 2)) :=
  Chain.ofTwist δ hδ ν (fun j c h => plainFrame (stdOrd κ t j c h)) (LatFrame.refl k _)
end Chains
section Laws
variable {k : Type*} [Field k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace TypeDatum
variable (P : TypeDatum k a) {μ : kˣ →* ℂˣ}
end TypeDatum
section
variable {r s s' : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s] [Fintype s'] [DecidableEq s']
  {δ : kˣ →* ℂˣ}
end
variable {s : ℕ} {X : ℕ → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type*} [Fintype Z] [DecidableEq Z]
  {r : Type*} [Fintype r] [DecidableEq r]
end Laws
section Nonempty
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
end Nonempty
end GlobalTheory.StepData


