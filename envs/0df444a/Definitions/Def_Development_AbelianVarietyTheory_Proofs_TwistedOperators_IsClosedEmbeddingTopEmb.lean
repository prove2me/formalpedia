-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingTopEmb
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingTopEmb
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T23:23:05.897785+00:00
-- url     : https://prove2.me/theorems/34c696e0-2da8-4105-b02c-774db6ecc7f4
-- title:
--   Is Closed Embedding Top Emb
-- statement:
--   Definitions and structural lemmas for Is Closed Embedding Top Emb, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClosedEmbeddingTopEmb.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatSweepSmoothlyInducedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGLMulRightColumnsEqZeroOfRankStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftColumnsMulVecInjectiveOfRankEqCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RankFiltrationExists
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_JacquetFiniteLength_two
import Theorems.Thm_GlobalTheory_SmGL_leviEmb_mem_parabLower
import Theorems.Thm_GlobalTheory_SmGL_mem_parabLower_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences Matrix Topology
open scoped TensorProduct
namespace GlobalTheory.RankStrataProof
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
section Lower
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]
open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype b] [DecidableEq a]
  [DecidableEq b] [DecidableEq c] [DecidableEq d] in

theorem _root_.GlobalTheory.RankStrataProof.mul_apply_of_cols {n : Type} (e : c ⊕ d ≃ a) {x : Matrix b a k} (hx : ∀ i j, x i (e (.inr j)) = 0)
    (g : Matrix a n k) (i : b) (l : n) : (x * g) i l = ∑ m, x i (e (.inl m)) * g (e (.inl m)) l := by
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_sum_type]
  simp [hx]
def rAct (s : Set ℕ) (x : RankIn k a b s) (g : GL a k) : RankIn k a b s :=
  ⟨act x.1 (g, 1), by rw [rank_act]; exact x.2⟩
open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.rAct_val (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g : GL a k) : (_root_.GlobalTheory.RankStrataProof.rAct s x g).1 = x.1 * g.val := by
  unfold _root_.GlobalTheory.RankStrataProof.rAct _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.act
  simp
open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.rAct_one (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) : _root_.GlobalTheory.RankStrataProof.rAct s x 1 = x := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.rAct_val]
  simp
open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.rAct_mul (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g h : GL a k) :
    _root_.GlobalTheory.RankStrataProof.rAct s x (g * h) = _root_.GlobalTheory.RankStrataProof.rAct s (_root_.GlobalTheory.RankStrataProof.rAct s x g) h := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.rAct_val, _root_.GlobalTheory.RankStrataProof.rAct_val, _root_.GlobalTheory.RankStrataProof.rAct_val, Units.val_mul, Matrix.mul_assoc]
theorem continuous_rAct (s : Set ℕ) : Continuous fun p : RankIn k a b s × GL a k => rAct s p.1 p.2 := by
  refine Continuous.subtype_mk (f := fun p : RankIn k a b s × GL a k => act p.1.1 (p.2, 1)) ?_ _
  exact (continuous_const.matrix_mul (continuous_subtype_val.comp continuous_fst)).matrix_mul
    (Units.continuous_val.comp continuous_snd)
variable (k b) in

abbrev ColZero (e : c ⊕ d ≃ a) (s : Set ℕ) : Type :=
  {x : RankIn k a b s // ∀ i j, x.1 i (e (.inr j)) = 0}
def pAct (e : c ⊕ d ≃ a) (s : Set ℕ) (y : ColZero k b e s) (p : parabLower k (two e)) : ColZero k b e s :=
  ⟨rAct s y.1 p, fun i j => by
    rw [rAct_val, mul_apply_of_cols e y.2]
    simp [(mem_parabLower_two k).1 p.2]⟩
def fstBlock (e : c ⊕ d ≃ a) : GL c k →* parabLower k (two e) :=
  ((emb₂ k e).codRestrict _ fun _ => leviEmb_mem_parabLower k _ _).comp (MonoidHom.inl _ _)
variable (b) in

def colRep (e : c ⊕ d ≃ a) (s : Set ℕ) (ν : kˣ →* ℂˣ) :
    Representation ℂ (GL c k) (SB (ColZero k b e s)) :=
  twist (sbRep (fun y g => pAct e s y (fstBlock e g))
    (fun y => Subtype.ext (by rw [map_one]; exact rAct_one s y.1))
    (fun y g h => Subtype.ext (by rw [map_mul]; exact rAct_mul s y.1 _ _))
    (fun g => ((continuous_rAct s).comp (continuous_subtype_val.prodMk continuous_const)).subtype_mk _))
    (detChar c ν)
end Lower
section Open
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
theorem isLocallyConstant_char {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ψ : G →* ℂˣ} (h : IsSmoothChar ψ) : IsLocallyConstant fun y => (ψ y : ℂ) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (ψ.ker : Set G)) := IsOpen.preimage (by fun_prop) h
  filter_upwards [this.mem_nhds (show x ∈ _ by simp)] with y hy
  have hy' : ψ (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at hy'
  rw [hy']
def divChar {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ψ : G →* ℂˣ} (h : IsSmoothChar ψ) : SB G ≃ₗ[ℂ] SB G where
  toFun w := ⟨fun y => (ψ⁻¹ y : ℂ) * w.1 y, (isLocallyConstant_char h.inv).mul w.2.1, w.2.2.mul_left⟩
  invFun w := ⟨fun y => (ψ y : ℂ) * w.1 y, (isLocallyConstant_char h).mul w.2.1, w.2.2.mul_left⟩
  map_add' _ _ := Subtype.ext (funext fun _ => mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => mul_left_comm _ _ _)
  left_inv w := Subtype.ext (funext fun y => by simp)
  right_inv w := Subtype.ext (funext fun y => by simp)
def topM (e : a ⊕ c ≃ b) (y : Matrix a a k) : Matrix b a k := (fromRows y 0).submatrix e.symm id
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype c] [DecidableEq a]
  [DecidableEq b] [DecidableEq c] [Fintype a] [Fintype b] in
@[simp] theorem topM_inl (e : a ⊕ c ≃ b) (y : Matrix a a k) (i l : a) : topM e y (e (.inl i)) l = y i l := by
  simp [topM]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype c] [DecidableEq a]
  [DecidableEq b] [DecidableEq c] [Fintype a] [Fintype b] in
@[simp] theorem topM_inr (e : a ⊕ c ≃ b) (y : Matrix a a k) (i : c) (l : a) :
    topM e y (e (.inr i)) l = 0 := by
  simp [topM]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq b] [DecidableEq c] in
theorem rank_topM (e : a ⊕ c ≃ b) (y : GL a k) : (topM e y.val).rank = Fintype.card a := by
  refine le_antisymm (rank_le_card_width _) ?_
  have h : (topM e y.val).submatrix (fun i => e (.inl i)) (Equiv.refl a) = y.val := by
    ext i l; simp
  have h2 := rank_submatrix_le (topM e y.val) (fun i => e (.inl i)) (Equiv.refl a)
  rwa [h, rank_of_isUnit _ y.isUnit] at h2
def topEmb (e : a ⊕ c ≃ b) {κ : ℕ} (hκ : κ = Fintype.card a) (y : GL a k) : RankIn k a b {κ} :=
  ⟨topM e y.val, (rank_topM e y).trans hκ.symm⟩
def lAct (s : Set ℕ) (x : RankIn k a b s) (h : GL b k) : RankIn k a b s :=
  ⟨act x.1 (1, h), by rw [rank_act]; exact x.2⟩
end Open
end GlobalTheory.RankStrataProof


