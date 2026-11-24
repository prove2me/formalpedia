-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationMaximalQuotient
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationMaximalQuotient
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T12:16:36.137393+00:00
-- url     : https://prove2.me/theorems/73991c56-0715-4ada-b6bc-ec441c4d1dd3
-- title:
--   Filtration Maximal Quotient
-- statement:
--   Definitions and structural lemmas for Filtration Maximal Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationMaximalQuotient.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_mem_canT
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_vecF_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Module
namespace Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
lemma qb_std_can (mu : Fin n → ℤ) : StdT (canT mu) := by
  intro c hc t
  apply card_le_card
  apply filter_subset_filter
  intro b hb
  rw [qb_mem_canT] at hb ⊢
  refine lt_of_lt_of_le hb ?_
  unfold colH
  refine card_le_card fun m hm => ?_
  simp only [mem_filter, mem_univ, true_and] at hm ⊢
  omega
def standardBasis (hS : SBasis) (mu : Fin n → ℤ) (hmu : Dominant mu) : Basis {I : TIdx mu // StdT I} ℤ ↥(SMu mu) :=
  (Basis.span (hS n mu hmu).1).map (LinearEquiv.ofEq _ _ (hS n mu hmu).2)
def qb_bS (hS : SBasis) {nu mu : Fin n → ℤ} (hnu : Dominant nu) (h : nu = mu) :
    Basis {I : TIdx nu // StdT I} ℤ ↥(SMu mu) := h ▸ standardBasis hS nu hnu
def qb_canIdx {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) (j : {j : CF.J // CF.mu j = mu}) : qb_Idx CF :=
  ⟨j.1, canT _, qb_std_can _⟩
lemma qb_canIdx_inj {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) : Function.Injective (qb_canIdx CF mu) :=
  fun j j' h => Subtype.ext (congrArg Sigma.fst h)
lemma qb_can_li (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) :
    LinearIndependent ℤ (fun j : {j : CF.J // CF.mu j = mu} => CF.vec j.1 (canT (CF.mu j.1))) := by
  have h := (qb_basisR hA CF ℤ).1
  rw [qb_vecF_int] at h
  exact h.comp (qb_canIdx CF mu) (qb_canIdx_inj CF mu)
lemma qb_can_span {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) :
    Submodule.span ℤ (Set.range fun j : {j : CF.J // CF.mu j = mu} => CF.vec j.1 (canT (CF.mu j.1))) = CF.MM mu := by
  unfold ColFam.MM
  congr 1
  ext x
  constructor
  · rintro ⟨⟨j, hj⟩, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, hj⟩, rfl⟩
def qb_bM (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) :
    Basis {j : CF.J // CF.mu j = mu} ℤ ↥(CF.MM mu) :=
  (Basis.span (qb_can_li hA CF mu)).map (LinearEquiv.ofEq _ _ (qb_can_span CF mu))
section abs
variable {R : Type*} [CommRing R] {V A B W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup W] [Module R W] {ι κ : Type*} [DecidableEq κ] {φ : κ → Type*}
def qb_aT (bA : ∀ k, Basis (φ k) R A) (bB : Basis κ R B) : Basis (Σ k, φ k) R (TensorProduct R A B) :=
  (Finsupp.basis bA).map (TensorProduct.equivFinsuppOfBasisRight bB).symm
def qb_aPsi (b : Basis ι R V) (s : Set ι) (c : Basis ↥s R W) : V →ₗ[R] W :=
  c.repr.symm.toLinearMap ∘ₗ Finsupp.lsubtypeDomain s ∘ₗ b.repr.toLinearMap
end abs
def qb_sMu {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) : Set (qb_Idx CF) := {y | CF.mu y.1 = mu}
def qb_eqS {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) :
    (Σ j : {j : CF.J // CF.mu j = mu}, {I : TIdx (CF.mu j.1) // StdT I}) ≃ ↥(qb_sMu CF mu) where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
  left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
end Formalism.InvariantFactorPaths.ColumnFamilies


