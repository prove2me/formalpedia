-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_TannerFamily
-- name    : QEC_Coding_ExpanderCodes_TannerFamily
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:18:17.897706+00:00
-- url     : https://prove2.me/theorems/d018a651-d1e0-4641-8aea-6581e1c8f235
-- title:
--   Tanner Family
-- statement:
--   Definitions and structural lemmas for Tanner Family, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerFamily.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerPairExistence
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
import Theorems.Thm_QEC_Coding_LiftedProduct_card_qubitIndex
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_qubitIndex

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
universe u
variable {A F W R R' : Type u} {G : A → Type u}
variable [Field F] [Fintype F]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
variable [∀ a, Group (G a)] [∀ a, Fintype (G a)]
variable [∀ a, DecidableEq (G a)]
abbrev FamilyQubitIndex (a : A) :=
  LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') (G a)
abbrev FamilyCheckIndex (a : A) :=
  QEC.Coding.FiniteFieldCSSPresentation.CheckIndex F
    (LiftedProduct.C0Index (Fin 2 × R) W (G a))
    (LiftedProduct.C2Index W (Fin 2 × R') (G a))
noncomputable local instance _p2m_local_instance_4063ed27f1_34 : DecidableEq F := Classical.decEq F
noncomputable local instance _p2m_local_instance_4063ed27f1_35 (a : A) : DecidableEq
    (FamilyQubitIndex (W := W) (R := R) (R' := R') (G := G) a) :=
  Classical.decEq _
def canonicalRadius (a : A) : Nat :=
  Fintype.card (G a) / Fintype.card W
noncomputable def canonicalRelativeDistance : ℝ :=
  1 /
    (2 * (Fintype.card W : ℝ) ^ 2 *
      ((Fintype.card W : ℝ) ^ 2 +
        4 * Fintype.card R * Fintype.card R'))
noncomputable def semanticFamily
    (label : ∀ a, W → G a) (h : Matrix R W F) (h' : Matrix R' W F)
    (hW : 0 < Fintype.card W)
    (hGroupCofinal : ∀ N : Nat, ∃ a : A, N ≤ Fintype.card (G a)) :
    QEC.QLDPC.QuantumCodeFamily A
      (fun a => FamilyQubitIndex
        (W := W) (R := R) (R' := R') (G := G) a)
      (fun a => FamilyCheckIndex
        (F := F) (W := W) (R := R) (R' := R') (G := G) a) where
  presentation a := semanticPresentation (label a) h h'
  cofinal_blockLength N := by
    obtain ⟨a, ha⟩ := hGroupCofinal N
    refine ⟨a, ha.trans ?_⟩
    change Fintype.card (G a) ≤ Fintype.card
      (FamilyQubitIndex (W := W) (R := R) (R' := R') (G := G) a)
    rw [card_qubitIndex]
    apply Nat.le_mul_of_pos_right
    exact Nat.add_pos_left (Nat.mul_pos hW hW) _
end QEC.Coding.TannerLiftedProduct


