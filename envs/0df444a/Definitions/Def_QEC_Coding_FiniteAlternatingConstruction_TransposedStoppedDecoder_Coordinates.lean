-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
-- name    : QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T05:56:17.145538+00:00
-- url     : https://prove2.me/theorems/3f77be2f-7ab7-4678-801b-b1b58e65673c
-- title:
--   Coordinates
-- statement:
--   Definitions and structural lemmas for Coordinates, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement hiding Two
open BDL26RZLocalReplacement hiding Two
open BDL26RZMap1CoordinateBridge hiding Two
open BDL26RXDecoderAdapter
open MultiscaleDecoder (BDL26Field)
open scoped Classical BigOperators
def rxDualX (P : TannerSquarePresentation) (S : OddScale) :
    RX2 P S ≃ RZX (transposePresentation P) S := Equiv.refl _
def rxDualQ (P : TannerSquarePresentation) (S : OddScale) :
    RX1 P S ≃ RZQ (transposePresentation P) S := Equiv.refl _
def rxDualZ (P : TannerSquarePresentation) (S : OddScale) :
    RX0 P S ≃ RZZ (transposePresentation P) S := Equiv.refl _
def rxDualFace (P : TannerSquarePresentation) (S : OddScale) :
    RXFace P S ≃ RZFace (transposePresentation P) S where
  toFun
    | .inl ⟨x,f,b⟩ => .inl ⟨x,f,b⟩
    | .inr (.inl ⟨a,e,b⟩) =>
        .inr (.inl ⟨(transposeQZEdgeEquiv P).symm a,e,b⟩)
    | .inr (.inr ⟨f,b⟩) => .inr (.inr ⟨f,b⟩)
  invFun
    | .inl ⟨x,f,b⟩ => .inl ⟨x,f,b⟩
    | .inr (.inl ⟨a,e,b⟩) =>
        .inr (.inl ⟨transposeQZEdgeEquiv P a,e,b⟩)
    | .inr (.inr ⟨f,b⟩) => .inr (.inr ⟨f,b⟩)
  left_inv := by
    rintro (⟨x,f,b⟩ | (⟨a,e,b⟩ | ⟨f,b⟩)) <;> rfl
  right_inv := by
    rintro (⟨x,f,b⟩ | (⟨a,e,b⟩ | ⟨f,b⟩)) <;> rfl
def rzDualX (P : TannerSquarePresentation) (S : OddScale) :
    RZZ P S ≃ RX0 (transposePresentation P) S := Equiv.refl _
def rzDualQ (P : TannerSquarePresentation) (S : OddScale) :
    RZQ P S ≃ RX1 (transposePresentation P) S := Equiv.refl _
def rzDualZ (P : TannerSquarePresentation) (S : OddScale) :
    RZX P S ≃ RX2 (transposePresentation P) S := Equiv.refl _
def rzDualFace (P : TannerSquarePresentation) (S : OddScale) :
    RZFace P S ≃ RXFace (transposePresentation P) S where
  toFun
    | .inl ⟨z,f,b⟩ => .inl ⟨z,f,b⟩
    | .inr (.inl ⟨a,e,b⟩) =>
        .inr (.inl ⟨(transposeXQEdgeEquiv P).symm a,e,b⟩)
    | .inr (.inr ⟨f,b⟩) => .inr (.inr ⟨f,b⟩)
  invFun
    | .inl ⟨z,f,b⟩ => .inl ⟨z,f,b⟩
    | .inr (.inl ⟨a,e,b⟩) =>
        .inr (.inl ⟨transposeXQEdgeEquiv P a,e,b⟩)
    | .inr (.inr ⟨f,b⟩) => .inr (.inr ⟨f,b⟩)
  left_inv := by
    rintro (⟨z,f,b⟩ | (⟨a,e,b⟩ | ⟨f,b⟩)) <;> rfl
  right_inv := by
    rintro (⟨z,f,b⟩ | (⟨a,e,b⟩ | ⟨f,b⟩)) <;> rfl
end QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates


