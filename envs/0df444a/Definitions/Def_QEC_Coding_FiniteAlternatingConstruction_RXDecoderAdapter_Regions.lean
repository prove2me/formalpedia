-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T01:51:40.726363+00:00
-- url     : https://prove2.me/theorems/f43db951-59b3-4243-a932-8267edf5cf06
-- title:
--   Regions
-- statement:
--   Definitions and structural lemmas for Regions, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Regions.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightCertificates
set_option autoImplicit false
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26DecodingGraph MultiscaleDecoder
open scoped Classical
noncomputable def localX (P : TannerSquarePresentation) (S : OddScale) :
    LocalComplexData P.X (RX2 P S) (RX1 P S) where
  syndromeRegion x := fiberRegion (rxSyndromeOwner P S) (.x x)
  correctionRegion x := fiberRegion (rxCorrectionOwner P S) (.x x)
noncomputable def localQ (P : TannerSquarePresentation) (S : OddScale) :
    LocalComplexData P.Q (RX2 P S) (RX1 P S) where
  syndromeRegion q := fiberRegion (rxSyndromeOwner P S) (.q q)
  correctionRegion q := fiberRegion (rxCorrectionOwner P S) (.q q)
noncomputable def localZ (P : TannerSquarePresentation) (S : OddScale) :
    LocalComplexData P.Z (RX2 P S) (RX1 P S) where
  syndromeRegion z := fiberRegion (rxSyndromeOwner P S) (.z z)
  correctionRegion z := fiberRegion (rxCorrectionOwner P S) (.z z)
noncomputable def fibreEquiv {A B L : Type} [Fintype B] [DecidableEq B]
    [DecidableEq L] (owner : B → L) (label : L) (f : A → B)
    (hi : Function.Injective f) (hf : ∀ a, owner (f a) = label)
    (hs : ∀ b, owner b = label → ∃ a, f a = b) :
    A ≃ LocalRegionIndex (fiberRegion owner label) :=
  Equiv.ofBijective (fun a => ⟨f a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf a⟩⟩)
    ⟨fun a b h => hi (congrArg Subtype.val h), by
      intro b
      obtain ⟨a,ha⟩ := hs b.1 (Finset.mem_filter.mp b.2).2
      exact ⟨a, Subtype.ext ha⟩⟩
noncomputable def xCorrectionEquiv (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    DoubleCylinderEdge P x S ≃ LocalRegionIndex ((localX P S).correctionRegion x) := by
  apply fibreEquiv (rxCorrectionOwner P S) (.x x) (fun e => Sum.inl ⟨x,e⟩)
  · intro a b h
    cases h
    rfl
  · intro a
    rfl
  · intro b hb
    rcases b with ⟨y,e⟩ | ⟨q,v⟩
    · have hy : y = x := Vertex.x.inj hb
      subst y
      exact ⟨e,rfl⟩
    · cases hb
noncomputable def xSyndromeEquiv (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    DoubleCylinderFace P x S ≃ LocalRegionIndex ((localX P S).syndromeRegion x) := by
  apply fibreEquiv (rxSyndromeOwner P S) (.x x) (fun f => Sum.inl (Sum.inl ⟨x,f⟩))
  · intro a b h
    cases h
    rfl
  · intro a
    rfl
  · intro b hb
    rcases b with (⟨y,f⟩ | ⟨q,e⟩) | ⟨z,c⟩
    · have hy : y = x := Vertex.x.inj hb
      subst y
      exact ⟨f,rfl⟩
    · cases hb
    · cases hb
noncomputable def qCorrectionEquiv (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    QDoubleCylinderVertex P q S ≃ LocalRegionIndex ((localQ P S).correctionRegion q) := by
  apply fibreEquiv (rxCorrectionOwner P S) (.q q) (fun v => Sum.inr ⟨q,v⟩)
  · intro a b h
    cases h
    rfl
  · intro a
    rfl
  · intro b hb
    rcases b with ⟨x,e⟩ | ⟨r,v⟩
    · cases hb
    · have hr : r = q := Vertex.q.inj hb
      subst r
      exact ⟨v,rfl⟩
noncomputable def qSyndromeEquiv (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    QDoubleCylinderEdge P q S ≃ LocalRegionIndex ((localQ P S).syndromeRegion q) := by
  apply fibreEquiv (rxSyndromeOwner P S) (.q q) (fun e => Sum.inl (Sum.inr ⟨q,e⟩))
  · intro a b h
    cases h
    rfl
  · intro a
    rfl
  · intro b hb
    rcases b with (⟨x,f⟩ | ⟨r,e⟩) | ⟨z,c⟩
    · cases hb
    · have hr : r = q := Vertex.q.inj hb
      subst r
      exact ⟨e,rfl⟩
    · cases hb
noncomputable def zSyndromeEquiv (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) :
    Fin 2 ≃ LocalRegionIndex ((localZ P S).syndromeRegion z) := by
  apply fibreEquiv (rxSyndromeOwner P S) (.z z) (fun c => Sum.inr (z,c))
  · intro a b h
    exact (Prod.mk.inj (Sum.inr.inj h)).2
  · intro a
    rfl
  · intro b hb
    rcases b with (⟨x,f⟩ | ⟨q,e⟩) | ⟨w,c⟩
    · cases hb
    · cases hb
    · have hw : w = z := Vertex.z.inj hb
      subst w
      exact ⟨c,rfl⟩
end QEC.Coding.BDL26RXDecoderAdapter


