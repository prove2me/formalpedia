-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T01:55:00.775552+00:00
-- url     : https://prove2.me/theorems/19eb7329-c77c-400f-b96a-7fc88bf0805a
-- title:
--   Sectors
-- statement:
--   Definitions and structural lemmas for Sectors, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Sectors.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

set_option autoImplicit false
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
noncomputable def xSector (P : TannerSquarePresentation) (S : OddScale) : Finset (RX2 P S) :=
  Finset.univ.filter fun p => ∃ x : P.X, rxSyndromeOwner P S p = Vertex.x x
noncomputable def qSector (P : TannerSquarePresentation) (S : OddScale) : Finset (RX2 P S) :=
  Finset.univ.filter fun p => ∃ q : P.Q, rxSyndromeOwner P S p = Vertex.q q
noncomputable def zSector (P : TannerSquarePresentation) (S : OddScale) : Finset (RX2 P S) :=
  Finset.univ.filter fun p => ∃ z : P.Z, rxSyndromeOwner P S p = Vertex.z z
noncomputable def qCorrectionSector (P : TannerSquarePresentation) (S : OddScale) :
    Finset (RX1 P S) :=
  Finset.univ.filter fun p => ∃ q : P.Q, rxCorrectionOwner P S p = Vertex.q q
theorem mem_zSector (P : TannerSquarePresentation) (S : OddScale) (p : RX2 P S) :
    p ∈ zSector P S ↔ ∃ z, rxSyndromeOwner P S p = Vertex.z z := by
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ p))
noncomputable def zPairEquiv (P : TannerSquarePresentation) (S : OddScale) :
    (P.Z × Fin 2) ≃ LocalRegionIndex (zSector P S) :=
  Equiv.ofBijective
    (fun p => ⟨Sum.inr p, (mem_zSector P S _).mpr ⟨p.1,rfl⟩⟩)
    ⟨by
      intro a b h
      exact Sum.inr.inj (congrArg Subtype.val h), by
      intro p
      rcases p with ⟨((⟨x,f⟩ | ⟨q,e⟩) | ⟨z,c⟩),hp⟩
      · obtain ⟨z,hz⟩ := (mem_zSector P S _).mp hp
        cases hz
      · obtain ⟨z,hz⟩ := (mem_zSector P S _).mp hp
        cases hz
      · exact ⟨(z,c), Subtype.ext rfl⟩⟩
end QEC.Coding.BDL26RXDecoderAdapter


