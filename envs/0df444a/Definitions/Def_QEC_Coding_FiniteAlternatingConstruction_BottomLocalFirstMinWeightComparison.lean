-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
-- name    : QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T06:01:50.974338+00:00
-- url     : https://prove2.me/theorems/86f7e7cd-329d-4565-bde5-2c2d9ff94088
-- title:
--   Bottom Local First Min Weight Comparison
-- statement:
--   Definitions and structural lemmas for Bottom Local First Min Weight Comparison, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26FirstReplacementSparseExactness
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
abbrev Bit := BDL26FiniteTannerSquare.Field
abbrev Seed := baseTannerSquarePresentation
abbrev center : Seed.X := (0 : BDL26FiniteAlternatingCore.BaseX)
abbrev RawQ (S : OddScale) := RX1 Seed S
abbrev W (S : OddScale) := Word Bit (RawQ S)
abbrev V (S : OddScale) := Word Bit (RX0 Seed S)
def oldQ (b : Fin 2) : Seed.Q := Fin.castLE (by decide : 2 ≤ 5) b
def oldFace (b : Fin 2) : XStarFace Seed center :=
  ⟨Fin.castLE (by decide : 2 ≤ 4) b, by fin_cases b <;> decide⟩
def armEdge (b : Fin 2) : QStarEdge Seed (oldQ b) :=
  ⟨b, by fin_cases b <;> decide⟩
def sliceIndex (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) : Fin (S.half-1) :=
  ⟨k.val, by have := k.isLt; omega⟩
def height (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) : Fin (S.half+1) :=
  ⟨k.val+1, by have := k.isLt; omega⟩
def arm (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) (b : Fin 2) : RawQ S :=
  .inr ⟨oldQ b, (0,.inr (armEdge b,sliceIndex S large k))⟩
def horizontal (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15)
    (b : Fin 2) (i : Fin S.half) : RawQ S :=
  .inl ⟨center,.inl (0,subdivisionHorizontalEdge Seed center S (oldFace b) i (height S large k))⟩
abbrev Atom (S : OddScale) := Fin 2 ⊕ (Fin 2 × Fin S.half)
def atom (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) : Atom S → RawQ S
  | .inl b => arm S large k b
  | .inr (b,i) => horizontal S large k b i
def interiorLayer (S : OddScale) : RawQ S → Nat
  | .inl ⟨_,.inl (_, .inr (.inl (_,_,j)))⟩ => j.val
  | .inr ⟨_,(_, .inr (_,j))⟩ => j.val
  | _ => S.half
def evaluate (S : OddScale) (q : RawQ S) : W S →ₗ[Bit] Bit where
  toFun w := w q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def sliceReadout (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) : W S →ₗ[Bit] Bit :=
  ∑ b : Fin 2, (evaluate S (arm S large k b)+
    ∑ i : Fin S.half, evaluate S (horizontal S large k b i))
def grid (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15)
    (b : Fin 2) (i : Fin (S.half+1)) : RX0 Seed S :=
  ⟨center,(0,subdivisionGridVertex Seed center S (oldFace b) i (height S large k))⟩
def armVertex (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) (b : Fin 2) : RX0 Seed S :=
  ⟨center,(0,.inr (.inl (xStarFaceQZEdge Seed center (oldFace b) 0,sliceIndex S large k)))⟩
end QEC.Coding.BDL26FirstReplacementSparseExactness
namespace QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators
abbrev F := BDL26FiniteTannerSquare.Field
abbrev P1 (S : OddScale) := levelOnePresentation S
abbrev P2 (S : OddScale) := levelTwoPresentation S
abbrev Error (S : OddScale) := Word F (P2 S).Q
abbrev Syndrome (S : OddScale) := Word F (P2 S).Z
abbrev OldWord (S : OddScale) := Word F (P1 S).Q
def minimumSame {E Z : Type} [DecidableEq Z]
    (syndrome : E → Z) (weight : E → Nat) (sigma : Z) : List E → Option E
  | [] => none
  | a :: rest =>
      if syndrome a = sigma then
        match minimumSame syndrome weight sigma rest with
        | none => some a
        | some b => if weight a ≤ weight b then some a else some b
      else minimumSame syndrome weight sigma rest
def ownerFirstLookup {E Z : Type} [DecidableEq Z]
    (entries : List E) (syndrome : E → Z) (isLocal : E → Bool)
    (weight : E → Nat) (fallback : E) (sigma : Z) : E :=
  match search (fun e => isLocal e && decide (syndrome e = sigma)) entries with
  | some e => e
  | none => (minimumSame syndrome weight sigma entries).getD fallback
def actualWeight (S : OddScale) (e : Word F (ExecutableQ S)) : Nat :=
  HammingWeight (toActualError S e)
def executableComparison (S : OddScale) (sigma : Word F (ExecutableZ S)) :
    Word F (ExecutableQ S) :=
  ownerFirstLookup (allWords (ExecutableQ S)) (executableSyndrome S)
    (executableLocal S) (actualWeight S) 0 sigma
def ownerFirstMinWeightFallback (S : OddScale) (sigma : Syndrome S) : Error S :=
  toActualError S (executableComparison S (toExecutableSyndrome S sigma))
abbrev rho (S : OddScale) : Error S →ₗ[F] OldWord S := rzQParity (P1 S) S
def comparisonBaseAdapter (S : OddScale) :
    MultiscaleDecoder.F17LevelTwoBaseAdapterV2 (decoderData S)
      (decodingGraph S 2) (show 2 ≤ 2 from le_rfl) where
  decode := fun sigma => ownerFirstMinWeightFallback S sigma.val
end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
namespace QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
def sliceIndex (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) : Fin (S.half-1) :=
  ⟨k.val, by have := k.isLt; omega⟩
def height (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) : Fin (S.half+1) :=
  ⟨k.val+1, by have := k.isLt; omega⟩
def arm (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) (b : Fin 2) : RawQ S :=
  .inr ⟨oldQ b, (0,.inr (armEdge b,sliceIndex S n large k))⟩
def horizontal (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1))
    (b : Fin 2) (i : Fin S.half) : RawQ S :=
  .inl ⟨center,.inl (0,subdivisionHorizontalEdge Seed center S (oldFace b) i (height S n large k))⟩
def atom (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) : Atom S → RawQ S
  | .inl b => arm S n large k b
  | .inr (b,i) => horizontal S n large k b i
def sliceReadout (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) : W S →ₗ[Bit] Bit :=
  ∑ b : Fin 2, (evaluate S (arm S n large k b)+
    ∑ i : Fin S.half, evaluate S (horizontal S n large k b i))
def grid (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1))
    (b : Fin 2) (i : Fin (S.half+1)) : RX0 Seed S :=
  ⟨center,(0,subdivisionGridVertex Seed center S (oldFace b) i (height S n large k))⟩
def armVertex (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) (b : Fin 2) : RX0 Seed S :=
  ⟨center,(0,.inr (.inl (xStarFaceQZEdge Seed center (oldFace b) 0,sliceIndex S n large k)))⟩
end QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
namespace QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators
end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison


