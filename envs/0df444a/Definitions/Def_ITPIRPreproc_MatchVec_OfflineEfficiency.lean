-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_OfflineEfficiency
-- name    : ITPIRPreproc_MatchVec_OfflineEfficiency
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:20:19.726622+00:00
-- url     : https://prove2.me/theorems/d09548a1-4a59-4373-adec-081322a3da58
-- title:
--   Shared non-streaming efficiency interface for Claim 6.2.4
-- statement:
--   This module isolates the non-streaming fields of the §4.1 efficiency structure, provides a structure update that installs streaming initialization and per-chunk programs without changing any other field, and gives the obvious reassembly lemma. It also fixes common lower bounds $2^{32}(|C_0|+1)$ and $c_0+32$ for the constants used in the two parts of Claim 6.2.4. These are only bookkeeping devices for constructing one implementation with shared codes and programs; they do not alter the mathematical cost model.
-- source:
--   Dujmovic–Lai–Wichs, STOC 2027 submission #572, §4.1 (printed p.12, PDF p.14) and Claim 6.2.4 (printed p.23, PDF p.25)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_Efficiency

open scoped ENNReal

namespace ITPIRPreproc.MatchVec

open WordRAM

namespace OCHPImpl

variable {P : ∀ m : ℕ, OCHP (m * m)} (I : OCHPImpl P)

/-- All the requirements of `Efficient` other than its two streaming fields.  This is the
interface shared by the non-streaming and streaming constructions of the activation-bit
primitive. -/
structure NonStreamEfficient (m : ℕ) (tB tS tQ tD tA : ℝ) (qLen aLen : ℕ) : Prop where
  key_len : ∀ R : (P m).Key, (I.encKey m R).length ≤ qLen
  ans_len : ∀ (D : Fin (m * m) → Bool) (Q : (P m).Key),
    (I.encAns m ((P m).answer D Q)).length ≤ aLen
  table_det : Deterministic I.tableProg
  table_ok : Halts I.tableProg (encNat m) zeroTape ∧
    output I.tableProg (encNat m) zeroTape = I.table m ∧
    (cost I.tableProg (encNat m) zeroTape : ℝ) ≤ numChunks m * tS ∧
    (workingBits I.tableProg (encNat m) zeroTape : ℝ) ≤ numChunks m * tS
  sampleKey_ok :
    (∀ τ, Halts I.sampleKey (I.sampleKeyInput m) τ ∧
      (cost I.sampleKey (I.sampleKeyInput m) τ : ℝ) ≤ tB) ∧
    ∀ x : List Bool, coinTape {τ | output I.sampleKey (I.sampleKeyInput m) τ = x} =
      ((Finset.univ.filter fun R => I.encKey m R = x).card : ℝ≥0∞) /
        (Fintype.card (P m).Key : ℝ≥0∞)
  sampleCompat_ok : ∀ i : Fin (m * m),
    (∀ τ, Halts I.sampleCompat (I.sampleCompatInput m i) τ ∧
      (cost I.sampleCompat (I.sampleCompatInput m i) τ : ℝ) ≤ tB) ∧
    ∀ x : List Bool, coinTape {τ | output I.sampleCompat (I.sampleCompatInput m i) τ = x} =
      (((P m).compat i).filter fun R => I.encKey m R = x).card / (((P m).compat i).card : ℝ≥0∞)
  test_det : Deterministic I.testCompat
  test_ok : ∀ (i : Fin (m * m)) (R : (P m).Key),
    Halts I.testCompat (I.keyInput m i R) zeroTape ∧
    output I.testCompat (I.keyInput m i R) zeroTape = [decide (i ∈ (P m).sel R)] ∧
    (cost I.testCompat (I.keyInput m i R) zeroTape : ℝ) ≤ tB
  query_ok : ∀ (i : Fin (m * m)), ∀ R ∈ (P m).compat i,
    (∀ τ, Halts I.query (I.keyInput m i R) τ ∧
      (cost I.query (I.keyInput m i R) τ : ℝ) ≤ tQ) ∧
    ∀ x : List Bool, coinTape {τ | output I.query (I.keyInput m i R) τ = x} =
      ((P m).query i R).toOuterMeasure
        {p | encBits (I.encKey m p.1) ++ I.encSecret m p.2 = x}
  query_args : ∀ (i : Fin (m * m)) (R : (P m).Key), ((I.keyArgs m i R).length : ℝ) ≤ tQ
  answer_args : ∀ Q : (P m).Key, ((I.answerArgs m Q).length : ℝ) ≤ tA
  decode_args : ∀ (i : Fin (m * m)) (R : (P m).Key) (z : (P m).HintVal) (Q : (P m).Key)
      (u : (P m).Secret) (a : (P m).AnsVal), ((I.decodeArgs m i R z Q u a).length : ℝ) ≤ tD
  answer_det : Deterministic I.answer
  answer_ok : ∀ (D : Fin (m * m) → Bool) (Q : (P m).Key),
    Halts I.answer (I.answerInput m D Q) zeroTape ∧
    output I.answer (I.answerInput m D Q) zeroTape = I.encAns m ((P m).answer D Q) ∧
    (cost I.answer (I.answerInput m D Q) zeroTape : ℝ) ≤ tA
  decode_det : Deterministic I.decode
  decode_ok : ∀ (i : Fin (m * m)) (R : (P m).Key) (z : (P m).HintVal) (Q : (P m).Key)
      (u : (P m).Secret) (a : (P m).AnsVal),
    Halts I.decode (I.decodeInput m i R z Q u a) zeroTape ∧
    decodeBit (output I.decode (I.decodeInput m i R z Q u a) zeroTape) =
      (P m).decode i R z Q u a ∧
    (cost I.decode (I.decodeInput m i R z Q u a) zeroTape : ℝ) ≤ tD

/-- Install initialization and per-chunk programs, leaving every non-streaming component
definitionally unchanged. -/
def withStreams (I : OCHPImpl P) (si sc : Program) : OCHPImpl P :=
  { I with streamInit := si, streamChunk := sc }

/-- Reassemble the full efficiency structure from its non-streaming and streaming parts. -/
theorem efficientOfNonStream (I : OCHPImpl P) {m : ℕ} {tB tS tQ tD tA : ℝ} {qLen aLen : ℕ}
    (h : I.NonStreamEfficient m tB tS tQ tD tA qLen aLen)
    (sd : Deterministic I.streamInit ∧ Deterministic I.streamChunk)
    (so : ∀ (keys : List (P m).Key), numChunks m ≤ keys.length →
      ∀ D : Fin (m * m) → Bool,
        (Halts I.streamInit (I.streamInitInput m keys) zeroTape ∧
          (cost I.streamInit (I.streamInitInput m keys) zeroTape : ℝ) ≤ keys.length * tS ∧
          (((I.streamInitInput m keys).length +
              workingBits I.streamInit (I.streamInitInput m keys) zeroTape : ℕ) : ℝ) ≤
            keys.length * tS) ∧
        (∀ k < numChunks m,
          let inp := streamChunkInput m (chunk D k) (I.streamState m keys D k)
          Halts I.streamChunk inp zeroTape ∧
          (cost I.streamChunk inp zeroTape : ℝ) ≤ keys.length * tS ∧
          ((inp.length + workingBits I.streamChunk inp zeroTape : ℕ) : ℝ) ≤
            keys.length * tS) ∧
        I.streamState m keys D (numChunks m) = I.hintsCode m keys D) :
    I.Efficient m tB tS tQ tD tA qLen aLen where
  key_len := h.key_len
  ans_len := h.ans_len
  table_det := h.table_det
  table_ok := h.table_ok
  sampleKey_ok := h.sampleKey_ok
  sampleCompat_ok := h.sampleCompat_ok
  test_det := h.test_det
  test_ok := h.test_ok
  query_ok := h.query_ok
  query_args := h.query_args
  answer_args := h.answer_args
  decode_args := h.decode_args
  answer_det := h.answer_det
  answer_ok := h.answer_ok
  decode_det := h.decode_det
  decode_ok := h.decode_ok
  stream_det := sd
  stream_ok := so

end OCHPImpl

/-- A convenient common lower bound for the two constructions of Claim 6.2.4.  It absorbs
fixed instruction overhead and the supplied matching-vector cost constant. -/
def activationCostFloor (C₀ : ℝ) : ℝ := 2 ^ 32 * (|C₀| + 1)

/-- A common polynomial-exponent floor for the two constructions. -/
def activationExponentFloor (c₀ : ℕ) : ℕ := c₀ + 32

end ITPIRPreproc.MatchVec


