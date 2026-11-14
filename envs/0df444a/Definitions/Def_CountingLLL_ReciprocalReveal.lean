-- Prove2me | Definitions.Def_CountingLLL_ReciprocalReveal
-- name    : CountingLLL_ReciprocalReveal
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T09:48:37.937343+00:00
-- url     : https://prove2.me/theorems/5fc27b39-728d-420d-80c6-53cf78e9e32a
-- title:
--   ReciprocalTest encoded as a reveal machine
-- statement:
--   Encode the operational ReciprocalTest as a deterministic reveal machine with a tagged coordinate for each oracle bit, fair bit, and finite-uniform draw. All outcomes are represented as natural numbers; the decoder reduces a uniform value modulo the target range. The representation is deterministic, and its law preservation and freshness are separate theorems.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTest
import Definitions.Def_CountingLLL_RevealMachine
set_option autoImplicit false

/-! A generic reveal-machine encoding of each atomic ReciprocalTest step.
Oracle and fair bits and finite-uniform values are embedded into ℕ. This is
only a deterministic interface; its input law and freshness invariants are
separate theorems. -/
namespace CountingLLL.ReciprocalTest
open CountingLLL.RevealMachine

abbrev ReadIndex := ℕ ⊕ (ℕ ⊕ (ℕ × ℕ))

def readIndex (s : State) : Option ReadIndex :=
  match s.phase with
  | .start | .initialCheck => some (.inr (.inl s.fairUsed))
  | .coinOracle _ => some (.inl s.oracleUsed)
  | .coinFair _ => some (.inr (.inl s.fairUsed))
  | .uniformCheck => some (.inr (.inr (s.j-1, s.uniformUsed)))
  | .loop | .done _ => none

def entropyCode (ω : Entropy) : ReadIndex → ℕ
  | .inl i => if ω.1 i then 1 else 0
  | .inr (.inl i) => if ω.2.1 i then 1 else 0
  | .inr (.inr a) => (ω.2.2 a).val

def uniformEntropy (v : ℕ) : Entropy :=
  (fun _ => decide (v ≠ 0), fun _ => decide (v ≠ 0),
    fun a => ⟨v % (a.1+1), Nat.mod_lt _ (Nat.succ_pos _)⟩)

def revealProgram : Program State ReadIndex ℕ where
  query := readIndex
  read := fun s v => step (uniformEntropy v) s
  silent := fun s => step (uniformEntropy 0) s
end CountingLLL.ReciprocalTest


