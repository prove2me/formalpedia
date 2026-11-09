-- Prove2me | Definitions.Def_NashAmplification_Filtering_Encoding
-- name    : NashAmplification_Filtering_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:19:29.888379+00:00
-- url     : https://prove2.me/theorems/7d06e24f-c60f-4a8d-af15-4b83a8d18cef
-- title:
--   Complete rational table and profile encodings
-- statement:
--   Computational data use raw pairs $(a,b)$ of natural numbers with $b>0$, interpreted as $a/b$. Unreduced fractions remain distinct inputs. A table carries $k$ positive action counts and exactly $k\prod_r n_r$ payoff entries in player-then-mixed-radix order, each in $[0,1]$. A profile carries the counts and exactly $\sum_r n_r$ probabilities. Normalization is tested by the equilibrium premise, rather than imposed on arbitrary machine inputs.
--
--   All integers use the referenced binary natural-number encoder. Symbol 2 frames numerator and denominator words; symbol 3 frames table or list entries. An extra closing separator has constant cost. No encoder normalizes fractions, pads its input, solves a game, or constructs the output game. The recovery input concatenates the supplied table and profile using tagged copies of this finite alphabet. Signed rational threshold outputs carry a sign, numerator magnitude and positive denominator.
--
--   One-round filtering inputs contain their size, parameters and complete mass, weight and value lists. These encodings fix the input-length meaning of the polynomial-time guarantees. Proof fields are not encoded. Zero is the empty binary word with its delimiter; this convention changes ordinary binary length by constant overhead per entry.
-- source:
--   Deng, Li, Wang and Zhang, Hardness Amplification for Approximate Nash Equilibrium with a Constant Number of Players, STOC 2027 submission #120 (October 2026), SHA-256 c201a27da9b9920a924945f1a30c7919ae6b922c99430223ee9bbcdec5b0ffa8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/120.pdf, §2 computational convention, PDF p. 6 (printed p. 5); Appendix B, PDF pp. 29–32 (printed pp. 28–31)

import Definitions.Def_NashAmplification_Filtering_Model
import Definitions.Def_OnlineCRS_Combine_encNat
import Mathlib.Computability.TuringMachine.Computable

open scoped BigOperators
noncomputable section

namespace NashAmplification.Filtering
open OnlineCRS.Combine

/-- Raw, possibly unreduced, nonnegative rational. No input normalization occurs. -/
structure RawRat where
  num : ℕ
  den : ℕ
  den_pos : 0 < den
  deriving DecidableEq

def RawRat.value (r : RawRat) : ℝ := (r.num : ℝ) / r.den

def zeroRat : RawRat := ⟨0,1,by decide⟩

/-- Complete input payoff table; the list order is player then mixed-radix pure profile. -/
structure Table (k : ℕ) where
  sizes : List ℕ
  sizes_length : sizes.length = k
  sizes_pos : ∀ n ∈ sizes, 0 < n
  entries : List RawRat
  entries_length : entries.length = k * sizes.prod
  bounded : ∀ r ∈ entries, r.num ≤ r.den

/-- A supplied profile contains every probability, including zero probabilities. -/
structure RawProfile (k : ℕ) where
  sizes : List ℕ
  sizes_length : sizes.length = k
  sizes_pos : ∀ n ∈ sizes, 0 < n
  entries : List RawRat
  entries_length : entries.length = sizes.sum

def Table.counts {k : ℕ} (G : Table k) : Fin k → ℕ := fun i => G.sizes.getD i.val 0

def Table.utility {k : ℕ} (G : Table k) : Utility G.counts :=
  fun i a => (G.entries.getD (i.val * G.sizes.prod + tupleRank a) zeroRat).value

def RawProfile.at {k : ℕ} (σ : RawProfile k) (i a : ℕ) : ℝ :=
  (σ.entries.getD ((σ.sizes.take i).sum + a) zeroRat).value

def RawProfile.on {k : ℕ} (σ : RawProfile k) (n : Fin k → ℕ) : Mixed n :=
  fun i a => σ.at i.val a.val

/-- A uniform table can be read on a common action set without dependent transports. -/
def uniformUtility {C : ℕ} (H : Table C) (n : ℕ) : Fin C → (Fin C → Fin n) → ℝ :=
  fun i a => (H.entries.getD (i.val * n^C + tupleRank a) zeroRat).value

def uniformProfile {C : ℕ} (σ : RawProfile C) (n : ℕ) : Fin C → Fin n → ℝ :=
  fun i a => σ.at i.val a.val

/-- Framed words: separator 2 inside each rational, separator 3 between entries. -/
def pack (sep : Sym) (rows : List (List Sym)) : List Sym :=
  rows.flatMap (fun row => row ++ [sep])

def encRaw (r : RawRat) : List Sym := pack 2 [encNat r.num, encNat r.den]

def encGame {k : ℕ} (G : Table k) : List Sym :=
  pack 3 (G.sizes.map encNat ++ G.entries.map encRaw)

def encProfile {k : ℕ} (σ : RawProfile k) : List Sym :=
  pack 3 (σ.sizes.map encNat ++ σ.entries.map encRaw)

/-- Concatenation with distinct alphabet tags; no H is computed to encode this pair. -/
def encGameProfile {k C : ℕ} (p : Table k × RawProfile C) : List (Sym ⊕ Sym) :=
  (encGame p.1).map Sum.inl ++ (encProfile p.2).map Sum.inr

/-- Signed reduced rational output, numerator sign followed by its magnitude and denominator. -/
def encSigned (x : ℚ) : List Sym :=
  (if x.num < 0 then [1] else [0]) ++ pack 2 [encNat x.num.natAbs, encNat x.den]

/-- One filtering-round input, with arbitrary number of entries and no hidden computation. -/
structure RoundInput where
  n : ℕ
  n_pos : 0 < n
  ρ : List RawRat
  w : List RawRat
  v : List RawRat
  lengths : ρ.length = n ∧ w.length = n ∧ v.length = n
  q : RawRat
  h : RawRat

def RoundInput.rho (d : RoundInput) (i : Fin d.n) : ℝ := (d.ρ.getD i.val zeroRat).value
def RoundInput.weight (d : RoundInput) (i : Fin d.n) : ℝ := (d.w.getD i.val zeroRat).value
def RoundInput.assigned (d : RoundInput) (i : Fin d.n) : ℝ := (d.v.getD i.val zeroRat).value

def encRound (d : RoundInput) : List Sym :=
  pack 3 ([encNat d.n, encRaw d.q, encRaw d.h] ++ (d.ρ ++ d.w ++ d.v).map encRaw)

def encRoundOutput (o : ℚ × List RawRat) : List (Sym ⊕ Sym) :=
  (encSigned o.1).map Sum.inl ++ (pack 3 (o.2.map encRaw)).map Sum.inr
end NashAmplification.Filtering


