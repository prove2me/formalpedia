-- Prove2me | Definitions.Def_QTolTest1673_Unified_Supplement_Records
-- name    : QTolTest1673_Unified_Supplement_Records
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:19:31.928694+00:00
-- url     : https://prove2.me/theorems/c65692de-c6ae-42e1-8fcd-523401822f40
-- title:
--   Truth-table records, odd parity and coordinate subcubes
-- statement:
--   For a record $S\subseteq X$, define the truth-table character $\chi_S(f)=\prod_{x\in S}f(x)$. Under an oracle law $D$, the inner product of its two record vectors is computed as
--   $$\langle T\mid S\rangle_D=\sum_fD(f)\chi_T(f)\chi_S(f).$$
--   A good-record family contains the empty record and has inner products equal to $\mathbf1_{S=T}$. The expected acceptance probability under $D$ is the finite weighted sum of the algorithm's acceptance probabilities.
--
--   A coordinate subcube through $x$ fixes every coordinate outside its free coordinate set $U$. Odd-parity strings are exactly sign assignments with product $-1$; their average is the uniform average on that subtype. Coordinate subsets of size $s$ are likewise a subtype with its uniform finite average. These constructions support the comparison lemma and the two Section 11 combinatorial lemmas. Odd-parity uses have length $2^s\ge2$, and coordinate-set uses assume $s\le n$; neither averages over an empty subtype.
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, §9.1–9.2 pp.41–43; §11.3–11.4 pp.51–52

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Model

noncomputable section
open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum

namespace QTolTest1673.Unified.Supplement

/-- Truth-table Fourier character, §9.1 p.42 (not an input-space Fourier character). -/
def recordSign {X : Type} (S : Finset X) (f : X → Bool) : ℝ :=
  ∏ x ∈ S, if f x then (-1 : ℝ) else 1

/-- Expected acceptance under a fixed finite oracle law. -/
def acceptMean {X : Type} [Fintype X] [DecidableEq X]
    (A : AdaptiveQueryAlg X Bool) (D : PMF (X → Bool)) : ℝ :=
  ∑ f, (D f).toReal * A.outProb f true

/-- Inner product of record vectors Σ_f sqrt(D(f))χ_S(f)|f⟩ and its T counterpart. -/
def recordInner {X : Type} [Fintype X] (D : PMF (X → Bool)) (S T : Finset X) : ℝ :=
  ∑ f, (D f).toReal * recordSign S f * recordSign T f

/-- Good-record family: includes ∅, and the actual record vectors are orthonormal. -/
def GoodRecords {X : Type} [Fintype X] (D : PMF (X → Bool))
    (G : Set (Finset X)) : Prop :=
  ∅ ∈ G ∧ ∀ S ∈ G, ∀ T ∈ G, recordInner D S T = if S = T then 1 else 0

/-- Restriction to a U-subcube through x: outside U the coordinates are fixed. -/
def subcube {n : ℕ} (U : Finset (Fin n)) (x : V n) : Finset (V n) :=
  Finset.univ.filter fun y => ∀ i, i ∉ U → y i = x i

/-- Uniform distribution on sign strings with odd parity, represented without a conditional default. -/
abbrev OddStrings (L : ℕ) := {f : Fin L → Bool // recordSign Finset.univ f = -1}

/-- Finite average over odd-parity strings (all theorem uses have L=2^s≥2). -/
def oddAvg (L : ℕ) (g : (Fin L → Bool) → ℝ) : ℝ :=
  letI : Fintype (OddStrings L) := Fintype.ofFinite _
  avg (fun f : OddStrings L => g f.val)

/-- Uniform s-subset of n coordinates; assumptions s≤n ensure nonemptiness. -/
abbrev CoordSets (n s : ℕ) := {U : Finset (Fin n) // U.card = s}

end QTolTest1673.Unified.Supplement


