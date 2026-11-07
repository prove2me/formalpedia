-- Prove2me | Definitions.Def_SubexpPrimes_CombTerm
-- name    : SubexpPrimes_CombTerm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:00:49.142296+00:00
-- url     : https://prove2.me/theorems/6cb7ebbe-d457-49eb-a761-fcf6048cc3ef
-- title:
--   Combinations of contractions at scale $s$; the zero-test hypothesis
-- statement:
--   A **combination of contractions** is a sum $S=\sum_{j=1}^h b_j2^{a_j}Z(G_j)$. A quantity $A$ is **within $\eta$ of a combination at scale $s$** if networks and integers with the bounds of Lemma 2.7, namely $h\le\mathrm{poly}(s)$, $\Theta(s)$ edges, $O(s)$ weighted vertices of precision $O(s)$, the hypotheses of Theorem 2.5, $|b_j|\le2^{O(s)}$ and $|a_j|=O(s)$, can be constructed in time $\mathrm{poly}(s+L)$, with $|A-S|\le\eta$.
--
--   A **dyadic threshold** for $\delta$ is a dyadic number strictly between $\delta/4$ and $3\delta/4$, with an accuracy $k=O(s)$ such that $2^{-k}\le\delta/8$, computed in polynomial time. The **zero-test hypothesis** is $A\ge0$, and $A=0$ or $A\ge\delta$, for some $\delta\ge2^{-s}$ with $\eta\le\delta/8$.
--
--   **Formalization Note** All of these are families over an index, with one builder, one entry machine and one constant, and $L$ is read as the length of the index word.
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Lemma 2.7 and the definition after it, p.16; proof of Corollary 2.8(b), p.17

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_NetDesc_Evaluable

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

/-- **One term `b 2^a Z(G)` of a combination of contractions** — Gajulapalli, *Deterministic
Construction of Primes in Subexponential Time* (manuscript, sha256 6ad4d3de…), Lemma 2.7, p.16. -/
structure CombTerm where
  /-- the network -/
  D : NetDesc
  /-- the coefficient `b_j` -/
  b : ℤ
  /-- the normalization `a_j` -/
  a : ℤ

/-- The word of a list of terms: per term, the description and `b`, `a` in binary. -/
def combWord (ts : List CombTerm) : List Bool :=
  Encoding.encodeList (fun t => Encoding.encodeList id [t.D.encode, intWord t.b, intWord t.a]) ts

/-- The value of a combination: `S = ∑_j b_j 2^{a_j} Z(G_j)`. -/
noncomputable def combValue (T : (D : NetDesc) → D.Tables ℚ) (ts : List CombTerm) : ℝ :=
  (ts.map fun t => (t.b : ℝ) * (2 : ℝ) ^ t.a * (((t.D.net (T t.D)).Z : ℚ) : ℝ)).sum

/-- The conditions of Lemma 2.7 on one term at scale `s`, with one constant `c`: the hypotheses of
Theorem 2.5, `Θ(s)` edges, `|b| ≤ 2^{O(s)}`, `|a| = O(s)`. Since `w, p ≤ c m` and `m ≤ c s`, the
network has `O(s)` weighted vertices of precision `O(s)`. -/
def TermOK (c s : ℕ) (E : PrimitiveMachine) (outE : Fin E.tapeCount)
    (T : (D : NetDesc) → D.Tables ℚ) (t : CombTerm) : Prop :=
  t.D.Evaluable c E outE (T t.D) ∧ s ≤ c * t.D.m ∧ t.D.m ≤ c * s ∧
    |t.b| ≤ 2 ^ (c * s) ∧ |t.a| ≤ c * s

/-- **A family of combinations of contractions at scale `s`** (p.16): "networks and integers as in
Lemma 2.7 … can be constructed in time poly(s + L)". One builder, one entry machine and one
constant serve all valid indices, and `L` is read as the length of the index word. -/
def CombinationFamily {α : Type*} (enc : α → List Bool) (valid : α → Prop) (s : α → ℕ)
    (ts : α → List CombTerm) (T : (D : NetDesc) → D.Tables ℚ) : Prop :=
  ∃ (B : PrimitiveMachine) (outB : Fin B.tapeCount) (E : PrimitiveMachine)
    (outE : Fin E.tapeCount) (c : ℕ),
    ∀ a, valid a →
      2 ≤ s a ∧
      RunsWithin B outB (enc a) (combWord (ts a)) (polyBound c (s a + (enc a).length))
        (polyBound c (s a + (enc a).length)) ∧
      (ts a).length ≤ c * s a ^ c ∧
      ∀ t ∈ ts a, TermOK c (s a) E outE T t

/-- **"`A` is within `η` of a combination of contractions at scale `s`"** (p.16), for a family
indexed by `α`: `|A - S| ≤ η`. -/
def WithinCombination {α : Type*} (enc : α → List Bool) (valid : α → Prop) (s : α → ℕ)
    (A η : α → ℝ) : Prop :=
  ∃ (ts : α → List CombTerm) (T : (D : NetDesc) → D.Tables ℚ),
    CombinationFamily enc valid s ts T ∧ ∀ a, valid a → |A a - combValue T (ts a)| ≤ η a

/-- **A dyadic threshold, built with the family** (proof of Corollary 2.8(b), p.17: "when δ is
irrational, such as δ = ln 2, we use a dyadic threshold in this range"): a dyadic `τ = t / 2^j`
strictly between `δ/4` and `3δ/4`, and an accuracy `k = O(s)` with `2^{-k} ≤ δ/8`, computed in
polynomial time from the index. -/
def HasThreshold {α : Type*} (enc : α → List Bool) (valid : α → Prop) (s : α → ℕ)
    (δ : α → ℝ) : Prop :=
  ∃ (t : α → ℤ) (j k : α → ℕ) (B : PrimitiveMachine) (outB : Fin B.tapeCount) (c : ℕ),
    ∀ a, valid a →
      δ a / 4 < (t a : ℝ) / 2 ^ j a ∧ (t a : ℝ) / 2 ^ j a < 3 * δ a / 4 ∧
      k a ≤ c * s a ∧ (2 : ℝ) ^ (-(k a : ℤ)) ≤ δ a / 8 ∧
      RunsWithin B outB (enc a)
        (Encoding.encodeList id [dyadicWord (t a) (j a), Encoding.encodeNat (k a)])
        (polyBound c (s a + (enc a).length)) (polyBound c (s a + (enc a).length))

/-- **The hypothesis of Corollary 2.8(b)** (p.16): `A ≥ 0`, and either `A = 0` or `A ≥ δ`, for some
`δ ≥ 2^{-s}` with `η ≤ δ/8`. -/
def ZeroTestHyp (A δ η : ℝ) (s : ℕ) : Prop :=
  0 ≤ A ∧ (A = 0 ∨ δ ≤ A) ∧ (2 : ℝ) ^ (-(s : ℤ)) ≤ δ ∧ η ≤ δ / 8

end SubexpPrimes


