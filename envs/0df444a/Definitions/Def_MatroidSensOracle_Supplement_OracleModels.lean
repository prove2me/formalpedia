-- Prove2me | Definitions.Def_MatroidSensOracle_Supplement_OracleModels
-- name    : MatroidSensOracle_Supplement_OracleModels
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:05:48.184798+00:00
-- url     : https://prove2.me/theorems/3753931b-d03d-4317-a1aa-44c0da20dcc2
-- title:
--   One row of an oracle table, black-box augmentation and $\alpha$-factor algorithms, and the information-theoretic oracles of §10
-- statement:
--   1. **One table row.** A word-RAM oracle *serves* a set of queries if, on the given input, its preprocessing halts within $T_P$ steps and stores at most the given number of bits on every coin sequence, and every query in the set halts within $T_Q$ steps on all coins and is answered wrongly with probability at most the given error.
--   2. **Optimal augmentation** (Theorem 5.6, [48]; p.30). A word-RAM program computes an optimal augmentation within $T_A(n,f)$ steps if, on every instance $(G,s,f)$ with $n\ge2$, $f\ge1$, it halts within that many steps and outputs a list $I^*$ of $f$ vertex pairs such that inserting $I^*$ as new edges maximizes $\mu_{G+I}(s)$ over all lists $I$ of $f$ pairs.
--   3. **$\alpha$-factor algorithms** ([5, 40]; p.45). A word-RAM program finds $\alpha$-factors within $T_A$ steps if, on every undirected graph and every $\alpha$, it decides whether an $\alpha$-factor exists and, if so, outputs one.
--   4. **Information-theoretic oracles** (§10). A preprocessing map sends an instance and random coins to a bit string. A query map sends the string, a query and fresh coins to an answer. Both are measurable in the coins and there is no time bound. Such an oracle is correct on a class of instances with error $\delta$ if every member and query is answered wrongly with probability at most $\delta$. It stores at least $B$ bits on the class if some member and some coin sequence give a string of length at least $B$.
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), §5.3 p.30, proof of Theorem 8.8 p.45, §10 pp.54–57 (PDF pp.33, 48, 57–60)

import Mathlib
import Definitions.Def_MatroidSensOracle_WordRAM
import Definitions.Def_MatroidSensOracle_Supplement_GraphProblems

open MeasureTheory

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-!
# Oracle bookkeeping on the word RAM, the black-box algorithms behind `T_aug` and `T_α`, and the
# information-theoretic oracle model of the lower bounds (§10)

Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version, sha256 0de50841…).
* §5.3, p.30 (PDF p.33): "Theorem 5.6 ([48], Theorem 3.1). There exists a polynomial time algorithm
  to solve the following problem: Given an unweighted directed graph G = (V, E) with a fixed source s
  and a number f, output a set I∗ ⊆ V × V of f edges such that adding the edges of I∗ to G results in
  the maximum increase in the s-min-cut value of G […]. We compute this augmentation in polynomial
  time T_aug during preprocessing".
* §8.2.2 and the proof of Theorem 8.8, p.45 (PDF p.48): "finding the α-factor of G takes O(T_α) time
  [5, 40]".
* §10, p.54 (PDF p.57): "any (s, t)-Bounded Max-Flow sensitivity oracle requires Ω(min{(m★)², n²})
  space, irrespective of the query time"; the proofs (pp.55–57) count the bits an oracle must store
  to answer all queries of a family of graphs indexed by a `p × p` matrix.

**Formalization Note.**
* `Oracle.Serves O w inp TP space Qs enc TQ ok err` bundles the three clauses of one row of a table
  for the base word-RAM oracle `O` on the input words `inp`: preprocessing within `TP` steps storing
  at most `space` bits on every coin sequence, and for every query `q ∈ Qs` (encoded by `enc q`) the
  query halts within `TQ` steps on all coins and answers `ok q` except with probability `≤ err`.
* `AugAlgorithm A b TA`: the word-RAM program `A` solves the augmentation task of Theorem 5.6 on
  every instance `(G, s, f)` with `n ≥ 2`, `f ≥ 1`, within `TA n f` steps on every coin sequence and
  every word width `w ≥ b(⌊log₂(n + f + 2)⌋ + 1)`. Its input words are `encodeWith G [n, f, s]`; it
  outputs the list `I∗` of `f` pairs in cells `0, 1, …` (tail, head of each pair). `I∗` must maximize
  `μ_{G+I}(s)` over all lists `I` of `f` pairs, inserted as new edges of the multigraph `G + I` (the
  insertions a query makes).
* `FactorAlgorithm A b TA`: `A` decides whether the undirected graph `G` has an `α`-factor and, if it
  has, outputs one, within `TA inp` steps (`inp` = its input words `encodeWith G [n] ++ α`) on every
  coin sequence and every word width `w ≥ b(⌊log₂(n + Σα + 2)⌋ + 1)`. Output: word `0` is `1` iff an
  `α`-factor exists; then the low bits of words `1, …, m` mark one (edges of `G` in lexicographic
  order).
* `InfoOracle X Qy A`: an information-theoretic sensitivity oracle for instances `X`, queries `Qy`
  and answers `A`: a preprocessing map from an instance and a coin sequence to a bit string, and a
  query map from a bit string, a query and fresh coins to an answer, both measurable in the coins. No
  time is counted. It is correct for a class `𝒢` and a query set with error `δ` if on every member
  and every query the answer is wrong with probability at most `δ` (over both coin sequences, the
  base `coinLaw`). Its space on `x` is the worst case over the coins of the length of the stored
  string, so "space `≥ B` on some member" is `∃ x ∈ 𝒢, ∃ ω, B ≤ |P x ω|`.
-/

/-- One row of an oracle table: preprocessing bound and stored bits, and for every query in `Qs`
the query bound and the error bound for the output condition `ok q`. -/
def _root_.MatroidSensOracle.Oracle.Serves {α : Type} (O : Oracle) (w : ℕ) (inp : List ℤ) (TP : ℕ)
    (space : ℝ) (Qs : Set α) (enc : α → List ℤ) (TQ : ℕ) (ok : α → (ℤ → BitVec w) → Prop)
    (err : ℝ) : Prop :=
  O.PrepWithin w inp TP space ∧
    ∀ q ∈ Qs, O.QueryWithin w inp (enc q) TP TQ ∧ O.ErrorAtMost w inp (enc q) TP TQ (ok q) err

variable {n : ℕ}

/-- The multigraph `G + I` for a list `I` of pairs inserted as new zero-cost edges. -/
def _root_.MatroidSensOracle.InputGraph.plusPairs (G : InputGraph n) (I : List (Fin n × Fin n)) :
    CostMultigraph (Fin n) :=
  G.plus ⟨I.map fun e => (e.1, e.2, 0), ∅⟩

/-- `I` is an optimal augmentation of `G` for `s` by `f` edges: `|I| = f` and `μ_{G+I}(s)` is
maximal among all lists of `f` pairs. -/
def IsOptAug (G : InputGraph n) (s : Fin n) (f : ℕ) (I : List (Fin n × Fin n)) : Prop :=
  I.length = f ∧ ∀ J : List (Fin n × Fin n), J.length = f →
    sMinCutValue (G.plusPairs J) s ≤ sMinCutValue (G.plusPairs I) s

/-- The program `A` computes an optimal augmentation within `TA n f` steps (see the note). -/
def AugAlgorithm (A : List Instr) (b : ℕ) (TA : ℕ → ℕ → ℝ) : Prop :=
  ∀ (n f : ℕ) (G : InputGraph n) (s : Fin n), 2 ≤ n → 1 ≤ f →
    ∀ w : ℕ, b * (Nat.log 2 (n + f + 2) + 1) ≤ w → ∀ ω : Coins,
      ∃ mA, exec A ω ⌊TA n f⌋₊ 0 0 (loadWords w (encodeWith G [(n : ℤ), f, (s : ℕ)])) = some mA ∧
        ∃ I : List (Fin n × Fin n), IsOptAug G s f I ∧
          ∀ i : Fin I.length, (mA (2 * (i : ℕ))).toNat = ((I.get i).1 : ℕ) ∧
            (mA (2 * (i : ℕ) + 1)).toNat = ((I.get i).2 : ℕ)

/-- The input words of the `α`-factor task: `encodeWith G [n]`, then `α(0), …, α(n − 1)`. -/
def factorInput (G : InputGraph n) (α : Fin n → ℕ) : List ℤ :=
  encodeWith G [(n : ℤ)] ++ List.ofFn fun v => ((α v : ℕ) : ℤ)

/-- The program `A` finds an `α`-factor of an undirected graph or reports that none exists, within
`TA (factorInput G α)` steps (see the note). -/
def FactorAlgorithm (A : List Instr) (b : ℕ) (TA : List ℤ → ℝ) : Prop :=
  ∀ (n : ℕ) (G : InputGraph n) (α : Fin n → ℕ), G.Undirected →
    ∀ w : ℕ, b * (Nat.log 2 (n + ∑ v, α v + 2) + 1) ≤ w → ∀ ω : Coins,
      ∃ mA, exec A ω ⌊TA (factorInput G α)⌋₊ 0 0 (loadWords w (factorInput G α)) = some mA ∧
        ((mA 0).toNat = 1 ↔ HasFactor G.toMultigraph α) ∧
        (HasFactor G.toMultigraph α →
          IsFactor G.toMultigraph α
            (Finset.univ.filter fun e : Fin G.toMultigraph.m => (mA ((e : ℕ) + 1)).getLsbD 0 = true))

/-- An information-theoretic sensitivity oracle: preprocessing to a bit string and query. -/
structure InfoOracle (X Qy A : Type) where
  prep : X → Coins → List Bool
  query : List Bool → Qy → Coins → A

/-- The oracle is measurable in the coins and, on every member of `𝒢` and every query in `Qs`,
answers `ans` except with probability at most `δ`. -/
def InfoOracle.Correct {X Qy A : Type} (O : InfoOracle X Qy A) (𝒢 : Set X) (Qs : Set Qy)
    (ans : X → Qy → A) (δ : ℝ) : Prop :=
  (∀ x s, MeasurableSet {ω : Coins | O.prep x ω = s}) ∧
  (∀ S q a, MeasurableSet {ω : Coins | O.query S q ω = a}) ∧
  ∀ x ∈ 𝒢, ∀ q ∈ Qs,
    (coinLaw.prod coinLaw) {p : Coins × Coins | O.query (O.prep x p.1) q p.2 ≠ ans x q} ≤
      ENNReal.ofReal δ

/-- The oracle stores at least `B` bits on some member of `𝒢` for some coin sequence (its
worst-case space on that member is at least `B`). -/
def InfoOracle.SpaceAtLeast {X Qy A : Type} (O : InfoOracle X Qy A) (𝒢 : Set X) (B : ℝ) : Prop :=
  ∃ x ∈ 𝒢, ∃ ω : Coins, B ≤ ((O.prep x ω).length : ℝ)

end MatroidSensOracle.Supplement


