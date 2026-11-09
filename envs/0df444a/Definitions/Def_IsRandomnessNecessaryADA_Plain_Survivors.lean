-- Prove2me | Definitions.Def_IsRandomnessNecessaryADA_Plain_Survivors
-- name    : IsRandomnessNecessaryADA_Plain_Survivors
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:18:18.318256+00:00
-- url     : https://prove2.me/theorems/6d3caa5e-d91d-4a1a-869b-baacb0cddf08
-- title:
--   Naturalness, survivor sets, common points and threshold paths
-- statement:
--   For a fixed sample and history, a natural mechanism returns the same real answer to queries agreeing at every sample position. A bit-natural mechanism need only return the same bit $\mathbf1\{a\ge1/2\}$. A dataset survives transcript $T$ precisely when deterministic replay of its recorded queries yields exactly $T$.
--
--   Writing $H_T$ for this finite set, the next branch at query $q$ and real answer $a$ is $\{S\in H_T:m(S,T,q)=a\}$. A query separates accurate branches when
--   $$|a-Pq|\le1/10\ \Longrightarrow\ |H_{T,q,a}|\le(9/10)|H_T|\quad\text{for every real }a.$$
--   A common point occurs in at least $(8/10)|H_T|$ candidate datasets, counting its presence once in each dataset. A threshold path specifies a common set and an arbitrary enumeration of its complement; its $j$th pattern turns on the common set and the first $j$ complement points, including both endpoints. The exact attack horizon is $\lceil\log_{10/9}(N^n)\rceil+1$. These definitions provide the operational finite objects of Section 3; none assert a separating query exists.
-- source:
--   Edith Cohen, Haim Kaplan, Yishay Mansour, Shay Sapir, Uri Stemmer, Eliad Tsfadia, STOC 2027 submission #267 (October 2026), Definition 2.3, p.8; Definition 3.2 and Eq.(1), p.8; Remark 3.4/Lemma 3.5, p.9; §4.2, p.10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/267.pdf; PDF/printed pages coincide.

import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol

set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain

/-- Definition 2.3 with the history/state held fixed, as on p.4. -/
def IsNatural {X : Type} {n : ℕ} (m : Mechanism X n) : Prop :=
  ∀ s T q q', (∀ t, q (s t) = q' (s t)) → m s T q = m s T q'

/-- Remark 3.4 uses exactly the tie convention 1{a ≥ 1/2}. -/
noncomputable def responseBit (a : ℝ) : Bool := decide ((1 / 2 : ℝ) ≤ a)

noncomputable def IsBitNatural {X : Type} {n : ℕ} (m : Mechanism X n) : Prop :=
  ∀ s T q q', (∀ t, q (s t) = q' (s t)) →
    responseBit (m s T q) = responseBit (m s T q')

/-- Consistency means literal equality of every replayed real answer. -/
def Consistent {X : Type} {n : ℕ} (m : Mechanism X n)
    (s : Fin n → X) (T : Transcript (StatisticalQuery X)) : Prop :=
  replayQueries m s (T.map Prod.fst) = T

noncomputable def survivors {X : Type} [Fintype X] {n : ℕ}
    (m : Mechanism X n) (T : Transcript (StatisticalQuery X)) : Finset (Fin n → X) := by
  classical
  exact Finset.univ.filter (fun s => Consistent m s T)

noncomputable def nextSurvivors {X : Type} [Fintype X] {n : ℕ}
    (m : Mechanism X n) (T : Transcript (StatisticalQuery X))
    (q : StatisticalQuery X) (a : ℝ) : Finset (Fin n → X) := by
  classical
  exact (survivors m T).filter (fun s => m s T q = a)

/-- A single query must work for all accurate branches simultaneously. -/
noncomputable def SeparatesAccurate {X : Type} [Fintype X] {n : ℕ}
    (m : Mechanism X n) (T : Transcript (StatisticalQuery X))
    (p : PMF X) (q : StatisticalQuery X) : Prop :=
  ∀ a : ℝ, |a - populationMean p q| ≤ 1 / 10 →
    (nextSurvivors m T q a).card ≤ (9 / 10 : ℝ) * (survivors m T).card

/-- Count presence once per dataset even when sample entries repeat. -/
noncomputable def commonPoints {N n : ℕ} (H : Finset (Fin n → Fin N)) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun i =>
    (8 / 10 : ℝ) * H.card ≤ (H.filter (fun s => ∃ t, s t = i)).card)

/-- Definition 3.2: any ordering of the complement is allowed. -/
structure ThresholdPath (N : ℕ) where
  common : Finset (Fin N)
  length : ℕ
  change : Fin length ↪ Fin N
  complement : ∀ i, i ∈ common ↔ ∀ t, change t ≠ i

noncomputable def thresholdPattern {N : ℕ} (p : ThresholdPath N)
    (j : Fin (p.length + 1)) : BooleanQuery (Fin N) :=
  fun i => decide (i ∈ p.common ∨ ∃ t : Fin p.length, t.val < j.val ∧ p.change t = i)

/-- The set of common points is computed from the consistency set. -/
noncomputable def IsCommonThresholdPath {N n : ℕ} (H : Finset (Fin n → Fin N))
    (p : ThresholdPath N) : Prop := p.common = commonPoints H

/-- Exact horizon on p.10; the argument is positive in all theorem uses. -/
noncomputable def attackHorizon (n N : ℕ) : ℕ :=
  Nat.ceil (Real.log ((N : ℝ) ^ n) / Real.log (10 / 9 : ℝ)) + 1

end IsRandomnessNecessaryADA.Plain


