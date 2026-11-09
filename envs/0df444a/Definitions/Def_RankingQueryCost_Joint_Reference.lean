-- Prove2me | Definitions.Def_RankingQueryCost_Joint_Reference
-- name    : RankingQueryCost_Joint_Reference
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:24:45.571611+00:00
-- url     : https://prove2.me/theorems/dfb2a5d6-8ef3-4560-9984-c4b3e84a06dc
-- title:
--   Pivot records, reference ranks, and public quadratic certificates
-- statement:
--   A pivot tree stores its observed loser/pivot/winner partitions and terminal blocks. Consistency requires the pivot comparisons to be recorded; it does not assume accuracy. Full reference stars define observed counts $c_i$, the count-sorted order $\sigma$ with the pivot order as tie rule, and sorted full reference scores $t_j$. For true reference ranks $g_1<\cdots<g_K$, use sentinels $g_0=-1$, $g_{K+1}=n$, and
--
--   $$H(g)=\max_{p<q}(g_q-g_p)^2/(q-p),\qquad\Lambda=\sum_{U\text{ terminal}}|U|(|U|-1)^2.$$
--
--   Public intervals are exactly (17)–(18), with $D=2s$ and the same sentinels. Their spacing bound gives $V=\Lambda+4s(b-1)^2+24s\overline H$. Dense references use $T_2=\sum_{\ell=0}^{n-1}(\ell-(n/k)\#\{a\in S:t_a<\ell\})^2$ and $V=16T_2+48n^2s/k$. These are computed from the record, without a compatible-order list or a hidden rank.
--
--   **Formalization Note** Every finite maximum has an explicit zero base, harmless for these nonnegative squared ratios. Sentinel indices are included. Partial-score defaults are only used outside the full-star hypotheses of the statements.
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), §4.1, equations (15)–(19), pp. 15–18, PDF pp. 16–19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Transcript
import Definitions.Def_RankingQueryCost_Joint_Scale

set_option autoImplicit false

noncomputable section

namespace RankingQueryCost.Joint

attribute [local instance] Classical.propDecidable

/-- A pivot tree records the actual pivot partition, without an accuracy assumption. -/
inductive PivotTree (n : ℕ) where
  | leaf (objects : Finset (Fin n))
  | node (pivot : Fin n) (left right : PivotTree n)

namespace PivotTree

def objects {n : ℕ} : PivotTree n → Finset (Fin n)
  | .leaf U => U
  | .node p l r => insert p (objects l ∪ objects r)

def order {n : ℕ} : PivotTree n → List (Fin n)
  | .leaf U => U.sort (· ≤ ·)
  | .node p l r => order l ++ [p] ++ order r

def leafMass {n : ℕ} : PivotTree n → ℕ
  | .leaf U => U.card * (U.card - 1) ^ 2
  | .node _ l r => leafMass l + leafMass r

/-- Node comparisons must be present in the record. They are observed partitions,
not partitions asserted to agree with an unknown true order. -/
def Consistent {n : ℕ} (T : Transcript n) (b : ℕ) : PivotTree n → Prop
  | .leaf U => U.card ≤ b
  | .node p l r =>
    p ∉ objects l ∧ p ∉ objects r ∧ Disjoint (objects l) (objects r) ∧
    (∀ i ∈ objects l, RecordedForward T i p) ∧
    (∀ i ∈ objects r, RecordedForward T p i) ∧
    Consistent T b l ∧ Consistent T b r

end PivotTree

/-- Full stars at every selected reference, including any cached answers. -/
def StarsPresent {n : ℕ} (T : Transcript n) (S : Finset (Fin n)) : Prop :=
  ∀ e : Pair n, e.1.1 ∈ S ∨ e.1.2 ∈ S → (T e).isSome = true

/-- The observed number of wins of i against the references, excluding i itself. -/
def referenceCount {n : ℕ} (T : Transcript n) (S : Finset (Fin n)) (i : Fin n) : ℕ :=
  (S.filter fun a => RecordedForward T a i).card

/-- Sort counts, with the earlier pivot order as the public tie rule. -/
def referenceOrder {n : ℕ} (T : Transcript n) (S : Finset (Fin n))
    (prior : List (Fin n)) : Fin n → ℝ :=
  let L := (List.finRange n).mergeSort fun i j =>
    decide (referenceCount T S i < referenceCount T S j ∨
      (referenceCount T S i = referenceCount T S j ∧ prior.idxOf i ≤ prior.idxOf j))
  fun i => (L.idxOf i : ℝ)

/-- Full observed reference score, computed entirely from its acquired star. -/
def observedScore {n : ℕ} (T : Transcript n) (i : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun a => RecordedForward T a i).card

/-- Finite maximum with an explicit 0 base. All spacing terms are nonnegative. -/
def finiteMaximum (m : ℕ) (f : ℕ → ℝ) : ℝ :=
  (List.range m).foldl (fun v j => max v (f j)) 0

def trueReferenceRank {n : ℕ} (r : Rank n) (S : Finset (Fin n)) (j : ℕ) : ℝ :=
  if j = 0 then -1
  else if j = S.card + 1 then n
  else (((S.toList.map fun a => (r a : ℕ)).mergeSort (· ≤ ·))[j - 1]?.getD 0 : ℝ)

def spacingStatistic (K : ℕ) (g : ℕ → ℝ) : ℝ :=
  finiteMaximum (K + 2) fun p => finiteMaximum (K + 2) fun q =>
    if p < q then (g q - g p) ^ 2 / ((q : ℝ) - p) else 0

def sortedReferenceScore {n : ℕ} (T : Transcript n) (S : Finset (Fin n)) (j : ℕ) : ℝ :=
  (((S.toList.map (observedScore T)).mergeSort (· ≤ ·))[j - 1]?.getD 0 : ℝ)

/-- Equation (17), with sentinels. Within the source domain all denominators are positive. -/
def referenceLower {n : ℕ} (s : ℕ) (T : Transcript n) (S : Finset (Fin n)) (j : ℕ) : ℝ :=
  if j = 0 then -1 else if j = S.card + 1 then n else
  (List.range j).foldl (fun x a => max x
    (sortedReferenceScore T S (a + 1) - (2 * s : ℝ) / (j - a : ℕ))) ((j : ℝ) - 1)

/-- Equation (18), with sentinels. -/
def referenceUpper {n : ℕ} (s : ℕ) (T : Transcript n) (S : Finset (Fin n)) (j : ℕ) : ℝ :=
  if j = 0 then -1 else if j = S.card + 1 then n else
  (List.range (S.card + 1 - j)).foldl (fun x a => min x
    (sortedReferenceScore T S (j + a) + (2 * s : ℝ) / (a + 1 : ℕ)))
      ((n : ℝ) - S.card + j - 1)

/-- Equation (19); this is public data, with no compatible-order list as input. -/
def publicSpacing {n : ℕ} (s : ℕ) (T : Transcript n) (S : Finset (Fin n)) : ℝ :=
  finiteMaximum (S.card + 2) fun p => finiteMaximum (S.card + 2) fun q =>
    if p < q then (referenceUpper s T S q - referenceLower s T S p) ^ 2 /
      ((q : ℝ) - p) else 0

def sparseCertificate {n : ℕ} (s b : ℕ) (P : PivotTree n)
    (T : Transcript n) (S : Finset (Fin n)) : ℝ :=
  (P.leafMass : ℝ) + 4 * s * ((b : ℝ) - 1) ^ 2 + 24 * s * publicSpacing s T S

/-- The full observed scores of references define the dense quadratic statistic. -/
def quadraticStatistic {n : ℕ} (k : ℕ) (T : Transcript n) (S : Finset (Fin n)) : ℝ :=
  ∑ l : Fin n, ((l : ℕ) - ((n : ℝ) / k) *
    (S.filter fun a => observedScore T a < l.val).card) ^ 2

def denseCertificate {n : ℕ} (s k : ℕ) (T : Transcript n) (S : Finset (Fin n)) : ℝ :=
  16 * quadraticStatistic k T S + 24 * (2 * (n : ℝ) ^ 2 * s / k)

end RankingQueryCost.Joint


