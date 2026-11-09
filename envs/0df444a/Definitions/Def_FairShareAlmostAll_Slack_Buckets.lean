-- Prove2me | Definitions.Def_FairShareAlmostAll_Slack_Buckets
-- name    : FairShareAlmostAll_Slack_Buckets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:36.807045+00:00
-- url     : https://prove2.me/theorems/71e3d3d7-5288-47d1-8c71-252366b8a843
-- title:
--   Prescribed buckets, reserves, buffers, cutoffs and requests
-- statement:
--   Fix integer $q\ge16$. The prescribed sizes are $w_h=\lceil q(1+1/q)^{h-1}\rceil$, and $H$ is the least positive index whose cumulative size reaches $m$. Consecutive buckets contain those ranks, with the last bucket truncated at $m$.
--
--   Reserve ranks are $1,1+q,1+2q,\ldots$ in paper notation. Each $E_h$ consists of the first $\lfloor |C_h|/q\rfloor$ nonreserve goods of $C_h$, and $S=M\setminus(R\cup E)$, $S_h=S\cap C_h$. The cutoff $h_i$ is the first full bucket of size at least $q/b_i$, or $H$; $T_i$ contains later buckets. Define
--   $$\lambda_{iP}=\begin{cases}u_i(P\cap T_i)/u_i(T_i)&u_i(T_i)>0,\\0&u_i(T_i)=0,\end{cases}\quad d_{j,iP}=\begin{cases}|P\cap C_j|&j\le h_i,\\|C_j|\lambda_{iP}&j>h_i.\end{cases}$$
--   Configurations have capped value at least one and avoid $C_1$. Construction assumptions contain only the section's standing hypotheses; bucket and buffer well-definedness remain theorem conclusions. Goods use zero-based indices, so reserve membership is $g\bmod q=0$.
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 7 (PDF p. 8), §2–§2.2, printed pp. 7–9 (PDF pp. 8–10); source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance

namespace FairShareAlmostAll.Slack

noncomputable def prescribedSize (q h : ℕ) : ℕ :=
  ⌈(q : ℝ) * (1 + 1 / (q : ℝ)) ^ (h - 1)⌉₊

noncomputable def prefixSize (q h : ℕ) : ℕ :=
  ∑ k ∈ Finset.range h, prescribedSize q (k + 1)

/-- Nat infimum is the least admissible positive index; bucket_supply proves existence. -/
noncomputable def bucketCount (q m : ℕ) : ℕ :=
  sInf {h : ℕ | 0 < h ∧ m ≤ prefixSize q h}

noncomputable def bucket (q m h : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun g => prefixSize q (h - 1) ≤ g.val ∧ g.val < prefixSize q h)

def reserve (q m : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun g => g.val % q = 0)

/-- First floor(|C_h|/q) nonreserve ranks; cardinality is a theorem, not an axiom. -/
noncomputable def buffer (q m h : ℕ) : Finset (Fin m) := by
  classical
  let available := bucket q m h \ reserve q m
  exact available.filter (fun g => (available.filter (fun r => r < g)).card < (bucket q m h).card / q)

noncomputable def allBuffers (q m : ℕ) : Finset (Fin m) := by
  classical
  exact (Finset.Icc 1 (bucketCount q m)).biUnion (buffer q m)

noncomputable def ordinary (q m : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ \ (reserve q m ∪ allBuffers q m)

noncomputable def ordinaryBucket (q m h : ℕ) : Finset (Fin m) := by
  classical
  exact ordinary q m ∩ bucket q m h

noncomputable def cutoff {n m : ℕ} (X : Instance n m) (q : ℕ) (i : Fin n) : ℕ :=
  sInf {h : ℕ | 1 ≤ h ∧ h ≤ bucketCount q m ∧
    (h = bucketCount q m ∨ (bucket q m h).card ≥ (q : ℝ) / X.entitlement i)}

noncomputable def tail {n m : ℕ} (X : Instance n m) (q : ℕ) (i : Fin n) : Finset (Fin m) := by
  classical
  exact ((Finset.Icc 1 (bucketCount q m)).filter (fun h => cutoff X q i < h)).biUnion (bucket q m)

noncomputable def tailFraction {n m : ℕ} (X : Instance n m) (q : ℕ) (i : Fin n)
    (P : Finset (Fin m)) : ℝ := by
  classical
  exact if 0 < cappedValue X i (tail X q i)
    then cappedValue X i (P ∩ tail X q i) / cappedValue X i (tail X q i) else 0

noncomputable def request {n m : ℕ} (X : Instance n m) (q j : ℕ) (i : Fin n)
    (P : Finset (Fin m)) : ℝ := by
  classical
  exact if j ≤ cutoff X q i then ((P ∩ bucket q m j).card : ℝ)
    else (bucket q m j).card * tailFraction X q i P

noncomputable def Configuration {n m : ℕ} (X : Instance n m) (q : ℕ) (i : Fin n)
    (P : Finset (Fin m)) : Prop :=
  1 ≤ cappedValue X i P ∧ Disjoint P (bucket q m 1)

/-- Exactly the standing model and Section 2 assumptions, no derived invariant. -/
noncomputable def ConstructionAssumptions {n m : ℕ} (X : Instance n m) (q : ℕ) : Prop :=
  2 ≤ n ∧ 16 ≤ q ∧ totalEntitlement X ≤ 1 ∧
  (∀ i, X.entitlement i ≤ 1 / (q : ℝ)^2) ∧ (active X).Nonempty ∧
  ∀ i, Antitone (X.value i)

end FairShareAlmostAll.Slack


