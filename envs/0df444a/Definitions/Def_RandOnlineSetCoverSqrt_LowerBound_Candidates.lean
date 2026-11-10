-- Prove2me | Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Candidates
-- name    : RandOnlineSetCoverSqrt_LowerBound_Candidates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T19:33:31.286601+00:00
-- url     : https://prove2.me/theorems/95eb8bfc-729b-43be-a005-c4ac70c863b5
-- title:
--   Candidate families, forcing batches, expansion and exact parameters
-- statement:
--   A candidate cover is a subset $W\subseteq[m]$; a candidate family is a finite set of distinct candidates. The predicate that $C$ is $(m,k,q,r)$-union-expanding includes $1\le k\le r\le m$, $q\ge2$, the requirement that every member has size $k$, and
--
--   $$\left|\bigcup_{W\in Q}W\right|>r\quad\text{for every }Q\subseteq C\text{ with }|Q|=q.$$
--
--   A finite batch $B$ is $r$-forcing for $D$ when, for every purchased set $X$ of size at most $r$, covering every request of $B$ is equivalent to containing some member of $D$. The explicit batch lists, in a fixed algorithm-independent order, all nonempty incidences $A$ whose complement has size at most $r$ and which intersect every $W\in D$.
--
--   The exact length bound and construction parameters are
--
--   $$B(m,r)=\sum_{j=0}^{r}\binom mj,\quad k(m)=\lfloor\sqrt m\rfloor,\quad q(m)=\lceil\sqrt m\rceil,\quad r(m)=\lfloor m/32\rfloor,$$
--   $$M(m)=2^{4q(m)},\qquad H(m)=(4q(m)+1)B(m,r(m)).$$
--
--   Binomial terms beyond $m$ vanish. Natural-number division by $32$ is the displayed floor. The common horizon allows terminal padding by the universal incidence $[m]$. These definitions contain no existence or lower-bound assumption and are shared by the milestones and goal.
-- source:
--   Ilan Doron-Arad, Joseph (Seffi) Naor, STOC 2027 submission #1160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1160.pdf, §3, equation (1), Definition 3.2 and proof of Lemma 3.1, printed pp. 7–8 / PDF pp. 8–9; Lemma 3.5, printed p. 9 / PDF p. 10; proof of Theorem 1.2, printed p. 11 / PDF p. 12

import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Canonical

namespace RandOnlineSetCoverSqrt.LowerBound

abbrev Candidate (m : ℕ) := Finset (Fin m)
abbrev Family (m : ℕ) := Finset (Candidate m)

/-- Definition 3.2, printed p. 8 / PDF p. 9, including its parameter domain.
The subfamily Q represents q distinct candidates, with no disjointness requirement. -/
def UnionExpanding {m : ℕ} (k q r : ℕ) (C : Family m) : Prop :=
  1 ≤ k ∧ k ≤ r ∧ r ≤ m ∧ 2 ≤ q ∧
  (∀ W ∈ C, W.card = k) ∧
  ∀ Q ⊆ C, Q.card = q → r < (Q.biUnion id).card

/-- §3 forcing-batch definition, printed p. 8 / PDF p. 9: both directions are required. -/
def Forcing {m : ℕ} (r : ℕ) (D : Family m) (B : List (Element m)) : Prop :=
  ∀ X : Candidate m, X.card ≤ r →
    (CoversBatch X B ↔ ∃ W ∈ D, W ⊆ X)

/-- The explicit batch in the proof of Lemma 3.1, in a fixed order independent of algorithms.
Only nonempty incidences are elements of the universe. -/
noncomputable def forcingBatch {m : ℕ} (r : ℕ) (D : Family m) : List (Element m) := by
  classical
  exact ((Finset.univ : Finset (Element m)).filter
    (fun u => (Finset.univ \ u.val).card ≤ r ∧
      ∀ W ∈ D, (u.val ∩ W).Nonempty)).toList

/-- Lemma 3.1's exact length bound; binomial coefficients with j > m vanish. -/
def batchBound (m r : ℕ) : ℕ := ∑ j ∈ Finset.range (r + 1), Nat.choose m j

/-- Lemma 3.5 and Theorem 1.2 use these exact parameters, for every large integer m. -/
noncomputable def kParam (m : ℕ) : ℕ := ⌊Real.sqrt (m : ℝ)⌋₊
noncomputable def qParam (m : ℕ) : ℕ := ⌈Real.sqrt (m : ℝ)⌉₊
def rParam (m : ℕ) : ℕ := m / 32
noncomputable def familySize (m : ℕ) : ℕ := 2 ^ (4 * qParam m)

/-- Common finite horizon: all T+1 batches, followed only by universal-incidence padding. -/
noncomputable def horizon (m : ℕ) : ℕ :=
  (4 * qParam m + 1) * batchBound m (rParam m)

end RandOnlineSetCoverSqrt.LowerBound


