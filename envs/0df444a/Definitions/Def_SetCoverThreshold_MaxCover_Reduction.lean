-- Prove2me | Definitions.Def_SetCoverThreshold_MaxCover_Reduction
-- name    : SetCoverThreshold_MaxCover_Reduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:02:30.785697+00:00
-- url     : https://prove2.me/theorems/b44c8f16-8031-401c-88eb-42ad89cc9696
-- title:
--   The reduction of §4 with the explicit partition system of §5; weights w_r and good random strings
-- statement:
--   This file defines the max $k'$-cover instance of the proof of Theorem 5.3 (Feige, J. ACM 45(4), 1998, §4 p. 645 and §5 p. 649), built from a 3CNF-5 formula $\varphi$, the number $\ell$ of repetitions, the number $k$ of provers and a code.
--
--   1. **Explicit partition system (p. 649).** "Treat the points in a partition system as vectors in $\{0,\dots,k-1\}^L$, and let the $i$th *partition* partition the points into $k$ disjoint subsets according to their value on the $i$th coordinate." With $L=2^\ell$ the partitions are labelled by the $\ell$-bit strings, and there are $m=k^L$ points.
--   2. **Points.** "With each random string $r$, we associate a distinct partition system $B_r$" (p. 645): the points are the pairs $(r,b)$ with $r$ a random string and $b$ a point of the partition system, $N=mR$ in total, $R=(3M)^\ell$.
--   3. **Sets (p. 645).** "With each question-answer pair $(q, a)$ of prover $P_i$ … we associate a subset $S_{(q,a,i)}$ … For $r$ such that $(q, i)\in r$, consider the induced sequence of distinguished variables, and extract from $a$ on a coordinate by coordinate basis an assignment $a_r$ to this sequence of variables. One of the partitions of partition system $B_r(m, L, k, d)$ has label $a_r$. The subset $S_{(q,a,i)}$ contains the points of subset $B(r, a_r, i)$, for all $r$ with $(q, i) \in r$." Here $(q,i)\in r$ means that prover $P_i$ receives $q$ on $r$; $q$ ranges over the questions prover $i$ can receive and $a$ over canonical answers to $q$. The construction is defined for any partition system with $\ell$-bit partition labels and is instantiated with the explicit one.
--   4. **Budget $kQ$.** $Q$ is the number of possible questions to one prover (the same for all provers when all code words have weight $\ell/2$); the budget $k'=kQ$ is taken as the total number of (prover, question) pairs.
--   5. **Weights and good $r$ (pp. 646, 649).** For a collection $\mathcal C$ of sets, $w_r$ is "the number of sets that participate in covering the $m$ points of $B_r$", i.e. the number of $S_{(q,a,i)}\in\mathcal C$ with $(q,i)\in r$. In §5, "call $r$ *good* if two conditions hold: $w_r \le 3k/\epsilon$, and the $w_r$ sets that participate in covering points in the partition system $r$ contain at least two sets from the same partition":
--   $$w_r\le \frac{3k}{\varepsilon}\quad\text{and}\quad \exists\,S_{(q,a,i)},S_{(q',a',i')}\in\mathcal C:\ (q,i),(q',i')\in r,\ i\ne i',\ a_r=a'_r .$$
--
--   These objects are what Proposition 5.4, the decoding step and the gap claim are about.
--
--   **Formalization Note** The $\ell$-bit labels are used directly as the $L=2^\ell$ coordinates, so points are functions from $\ell$-bit strings to $\{0,\dots,k-1\}$. Two sets "from the same partition" are taken to contribute *distinct* subsets of it, i.e. to belong to different provers $i\ne i'$. Counts are natural numbers; the fraction of good $r$ is stated in later theorems as a count compared with a multiple of $R$.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 645 (the sets S_(q,a,i)), p. 646 (weights w_r), p. 649 (explicit partition system and good r, proof of Theorem 5.3)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem

namespace SetCoverThreshold.MaxCover

/-- The **explicit partition system of §5** (p. 649): the points are the vectors
`x : ι → Fin k` (so there are `k^{|ι|}` of them), and the partition with index `i : ι` splits
them into `k` disjoint subsets according to the value `x i` of the `i`th coordinate. Point `x`
lies in subset `cubeSystem k ι x i` of partition `i`. -/
def cubeSystem (k : ℕ) (ι : Type) : (ι → Fin k) → ι → Fin k := fun x i => x i

open Classical in
/-- The questions prover `i` may receive: the image of the random strings under `question`. -/
noncomputable def possibleQuestions (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (i : Fin k) : Finset (Question φ ℓ) :=
  Finset.univ.image (fun r => question φ code r i)

/-- The index `(q, a, i)` of a set `S_(q,a,i)` of the reduction (p. 645): a prover `i`, a
question `q` that prover `i` may receive, and a canonical answer `a` to it. -/
abbrev SetIdx (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool) : Type :=
  Σ i : Fin k, Σ q : possibleQuestions φ code i, Answer φ q.1

/-- `kQ`: the total number of (prover, question) pairs, i.e. `k` times the number `Q` of possible
questions to a single prover when that number is the same for all provers. -/
noncomputable def coverBudget (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool) : ℕ :=
  ∑ i, (possibleQuestions φ code i).card

open Classical in
/-- **The set `S_(q,a,i)` of the reduction of §4** (p. 645), for a partition system on the
points `B` whose partitions are labelled by the `ℓ`-bit strings and whose parts are labelled by
the provers (`part b p` is the part of partition `p` containing the point `b`). The points of the
instance are the pairs `(r, b)` (one copy of the partition system for each random string `r`), and
`S_(q,a,i)` contains the point `(r, b)` iff prover `i` receives `q` on `r` and `b` lies in the
`i`th subset of the partition whose label is the assignment `a_r` that `a` induces on the
distinguished variables of `r`. -/
noncomputable def reductionSet (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    {B : Type} [Fintype B] (part : B → (Fin ℓ → Bool) → Fin k) (s : SetIdx φ code) :
    Finset (RandString φ ℓ × B) :=
  Finset.univ.filter (fun x =>
    question φ code x.1 s.1 = s.2.1.1 ∧ part x.2 (answerBits (fun j => (x.1 j).2) s.2.2) = s.1)

open Classical in
/-- The points covered by a collection `C` of sets of the §5 instance: the reduction of §4 with
the explicit partition system `cubeSystem k (Fin ℓ → Bool)` (with `m = k^L` points, `L = 2^ℓ`)
in every copy. -/
noncomputable def coveredMaxCover (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (C : Finset (SetIdx φ code)) : Finset (RandString φ ℓ × ((Fin ℓ → Bool) → Fin k)) :=
  C.biUnion (reductionSet φ code (cubeSystem k (Fin ℓ → Bool)))

open Classical in
/-- `w_r`: the number of sets of the collection `C` that participate in covering points of the
partition system of `r`, i.e. the sets `S_(q,a,i) ∈ C` with `(q, i) ∈ r`. -/
noncomputable def setWeight (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (C : Finset (SetIdx φ code)) (r : RandString φ ℓ) : ℕ :=
  (C.filter (fun s => s.2.1.1 = question φ code r s.1)).card

/-- **Good random strings in §5** (p. 649): `r` is good if `w_r ≤ 3k/ε` and the sets of `C`
participating in covering points of the partition system of `r` contain two sets from the same
partition, i.e. two sets `S_(q,a,i)`, `S_(q',a',i')` with `(q,i), (q',i') ∈ r`, `i ≠ i'`, whose
answers induce the same label `a_r = a'_r`. -/
def IsGood (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool) (ε : ℝ)
    (C : Finset (SetIdx φ code)) (r : RandString φ ℓ) : Prop :=
  (setWeight φ code C r : ℝ) ≤ 3 * k / ε ∧
    ∃ s ∈ C, ∃ s' ∈ C, s.1 ≠ s'.1 ∧ s.2.1.1 = question φ code r s.1 ∧
      s'.2.1.1 = question φ code r s'.1 ∧
      answerBits (fun j => (r j).2) s.2.2 = answerBits (fun j => (r j).2) s'.2.2

open Classical in
/-- The number of good random strings. -/
noncomputable def goodCount (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool) (ε : ℝ)
    (C : Finset (SetIdx φ code)) : ℕ :=
  (Finset.univ.filter (IsGood φ code ε C)).card

end SetCoverThreshold.MaxCover


