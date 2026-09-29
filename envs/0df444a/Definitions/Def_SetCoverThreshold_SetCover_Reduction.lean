-- Prove2me | Definitions.Def_SetCoverThreshold_SetCover_Reduction
-- name    : SetCoverThreshold_SetCover_Reduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:55:05.336298+00:00
-- url     : https://prove2.me/theorems/009d91f2-135a-4349-bc44-4f63dda69dc0
-- title:
--   The set-cover instance of Section 4: subsets $S_{(q,a,i)}$ over $N=mR$ points
-- statement:
--   The reduction of Section 4 (p. 645) from the $k$-prover proof system to set cover. Fix a 3CNF-5 formula $\varphi$, $\ell$, $k$, a code, and for every random string $r$ a partition system $B_r(m,2^\ell,k,d)$.
--
--   - **Points.** "With each random string r, we associate a distinct partition system B_r(m, L, k, d) … (Altogether there are N = mR points in our set cover problem.)" A point is a pair $(r,b)$ of a random string and a point $b$ of $B_r$.
--   - **Labels.** "Each of the L partitions is labeled by an ℓ-bit string p, that corresponds to an assignment to the respective sequence of distinguished variables. Each subset in a partition is labeled by a unique prover i." The partition with label $p$ is the one whose index is $p$ read as a binary number.
--   - **Subsets.** "With each question-answer pair (q, a) of prover P_i, where 1 ≤ i ≤ k, we associate a subset S_(q,a,i) as follows: … For r such that (q, i) ∈ r, consider the induced sequence of distinguished variables, and extract from a on a coordinate by coordinate basis an assignment a_r to this sequence of variables. One of the partitions of partition system B_r(m, L, k, d) has label a_r. The subset S_(q,a,i) contains the points of subset B(r, a_r, i), for all r with (q, i) ∈ r." Here $(q,i)\in r$ means that prover $P_i$ receives question $q$ on $r$; $q$ ranges over the questions of prover $P_i$ and $a$ over canonical answers to $q$.
--   - **Q.** "Let Q denote the number of possible different questions that a prover may receive. … Hence, Q = n^{ℓ/2} · (5n/3)^{ℓ/2}."
--   - **Weights** (p. 646). For a collection $\mathcal C$ of subsets, $w_r$ is the number of members $S_{(q,a,i)}\in\mathcal C$ with $(q,i)\in r$ ("the number of subsets that participate in covering the m points of B_r(m, L, k, d)").
--
--   A collection $\mathcal C$ *covers* when every point $(r,b)$ lies in some member.
--
--   **Formalization Note** The partition systems are a family $r\mapsto B_r$, which the pairing $(r,b)$ makes disjoint. $Q$ is written $n^{\lfloor\ell/2\rfloor}M^{\lfloor\ell/2\rfloor}$ with $M=5n/3$; for a code of words of weight $\ell/2$ (and $k\ge1$) $\ell$ is even and $Q$ is exactly the number of questions of each prover.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 645, Section 4 (the reduction, Q); p. 646 (weights w_r)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem
import Definitions.Def_SetCoverThreshold_SetCover_PartitionSystem

namespace SetCoverThreshold.SetCover

/-- The labelling of the `2^ℓ` partitions of a partition system by `ℓ`-bit strings
(Feige 1998, p. 645): the bit string `p` is read as a base-2 number. -/
def labelEquiv (ℓ : ℕ) : (Fin ℓ → Bool) ≃ Fin (2 ^ ℓ) :=
  (Equiv.piCongrRight fun _ => finTwoEquiv.symm).trans finFunctionFinEquiv

namespace Formula5

variable (φ : Formula5)

/-- The questions prover `P_i` may receive: a clause on the coordinates where its code word has
bit `1`, a variable where it has bit `0`. -/
def ProverQuestion {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (i : Fin k) : Type :=
  { q : Fin ℓ → φ.QCoord // ∀ j, (q j).isLeft = code i j }

instance {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (i : Fin k) :
    Fintype (φ.ProverQuestion code i) := by
  unfold ProverQuestion; infer_instance

instance {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (i : Fin k) :
    DecidableEq (φ.ProverQuestion code i) := by
  unfold ProverQuestion; infer_instance

/-- `Q = n^{ℓ/2} · (5n/3)^{ℓ/2}`, the number of possible questions to a single prover
(Feige 1998, p. 645), written with `M = 5n/3` clauses. -/
def numQuestions (ℓ : ℕ) : ℕ := φ.n ^ (ℓ / 2) * φ.M ^ (ℓ / 2)

/-- Index set of the subsets of the §4 set-cover instance: a triple `(i, q, a)` of a prover `i`,
a question `q` of prover `i` and a canonical answer `a` to it. -/
abbrev SetIdx {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) : Type :=
  Σ i : Fin k, Σ q : φ.ProverQuestion code i, φ.Answer q.1

/-- The points of the §4 set-cover instance: pairs `(r, b)` of a random string `r` and a point
`b` of the `r`-th partition system; there are `N = mR` of them. -/
abbrev Point (ℓ m : ℕ) : Type := φ.RandomString ℓ × Fin m

/-- The subset `S_(q,a,i)` of the §4 reduction (Feige 1998, p. 645), for a family `P` of partition
systems `B_r(m, 2^ℓ, k, d)`, one per random string `r`: it contains the points of `B(r, a_r, i)`
(the `i`-th subset of the partition labelled `a_r`) for every `r` on which prover `P_i` receives
`q`, where `a_r` is the assignment that `a` induces on the distinguished variables of `r`. -/
def scSet {ℓ k m d : ℕ} (code : Fin k → Fin ℓ → Bool)
    (P : φ.RandomString ℓ → PartitionSystem m (2 ^ ℓ) k d) (x : φ.SetIdx code) :
    Finset (φ.Point ℓ m) :=
  Finset.univ.filter fun rb =>
    φ.question code rb.1 x.1 = x.2.1.1 ∧
      (P rb.1).part rb.2 (labelEquiv ℓ (φ.inducedAssignment code rb.1 x.1 x.2.2.1)) = x.1

/-- A collection `𝒞` of subsets of the §4 instance covers the `N = mR` points. -/
def IsSCCover {ℓ k m d : ℕ} (code : Fin k → Fin ℓ → Bool)
    (P : φ.RandomString ℓ → PartitionSystem m (2 ^ ℓ) k d) (𝒞 : Finset (φ.SetIdx code)) : Prop :=
  ∀ pt : φ.Point ℓ m, ∃ x ∈ 𝒞, pt ∈ φ.scSet code P x

/-- The weight `w_r = Σ_{(q,i) ∈ r} w_{q,i}` of a random string `r` with respect to a collection
`𝒞` (Feige 1998, p. 646): the number of members `S_(q,a,i)` of `𝒞` with `q` the question prover
`P_i` receives on `r`. -/
def weight {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (𝒞 : Finset (φ.SetIdx code))
    (r : φ.RandomString ℓ) : ℕ :=
  (𝒞.filter fun x => φ.question code r x.1 = x.2.1.1).card

end Formula5

end SetCoverThreshold.SetCover


