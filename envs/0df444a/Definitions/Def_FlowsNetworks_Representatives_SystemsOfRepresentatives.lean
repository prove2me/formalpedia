-- Prove2me | Definitions.Def_FlowsNetworks_Representatives_SystemsOfRepresentatives
-- name    : FlowsNetworks_Representatives_SystemsOfRepresentatives
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:47.543774+00:00
-- url     : https://prove2.me/theorems/20bf51c0-1472-4425-94dd-f8c469d50a47
-- title:
--   Families of subsets, the index set I(X), and systems of distinct, restricted and common representatives
-- statement:
--   Following Chapter II, §10 of Ford and Fulkerson's *Flows in Networks*, this file sets up the objects of the set-representative theorems.
--
--   1. The **fundamental set** is $E = \{e_1, \dots, e_m\}$; the element $e_i$ is identified with its index $i \in \{1, \dots, m\}$. A **family** $\mathcal S = \{S_1, \dots, S_n\}$ is a list of $n$ subsets of $E$ indexed by $j = 1, \dots, n$; different indices may carry the same set.
--   2. For $X \subseteq \{1, \dots, n\}$, $I(X) \subseteq \{1, \dots, m\}$ is the **index set** of $\bigcup_{j \in X} S_j$; in particular $I(\emptyset) = \emptyset$.
--   3. A **list of representatives** is a choice $r_1, \dots, r_n$ of elements, $r_j$ representing $S_j$. The number of **occurrences** of $e_i$ in the list is the number of indices $j$ with $r_j = e_i$.
--   4. A **system of distinct representatives (SDR)** for $\mathcal S$ is a list with $r_j \in S_j$ for every $j$ and $r_1, \dots, r_n$ pairwise distinct.
--   5. Given integers $0 \le a_i \le a'_i$, a **system of restricted representatives (SRR)** for $\mathcal S$ in which $e_i$ occurs at least $a_i$ and at most $a'_i$ times is a list with $r_j \in S_j$ for every $j$ (not necessarily distinct) in which each $e_i$ occurs at least $a_i$ and at most $a'_i$ times.
--   6. For a second family $\mathcal T = \{T_1, \dots, T_n\}$ of the same length, a **common SRR** is a single list $r_1, \dots, r_n$ together with a permutation $\sigma$ of $\{1, \dots, n\}$ such that $r_j \in S_j$ and $r_j \in T_{\sigma(j)}$ for every $j$ (each representative represents one set of $\mathcal S$ and one set of $\mathcal T$, and every set of either family is represented exactly once), with each $e_i$ occurring at least $a_i$ and at most $a'_i$ times. A **common SDR** is such a list whose entries are pairwise distinct.
--   7. The **permutation matrix** of a permutation $\sigma$ of $\{1, \dots, n\}$ is the $n \times n$ matrix with entry $1$ in position $(i, j)$ when $\sigma(i) = j$ and $0$ otherwise.
--
--   These objects carry every statement of the mission: Hall's theorem and its corollaries, the existence theorem for systems of restricted representatives, the marginal-element theorems, the common-SRR theorem and the partition-constrained SDR theorem.
--
--   **Formalization Note** $E$ is `Fin m`, a family is `Fin n → Finset (Fin m)`, and a list of representatives is a function `r : Fin n → Fin m` (indices start at $0$). The bounds $a_i, a'_i$ are natural numbers: the page states only $0 \le a_i \le a'_i$, and integrality is implicit in counting occurrences. A common SRR is a pair `(r, σ)` with `σ : Equiv.Perm (Fin n)`, which encodes the network of Fig. 10.2 (p. 64): each unit of flow passes through one $S_j$, one element $e_i$ and one $T_k$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, pp. 54–55 (§10, SDR), p. 59 (SRR), pp. 63–64 (common SRR, Fig. 10.2)

import Mathlib

namespace FlowsNetworks.Representatives

/-! Systems of representatives (Ford–Fulkerson, *Flows in Networks*, Chapter II, §10,
pp. 54–55, 59, 63–64). The fundamental set `E = {e₁, …, e_m}` is `Fin m` (the element `eᵢ` is the
index `i`), and a family `𝒮 = {S₁, …, S_n}` of subsets of `E` is an indexed family
`S : Fin n → Finset (Fin m)`; different indices may carry the same set. A system of
representatives is a list `r₁, …, r_n` of elements, written as a function `r : Fin n → Fin m`,
where `r j` represents `S j`. -/

/-- `I(X) ⊆ {1, …, m}`: the index set of the union `⋃_{j ∈ X} S_j` of the sets of the family with
indices in `X` (empty when `X` is empty). -/
def indexSet {m n : ℕ} (S : Fin n → Finset (Fin m)) (X : Finset (Fin n)) : Finset (Fin m) :=
  X.biUnion S

/-- The number of times the element `eᵢ` occurs in the list of representatives `r₁, …, r_n`, i.e.
the number of indices `j` with `r j = i`. -/
def occurrences {m n : ℕ} (r : Fin n → Fin m) (i : Fin m) : ℕ :=
  (Finset.univ.filter (fun j => r j = i)).card

/-- `r` is a system of distinct representatives (SDR) for `𝒮 = {S₁, …, S_n}` (p. 55): the
representatives `r₁, …, r_n` are distinct elements of `E` and `r j ∈ S j` for every `j`. -/
def IsSDR {m n : ℕ} (S : Fin n → Finset (Fin m)) (r : Fin n → Fin m) : Prop :=
  Function.Injective r ∧ ∀ j, r j ∈ S j

/-- `r` is a system of restricted representatives (SRR) for `𝒮 = {S₁, …, S_n}` in which `eᵢ`
occurs at least `a i` and at most `a' i` times (p. 59): `r j ∈ S j` for every `j`, the
representatives need not be distinct, and every element `eᵢ` occurs among `r₁, …, r_n` at least
`a i` and at most `a' i` times. -/
def IsSRR {m n : ℕ} (S : Fin n → Finset (Fin m)) (a a' : Fin m → ℕ) (r : Fin n → Fin m) : Prop :=
  (∀ j, r j ∈ S j) ∧ ∀ i, a i ≤ occurrences r i ∧ occurrences r i ≤ a' i

/-- `(r, σ)` is a common SRR for `𝒮 = {S₁, …, S_n}` and `𝒯 = {T₁, …, T_n}` in which `eᵢ` occurs at
least `a i` and at most `a' i` times (pp. 63–64, the network of Fig. 10.2): one list of `n`
representatives `r₁, …, r_n`, where `r j` represents `S j` and also `T (σ j)`, for a permutation
`σ` of `{1, …, n}` (so every `S_j` and every `T_k` is represented exactly once), and every
element `eᵢ` occurs in the list at least `a i` and at most `a' i` times. -/
def IsCommonSRR {m n : ℕ} (S T : Fin n → Finset (Fin m)) (a a' : Fin m → ℕ)
    (r : Fin n → Fin m) (σ : Equiv.Perm (Fin n)) : Prop :=
  (∀ j, r j ∈ S j ∧ r j ∈ T (σ j)) ∧ ∀ i, a i ≤ occurrences r i ∧ occurrences r i ≤ a' i

/-- `(r, σ)` is a common SDR for `𝒮 = {S₁, …, S_n}` and `𝒯 = {T₁, …, T_n}` (p. 67): the
representatives `r₁, …, r_n` are distinct, and `r j` represents both `S j` and `T (σ j)` for a
permutation `σ` of `{1, …, n}`. -/
def IsCommonSDR {m n : ℕ} (S T : Fin n → Finset (Fin m)) (r : Fin n → Fin m)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  Function.Injective r ∧ ∀ j, r j ∈ S j ∧ r j ∈ T (σ j)

/-- The `n × n` permutation matrix of `σ`: its `(i, j)` entry is `1` if `σ i = j` and `0`
otherwise. -/
def permMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => if σ i = j then 1 else 0

end FlowsNetworks.Representatives


