-- Prove2me | Definitions.Def_MusicStreaming_CoreSelection_Setting
-- name    : MusicStreaming_CoreSelection_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:40.800544+00:00
-- url     : https://prove2.me/theorems/af9b9905-dfc9-4039-8978-6b5ebdac737c
-- title:
--   §2–§4, pp. 7–14 — streaming problems, user-centric index, rewards, the streaming game, A(N, M, t), the domain 𝒫* and the axioms of Theorem 3
-- statement:
--   This module fixes the model of Bergantiños and Moreno-Ternero for Theorem 3.
--
--   **Problems.** There are $n$ artists $N$ and a population of potential users. A **streaming problem** $(N, M, t)$ records, for each user $j$ of a finite set $M$ and each artist $i \in N$, the number $t_{ij} \in \mathbb N$ of times user $j$ played artist $i$. Every user of $M$ has played some artist (the paper's standing assumption $L^j \neq \emptyset$). For a user $j$ write
--   $$
--   T^j = \sum_{i \in N} t_{ij}, \qquad L^j = \{ i \in N : t_{ij} > 0 \}
--   $$
--   for the total streams of $j$ and the list of artists $j$ played.
--
--   **Indices and rewards.** A **popularity index** $I$ assigns to every problem a vector $I(N,M,t) \in \mathbb R^N$. Each user pays $1$, so $m = |M|$ is shared, and artist $i$ receives
--   $$
--   R^I_i(N,M,t) = \frac{I_i(N,M,t)}{\sum_{i' \in N} I_{i'}(N,M,t)}\, m .
--   $$
--   The **user-centric index** is $U_i(N,M,t) = \sum_{j \in M} t_{ij}/T^j$.
--
--   **The streaming game.** To each problem corresponds the TU game on the artists $v(S) = |\{ j \in M : L^j \subseteq S \}|$, the number of users who only played artists in $S$; its core is $C(N,v) = \{x : \sum_{i\in N} x_i = v(N),\ \sum_{i \in S} x_i \ge v(S) \text{ for all } S \subseteq N\}$. The set $A(N,M,t)$ consists of the vectors $x = \sum_{j \in M} x^j$ where each $x^j \in \mathbb R^N$ is nonnegative, vanishes outside $L^j$ and sums to $1$.
--
--   **The domain $\mathcal P^*$ and the axioms.** A problem is in $\mathcal P^*$ when no user of it has played every artist: $L^j \neq N$ for all $j \in M$. On $\mathcal P^*$ an index is required to be nonnegative with positive total on every problem with at least one user, and the three axioms of Theorem 3 read:
--
--   1. **Homogeneity.** If $\lambda \ge 0$ and $t_{ij} = \lambda t_{i'j}$ for all $j \in M$, then $I_i(N,M,t) = \lambda I_{i'}(N,M,t)$.
--   2. **Additivity.** If $M = M^1 \cup M^2$ with $M^1 \cap M^2 = \emptyset$ and $t$ agrees with $t^1$ on $M^1$ and with $t^2$ on $M^2$, then $I(N,M,t) = I(N,M^1,t^1) + I(N,M^2,t^2)$.
--   3. **Core selection.** $R^I(N,M,t) \in C(N,v)$.
--
--   These objects are the vocabulary of Theorem 3 and of every step of its proof.
--
--   **Formalization Note** Artists are `Fin n` (artist $i$ of the paper is index $i-1$), users are natural numbers, and a problem is a finitely supported map $t : \mathbb N \to_0 (\mathrm{Fin}\ n \to \mathbb N)$ whose support is $M$; so a user belongs to the problem exactly when its column is nonzero, which builds in $L^j \neq \emptyset$, and streams are natural numbers. Removing users and splitting problems are done on the finsupp, so an index can only see the columns of the users of the problem. The core is the published `Supermodularity.Cooperative.Core` on `Finset.univ`. Additivity is stated for disjoint user groups: the page's "$M = M^1 \cup M^2$" without disjointness would force $I = 2I$ for $M^1 = M^2$, and no index would satisfy it; every proof in the paper uses disjoint splits. The domain $\mathcal P^*$ is read as the proof of Theorem 3 uses it (the proof applies the axioms to one- and two-user problems "in $\mathcal P^*$" and draws a third user from the population): no user plays every artist, and "at least three users" is a property of the user population $\mathbb N$, which is infinite. The problem layer (`Problem`, `userTotal`, `listened`, `Index`, `reward`) comes from the shared module `MusicStreaming.Axioms.Setting`, and `game`, `allocSet` from the shared module `MusicStreaming.Core.Setting`; `userCentric` is restated here with the same body as the shared one.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, pp. 7–14, §2 (problems, T^j, L^j, index, reward R^I, user-centric U), §3 p. 11 (homogeneity, additivity), §4 pp. 13–14 (game v, core C(N, v), A(N, M, t), core selection, 𝒫*)

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MusicStreaming_Axioms_Setting
import Definitions.Def_MusicStreaming_Core_Setting

namespace MusicStreaming.CoreSelection

/-- The user-centric index `U_i = ∑_{j ∈ M} t_ij / T^j` (p. 9). -/
noncomputable def userCentric {n : ℕ} (t : MusicStreaming.Axioms.Problem n) (i : Fin n) : ℝ :=
  ∑ j ∈ t.support, (t j i : ℝ) / (MusicStreaming.Axioms.userTotal t j : ℝ)

/-- The domain `𝒫*` as the proof of Theorem 3 uses it (p. 14, pp. 23–25): no user of the problem
has played every artist. The clause "at least three users" is read as a property of the user
population, which is the infinite set `ℕ`. -/
def InPStar {n : ℕ} (t : MusicStreaming.Axioms.Problem n) : Prop :=
  ∀ j ∈ t.support, MusicStreaming.Axioms.listened t j ≠ Finset.univ

/-- The index requirements of p. 8 on `𝒫*`: nonnegative, with positive total on every nonempty
problem. -/
def IsIndexOn {n : ℕ} (I : MusicStreaming.Axioms.Index n) : Prop :=
  ∀ t : MusicStreaming.Axioms.Problem n, InPStar t → t ≠ 0 → (∀ i, 0 ≤ I t i) ∧ 0 < ∑ i, I t i

/-- Homogeneity (p. 11) on `𝒫*`: if `t_ij = λ t_{i'j}` for all `j ∈ M` with `λ ≥ 0`, then
`I_i = λ I_{i'}`. -/
def HomogeneityOn {n : ℕ} (I : MusicStreaming.Axioms.Index n) : Prop :=
  ∀ (t : MusicStreaming.Axioms.Problem n) (i i' : Fin n) (c : ℝ), InPStar t → 0 ≤ c →
    (∀ j ∈ t.support, (t j i : ℝ) = c * t j i') → I t i = c * I t i'

/-- Additivity (p. 11) on `𝒫*`, for a split of the users into two disjoint groups. -/
def AdditivityOn {n : ℕ} (I : MusicStreaming.Axioms.Index n) : Prop :=
  ∀ t₁ t₂ : MusicStreaming.Axioms.Problem n, InPStar t₁ → InPStar t₂ → Disjoint t₁.support t₂.support →
    I (t₁ + t₂) = I t₁ + I t₂

/-- Core selection (p. 14) on `𝒫*`: the rewards lie in the core `C(N, v)` of the streaming game. -/
def CoreSelectionOn {n : ℕ} (I : MusicStreaming.Axioms.Index n) : Prop :=
  ∀ t : MusicStreaming.Axioms.Problem n, InPStar t →
    MusicStreaming.Axioms.reward I t ∈ Supermodularity.Cooperative.Core Finset.univ (MusicStreaming.Core.game t)

end MusicStreaming.CoreSelection


