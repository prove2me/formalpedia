-- Prove2me | Definitions.Def_ForkJoinCtrl_Tracking_Network
-- name    : ForkJoinCtrl_Tracking_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:10.19649+00:00
-- url     : https://prove2.me/theorems/2991712d-6212-42cf-907b-3b6aef041556
-- title:
--   §2, pp. 5–8 — the multiclass fork-join network with shared and dedicated servers, its rates and holding costs
-- statement:
--   A **fork-join network** has $J\ge 1$ job types $\mathcal J=\{1,\dots,J\}$, $I$ shared servers $\mathcal I=\{1,\dots,I\}$ and a finite set of dedicated servers. An incidence $P_{ij}\in\{0,1\}$ records whether shared server $i$ processes type $j$ jobs; $\mathcal I_j=\{i: P_{ij}=1\}$ and $\mathcal J_i=\{j : P_{ij}=1\}$. Each dedicated server $k$ belongs to exactly one job type, and $\mathcal K_j$ is the (possibly empty) set of dedicated servers of type $j$; the sets $\mathcal K_j$ are pairwise disjoint. Every arriving type $j$ job forks into one task for each server in $\mathcal K_j\cup\mathcal I_j$ and leaves when all of them are done.
--
--   The standing structure of §2 is part of the definition:
--
--   1. $|\mathcal I_j|\ge 1$ for every $j$ and $|\mathcal J_i|\ge 2$ for every $i$;
--   2. limiting arrival rates $\lambda_j>0$, dedicated service rates $\mu_k>0$, shared service rates $\mu_{ij}>0$ for $i\in\mathcal I_j$;
--   3. holding cost rates $h_j\ge 0$ with $\max_j h_j>0$;
--   4. squared coefficients of variation $\beta_j^2$ (inter-arrival times), $\sigma_k^2$, $\sigma_{ij}^2$ (service times), tied to the primitives in the model.
--
--   The file also defines, for a type $j$, the maximum $\max_{k\in\mathcal K_j} q_k\vee\max_{i\in\mathcal I_j} q_i$ (well defined because $\mathcal I_j\neq\emptyset$), the partial sums $\sum_{l=1}^n x_l$ with the paper's index base, and the renewal counting map $t\mapsto\sup\{n\in\mathbb N:\sum_{l=1}^n x_l\le t\}$ of §2.1.
--
--   **Formalization Note** Indices are 0-based (`Fin J`, `Fin I`, `Fin K`); the owner map `own : Fin K → Fin J` encodes the sets $\mathcal K_j$. The counting map is $\mathbb N$-valued via `sSup`; it returns the junk value $0$ only when the partial sums stay bounded, which for the paper's strictly positive i.i.d. primitives is a null event.
-- source:
--   Özkan, Control of Fork-Join Processing Networks with Multiple Job Types and Parallel Shared Resources, arXiv:2002.01496v1, pp. 5–6, §1.2, §2, §2.1; p. 8, §2.3

import Mathlib

namespace ForkJoinCtrl.Tracking

open scoped BigOperators

/-!
Özkan, *Control of Fork-Join Processing Networks with Multiple Job Types and Parallel Shared
Resources*, arXiv:2002.01496v1, §1.2 (p. 5), §2 (pp. 5–6), §2.3 (p. 8): the network structure,
its constants, and the partial-sum / renewal-counting maps of §2.1 (p. 6).

Indexing is 0-based: the job types `𝒥 = {1, …, J}` are `Fin J`, the shared servers
`ℐ = {1, …, I}` are `Fin I`, and the dedicated servers (all `𝒦_j` together) are `Fin K`.
-/

/-- A fork-join network with `J` job types, `I` shared servers and `K` dedicated servers
(§2, pp. 5–6), with the constants of §2.1 and §2.3.

* `own k` is the job type served by dedicated server `k`, so `𝒦_j = {k | own k = j}`; these sets
  are pairwise disjoint and may be empty (`K_j = 0`).
* `P i j = true` iff type `j` jobs are processed in shared server `i` (`P_ij = 1`).
* Standing structure (p. 5): `J ∈ ℕ₊`, `|ℐ_j| ≥ 1` for every `j`, `|𝒥_i| ≥ 2` for every `i`.
* `lam j = λ_j > 0` (limiting arrival rate), `muK k = µ_k > 0`, `mu i j = µ_ij > 0` for the
  incident pairs (p. 6).
* `h j = h_j ≥ 0` with `max_j h_j > 0` (holding cost rates, p. 8).
* `beta2 j = β_j²`, `sig2K k = σ_k²`, `sig2 i j = σ_ij²`: the squared coefficients of variation of
  the inter-arrival and service times (p. 6); they are tied to the primitives in `Model`. -/
structure Network where
  J : ℕ
  I : ℕ
  K : ℕ
  own : Fin K → Fin J
  P : Fin I → Fin J → Bool
  lam : Fin J → ℝ
  muK : Fin K → ℝ
  mu : Fin I → Fin J → ℝ
  h : Fin J → ℝ
  beta2 : Fin J → ℝ
  sig2K : Fin K → ℝ
  sig2 : Fin I → Fin J → ℝ
  J_pos : 0 < J
  exists_server : ∀ j : Fin J, ∃ i : Fin I, P i j = true
  two_le_card_types : ∀ i : Fin I, 2 ≤ (Finset.univ.filter (fun j : Fin J => P i j = true)).card
  lam_pos : ∀ j, 0 < lam j
  muK_pos : ∀ k, 0 < muK k
  mu_pos : ∀ i j, P i j = true → 0 < mu i j
  h_nonneg : ∀ j, 0 ≤ h j
  h_max_pos : ∃ j, 0 < h j

variable (N : Network)

/-- `ℐ_j = {i ∈ ℐ : P_ij = 1}`, the shared servers that process type `j` jobs (p. 5). -/
def Network.Ij (j : Fin N.J) : Finset (Fin N.I) :=
  Finset.univ.filter (fun i => N.P i j = true)

/-- `𝒥_i = {j ∈ 𝒥 : P_ij = 1}`, the job types processed in shared server `i` (p. 5). -/
def Network.Ji (i : Fin N.I) : Finset (Fin N.J) :=
  Finset.univ.filter (fun j => N.P i j = true)

/-- `𝒦_j`, the dedicated servers associated with type `j` jobs (p. 5). -/
def Network.Kj (j : Fin N.J) : Finset (Fin N.K) :=
  Finset.univ.filter (fun k => N.own k = j)

theorem Network.Ij_nonempty (j : Fin N.J) : (N.Ij j).Nonempty := by
  obtain ⟨i, hi⟩ := N.exists_server j
  exact ⟨i, by simp [Network.Ij, hi]⟩

/-- `max_{k ∈ 𝒦_j} q_k ∨ max_{i ∈ ℐ_j} q_i`: the maximum of the values `qk k` over the dedicated
servers of type `j` and `qi i` over the shared servers of type `j` (the set of values is nonempty
because `ℐ_j ≠ ∅`; when `𝒦_j = ∅` only the shared-server values enter). -/
noncomputable def Network.jobMax (j : Fin N.J) (qk : Fin N.K → ℝ) (qi : Fin N.I → ℝ) : ℝ :=
  ((N.Kj j).image qk ∪ (N.Ij j).image qi).max'
    (Finset.Nonempty.mono Finset.subset_union_right ((N.Ij_nonempty j).image qi))

/-- Partial sums with the paper's index base: `partialSum x n = ∑_{l=1}^{n} x_l`, so
`partialSum x 0 = 0` (p. 6: `U_j(0) := 0`, `U_j(n) := ∑_{l=1}^n u_{jl}`). -/
def partialSum (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 n, x l

/-- The renewal counting map `count x t = sup {n ∈ ℕ : partialSum x n ≤ t}` (p. 6: `A_j`, `S_k`,
`S_ij`). For `t ≥ 0` the set contains `0`. If the set is unbounded (the partial sums stay bounded,
which for the strictly positive i.i.d. primitives of the paper happens only on a null set), Lean's
`sSup` on `ℕ` returns the junk value `0`. -/
noncomputable def count (x : ℕ → ℝ) (t : ℝ) : ℕ :=
  sSup {n : ℕ | partialSum x n ≤ t}

end ForkJoinCtrl.Tracking


