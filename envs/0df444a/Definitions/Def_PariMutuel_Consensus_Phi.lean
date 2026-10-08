-- Prove2me | Definitions.Def_PariMutuel_Consensus_Phi
-- name    : PariMutuel_Consensus_Phi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:03:35.050554+00:00
-- url     : https://prove2.me/theorems/3996a411-0434-453f-99cf-cdaa433ce224
-- title:
--   The Eisenberg–Gale program: $\varphi$, domain $D$ (4)–(5), maximizers, and the construction (6)–(7)
-- statement:
--   Fix a pari-mutuel market with subjective probability matrix $P=(p_{ij})$ and budgets $b_i$. The function $\varphi$ of the $mn$ variables $\xi_{ij}$ is
--
--   $$
--   \varphi(\xi_{11},\dots,\xi_{mn})=\sum_{i=1}^m b_i\log\sum_{j=1}^n p_{ij}\,\xi_{ij},
--   $$
--
--   on the domain $D$ defined by (4) $\xi_{ij}\ge 0$ for all $i,j$ and (5) $\sum_{i=1}^m \xi_{ij}=1$ for all $j$; so each column of $\xi$ is a probability vector.
--
--   With the convention $\log 0=-\infty$, a **maximizer** of $\varphi$ on $D$ is a point $\bar\xi\in D$ at which every inner sum $\sum_j p_{ij}\bar\xi_{ij}$ is positive and $\varphi(\eta)\le\varphi(\bar\xi)$ for every $\eta\in D$ whose inner sums are all positive.
--
--   From a point $\bar\xi$ the paper builds the track probabilities and bets
--
--   $$
--   \text{(6)}\ \pi_j=\max_i \frac{b_i p_{ij}}{\sum_s p_{is}\bar\xi_{is}},\qquad \text{(7)}\ \beta_{ij}=\bar\xi_{ij}\,\pi_j .
--   $$
--
--   These objects carry the paper's variational proof of existence: the EXISTENCE THEOREM says that (6)–(7) at any maximizer are equilibrium probabilities and bets.
--
--   **Formalization Note** $\varphi$ is real-valued, so at a point with a zero inner sum Lean's `Real.log 0 = 0` would give a finite value where the paper has $-\infty$. The maximizer predicate therefore requires positive inner sums at $\bar\xi$ and compares only with points of $D$ whose inner sums are positive; the excluded points have $\varphi=-\infty$ on the page and can never be larger. The maximum in (6) is `Finset.sup'` over the nonempty set of bettors. The quotient in (6) is only meaningful where the inner sums are positive, which holds at every maximizer. $D$ is written `D m n` and does not depend on $P$ or $b$.
-- source:
--   Eisenberg and Gale, Consensus of subjective probabilities: the pari-mutuel method, Ann. Math. Statist. 30(1), 1959, pp. 166–167, φ, (4)–(5), (6)–(7)

import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market

namespace PariMutuel.Consensus

/-- The domain `D` of the variational problem (p. 166): matrices `ξ = (ξ_ij)` with
(4) `ξ_ij ≥ 0` for all `i, j` and (5) `∑_{i=1}^m ξ_ij = 1` for all `j` (column sums). -/
def D (m n : ℕ) : Set (Fin m → Fin n → ℝ) :=
  {ξ | (∀ i j, 0 ≤ ξ i j) ∧ ∀ j, ∑ i, ξ i j = 1}

namespace Market

variable {m n : ℕ}

/-- The function `φ(ξ) = ∑_i b_i log ∑_j p_ij ξ_ij` (p. 166), real-valued; at points with some
inner sum zero the paper's value is `−∞`, which `IsPhiMaximizer` accounts for. -/
noncomputable def phi (M : Market m n) (ξ : Fin m → Fin n → ℝ) : ℝ :=
  ∑ i, M.b i * Real.log (∑ j, M.P i j * ξ i j)

/-- `ξ` maximizes `φ` on `D` with the paper's convention `log 0 = −∞` (p. 167): `ξ ∈ D`, every
inner sum `∑_j p_ij ξ_ij` is positive, and `φ(η) ≤ φ(ξ)` for every `η ∈ D` whose inner sums are all
positive (the points of `D` with a zero inner sum have `φ = −∞` and are never larger). -/
def IsPhiMaximizer (M : Market m n) (ξ : Fin m → Fin n → ℝ) : Prop :=
  ξ ∈ D m n ∧ (∀ i, 0 < ∑ j, M.P i j * ξ i j) ∧
  ∀ η ∈ D m n, (∀ i, 0 < ∑ j, M.P i j * η i j) → M.phi η ≤ M.phi ξ

/-- The track probabilities (6) (p. 167): `π_j = max_i b_i p_ij / ∑_s p_is ξ_is`, the maximum
over the nonempty finite set of bettors taken as `Finset.sup'`. -/
noncomputable def trackProb (M : Market m n) (ξ : Fin m → Fin n → ℝ) (j : Fin n) : ℝ :=
  Finset.univ.sup' M.univ_nonempty (fun i => M.b i * M.P i j / ∑ s, M.P i s * ξ i s)

/-- The bets (7) (p. 167): `β_ij = ξ_ij π_j` with `π_j` from (6). -/
noncomputable def bets (M : Market m n) (ξ : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) : ℝ :=
  ξ i j * M.trackProb ξ j

end Market

end PariMutuel.Consensus


