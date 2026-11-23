-- Prove2me | Definitions.Def_BudgetAgg_NashChar_Supplement_LpModel
-- name    : BudgetAgg_NashChar_Supplement_LpModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:00:53.747806+00:00
-- url     : https://prove2.me/theorems/f9390e34-c5de-409e-a676-f19431805141
-- title:
--   Definitions 1, 4, 8–11 — ℓp utilities, efficiency, strategyproofness, single-minded profiles and proportionality
-- statement:
--   Let $N=[n]$ be the agents and $M=[m]$ the alternatives; $\Delta_m$ is the standard simplex of distributions. Each agent $i$ reports a peak $p_i\in\Delta_m$, a profile is $P=(p_1,\dots,p_n)$, and a mechanism is a map $f:(\Delta_m)^n\to\Delta_m$.
--
--   1. **$\ell_r$ utilities** (Definition 11). For every finite real exponent $r\ge1$, a peak $p$ and a distribution $q$,
--   $$u^{\ell_r}_p(q)=-\left(\sum_{j\in M}|p_j-q_j|^r\right)^{1/r}.$$
--   The two cases used by the impossibility results are
--   $$u^{\ell_1}_p(q)=-\sum_{j\in M}|p_j-q_j|,\qquad u^{\ell_\infty}_p(q)=-\max_{j\in M}|p_j-q_j|.$$
--   2. **Efficiency** (Definitions 1, 4). For a utility model $u$ (a utility for each peak), $q$ is efficient at $P$ if no distribution $q'$ has $u_{p_i}(q')\ge u_{p_i}(q)$ for all $i$ with strict inequality for some $i$; a mechanism is efficient if $f(P)$ is efficient at every $P$.
--   3. **Strategyproofness** (Definition 8 with $|N'|=1$). If $P'$ differs from $P$ only in agent $i$'s report, then $u_{p_i}(f(P))\ge u_{p_i}(f(P'))$, utilities measured at the true peak $p_i$.
--   4. **Single-minded profiles and proportionality** (Definitions 9, 10). $P$ is single-minded if every $p_{i,j}\in\{0,1\}$; $f$ is proportional if $f(P)_j=\sum_{i\in N}p_{i,j}/n$ for every single-minded $P$ and every $j$.
--
--   These are the notions of the impossibility theorems for $\ell_1$ and $\ell_\infty$ preferences (Theorems 1, 2, Lemma 5). The published Leontief notions of the base mission cannot be reused, since they are tied to Leontief utilities.
--
--   **Formalization Note** Agents and alternatives are `Fin n` and `Fin m` (0-based); distributions are points of `stdSimplex ℝ (Fin m)`, and `Profile`, `Mechanism` come from the published `BudgetAgg.NashChar.Setting`. The $\ell_\infty$ maximum is `Finset.sup'` over all of `Fin m`, which is nonempty because a distribution exists.
--   The finite exponent of `lpUtil` is a real in `Set.Ici 1`; thus its reciprocal is never evaluated at zero. The specialized `l1Util` and `lInfUtil` retain the displayed sum and maximum formulas.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, pp. 7–10, Definitions 1, 4, 8, 9, 10, 11

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

namespace BudgetAgg.NashChar.Supplement

open Finset BudgetAgg.NashChar

/-- Definition 11, pp. 9–10, for a finite exponent `r ≥ 1`: utility is the
negative `ℓr` distance to the peak. The `ℓ∞` case is `lInfUtil` below. -/
noncomputable def lpUtil {m : ℕ} (r : Set.Ici (1 : ℝ))
    (p q : stdSimplex ℝ (Fin m)) : ℝ :=
  - (∑ j, |p.1 j - q.1 j| ^ (r : ℝ)) ^ ((r : ℝ)⁻¹)

/-- `ℓ1` utility of a distribution `q` for an agent with peak `p`:
`u(q) = -∑_j |p_j - q_j|` (Definition 11, p. 10). -/
noncomputable def l1Util {m : ℕ} (p q : stdSimplex ℝ (Fin m)) : ℝ :=
  - ∑ j, |p.1 j - q.1 j|

/-- `ℓ∞` utility of a distribution `q` for an agent with peak `p`:
`u(q) = -max_j |p_j - q_j|` (Definition 11, p. 10). The maximum is over all of
`Fin m`, which is nonempty because `p` is a distribution. -/
noncomputable def lInfUtil {m : ℕ} (p q : stdSimplex ℝ (Fin m)) : ℝ :=
  - (Finset.univ : Finset (Fin m)).sup'
      ((positive_support_nonempty p).mono (Finset.filter_subset _ _))
      (fun j => |p.1 j - q.1 j|)

/-- Pareto efficiency of a distribution `q` at profile `P` for a utility model
`u (peak) (outcome)` (Definition 1, p. 7). -/
def IsEfficientFor {n m : ℕ} (u : stdSimplex ℝ (Fin m) → stdSimplex ℝ (Fin m) → ℝ)
    (P : Profile n m) (q : stdSimplex ℝ (Fin m)) : Prop :=
  ¬ ∃ q' : stdSimplex ℝ (Fin m),
    (∀ i, u (P i) q ≤ u (P i) q') ∧ (∃ i, u (P i) q < u (P i) q')

/-- Efficiency of a mechanism for a utility model (Definition 4, p. 8). -/
def IsEfficientMech {n m : ℕ} (u : stdSimplex ℝ (Fin m) → stdSimplex ℝ (Fin m) → ℝ)
    (f : Mechanism n m) : Prop :=
  ∀ P, IsEfficientFor u P (f P)

/-- Strategyproofness for a utility model (Definition 8 with `|N'| = 1`, p. 9): if
`P'` differs from `P` only in agent `i`'s report, then `i`, judged at her true peak
`P i`, weakly prefers `f P` to `f P'`. -/
def IsStrategyproofFor {n m : ℕ}
    (u : stdSimplex ℝ (Fin m) → stdSimplex ℝ (Fin m) → ℝ) (f : Mechanism n m) : Prop :=
  ∀ (i : Fin n) (P P' : Profile n m), (∀ j, j ≠ i → P' j = P j) →
    u (P i) (f P') ≤ u (P i) (f P)

/-- A single-minded profile: every entry of every peak is `0` or `1`
(Definition 9, p. 9). -/
def IsSingleMinded {n m : ℕ} (P : Profile n m) : Prop :=
  ∀ i j, (P i).1 j = 0 ∨ (P i).1 j = 1

/-- Proportionality (Definition 10, p. 9): on every single-minded profile,
`f(P)_j = ∑_i p_{i,j} / n` for every alternative `j`. -/
def IsProportional {n m : ℕ} (f : Mechanism n m) : Prop :=
  ∀ P : Profile n m, IsSingleMinded P →
    ∀ j, (f P).1 j = (∑ i, (P i).1 j) / (n : ℝ)

end BudgetAgg.NashChar.Supplement


