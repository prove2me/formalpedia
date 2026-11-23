-- Prove2me | Definitions.Def_LinearChoresCLS_SupportCE
-- name    : LinearChoresCLS_SupportCE
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:59:50.162408+00:00
-- url     : https://prove2.me/theorems/0ba92283-1b8a-4bc2-a538-577cc3da1777
-- title:
--   Finite support systems and data size for rational chores equilibria
-- statement:
--   For a finite linear chores market, a support certificate consists of prices $p_j$, agent ratios $\nu_a$, and an allocation $z_{aj}$ satisfying nonnegativity, exact earnings, market clearing, and
--   $$
--   \nu_a p_j\le d_{aj}\quad\text{for all }a,j,
--   \qquad z_{aj}>0\implies \nu_a p_j=d_{aj}.
--   $$
--   Thus $\nu_a$ is the minimum disutility per unit payment on the chores available to agent $a$. These are precisely the support conditions in the ratio characterization of individual optimality.
--
--   For rational markets, `RatChoresMarket.SupportCE` reads rational certificates in the real market. The file also defines `ratMarketDataSize`, the total Schrijver bit-size of disutilities, earnings and supplies plus the two dimensions; this is the data-size parameter used for uniform small-certificate bounds.
--
--   **Formalization Note** No support sets are stored separately: positive coordinates of $z$ determine them, avoiding duplicate support data and extensionality side conditions.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589, Definition 2.1 and the ratio characterization following Definition 2.2, p.6. Bit-size follows Del Pia–Dey–Molinaro, arXiv:1407.4798v1, §1.1, p.2, as reused in MIQPInNP.SmallSol.theorem_3.

import Mathlib
import Definitions.Def_LinearChoresCLS_ChoresSearch
import Definitions.Def_MIQPInNP_SmallSol_Setting

open scoped BigOperators
open Finset
open NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

/-- A finite complementary support system for a linear chores equilibrium. The scalar `ν a` is
agent `a`'s minimum disutility-per-payment ratio: `ν a * p j ≤ d_aj` for every chore, with equality
on every chore used with positive amount. Exact earnings and market clearing are included. -/
def ChoresMarket.SupportCE {N M : Type*} [Fintype N] [Fintype M]
    (F : ChoresMarket N M) (p : M → ℝ) (ν : N → ℝ) (z : N → M → ℝ) : Prop :=
  (∀ j, 0 ≤ p j) ∧ (∀ a, 0 ≤ ν a) ∧ (∀ a j, 0 ≤ z a j) ∧
    (∀ a j, ν a * p j ≤ F.disutil a j) ∧
    (∀ a j, 0 < z a j → ν a * p j = F.disutil a j) ∧
    (∀ a, ∑ j, p j * z a j = F.earn a) ∧
    (∀ j, ∑ a, z a j = F.supply j)

/-- The support system over a rational market with rational prices, ratios and allocation, read in
the real market by casting every coordinate. -/
def RatChoresMarket.SupportCE {nA nC : ℕ} (F : RatChoresMarket nA nC)
    (p : Fin nC → ℚ) (ν : Fin nA → ℚ) (z : Fin nA → Fin nC → ℚ) : Prop :=
  F.toReal.SupportCE (fun j => (p j : ℝ)) (fun a => (ν a : ℝ))
    (fun a j => (z a j : ℝ))

/-- Schrijver bit-size of the rational market data, with the two dimensions added explicitly so
that the size also dominates the numbers of agents and chores. -/
def ratMarketDataSize {nA nC : ℕ} (F : RatChoresMarket nA nC) : ℕ :=
  MIQPInNP.SmallSol.matSize F.disutil + MIQPInNP.SmallSol.vecSize F.earn +
    MIQPInNP.SmallSol.vecSize F.supply + nA + nC

end LinearChoresCLS


