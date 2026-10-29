-- Prove2me | Definitions.Def_PochetWolsey_BacklogStartup_StartupModel
-- name    : PochetWolsey_BacklogStartup_StartupModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:30:44.021801+00:00
-- url     : https://prove2.me/theorems/2977b0a7-5ee8-4140-a17e-a5b0a0a30b2c
-- title:
--   Original and projected start-up feasible sets
-- statement:
--   Let $d_t\ge0$ be demands over periods $1,\ldots,n$, with cumulative demands $d_{kl}$. Write $p=(s,y,z)$ for stocks, setups, and start-ups. For a given initial state $y_0\in\{0,1\}$, exact start-up plans satisfy $y,z\in\{0,1\}^n$ and
--   $$z_t\ge y_t-y_{t-1},\qquad z_t\le y_t,\qquad z_t\le1-y_{t-1}.$$
--   The original lot-sizing predicate additionally requires $s,x\ge0$, $s_{t-1}+x_t=d_t+s_t$, and $x_t\le My_t$.
--
--   The Wagner–Whitin start-up set $X^{WW-U-SC}$ is defined directly by (10.14)–(10.17): nonnegative stocks, binary $y,z$, the first two start-up inequalities, and
--   $$s_{k-1}+\sum_{u=k}^l d_{ul}y_u\ge d_{kl}\quad(1\le k\le l\le n).$$
--   It does not inherit the third exact start-up inequality. The stock expression in (10.11) is
--   $$R_{kl}(d,s,y,z)=\sum_{u=k}^l d_u\left(1-y_k-\sum_{j=k+1}^u z_j\right).$$
--   The printed hull system consists of $s\ge0$, $0\le y\le1$, $z_t\ge y_t-y_{t-1}$, $z_t\le y_t$, and $s_{k-1}\ge R_{kl}$ for every interval. Its corrected counterpart adds just $z\ge0$.
--
--   These are distinct constraint-defined sets, allowing the printed hull claim and its correction to be stated separately.
--
--   **Formalization Note** No stock endpoint is fixed. The terminal stock $s_n$ remains nonnegative and otherwise unused in the projected stock inequalities. The printed system deliberately has no lower bound on $z$; that omission is the recorded defect F1. Definitions accept arbitrary data; demand signs and the meaning of sufficiently large $M$ are hypotheses of the theorems using them.
--
--   Initial-state convention: the parameter `y0` is the same fixed binary datum in every feasible set in this item (printed p. 138 / PDF 155); it is not optimized.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, pp. 319, 321, 323 (PDF 332, 334, 336), (10.5)–(10.8), (10.11), (10.14)–(10.17), Theorem 10.15; initial setup datum: p. 138 (PDF 155), Section 4.3.6

import Mathlib
import Definitions.Def_PochetWolsey_BacklogStartup_Horizon

namespace PochetWolsey.BacklogStartup

noncomputable section

/-- Coordinates are (s,y,z). -/
abbrev StartupPoint (n : ℕ) :=
  (Fin (n + 1) → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)

/-- The exact start-up constraints (10.5)-(10.8), with the given initial state y₀. -/
def ExactStartup {n : ℕ} (y0 : ℝ) (y z : Fin n → ℝ) : Prop :=
  Binary y ∧ Binary z ∧
  ∀ t ∈ Finset.Icc 1 n,
    period y t - setupState y0 y (t - 1) ≤ period z t ∧
    period z t ≤ period y t ∧
    period z t ≤ 1 - setupState y0 y (t - 1)

/-- Original balance and on/off production constraints, with arbitrary initial stock. -/
def LSStartup {n : ℕ} (y0 : ℝ) (d : Fin n → ℝ) (M : ℝ) (p : StartupPoint n)
    (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ p.1 i) ∧ (∀ i, 0 ≤ x i) ∧ ExactStartup y0 p.2.1 p.2.2 ∧
  ∀ t ∈ Finset.Icc 1 n,
    stock p.1 (t - 1) + period x t = period d t + stock p.1 t ∧
    period x t ≤ M * period p.2.1 t

/-- The right-hand side of (10.11). -/
def startupStockRHS {n : ℕ} (d : Fin n → ℝ) (p : StartupPoint n)
    (k l : ℕ) : ℝ :=
  ∑ u ∈ Finset.Icc k l,
    period d u * (1 - period p.2.1 k - ∑ j ∈ Finset.Icc (k + 1) u, period p.2.2 j)

/-- The original WW-U-SC feasible set, (10.14)-(10.17). -/
def WWStartup {n : ℕ} (y0 : ℝ) (d : Fin n → ℝ) : Set (StartupPoint n) :=
  {p | (∀ i, 0 ≤ p.1 i) ∧ Binary p.2.1 ∧ Binary p.2.2 ∧
    (∀ t ∈ Finset.Icc 1 n,
      period p.2.1 t - setupState y0 p.2.1 (t - 1) ≤ period p.2.2 t ∧
      period p.2.2 t ≤ period p.2.1 t) ∧
    (∀ k ∈ Finset.Icc 1 n, ∀ l ∈ Finset.Icc k n,
      demandSum d k l ≤ stock p.1 (k - 1) +
        ∑ u ∈ Finset.Icc k l, demandSum d u l * period p.2.1 u)}

/-- The literal listed system of Theorem 10.15: no lower bound on z. -/
def PrintedStartupHull {n : ℕ} (y0 : ℝ) (d : Fin n → ℝ) : Set (StartupPoint n) :=
  {p | (∀ i, 0 ≤ p.1 i) ∧ UnitBox p.2.1 ∧
    (∀ t ∈ Finset.Icc 1 n,
      period p.2.1 t - setupState y0 p.2.1 (t - 1) ≤ period p.2.2 t ∧
      period p.2.2 t ≤ period p.2.1 t) ∧
    (∀ k ∈ Finset.Icc 1 n, ∀ l ∈ Finset.Icc k n,
      startupStockRHS d p k l ≤ stock p.1 (k - 1))}

/-- The correction isolated from the printed system: add only z ≥ 0. -/
def CorrectedStartupHull {n : ℕ} (y0 : ℝ) (d : Fin n → ℝ) : Set (StartupPoint n) :=
  {p | p ∈ PrintedStartupHull y0 d ∧ ∀ t, 0 ≤ p.2.2 t}

end
end PochetWolsey.BacklogStartup


