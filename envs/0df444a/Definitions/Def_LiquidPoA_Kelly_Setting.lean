-- Prove2me | Definitions.Def_LiquidPoA_Kelly_Setting
-- name    : LiquidPoA_Kelly_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:11.47864+00:00
-- url     : https://prove2.me/theorems/bc8b67b1-f936-4026-86cd-dd9732367c38
-- title:
--   Sections 2 and 4 — Kelly games, equilibrium, liquid welfare, and worst-case games
-- statement:
--   Fix a resource allocation mechanism $M$ with $n$ users. A **resource allocation game** gives each user $i$ a **valuation** $v_i:[0,1]\to\mathbb R_{\ge0}$ that is non-decreasing, concave and differentiable, and a **budget** $c_i\in\mathbb R_{\ge0}\cup\{+\infty\}$. User $i$'s utility at $s$ is $u_i(s)=v_i(g^M_i(s))-p^M_i(s)$ if $p^M_i(s)\le c_i$, and $-\infty$ otherwise. A **(pure Nash) equilibrium** is a signal vector $s$ such that for every user $i$, $s_i$ maximizes $y\mapsto u_i(y,s_{-i})$ over $y\ge 0$; eq$(\mathcal G^M)$ is the set of equilibria.
--
--   The **liquid welfare** of an allocation $d$, the optimum, and the **liquid price of anarchy** of a game and of the mechanism are
--
--   $$
--   LW(d)=\sum_{i=1}^n\min\{v_i(d_i),c_i\},\quad LW^*=\sup_{d\in\mathcal Q\cup\{\mathbf 0\}}LW(d),\quad
--   LPoA(\mathcal G^M)=\sup_{s\in eq(\mathcal G^M)}\frac{LW^*}{LW(g^M(s))},\quad LPoA(M)=\sup_{\mathcal G^M}LPoA(\mathcal G^M).
--   $$
--
--   The file also defines:
--
--   1. the **Kelly mechanism**, $g^{Kelly}_i(s)=s_i/\sum_j s_j$ and $p^{Kelly}_i(s)=s_i$ (pp. 7, 9);
--   2. the class $\mathcal C$ (p. 14): $y\mapsto g^M_i(y,s_{-i})$ concave and $y\mapsto p^M_i(y,s_{-i})$ convex on $[0,\infty)$ whenever some other signal is positive;
--   3. the coefficient $\lambda^M_i(s)=\big(\partial g^M_i(y,s_{-i})/\partial y|_{y=s_i}\big)^{-1}\cdot\partial p^M_i(y,s_{-i})/\partial y|_{y=s_i}$ (p. 9);
--   4. the game $\mathcal G^M(s,j)$ (p. 9): valuations $\tilde v_i(z)=\lambda^M_i(s)z+\kappa^M_i(s)$ with $\kappa^M_j(s)=0$, $\tilde c_j=+\infty$, and $\kappa^M_i(s)=\tilde c_i=p^M_i(s)$ for $i\ne j$;
--   5. the allocation $\tilde x$ giving the whole resource to user $j$, and the ratio of (6) for user $j$, $\big(\sum_{i\ne j}p^M_i(s)+\lambda^M_j(s)\big)/\big(\sum_{i\ne j}p^M_i(s)+\lambda^M_j(s)g^M_j(s)\big)$.
--
--   **Formalization Note** Budgets, liquid welfare, ratios and all suprema are in $[0,+\infty]$, so an infinite budget stays infinite, $x/0=+\infty$ for $x>0$, and an empty supremum is $0$. Utility $-\infty$ above the budget is encoded by feasibility: an equilibrium is affordable for every user, and only affordable deviations $y\ge0$ are compared. Kelly charges its signal at every profile (p. 9), not under the p. 6 convention; with that convention Theorem 5.1 fails ($n=2$, $v_1(x)=\varepsilon x$, $v_2(x)=x$, infinite budgets, $s=(1,0)$). At $s=\mathbf 0$ Lean's $0/0=0$ gives Kelly's allocation $\mathbf 0$, as on p. 4. Valuations are only constrained on $[0,1]$. Footnote 2 (at least two users with positive budgets and non-zero valuations) is not imposed; the game class is larger.
-- source:
--   Caragiannis, Voudouris, The efficiency of resource allocation mechanisms for budget-constrained users, arXiv:1707.03551v3, pp. 5–7, §2; p. 9, §4; p. 14, class C

import Mathlib
import Definitions.Def_LiquidPoA_Kelly_Mechanism

namespace LiquidPoA.Kelly

open Set Finset
open scoped ENNReal

/-- The class `𝒞` of Section 4, read as concavity and convexity in each own signal. -/
def InClassC {n : ℕ} (M : Mechanism n) : Prop :=
  ∀ s, IsSignal s → ∀ i, (∃ j, j ≠ i ∧ 0 < s j) →
    ConcaveOn ℝ (Ici 0) (allocIn M s i) ∧ ConvexOn ℝ (Ici 0) (payIn M s i)

/-- The Kelly rule of pp. 7 and 9: proportional shares and payment equal to signal. -/
noncomputable def kelly (n : ℕ) : Mechanism n where
  alloc s i := s i / ∑ j, s j
  pay s i := s i

/-- A resource allocation game with real valuations and possibly infinite budgets. -/
structure RAGame (n : ℕ) where
  v : Fin n → ℝ → ℝ
  c : Fin n → ℝ≥0∞

/-- The nonnegative, nondecreasing, concave, differentiable valuations of p. 5. -/
structure RAGame.IsAdmissible {n : ℕ} (G : RAGame n) : Prop where
  nonneg : ∀ i, ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ G.v i x
  mono : ∀ i, MonotoneOn (G.v i) (Icc 0 1)
  concave : ∀ i, ConcaveOn ℝ (Icc 0 1) (G.v i)
  diff : ∀ i, DifferentiableOn ℝ (G.v i) (Icc 0 1)

/-- A player can pay the charge at the signal profile. -/
def Affordable {n : ℕ} (M : Mechanism n) (G : RAGame n)
    (s : Fin n → ℝ) (i : Fin n) : Prop :=
  ENNReal.ofReal (M.pay s i) ≤ G.c i

/-- Real utility, used only when the player's payment is affordable. -/
def utility {n : ℕ} (M : Mechanism n) (G : RAGame n)
    (s : Fin n → ℝ) (i : Fin n) : ℝ :=
  G.v i (M.alloc s i) - M.pay s i

/-- Pure Nash equilibrium with budget feasibility and nonnegative deviations. -/
def IsEquilibrium {n : ℕ} (M : Mechanism n) (G : RAGame n)
    (s : Fin n → ℝ) : Prop :=
  IsSignal s ∧ ∀ i, Affordable M G s i ∧
    ∀ y : ℝ, 0 ≤ y → Affordable M G (Function.update s i y) i →
      utility M G (Function.update s i y) i ≤ utility M G s i

/-- Liquid welfare of an allocation: each value is capped by the player's budget. -/
noncomputable def LW {n : ℕ} (G : RAGame n) (d : Fin n → ℝ) : ℝ≥0∞ :=
  ∑ i, min (ENNReal.ofReal (G.v i (d i))) (G.c i)

/-- Optimal liquid welfare over the unit simplex and zero allocation. -/
noncomputable def optLW {n : ℕ} (G : RAGame n) : ℝ≥0∞ :=
  ⨆ (d : Fin n → ℝ) (_ : IsAllocation d), LW G d

/-- The game's liquid price of anarchy over all its pure Nash equilibria. -/
noncomputable def gameLPoA {n : ℕ} (M : Mechanism n) (G : RAGame n) : ℝ≥0∞ :=
  ⨆ (s : Fin n → ℝ) (_ : IsEquilibrium M G s), optLW G / LW G (M.alloc s)

/-- Liquid price of anarchy of a mechanism over all admissible games. -/
noncomputable def lpoa {n : ℕ} (M : Mechanism n) : ℝ≥0∞ :=
  ⨆ (G : RAGame n) (_ : G.IsAdmissible), gameLPoA M G

/-- The inverse allocation derivative times the payment derivative of p. 9. -/
noncomputable def lam {n : ℕ} (M : Mechanism n)
    (s : Fin n → ℝ) (i : Fin n) : ℝ :=
  (derivWithin (allocIn M s i) (Ici 0) (s i))⁻¹ *
    derivWithin (payIn M s i) (Ici 0) (s i)

/-- The affine worst-case game `𝒢ᴹ(s,j)` of Section 4. -/
noncomputable def worstGame {n : ℕ} (M : Mechanism n)
    (s : Fin n → ℝ) (j : Fin n) : RAGame n where
  v i z := lam M s i * z + if i = j then 0 else M.pay s i
  c i := if i = j then ⊤ else ENNReal.ofReal (M.pay s i)

/-- The unit allocation to player `j` in Lemma 4.1. -/
def unitAlloc {n : ℕ} (j : Fin n) : Fin n → ℝ := Pi.single j 1

/-- The expression on the right-hand side of equation (6). -/
noncomputable def ratio {n : ℕ} (M : Mechanism n)
    (s : Fin n → ℝ) (j : Fin n) : ℝ≥0∞ :=
  ENNReal.ofReal ((∑ i ∈ univ.erase j, M.pay s i) + lam M s j) /
    ENNReal.ofReal ((∑ i ∈ univ.erase j, M.pay s i) +
      lam M s j * M.alloc s j)

end LiquidPoA.Kelly


