-- Prove2me | Definitions.Def_GastRestlessLP_Exponential_Policy
-- name    : GastRestlessLP_Exponential_Policy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T00:17:59.956211+00:00
-- url     : https://prove2.me/theorems/8d41a034-6efa-4703-ac06-f4df00fd8fd2
-- title:
--   Admissible policies on the full simplex and the fluid recursion
-- statement:
--   A policy consists of deterministic maps $\pi_t$ from the full real state simplex to state-action occupation vectors, independent of $N$. For each $0\le t<T$ and simplex point $m$, admissibility requires all coordinates of $\pi_t(m)$ to be nonnegative, the active coordinates to sum to $\alpha$, and its state marginal to equal $m$.
--
--   The fluid recursion is $m^\pi(0)=m_0$, $y^\pi(t)=\pi_t(m^\pi(t))$, and $m^\pi(t+1)=\phi(y^\pi(t))$. Its total reward is the sum of one-step rewards for $t<T$. Lean extends the maps to ambient real vectors and all natural times; their values outside the simplex and decision horizon are unused. Such extensions impose no condition on the source policy. No global continuity or measurability of the real-simplex maps is required.
-- source:
--   Gast, Gaujal and Yan, arXiv:2106.10067v3 (22 December 2023), https://arxiv.org/abs/2106.10067v3, pp. 6–8, (5) and §3.2

import Definitions.Def_GastRestlessLP_Exponential_Model

open scoped BigOperators

namespace GastRestlessLP.Exponential

variable {S : Type} [Fintype S]

/-- Population-independent decision maps. Values outside the simplex and horizon are unused. -/
abbrev Policy (S : Type) := ℕ → (S → ℝ) → Allocation S

/-- Equation (5), on the entire real simplex at every decision epoch. -/
def Admissible (M : Model S) (T : ℕ) (π : Policy S) : Prop :=
  ∀ t < T, ∀ m, InSimplex m →
    (∀ s a, 0 ≤ π t m s a) ∧
    (∑ s, π t m s 1 = M.α) ∧ marginal (π t m) = m

/-- Deterministic fluid recursion, with the source's initial configuration. -/
def fluidState (M : Model S) (π : Policy S) : ℕ → S → ℝ
  | 0 => M.arm.ρ
  | t + 1 => phi M (π t (fluidState M π t))

/-- Fluid allocations and total fluid reward. -/
def fluidAllocation (M : Model S) (π : Policy S) (t : ℕ) : Allocation S :=
  π t (fluidState M π t)

def fluidValue (M : Model S) (T : ℕ) (π : Policy S) : ℝ :=
  ∑ t ∈ Finset.range T, reward M (fluidAllocation M π t)

end GastRestlessLP.Exponential


