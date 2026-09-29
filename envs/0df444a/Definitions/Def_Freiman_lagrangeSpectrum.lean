-- Prove2me | Definitions.Def_Freiman_lagrangeSpectrum
-- name    : Freiman_lagrangeSpectrum
-- status  : Definition
-- author  : @tp
-- created : 2026-09-08T23:20:49.755725+00:00
-- url     : https://prove2.me/theorems/291f32d7-1350-4bb2-b0f0-115c00587e41
-- title:
--   The classical Lagrange spectrum
-- statement:
--   For a real number $x$, let
--   $$
--   \delta(x)=\inf_{p\in\mathbb Z}|x-p|
--   $$
--   be its distance to the nearest integer. For an irrational real number $\xi$ and a positive integer $q$, put
--   $$
--   A_q(\xi)=\frac{1}{q\delta(q\xi)}.
--   $$
--   The Lagrange spectrum is the set of finite real values
--   $$
--   L=\left\{t\in\mathbb R:\text{there exists an irrational }\xi
--   \text{ with }\limsup_{q\to\infty}A_q(\xi)=t\right\}.
--   $$
--   The denominators $q$ run through all positive integers.
--
--   For a real sequence $(u_n)$, the finite equality $\limsup u_n=t$ is expressed by these two conditions: for every $\varepsilon>0$, one has $u_n\le t+\varepsilon$ for all sufficiently large $n$; and for every $\varepsilon>0$ and every $N$, there is an $n\ge N$ with $u_n>t-\varepsilon$.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.2, p. 7, the definition preceding Lemma 1.1. The finite limsup convention is also specified in formalization/MISSION.md in Freiman_Hall_ray_verification.zip.

import Mathlib.NumberTheory.Real.Irrational

namespace Freiman

def HasFiniteLimsup (u : ℕ → ℝ) (t : ℝ) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → u n ≤ t + ε) ∧
  (∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ t - ε < u n)

noncomputable def integerDistance (x : ℝ) : ℝ :=
  sInf (Set.range (fun p : ℤ => |x - (p : ℝ)|))

noncomputable def approximationValue (ξ : ℝ) (q : ℕ) : ℝ :=
  1 / ((q : ℝ) * integerDistance ((q : ℝ) * ξ))

def lagrangeSpectrum : Set ℝ :=
  {t | ∃ ξ : ℝ, Irrational ξ ∧
    HasFiniteLimsup (fun n : ℕ => approximationValue ξ (n + 1)) t}

end Freiman


