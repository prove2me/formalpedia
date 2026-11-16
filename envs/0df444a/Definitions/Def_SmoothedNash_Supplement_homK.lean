-- Prove2me | Definitions.Def_SmoothedNash_Supplement_homK
-- name    : SmoothedNash_Supplement_homK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:02:10.686042+00:00
-- url     : https://prove2.me/theorems/bc7950a1-bc24-4c14-a841-6248bb390712
-- title:
--   Homotopy $K(x,t) = (1-t)x - tF(x)/a$
-- statement:
--   With $a = L_0 + L_1$, the **homotopy** of Section 4.1 is
--   $$
--   K(x, t) = (1 - t)\, x - t\, \frac{F(x)}{a}, \qquad (x, t) \in \mathbb R^n \times \mathbb R .
--   $$
--   At $t = 0$ its only zero is $x = 0$; for $0 < t \le 1$ and $x \ne 0$, $K(x,t) = 0$ means $F(x) = \lambda x$ with $\lambda = a(1-t)/t$.
--
--   **Formalization Note** $a$ is passed as an argument; every use passes $L_0 + L_1$.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), §4.1.1, p.26

import Mathlib
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The homotopy `K(x, t) = (1 − t) x − t F(x)/a` of Section 4.1 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.26), with
`a = L0 + L1` passed as the argument `a`; the point `(x, t) ∈ ℝ^n × ℝ` is a pair. -/
noncomputable def homK {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (a : ℝ) (p : EuclideanSpace ℝ (Fin n) × ℝ) : EuclideanSpace ℝ (Fin n) :=
  (1 - p.2) • p.1 - (p.2 / a) • F p.1

end SmoothedNash.Supplement


