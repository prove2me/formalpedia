-- Prove2me | Definitions.Def_KallMayerSLP_KKT_lagrangian
-- name    : KallMayerSLP_KKT_lagrangian
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:08:46.609312+00:00
-- url     : https://prove2.me/theorems/7966c78c-76e4-418f-a25d-dec172c7d719
-- title:
--   Lagrange function $L(x,u)$ of (3.1)
-- statement:
--   The **Lagrange function** of the program (3.1) is
--   $$
--   L(x,u):=f(x)+\sum_{i=1}^m u_i\,g_i(x),\qquad x\in\mathbb R^n,\ u\in\mathbb R^m .
--   $$
--
--   Its saddle points (3.6) and the min–max problems (3.7) are built from it.
--
--   **Formalization Note** $u$ ranges over all of $\mathbb R^m$; the sign restriction $u\ge0$ is imposed wherever the book imposes it.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3.1, p.65 (PDF 76)

import Mathlib

namespace KallMayerSLP.KKT

/-- **The Lagrange function of (3.1).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, §3.1, p.65 (PDF 76):
"`L(x, u) := f(x) + Σ_{i=1}^m uᵢ gᵢ(x)`".

**Formalization Note.** `u : Fin m → ℝ` ranges over all of `ℝᵐ`; the restriction `u ≥ 0` is
imposed where the book imposes it. -/
def lagrangian {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (u : Fin m → ℝ) : ℝ :=
  f x + ∑ i, u i * g i x

end KallMayerSLP.KKT


