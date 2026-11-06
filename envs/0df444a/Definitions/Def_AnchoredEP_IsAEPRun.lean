-- Prove2me | Definitions.Def_AnchoredEP_IsAEPRun
-- name    : AnchoredEP_IsAEPRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:06.376909+00:00
-- url     : https://prove2.me/theorems/5d157a47-9920-4acb-990d-bd29d50be2ab
-- title:
--   Run of the Anchored Extra-Proximal framework (Algorithm 2)
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R^d$, $H:\mathbb R^d\rightrightarrows\mathbb R^d$ and $\rho\in\mathbb R$. Sequences $(z_k)$, $(z_{k+\frac12})$, $(v_k)$, $(r_k)$ in $\mathbb R^d$ and $(a_k)$, $(A_k)$ in $\mathbb R$ form a **run of the AEP framework with $K$ updates** if $v_0\in H(z_0)$, $A_0=0$, and for every $k<K$, writing $w_k=\frac{a_k}{A_k+a_k}z_0+\frac{A_k}{A_k+a_k}z_k$:
--
--   1. the step size is positive, $a_k>0$;
--   2. (10) $z_{k+\frac12}=\frac{a_k}{A_k+a_k}z_0+\frac{A_k}{A_k+a_k}\big(z_k-a_k(F(z_k)+v_k)\big)$;
--   3. (11) $r_{k+1}\in a_kF(z_{k+1})+a_kH(z_{k+1})+z_{k+1}-w_k$;
--   4. (12) $\|r_{k+1}\|\le\rho\|z_{k+1}-z_{k+\frac12}\|$;
--   5. (13) $A_{k+1}=A_k+a_k$ and $v_{k+1}=\frac1{a_k}\big(r_{k+1}-a_kF(z_{k+1})-z_{k+1}+w_k\big)$.
--
--   The point $z_0$ is the anchor. Conditions (11) and (13) give $v_{k+1}\in H(z_{k+1})$.
--
--   **Formalization Note** The stopping test $\|F(z_k)+v_k\|\le\varepsilon$ only truncates a run, so a run is described by the number $K$ of updates it performs; nothing is required for $k\ge K$. The choice of step sizes is left free, as in Algorithm 2.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Section 3.2, Eqs. (10)–(13), pp.5–6, and Algorithm 2, Appendix C.2, p.22

import Mathlib

namespace AnchoredEP

/-- **A run of the Anchored Extra-Proximal (AEP) framework, Algorithm 2.** Jiang–Yoon,
arXiv:2609.30212, Section 3.2, steps (i)–(iv) with Eqs. (10)–(13), pp.5–6, and Algorithm 2,
Appendix C.2, p.22.

`IsAEPRun F H ρ z zh v r a A K` says that the sequences `z, zh, v, r : ℕ → ℝ^d` and
`a, A : ℕ → ℝ` (with anchor `z 0 = z₀`) obey the first `K` iterations of Algorithm 2 with
parameter `ρ`:
* initialization: `v 0 ∈ H (z 0)` and `A 0 = 0`;
* for every `k < K`: the step `a k > 0`;
  (10) `zh k = a_k/(A_k + a_k) · z₀ + A_k/(A_k + a_k) · (z_k − a_k (F(z_k) + v_k))`;
  (11) `r_{k+1} ∈ a_k F(z_{k+1}) + a_k H(z_{k+1}) + z_{k+1} − w_k`, where
  `w_k = a_k/(A_k + a_k) · z₀ + A_k/(A_k + a_k) · z_k`;
  (12) `‖r_{k+1}‖ ≤ ρ ‖z_{k+1} − zh k‖`;
  (13) `A_{k+1} = A_k + a_k` and `v_{k+1} = (1/a_k)(r_{k+1} − a_k F(z_{k+1}) − z_{k+1} + w_k)`.

`zh k` is the extrapolated point `z_{k+½}`.

**Formalization Note.** The stopping test "if `‖F(z_k) + v_k‖ ≤ ε`, return `z_k`" only truncates
the run, so a run is described by the number `K` of updates performed; nothing is constrained
for `k ≥ K`. The way the step sizes `a_k` are chosen is left free, as in Algorithm 2. Condition
(11) is written as `∃ h ∈ H z_{k+1}, r_{k+1} = a_k F(z_{k+1}) + a_k h + z_{k+1} − w_k`; together
with (13) it gives `v_{k+1} = h ∈ H(z_{k+1})`, as noted on p.6. -/
def IsAEPRun {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ)
    (z zh v r : ℕ → EuclideanSpace ℝ (Fin d)) (a A : ℕ → ℝ) (K : ℕ) : Prop :=
  v 0 ∈ H (z 0) ∧ A 0 = 0 ∧
    ∀ k < K,
      0 < a k ∧
      zh k = (a k / (A k + a k)) • z 0 + (A k / (A k + a k)) • (z k - a k • (F (z k) + v k)) ∧
      (∃ h ∈ H (z (k + 1)), r (k + 1) = a k • F (z (k + 1)) + a k • h + z (k + 1)
          - ((a k / (A k + a k)) • z 0 + (A k / (A k + a k)) • z k)) ∧
      ‖r (k + 1)‖ ≤ ρ * ‖z (k + 1) - zh k‖ ∧
      A (k + 1) = A k + a k ∧
      v (k + 1) = (a k)⁻¹ • (r (k + 1) - a k • F (z (k + 1)) - z (k + 1)
          + ((a k / (A k + a k)) • z 0 + (A k / (A k + a k)) • z k))

end AnchoredEP


