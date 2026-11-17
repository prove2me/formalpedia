-- Prove2me | Definitions.Def_AvgCaseTI_Supplement_alphaM
-- name    : AvgCaseTI_Supplement_alphaM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:33:34.36788+00:00
-- url     : https://prove2.me/theorems/83fcd54e-3961-4c7d-bd91-55d7e3854c3a
-- title:
--   Matrices with prescribed $\mathbb F_q$-eigenvalue multiplicities: $C_m(n,q)$ and $\alpha_m(n,q)$
-- statement:
--   Let $\mathbb F_q$ be a finite field and $m:\mathbb F_q\to\mathbb N$. The class $C_m(n,q)$ consists of the matrices $A\in\mathrm M(n,q)$ whose characteristic polynomial factors as
--   $$
--   c_A(t)=f_0(t)\prod_{\lambda\in\mathbb F_q}(t-\lambda)^{m(\lambda)},\qquad f_0(t)\ne0\ \text{for all }t\in\mathbb F_q,
--   $$
--   that is, every $\lambda\in\mathbb F_q$ is an eigenvalue of algebraic multiplicity exactly $m(\lambda)$ (multiplicity $0$: not an eigenvalue). The proportion is
--   $$
--   \alpha_m(n,q):=\frac{|C_m(n,q)|}{|\mathrm M(n,q)|}.
--   $$
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), §6.1, pp.35–36 (PDF pp.37–38)

import Mathlib
import Definitions.Def_AvgCaseTI_hull

set_option autoImplicit false

namespace AvgCaseTI.Supplement

open AvgCaseTI

/-- **Prescribed algebraic multiplicities**: `A ∈ C_m(n, q)`, §6.1, p.35 (PDF p.37): every `λ ∈ F_q` is a
root of the characteristic polynomial of multiplicity exactly `m(λ)` (`0`: not an eigenvalue), i.e.
`c_A(t) = f₀(t) ∏_λ (t − λ)^{m(λ)}` with `f₀` free of roots in `F_q`. -/
def HasMults {K : Type*} [Field K] {n : ℕ} (m : K → ℕ) (A : Mat K n) : Prop :=
  ∀ a : K, A.charpoly.rootMultiplicity a = m a

/-- **`α_m(n, q) = |C_m(n, q)| / |M(n, q)|`.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), §6.1, p.36 (PDF p.38): "the probability of a random matrix A ∈ M(n, q) whose
F_q-eigenvalues' algebraic multiplicities are given by a fixed function m : F_q → N as
α_m(n, q) := |C_m(n, q)| / |M(n, q)|". -/
noncomputable def alphaM (K : Type*) [Field K] (m : K → ℕ) (n : ℕ) : ℝ :=
  (Nat.card {A : Mat K n // HasMults m A} : ℝ) / (Nat.card (Mat K n) : ℝ)

end AvgCaseTI.Supplement


