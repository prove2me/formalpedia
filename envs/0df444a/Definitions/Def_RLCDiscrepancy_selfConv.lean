-- Prove2me | Definitions.Def_RLCDiscrepancy_selfConv
-- name    : RLCDiscrepancy_selfConv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:13.002207+00:00
-- url     : https://prove2.me/theorems/7111965e-88f1-4dc4-994a-e25a1ce7cbbe
-- title:
--   Self-convolution $F_f$
-- statement:
--   For $f:\mathbb F_q^n\to\mathbb R$, let $\check f(x)=f(-x)$. The **self-convolution** of $f$ is $F_f=f*\check f$, i.e.
--
--   $$
--   F_f(w)=q^{-n}\sum_{x\in\mathbb F_q^n} f(x)\,f(x-w).
--   $$
--
--   $F_f$ is invariant under translating $f$ (Lemma 4.11), its Fourier coefficients are $|\hat f|^2\ge 0$ (Lemma 4.9), and its deviation controls the one-step variance of $\delta_{C,f}$ (Lemma 4.12). Note that this is the mirrored convolution, not $f*f$.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 4.8, p.29

import Mathlib

namespace RLCDiscrepancy

/-- **Self-convolution F_f** (Definition 4.8). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 4.8, p.29: "Let
f : F^n_q → R≥0 be a function. We define the reflected function f̌ : F^n_q → R by f̌(x) = f(−x).
We then define the self-convolution function F_f as F_f = f ∗ f̌. Equivalently, F_f can be defined
by F_f(w) = q^{−n} ∑_{x∈F^n_q} f(x) · f̌(w − x) = q^{−n} ∑_{x∈F^n_q} f(x) · f(x − w)."

**Formalization Note.** Defined by the last expression, for every real `f`. This is the mirrored
convolution f ∗ f̌, not f ∗ f. -/
noncomputable def selfConv {F : Type*} [Field F] [Fintype F] {n : ℕ} (f : (Fin n → F) → ℝ) : (Fin n → F) → ℝ :=
  fun w => (∑ x, f x * f (x - w)) / (Fintype.card F : ℝ) ^ n

end RLCDiscrepancy


