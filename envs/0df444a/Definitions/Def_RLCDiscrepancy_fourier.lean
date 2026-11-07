-- Prove2me | Definitions.Def_RLCDiscrepancy_fourier
-- name    : RLCDiscrepancy_fourier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:30.759707+00:00
-- url     : https://prove2.me/theorems/7a504624-317e-43ec-a253-50ff0fec9d7e
-- title:
--   Fourier transform $\hat f$ on $\mathbb F_q^n$
-- statement:
--   Let $\psi:\mathbb F_q\to\mathbb C^\times$ be an additive character and $\chi_y(x)=\psi(\langle x,y\rangle)$ with $\langle x,y\rangle=\sum_j x_jy_j$. The **Fourier transform** of $f:\mathbb F_q^n\to\mathbb R$ at $y\in\mathbb F_q^n$ is
--
--   $$
--   \hat f(y)=q^{-n}\sum_{x\in\mathbb F_q^n} f(x)\,\chi_y(x).
--   $$
--
--   The paper fixes $\psi(a)=\exp\!\big(\tfrac{2\pi i}{p}\operatorname{tr}(a)\big)$ with $\operatorname{tr}:\mathbb F_q\to\mathbb F_p$ the absolute trace; this is a nontrivial character. With the expectation normalization, $\hat f(0)=1$ for normalized $f$.
--
--   **Formalization Note** The character is a parameter `ψ : AddChar F ℂ`; the statements using $\hat f$ quantify over all characters (Lemma 4.9) or all nontrivial ones (Eq. (8)), so they contain the paper's. No complex conjugate is applied, as printed.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), §2.1, p.12

import Mathlib

namespace RLCDiscrepancy

/-- **Fourier transform f̂** with respect to an additive character `ψ` of F_q. Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), §2.1,
p.12: "The Fourier transform of f at y ∈ F^n_q is f̂(y) = q^{−n} ∑_{x∈F^n_q} f(x)χ_y(x), where
χ_y is the additive character of F^n_q associated with y. Specifically, if F_q has characteristic
p and q = p^m, then χ_y(x) = exp((2πi/p) tr(⟨x, y⟩)), where ⟨x, y⟩ = ∑_{j=1}^n x_j y_j".

**Formalization Note.** χ_y(x) is `ψ (x ⬝ᵥ y)` for a character `ψ : AddChar F ℂ`; the paper's
choice is ψ(a) = exp(2πi tr(a)/p), i.e. `ZMod.stdAddChar` composed with the absolute trace,
which is a nontrivial character. Statements using `fourier` quantify over ψ (all ψ, or all
nontrivial ψ), which contains the paper's. No complex conjugate is applied, as printed. `f` is
real valued, which covers every function the paper transforms. -/
noncomputable def fourier {F : Type*} [Field F] [Fintype F] {n : ℕ} (ψ : AddChar F ℂ) (f : (Fin n → F) → ℝ)
    (y : Fin n → F) : ℂ :=
  (∑ x, (f x : ℂ) * ψ (x ⬝ᵥ y)) / (Fintype.card F : ℂ) ^ n

end RLCDiscrepancy


