-- Prove2me | Definitions.Def_RestrictedAP_Counting_LowInfluence
-- name    : RestrictedAP_Counting_LowInfluence
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-22T22:49:56.861575+00:00
-- url     : https://prove2.me/theorems/0c5d7a3c-4be3-4024-bd78-c47900b87176
-- title:
--   Low-degree, low-influence functions and their truncated triple correlations
-- statement:
--   This module formalizes the elementary objects used in §5.1 and §5.2.5 of the counting-lemma argument.
--
--   For $z\in\mathbb C$, `trunc01` is the real-valued truncation
--   $$\operatorname{trunc}_{[0,1]}(z)=\max\{0,\min\{1,\operatorname{Re}z\}\}.$$
--   For $f:\Sigma^n\to\mathbb C$, `influence` encodes Definition 5.4:
--   $$I_i[f]=\mathbb E_{x\sim\nu^{\otimes n}}\,\mathbb E_{a,b\sim\nu}
--    \left|f(x_{-i},a)-f(x_{-i},b)\right|^2.$$
--   The sum over the full vector $x$ is equivalent to the paper's expectation over $x_{-i}$, because updating coordinate $i$ makes the value of $x_i$ irrelevant.
--
--   `truncatedError` is $\mathbb E_{\nu^{\otimes n}}|\operatorname{trunc}_{[0,1]}(f)-f|^2$, and `tripleTrunc` is
--   $$\mathbb E_{(x,y,z)\sim\mu^{\otimes n}}
--    \operatorname{trunc}_{[0,1]}(f(x))\operatorname{trunc}_{[0,1]}(f(y))
--    \operatorname{trunc}_{[0,1]}(f(z)).$$
--
--   Finally, `HasDegreeBound ν D f` says that in some orthonormal basis of $L^2(\Sigma,\nu)$ whose zeroth vector is the constant function $1$, the tensor-product Fourier expansion of $f$ has no coefficient supported on more than $D$ coordinates. This is Definitions 5.1–5.2 and Proposition 5.3, and is the finite-dimensional degree notion needed by the invariance principle.
--
--   **Formalization Note.** Complex functions and real truncations are kept in separate types, so no identification of $\mathbb C$ with $\mathbb R$ is needed. The module also includes the trivial observation that a probability distribution on a finite type makes that type nonempty.
-- source:
--   Amey Bhangale, Subhash Khot, Yang P. Liu and Dor Minzer, A Counting Lemma for Somewhat Restricted 3-APs, ACM STOC 2027 submission 1020, https://arxiv.org/abs/2608.17365, p. 28 Definitions 5.1–5.4 and Proposition 5.3, p. 30 truncation before Theorem 5.9, and pp. 43–47 Claims 5.22–5.26

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions

namespace RestrictedAP.Counting

open Classical

/-- A distribution on a finite type forces that type to be nonempty. -/
theorem nonempty_of_isDist {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (hμ : IsDist μ) : Nonempty Ω := by
  classical
  by_cases hΩ : Nonempty Ω
  · exact hΩ
  · have : IsEmpty Ω := ⟨fun x => hΩ ⟨x⟩⟩
    simpa using hμ.2

/-- The real-valued truncation of a complex number to `[0,1]`, from p. 30. -/
noncomputable def trunc01 (z : ℂ) : ℝ :=
  max 0 (min 1 z.re)

/-- The influence of coordinate `i`, Definition 5.4 (p. 28), with two independent
one-coordinate resamples. -/
noncomputable def influence {Sig : Type*} [Fintype Sig] {n : ℕ}
    (ν : Sig → ℝ) (i : Fin n) (f : (Fin n → Sig) → ℂ) : ℝ :=
  ∑ x : Fin n → Sig, tensorPow ν n x *
    ∑ a : Sig, ν a * ∑ b : Sig, ν b *
      ‖f (Function.update x i a) - f (Function.update x i b)‖ ^ 2

/-- The mean-square discrepancy between `f` and its truncation, used in Claims 5.22–5.26. -/
noncomputable def truncatedError {Sig : Type*} [Fintype Sig] {n : ℕ}
    (ν : Sig → ℝ) (f : (Fin n → Sig) → ℂ) : ℝ :=
  ∑ x : Fin n → Sig, tensorPow ν n x * ‖((trunc01 (f x) : ℂ) - f x)‖ ^ 2

/-- The triple correlation of the real-valued truncation of a complex function. -/
noncomputable def tripleTrunc {Sig : Type*} [Fintype Sig] {n : ℕ}
    (μ : Sig × Sig × Sig → ℝ) (f : (Fin n → Sig) → ℂ) : ℝ :=
  ∑ t : Fin n → Sig × Sig × Sig, tensorPow μ n t *
    (trunc01 (f (fun i => (t i).1)) * trunc01 (f (fun i => (t i).2.1)) *
      trunc01 (f (fun i => (t i).2.2)))

/-- `f` has Fourier degree at most `D`. The one-letter functions form an orthonormal basis
of `L²(Σ,ν)`, with the zeroth function constant one, and all coefficients of support size
greater than `D` vanish (Definitions 5.1–5.2 and Proposition 5.3, p. 28). -/
def HasDegreeBound {Sig : Type*} [Fintype Sig] [Nonempty Sig] {n : ℕ}
    (ν : Sig → ℝ) (D : ℕ) (f : (Fin n → Sig) → ℂ) : Prop :=
  ∃ φ : Fin (Fintype.card Sig) → Sig → ℂ,
    (∀ a, φ 0 a = 1) ∧
    (∀ j k, ∑ a, (ν a : ℂ) * star (φ j a) * φ k a = if j = k then 1 else 0) ∧
    ∃ coeff : (Fin n → Fin (Fintype.card Sig)) → ℂ,
      (∀ α, D < (Finset.univ.filter (fun i => α i ≠ 0)).card → coeff α = 0) ∧
      ∀ x, f x = ∑ α, coeff α * ∏ i, φ (α i) (x i)

end RestrictedAP.Counting


