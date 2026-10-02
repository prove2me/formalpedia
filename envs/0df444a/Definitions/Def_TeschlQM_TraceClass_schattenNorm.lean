-- Prove2me | Definitions.Def_TeschlQM_TraceClass_schattenNorm
-- name    : TeschlQM_TraceClass_schattenNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T09:20:35.971002+00:00
-- url     : https://prove2.me/theorems/c6b023a3-4d7b-4291-989f-5426f958d7be
-- title:
--   Singular value multiplicities and the Schatten p-norm ‖K‖_p, Eq. (6.19)
-- statement:
--   Let $\mathfrak{H}$ be a complex Hilbert space and $K \in \mathfrak{L}(\mathfrak{H})$ with adjoint $K^*$. For $\mu \in \mathbb{R}$ let
--   $$m_K(\mu) = \dim \operatorname{Ker}(K^*K - \mu) \in \{0, 1, 2, \dots\} \cup \{\infty\}$$
--   be the multiplicity of $\mu$ as an eigenvalue of $K^*K$. For compact $K$ the **singular values** $s_j(K) > 0$ are the positive square roots of the nonzero eigenvalues of $K^*K$, each repeated according to its multiplicity (Theorem 6.7). The **Schatten $p$-norm** is
--   $$\|K\|_p = \Big(\sum_j s_j(K)^p\Big)^{1/p} = \Big(\sum_{\mu > 0} m_K(\mu)\, \mu^{p/2}\Big)^{1/p} \in [0, \infty].$$
--   For $p = 2$ it is the Hilbert–Schmidt norm $\|K\|_2$ of (6.15).
--
--   **Formalization Note.** Rather than choosing an enumeration $j \mapsto s_j(K)$ (which would require Theorem 6.7 to exist), the sum over singular values with multiplicity is written as a sum over the positive reals $\mu$, weighted by the multiplicity $m_K(\mu)$, computed as `Cardinal.toENat` of the rank of Mathlib's eigenspace of $K^*K$. All quantities live in $[0,\infty]$ (`ℝ≥0∞`); a divergent series gives $\|K\|_p = \infty$, never a junk value $0$. The exponent $p$ is a real number; it is used only with $p \ge 1$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 141, Section 6.3, Eq. (6.19); singular values p. 137, Theorem 6.7

import Mathlib

namespace TeschlQM.TraceClass

open scoped ENNReal

/-- The multiplicity `dim Ker(K*K - μ) ∈ ℕ ∪ {∞}` of `μ` as an eigenvalue of `K*K`
(`0` if `μ` is not an eigenvalue). By Teschl, Theorem 6.7, p. 137, the singular values `s_j(K)` of a
compact `K` are the numbers `s_j > 0` such that `s_j²` runs through the nonzero eigenvalues of `K*K`,
counted with this multiplicity. -/
noncomputable def singularMultiplicity {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (K : H →L[ℂ] H) (μ : ℝ) : ℕ∞ :=
  Cardinal.toENat (Module.rank ℂ (Module.End.eigenspace
    ((ContinuousLinearMap.adjoint K ∘L K : H →L[ℂ] H) : H →ₗ[ℂ] H) (μ : ℂ)))

/-- Teschl (6.19), p. 141: the **Schatten `p`-norm** `‖K‖_p = (∑_j s_j(K)^p)^{1/p}`, the sum running
over the singular values of `K` counted with multiplicity. Since `s_j(K)²` runs through the nonzero
(i.e. positive) eigenvalues `μ` of `K*K` with multiplicity `dim Ker(K*K - μ)`, the sum is
`∑_{μ > 0} dim Ker(K*K - μ) · μ^{p/2}`. The value lies in `[0, ∞]`; it is `∞` exactly when the
series diverges. For `p = 2` this is the Hilbert–Schmidt norm (6.15), p. 140. -/
noncomputable def schattenNorm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (p : ℝ) (K : H →L[ℂ] H) : ℝ≥0∞ :=
  (∑' μ : {μ : ℝ // 0 < μ},
      ((singularMultiplicity K (μ : ℝ) : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (μ : ℝ) ^ (p / 2)) ^ (1 / p)

end TeschlQM.TraceClass


