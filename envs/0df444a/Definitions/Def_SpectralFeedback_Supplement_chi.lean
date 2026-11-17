-- Prove2me | Definitions.Def_SpectralFeedback_Supplement_chi
-- name    : SpectralFeedback_Supplement_chi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:54:20.623532+00:00
-- url     : https://prove2.me/theorems/348c1f7e-2663-4a94-b787-f37126b96429
-- title:
--   The secular function $\chi(x)=\lambda_{\max}(vv^*-\operatorname{diag}x)$, $v_i=\sqrt{x_i}$
-- statement:
--   For $x\in\mathbb R^r_+$ put $v_i=\sqrt{x_i}$ and define
--
--   $$
--   \chi(x)=\lambda_{\max}\bigl(vv^*-\operatorname{diag}x\bigr),
--   $$
--
--   the largest eigenvalue of the real symmetric $r\times r$ matrix with entries $\sqrt{x_ix_j}$ off the diagonal and $0$ on it. The paper writes $\chi_s$ for $\chi$ on $\mathbb R^s$. When at least two entries of $x$ are positive, $\chi(x)$ is the unique positive root $c$ of $\sum_i x_i/(x_i+c)=1$, and otherwise it is $0$; this is a property, not the definition.
--
--   With $F=\chi_r$, the spectral reward $f_r(A)=\chi(\lambda_1(A),\dots,\lambda_r(A))$ and the value $G_{m,r}(\rho)$ of (C.6) are the published reward and reward set of the base mission. Every theorem of this supplement is a statement about $G_{m,r}$ or $G_{m,s}$.
--
--   **Formalization Note** The matrix is taken with complex entries, which has the same eigenvalues, so its largest eigenvalue is the published `eigDesc · 0`. For $r=0$ the value is $0$. `Real.sqrt` clamps negative entries to $0$; the mission evaluates $\chi$ only on nonnegative vectors.
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), (3.1), p.3 (PDF p.5); (C.3), p.26 (PDF p.28); §E.3.1, p.82 (PDF p.84); §G.1.1, p.96 (PDF p.98)

import Mathlib
import Definitions.Def_SpectralFeedback_eigDesc

namespace SpectralFeedback

namespace Supplement

/-- **The secular function `χ`** (Qi, *Spectral Structure and Exact Arithmetic of Finite-Feedback
Measurement Discrimination*, manuscript (Nov. 2026), (3.1), p.3 (PDF p.5); (C.3), p.26 (PDF p.28);
§E.3.1, p.82 (PDF p.84); §G.1.1, p.96 (PDF p.98)): for `x ∈ ℝ^r_+`,
`χ(x) = λ_max(v v* − diag x)`, `v_i = √x_i`. The paper writes `χ_s` for `χ` on `ℝ^s`.

**Formalization Note** The real symmetric `r × r` matrix `v vᵀ − diag x` is taken with complex
entries (same eigenvalues) so that its largest eigenvalue is the published `eigDesc · 0`. For `r = 0`
the value is `0`. Off the orthant `Real.sqrt` clamps negative entries to `0`; the mission evaluates
`χ` only at nonnegative vectors. The secular-root description (the unique positive root `c` of
`∑ x_i/(x_i + c) = 1` when at least two entries are positive, else `0`) is a consequence stated in the
paper, not the definition. -/
noncomputable def chi (r : ℕ) (x : Fin r → ℝ) : ℝ :=
  eigDesc
    (Matrix.vecMulVec (fun i => ((Real.sqrt (x i) : ℝ) : ℂ)) (fun i => ((Real.sqrt (x i) : ℝ) : ℂ)) -
      Matrix.diagonal (fun i => ((x i : ℝ) : ℂ))) 0

end Supplement

end SpectralFeedback


