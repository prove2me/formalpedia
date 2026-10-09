-- Prove2me | Definitions.Def_RFRidge_Basic_LambdaMax
-- name    : RFRidge_Basic_LambdaMax
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T00:47:36.31466+00:00
-- url     : https://prove2.me/theorems/14538540-27f8-4c23-b900-df7135a208d5
-- title:
--   App. A.1, p. 17 — the biggest eigenvalue λ_max(Q) = sup_{‖f‖≤1} ⟨f, Qf⟩ of a bounded operator
-- statement:
--   For a bounded linear operator $Q$ on a Hilbert space $\mathcal L$, the *biggest eigenvalue* is
--   $$\lambda_{\max}(Q)=\sup_{\|f\|_{\mathcal L}\le1}\langle f,Qf\rangle_{\mathcal L}.$$
--
--   It is used in Proposition 8 and throughout the appendix to measure how far an operator is from the identity.
--
--   **Formalization Note** The Hilbert space is complex and the value is the real part of $\langle f,Qf\rangle$, which is the inner product itself for self-adjoint $Q$. The index set contains $f=0$ and every value is at most $\|Q\|$, so the supremum is a genuine real supremum; as on the page (the supremum includes $f=0$), $\lambda_{\max}(Q)\ge0$.
-- source:
--   Rudi & Rosasco, arXiv:1602.04474v5, App. A.1, p. 17

import Mathlib

namespace RFRidge.Basic

/-- The biggest eigenvalue `λ_max(Q) = sup_{‖f‖ ≤ 1} ⟨f, Q f⟩` of a bounded operator on a (complex)
Hilbert space (App. A.1, p. 17). The index set contains `0`, and every value is bounded by `‖Q‖`, so the
real supremum is a genuine one. With the paper's `‖f‖ ≤ 1` the value is always `≥ 0`. -/
noncomputable def lambdaMax {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Q : E →L[ℂ] E) : ℝ :=
  ⨆ f : {f : E // ‖f‖ ≤ 1}, RCLike.re (inner ℂ (f : E) (Q f))

end RFRidge.Basic


