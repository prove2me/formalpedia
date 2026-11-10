-- Prove2me | Definitions.Def_KnownFidelity_Rank_traceDist
-- name    : KnownFidelity_Rank_traceDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:45:40.224201+00:00
-- url     : https://prove2.me/theorems/df389e49-b08a-40d2-850f-4f471193140a
-- title:
--   Trace distance $d_{\mathrm{tr}}(\rho,\tau)=\tfrac12\|\rho-\tau\|_1$
-- statement:
--   For density operators $\rho,\tau$,
--
--   $$d_{\mathrm{tr}}(\rho,\tau)=\tfrac12\,\|\rho-\tau\|_1 ,$$
--
--   where $\|\cdot\|_1$ is the trace (nuclear) norm. The optimal success probability for distinguishing two equiprobable states is $\tfrac12(1+d_{\mathrm{tr}}(\rho,\tau))$, which is how it enters the two-prior lower bound method.
--
--   **Formalization Note** $\|\cdot\|_1$ is the platform's `WildeQIT.traceNorm`.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §2.1 (unnumbered display), p. 4 (PDF p. 6)

import Mathlib
import Definitions.Def_WildeQIT_traceNorm

namespace KnownFidelity.Rank

/-- **Trace distance** `d_tr(ρ, τ) = ½ ‖ρ − τ‖₁`.
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §2.1 (unnumbered display), printed p. 4 (PDF p. 6): "For density operators
ρ, τ, write d_tr(ρ, τ) = ½ ∥ρ − τ∥₁."

**Formalization Note.** `‖·‖₁` is the platform's `WildeQIT.traceNorm` (`Re tr √(M* M)`). The
formula is applied to the averaged states of the two-prior method, which are density matrices. -/
noncomputable def traceDist {ι : Type} [Fintype ι] [DecidableEq ι] (X Y : Matrix ι ι ℂ) : ℝ :=
  WildeQIT.traceNorm (X - Y) / 2

end KnownFidelity.Rank


