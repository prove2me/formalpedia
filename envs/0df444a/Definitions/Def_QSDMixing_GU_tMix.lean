-- Prove2me | Definitions.Def_QSDMixing_GU_tMix
-- name    : QSDMixing_GU_tMix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:51:54.35623+00:00
-- url     : https://prove2.me/theorems/97f5ea89-910b-44e8-8db0-28cceb9237a5
-- title:
--   The worst-case quantum mixing time $t_{\mathrm{mix}}(T,\omega,\epsilon)$
-- statement:
--   For a stationary state $\omega$, the worst-case initial-state quantum homogeneous mixing time is
--
--   $$
--   t_{\mathrm{mix}}(T,\omega,\epsilon)=\min\Big\{t\ge1:\ \sup_{\rho\in\mathcal D(\mathcal A)}\|T^t(\rho)-\omega\|_1\le\epsilon\Big\}.
--   $$
--
--   **Formalization Note** The value lies in $\mathbb N\cup\{\infty\}$ and is $\infty$ when no $t$ qualifies. The time $t$ runs over $t\ge1$; with $t=0$ allowed, Theorem 2 fails at $\mathcal A=\mathbb C\cdot1$.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), eq. (53), p.15

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_QSDMixing_GU_densityIn

set_option autoImplicit false

namespace QSDMixing.GU

/-- The worst-case initial-state quantum homogeneous mixing time
`t_mix(T, ω, ε) = min {t : sup_{ρ ∈ D(A)} ‖T^t ρ - ω‖₁ ≤ ε}`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), eq. (53), p.15.

**Formalization Note.** The value is in `ℕ∞`, and it is `⊤` when no `t` qualifies. `t` ranges over
`t ≥ 1`: with `t = 0` allowed, Theorem 2 fails at `A = ℂ·1`. The inner real `sSup` is `0` on an empty `D(A)`;
for a linear map sending `D(A)` into itself and `ω ∈ D(A)`, the set is nonempty and bounded. -/
noncomputable def tMix {n : Type} [Fintype n] [DecidableEq n]
    (A : StarSubalgebra ℂ (Matrix n n ℂ)) (T : Matrix n n ℂ → Matrix n n ℂ) (ω : Matrix n n ℂ)
    (ε : ℝ) : ℕ∞ :=
  sInf {K : ℕ∞ | ∃ t : ℕ, 1 ≤ t ∧ K = t ∧
    sSup {r | ∃ ρ ∈ densityIn A, r = WildeQIT.traceNorm (T^[t] ρ - ω)} ≤ ε}

end QSDMixing.GU


