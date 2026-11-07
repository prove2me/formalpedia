-- Prove2me | Definitions.Def_QSDMixing_GU_tMin
-- name    : QSDMixing_GU_tMin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:54:48.976248+00:00
-- url     : https://prove2.me/theorems/04be7efa-b705-4a75-a683-8be7b0d1c6f2
-- title:
--   The quantum mixing time $t_{\min}(\epsilon)$ from $\tau_n$
-- statement:
--   For the Gram matrix $X$ on $G/H$, the quantum homogeneous mixing time of $\Phi_X$ from the fixed initial state $\tau_n$ to $\omega_n$ is
--
--   $$
--   t_{\min}(\epsilon)=\min\{t\ge1:\ \|\Phi_X^t(\tau_n)-\omega_n\|_1\le\epsilon\}.
--   $$
--
--   **Formalization Note** The value lies in $\mathbb N\cup\{\infty\}$ and is $\infty$ when no $t$ qualifies. For $n\ge2$ and $\epsilon<1$, the time $t=0$ is never feasible, so the restriction to $t\ge1$ changes nothing there.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), eq. (70), p.17

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_GaussTesting_Ell2
import Definitions.Def_QSDMixing_GU_stabilizer
import Definitions.Def_QSDMixing_GU_gram
import Definitions.Def_QSDMixing_GU_cosetFintype
import Definitions.Def_QSDMixing_GU_schurChannel
import Definitions.Def_QSDMixing_GU_tauN
import Definitions.Def_QSDMixing_GU_omegaN

set_option autoImplicit false
open GaussTesting (Ell2)

namespace QSDMixing.GU

/-- The quantum mixing time of the Hadamard channel from the fixed initial state:
`t_min(ε) = min {t : ‖Φ_X^t(τ_n) - ω_n‖₁ ≤ ε}`, with `X` the Gram matrix on `G ⧸ H`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), eq. (70), p.17.

**Formalization Note.** The value is in `ℕ∞`, and it is `⊤` when no `t` qualifies. `t` ranges over `t ≥ 1`.
For `n ≥ 2`, `t = 0` is never feasible when `ε < 1`, since `‖τ_n - ω_n‖₁ = 2(1 - 1/n) ≥ 1`. -/
noncomputable def tMin {G ι : Type} [Group G] [Finite G]
    (U : G →* unitary (Ell2 ι →L[ℂ] Ell2 ι)) (ψ : Ell2 ι) (ε : ℝ) : ℕ∞ :=
  sInf {K : ℕ∞ | ∃ t : ℕ, 1 ≤ t ∧ K = t ∧
    WildeQIT.traceNorm ((schurChannel (gram U ψ))^[t] tauN - omegaN) ≤ ε}

end QSDMixing.GU


