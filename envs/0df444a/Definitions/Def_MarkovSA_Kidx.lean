-- Prove2me | Definitions.Def_MarkovSA_Kidx
-- name    : MarkovSA_Kidx
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:19.788687+00:00
-- url     : https://prove2.me/theorems/d0c743ad-09a5-4f4f-9e84-c66850a2a73c
-- title:
--   The index $K$: least $K_0$ with $t_k\le k$ for all $k\ge K_0$
-- statement:
--   For a sequence of mixing times $(t_k)$,
--
--   $$
--   K=\min\{K_0\ge0:\ t_k\le k\ \text{for every }k\ge K_0\}.
--   $$
--
--   The paper defines $K=\min\{k\ge0:k\ge t_k\}$ but uses $k\ge t_k$ for every $k\ge K$ (p.27); the two agree when $t_k\le k$ persists after its first occurrence, which is always the case for constant stepsizes ($K=t_\alpha$). This is reading R2.
--
--   **Formalization Note** If no such $K_0$ exists the value is a default $0$; every statement using $K$ assumes or implies that it exists.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, §2.2, p.6 and Appendix A, p.24 (reading R2)

import Mathlib

namespace MarkovSA

/-- The index `K` (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, §2.2, p.6, read by R2): the least `K₀` such that `t_k ≤ k` for **every** `k ≥ K₀`.

**Formalization Note.** The paper writes `K = min{k ≥ 0 : k ≥ t_k}` but uses `k ≥ t_k` for every `k ≥ K`
(p.27); this definition is what the proof uses and agrees with the printed one whenever `t_k ≤ k` persists
after its first occurrence (always for constant stepsizes, where `K = t_α`). On a sequence with no such
`K₀` it is the junk value `0`; every statement using it assumes such a `K₀` exists or implies it. -/
noncomputable def Kidx (t : ℕ → ℕ) : ℕ := sInf {K₀ : ℕ | ∀ k, K₀ ≤ k → t k ≤ k}

end MarkovSA


