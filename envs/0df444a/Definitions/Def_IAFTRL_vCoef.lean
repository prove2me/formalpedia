-- Prove2me | Definitions.Def_IAFTRL_vCoef
-- name    : IAFTRL_vCoef
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:41.650696+00:00
-- url     : https://prove2.me/theorems/9b0598e3-66ff-4215-ac83-055a4be6ae4d
-- title:
--   Reconstruction vectors $v_b(p)=M(p)^{-1}b$
-- statement:
--   For a distribution $p$ on $\mathcal A$, the **design matrix** is $M(p)=\sum_{a\in\mathcal A}p_a\,aa^\top$ and, when $M(p)\succ0$, the **reconstruction vector** of the action $b$ is
--   $$
--   v_b(p)=M(p)^{-1}b .
--   $$
--   IA-FTRL estimates the loss vector by $\hat\theta_t=v_{A_t}(p_t)\,Y_t$; the identity $\sum_b p_b\,v_b(p)\,b^\top=I_d$ makes this estimate unbiased.
--
--   **Formalization Note** $M(p)$ is the published `BanditAlgorithm.linearAllocationMatrix arms p`. Lean's inverse of a singular matrix is $0$; in this mission $v_b(p)$ is only used at distributions feasible for (2.3), where $M(p)\succ0$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 2.1, p.17

import Mathlib
import Definitions.Def_LinearBanditProtocol

namespace IAFTRL

open Matrix

/-- **Reconstruction vectors `v_b(p) = M(p)^{-1} b`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 2.1, p.17: "For any
`p ∈ 𝒫(𝒜)`, let `M(p) = Σ_{a∈𝒜} p_a a a^⊤` be the design matrix induced by `p`. To construct the loss
estimator, for any `p ∈ 𝒫(𝒜)` with `M(p) ≻ 0`, we define `v_a(p) = M(p)^{-1} a` for all `a ∈ 𝒜`."

`vCoef arms p b = M(p)^{-1} a_b` with `M(p) = BanditAlgorithm.linearAllocationMatrix arms p`.

**Formalization Note.** Mathlib's inverse of a singular matrix is `0`; every use of `vCoef` in this
mission is at a `p` feasible for (2.3), where `M(p) ≻ 0` follows from the mixture domination
(p.18). -/
noncomputable def vCoef {d K : ℕ} (arms : Fin K → Fin d → ℝ) (p : Fin K → ℝ) (b : Fin K) :
    Fin d → ℝ :=
  (BanditAlgorithm.linearAllocationMatrix arms p)⁻¹ *ᵥ arms b

end IAFTRL


