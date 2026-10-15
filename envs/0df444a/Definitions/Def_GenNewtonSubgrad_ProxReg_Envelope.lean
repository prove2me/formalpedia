-- Prove2me | Definitions.Def_GenNewtonSubgrad_ProxReg_Envelope
-- name    : GenNewtonSubgrad_ProxReg_Envelope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:03.308002+00:00
-- url     : https://prove2.me/theorems/7312b9d9-1d4b-43d4-b9a6-730316cb94d0
-- title:
--   Definition 6.1 and (6.3) — Moreau envelope $e_\lambda\varphi$, proximal mapping $\mathrm{Prox}_\lambda\varphi$, and $U_\lambda=\mathrm{rge}(I+\lambda\partial\varphi)$
-- statement:
--   Let $\varphi:E\to\overline{\mathbb R}$ and $\lambda>0$. The **Moreau envelope** (6.1) and the **proximal mapping** (6.2) are
--   $$e_\lambda\varphi(x)=\inf_{y\in E}\Big\{\varphi(y)+\frac1{2\lambda}\|y-x\|^2\Big\},\qquad \operatorname{Prox}_\lambda\varphi(x)=\operatorname*{argmin}_{y\in E}\Big\{\varphi(y)+\frac1{2\lambda}\|y-x\|^2\Big\}.$$
--   The proximal mapping is the (possibly empty, possibly multi-valued) set of minimizers. The set from which Algorithm 6.2 starts is (6.3)
--   $$U_\lambda=\operatorname{rge}(I+\lambda\partial\varphi)=\{y+\lambda w : w\in\partial\varphi(y)\}.$$
--
--   These are the objects through which Algorithm 6.2 is reduced to a gradient method for the $C^{1,1}$ function $e_\lambda\varphi$.
--
--   **Formalization Note.** The envelope takes values in the extended reals (`EReal`); where a statement differentiates it, finiteness on the relevant neighbourhood is part of the statement and the real-valued function $x\mapsto e_\lambda\varphi(x)$ (`toReal`) is differentiated. $\operatorname{Prox}_\lambda\varphi(x)$ is the argmin **set**, never a chosen point. Definition 6.1 assumes $\varphi$ proper and l.s.c. and $\lambda>0$; the objects are defined without these assumptions, which every theorem using them states.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 26, Definition 6.1 ((6.1), (6.2)) and Algorithm 6.2 (6.3)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff

namespace GenNewtonSubgrad.ProxReg

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Moreau envelope (6.1): `e_λφ(x) = inf_y φ(y) + ‖y - x‖² / (2λ)`, valued in `EReal`. -/
noncomputable def moreauEnv (φ : E → EReal) (lam : ℝ) (x : E) : EReal :=
  ⨅ y, φ y + ((‖y - x‖ ^ 2 / (2 * lam) : ℝ) : EReal)

/-- The proximal mapping (6.2): the **set** of minimizers of `y ↦ φ(y) + ‖y - x‖² / (2λ)`. -/
def prox (φ : E → EReal) (lam : ℝ) (x : E) : Set E :=
  {p | ∀ y, φ p + ((‖p - x‖ ^ 2 / (2 * lam) : ℝ) : EReal) ≤
    φ y + ((‖y - x‖ ^ 2 / (2 * lam) : ℝ) : EReal)}

/-- The set `U_λ = rge(I + λ∂φ)` of (6.3). -/
def rgeShift (φ : E → EReal) (lam : ℝ) : Set E :=
  {z | ∃ y, ∃ w ∈ NonconvexSplitting.Shared.LimitingSubdiff φ y, z = y + lam • w}

end GenNewtonSubgrad.ProxReg


