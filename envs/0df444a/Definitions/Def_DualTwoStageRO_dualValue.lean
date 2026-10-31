-- Prove2me | Definitions.Def_DualTwoStageRO_dualValue
-- name    : DualTwoStageRO_dualValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:41.584174+00:00
-- url     : https://prove2.me/theorems/bd0f8ce9-7d87-46a5-a74f-eafce2c9e30d
-- title:
--   Worst-case value of a here-and-now decision in the dualized model (6)
-- statement:
--   For $x\in\mathbb R^{n_x}$ and $(u,v,w,z)\in\mathcal V$ let
--
--   $$\Lambda(x,v,w)=\Bigl\{\lambda\in\mathbb R^p:\ \sum_{k=1}^pD_{kj}\lambda_k\ge w^\top A_{\cdot j}(x)+\sum_{i=1}^{m_1}v_iF_{ij}(x),\ j=1,\dots,n_\zeta\Bigr\},$$
--
--   where $A_{\cdot j}(x)$ is the $j$th column of $A(x)$ and $\lambda$ is free. The **worst-case value** of $x$ in the dualized model is
--
--   $$\Psi(x)=\sup_{(u,v,w,z)\in\mathcal V}\ \inf_{\lambda\in\Lambda(x,v,w)}\Bigl\{\sum_{i=0}^{m_1}v_if_i(x)+d^\top\lambda-w^\top b(x)-\sum_{i=0}^{m_1}z_i\Bigr\}.$$
--
--   Model (6) is $\inf_{x\in\mathcal X}\Psi(x)$, and $x$ is feasible for (6) when $\Psi(x)<+\infty$. In (6) the new adjustable variable $\lambda$ enters linearly.
--
--   **Formalization Note** Values are in `EReal`: the inner infimum over an empty $\Lambda$ is $+\infty$, and the supremum over an empty $\mathcal V$ is $-\infty$. The module also defines `lamFeasible`.
-- source:
--   de Ruiter, Zhen, den Hertog, Technical Note—Dual Approach for Two-Stage Robust Nonlinear Optimization, Operations Research 71(5):1794–1799, 2023, doi:10.1287/opre.2022.2289 (published version, sha256 75cbce38…fe03ac), Theorem 1, p.1796, model (6)

import Mathlib
import Definitions.Def_DualTwoStageRO_dualSet

namespace DualTwoStageRO

open Matrix

variable {nx ny nζ m1 m2 p : ℕ}

/-- The feasible set of the inner problem of (6) at `x` and `(u,v,w,z)`:
`{λ ∈ ℝ^p | Σ_{k=1}^p D_kj λ_k ≥ w⊤A_·j(x) + Σ_{i=1}^{m1} v_i F_ij(x), j = 1,…,nζ}`, `λ` free.
The paper's `v_i` (`i = 1,…,m1`) is `q.v i.succ`. -/
def lamFeasible (P : Problem nx ny nζ m1 m2 p) (x : Fin nx → ℝ) (q : DualPoint ny m1 m2) :
    Set (Fin p → ℝ) :=
  {lam | ∀ j : Fin nζ,
    q.w ⬝ᵥ (fun r => P.A x r j) + ∑ i : Fin m1, q.v i.succ * P.F i j x ≤ ∑ k, P.D k j * lam k}

/-- **Worst-case value of a here-and-now decision in the dualized model (6).**
de Ruiter, Zhen, den Hertog, *Technical Note—Dual Approach for Two-Stage Robust Nonlinear
Optimization*, Operations Research 71(5), 2023, Theorem 1, (6), p.1796:
`inf_{x∈X} sup_{(u,v,w,z)∈V} inf_λ { Σ_{i=0}^{m1} v_i f_i(x) + d⊤λ − w⊤b(x) − Σ_{i=0}^{m1} z_i |
Σ_{k=1}^p D_kj λ_k ≥ w⊤A_·j(x) + Σ_{i=1}^{m1} v_i F_ij(x), j = 1,…,nζ }`.
The optimal value of (6) is `⨅ x ∈ P.X, dualValue P x`.

**Formalization Note.** Values are in `EReal`: the inner infimum over an empty `λ`-set is `⊤`, and the
supremum over an empty `V` is `⊥`. `λ` is free (no sign constraint), as printed. "x is feasible for
(6)" is read as `dualValue P x < ⊤`. -/
noncomputable def dualValue (P : Problem nx ny nζ m1 m2 p) (x : Fin nx → ℝ) : EReal :=
  ⨆ q ∈ dualSet P, ⨅ lam ∈ lamFeasible P x q,
    ((∑ i, q.v i * P.f i x + P.d ⬝ᵥ lam - q.w ⬝ᵥ P.b x - ∑ i, q.z i : ℝ) : EReal)

end DualTwoStageRO


