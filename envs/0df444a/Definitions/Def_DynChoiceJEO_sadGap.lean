-- Prove2me | Definitions.Def_DynChoiceJEO_sadGap
-- name    : DynChoiceJEO_sadGap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:40.215523+00:00
-- url     : https://prove2.me/theorems/0241b756-b52c-482b-8ae8-78245c30da65
-- title:
--   SP gap $\epsilon^\Psi_{\mathrm{sad}}(\bar x,\bar y;p)=\max_{y\in Y}\Psi(\bar x,y;p)-\min_{x\in X}\Psi(x,\bar y;p)$
-- statement:
--   The **saddle-point (SP) gap** of a primal-dual pair $(\bar x,\bar y)$ on data $p$ is
--
--   $$\epsilon^\Psi_{\mathrm{sad}}(\bar x,\bar y;p):=\max_{y\in Y}\Psi(\bar x,y;p)-\min_{x\in X}\Psi(x,\bar y;p)=f(\bar x;p)-g(\bar y;p).$$
--
--   It certifies the quality of $(\bar x,\bar y)$: it is nonnegative, and $\bar x,\bar y$ are optimal for the primal and dual problems when it vanishes.
--
--   **Formalization Note** The paper's (9) defines the SP gap as $f(\bar x;p)-\mathcal P(p)+\mathcal D(p)-g(\bar y;p)$ and equates it with the expression above using strong duality $\mathcal P(p)=\mathcal D(p)$. This definition is the second expression, which in general exceeds the first by $\mathcal P(p)-\mathcal D(p)\ge0$; bounds on it are therefore at least as strong. Max/min are real suprema/infima.
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, eq. (9), p.10

import Mathlib
import Definitions.Def_DynChoiceJEO_fval
import Definitions.Def_DynChoiceJEO_gval

namespace DynChoiceJEO

/-- **SP gap `ε^Ψ_sad(x̄,ȳ;p) = max_{y∈Y} Ψ(x̄,y;p) − min_{x∈X} Ψ(x,ȳ;p)`.**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*, arXiv:1702.05702v5, eq. (9), p.10: "ϵ^Ψ_sad(x̄,ȳ;p) := f(x̄;p) − P(p) + D(p) − g(ȳ;p)
= max_{y∈Y} Ψ(x̄,y;p) − min_{x∈X} Ψ(x,ȳ;p)".

`sadGap Ψ X Y x̄ ȳ p` is `f(x̄;p) − g(ȳ;p)` (with `f = fval`, `g = gval`), i.e. the supremum of
`Ψ(x̄,·;p)` over `Y` minus the infimum of `Ψ(·,ȳ;p)` over `X`.

**Formalization Note** This is the **second line** of (9). The first line equals it when
`P(p) = D(p)` (strong duality, which the paper invokes via Sion's theorem on p.9); in general the
second line is the larger of the two by weak duality `D(p) ≤ P(p)`. max/min are `sSup`/`sInf`
of images, finite under the standing assumptions. -/
noncomputable def sadGap {N k : ℕ} {P : Type*} (Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ)
    (X : Set (Fin N → ℝ)) (Y : Set (Fin k → ℝ)) (xbar : Fin N → ℝ) (ybar : Fin k → ℝ) (p : P) :
    ℝ :=
  fval Ψ Y xbar p - gval Ψ X ybar p

end DynChoiceJEO


