-- Prove2me | Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
-- name    : ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:40:41.694298+00:00
-- url     : https://prove2.me/theorems/cc4b60c2-1417-475e-90be-558bc8a5ab58
-- title:
--   The one-sided directional derivative f′(x; v)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ and $x,v\in\mathbb R^n$. The (usual) **one-sided directional derivative** of $f$ at $x$ in the direction $v$ is
--
--   $$
--   f'(x;v)=\lim_{\delta\downarrow 0}\frac{f(x+\delta v)-f(x)}{\delta},
--   $$
--
--   whenever this limit exists. The predicate "$f$ has one-sided directional derivative $L$ at $x$ in direction $v$" says that this limit exists and equals the real number $L$.
--
--   It enters Theorem (2.1) twice: hypothesis (c) asks that $g'_x(x,u;\cdot)$ exist and equal $g^\circ_x(x,u;\cdot)$, and conclusions (2)–(3) assert the same for the max function.
--
--   **Formalization Note** The limit is a `Tendsto` along $\mathcal N_{>}(0)$ in $\mathbb R$, so $\delta=0$ is excluded.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 248, paragraph after Definition (1.3)

import Mathlib

open Filter Topology

namespace ClarkeGradients.MaxFunctions

/-- Clarke (1975), p. 248: the one-sided directional derivative
`f'(x; v) = lim_{δ ↓ 0} [f(x + δv) - f(x)] / δ` exists and equals `L`. -/
def HasOneSidedDirDeriv {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x v : EuclideanSpace ℝ (Fin n)) (L : ℝ) : Prop :=
  Tendsto (fun δ : ℝ => (f (x + δ • v) - f x) / δ) (𝓝[>] (0 : ℝ)) (𝓝 L)

end ClarkeGradients.MaxFunctions


