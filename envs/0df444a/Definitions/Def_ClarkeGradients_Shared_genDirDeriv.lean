-- Prove2me | Definitions.Def_ClarkeGradients_Shared_genDirDeriv
-- name    : ClarkeGradients_Shared_genDirDeriv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:40:22.982198+00:00
-- url     : https://prove2.me/theorems/8762809a-b069-49eb-985b-681763c953fe
-- title:
--   Definition (1.3) — the generalized directional derivative f°(x; v)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ and $x,v\in\mathbb R^n$. The **generalized directional derivative** of $f$ at $x$ in the direction $v$ is
--
--   $$
--   f^\circ(x;v)=\limsup_{h\to 0,\ \delta\downarrow 0}\frac{f(x+h+\delta v)-f(x+h)}{\delta},
--   $$
--
--   the upper limit being taken jointly as $h\to 0$ in $\mathbb R^n$ and $\delta\to 0$ through positive values.
--
--   For locally Lipschitz $f$ the difference quotient is bounded by $K|v|$ near $(0,0^+)$, so $f^\circ(x;v)$ is a finite real number; it is the support function of the generalized gradient $\partial f(x)$ (Proposition (1.4)).
--
--   It serves chunk 01-max-functions (Clarke p. 248, Definition (1.3); used in Proposition (1.4) p. 248 and Theorem (2.1) pp. 251–252) and chunk 02-flow-invariance (Clarke p. 248, Definition (1.3); used in Proposition (1.4) p. 248 and, via $d_E^\circ(e;v)=0$, for the tangent cone of Definition (3.6) p. 256).
--
--   **Formalization Note** The upper limit is Mathlib's `Filter.limsup` in $\mathbb R$ along the product filter $\mathcal N(0)\times\mathcal N_{>}(0)$. As the paper says, the definition is appropriate only for Lipschitz functions: when the quotient is unbounded, `Filter.limsup` in $\mathbb R$ returns a junk value (0), so every theorem using $f^\circ$ assumes $f$ locally Lipschitz.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 248, Definition (1.3)

import Mathlib

open Filter Topology

namespace ClarkeGradients.Shared

/-- Clarke (1975), Definition (1.3): the *generalized directional derivative*
`f°(x; v) = limsup_{h → 0, δ ↓ 0} [f(x + h + δv) - f(x + h)] / δ`,
the `limsup` being taken along `h → 0` in `ℝⁿ` and `δ → 0⁺` jointly.
(As in the paper, this is meaningful for locally Lipschitz `f`, for which the quotient is
bounded near `(0, 0⁺)`.) -/
noncomputable def genDirDeriv {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  limsup (fun p : EuclideanSpace ℝ (Fin n) × ℝ => (f (x + p.1 + p.2 • v) - f (x + p.1)) / p.2)
    (𝓝 (0 : EuclideanSpace ℝ (Fin n)) ×ˢ 𝓝[>] (0 : ℝ))

end ClarkeGradients.Shared


