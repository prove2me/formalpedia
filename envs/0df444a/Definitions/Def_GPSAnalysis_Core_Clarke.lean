-- Prove2me | Definitions.Def_GPSAnalysis_Core_Clarke
-- name    : GPSAnalysis_Core_Clarke
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T07:26:54.92521+00:00
-- url     : https://prove2.me/theorems/5f9b14c4-5997-4b69-9b15-01659cb406bf
-- title:
--   Clarke generalized directional derivative (3.1) and strict differentiability
-- statement:
--   Let $g:\mathbb R^n\to\mathbb R$ and $x,d\in\mathbb R^n$. **Clarke's generalized directional derivative** of $g$ at $x$ in the direction $d$ is
--
--   $$g^\circ(x;d)=\limsup_{y\to x,\ t\downarrow 0}\frac{g(y+td)-g(y)}{t},$$
--
--   the limit superior taken jointly as $y\to x$ and $t\to 0^+$, with values in the extended reals (Eq. (3.1) of the paper). For $g$ Lipschitz near $x$ it is finite.
--
--   The function $g$ is **strictly differentiable** at $x$, with strict gradient $\nabla g(x)\in\mathbb R^n$, if for every $w\in\mathbb R^n$
--
--   $$\lim_{y\to x,\ t\downarrow 0}\frac{g(y+tw)-g(y)}{t}=\nabla g(x)^T w .$$
--
--   This is the notion of Section 3.4 of the paper (following Clarke), used there for functions that are Lipschitz near $x$.
--
--   For an extended-valued $f$ that is Lipschitz near $\hat x$, the theorems of the mission apply these definitions to a real function $g$ that agrees with $f$ on a neighbourhood of $\hat x$; both notions depend only on the values near $\hat x$.
--
--   **Formalization Note** The limit superior is taken in `EReal` along the filter $\mathcal N(x)\times\mathcal N_{>0}(0)$, so it is never a default value.
-- source:
--   Audet, Dennis, Analysis of Generalized Pattern Searches, SIAM J. Optim. 13 (2003), p. 897, Eq. (3.1); p. 898, Section 3.4, strict differentiability

import Mathlib

open Filter Topology

namespace GPSAnalysis.Core

/-- Clarke's generalized directional derivative, Eq. (3.1) of Audet–Dennis (2003):
`g°(x; d) = limsup_{y → x, t ↓ 0} (g(y + t d) - g(y)) / t`,
computed for a real-valued `g` as an `EReal`-valued limit superior along `y → x`, `t → 0⁺`. -/
noncomputable def clarkeDirDeriv {n : ℕ} (g : (Fin n → ℝ) → ℝ) (x d : Fin n → ℝ) : EReal :=
  Filter.limsup
    (fun q : (Fin n → ℝ) × ℝ => (((g (q.1 + q.2 • d) - g q.1) / q.2 : ℝ) : EReal))
    (𝓝 x ×ˢ 𝓝[>] (0 : ℝ))

/-- Strict differentiability at `x` as defined in §3.4 (p. 898): there is a vector `grad`
(the strict derivative `D_s g(x)`) such that for every `w ∈ ℝⁿ`,
`lim_{y → x, t ↓ 0} (g(y + t w) - g(y)) / t = grad ᵀ w`. -/
def HasStrictDirGradAt {n : ℕ} (g : (Fin n → ℝ) → ℝ) (grad x : Fin n → ℝ) : Prop :=
  ∀ w : Fin n → ℝ,
    Tendsto (fun q : (Fin n → ℝ) × ℝ => (g (q.1 + q.2 • w) - g q.1) / q.2)
      (𝓝 x ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (grad ⬝ᵥ w))

end GPSAnalysis.Core


