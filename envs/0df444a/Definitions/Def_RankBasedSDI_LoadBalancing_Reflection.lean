-- Prove2me | Definitions.Def_RankBasedSDI_LoadBalancing_Reflection
-- name    : RankBasedSDI_LoadBalancing_Reflection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:27:46.421036+00:00
-- url     : https://prove2.me/theorems/c5dca4f4-7b5a-4b94-b04a-4e06db26fc93
-- title:
--   $C^{\uparrow}_0$ paths, the complementarity $\int_{[0,\infty)} x\,dz=0$ and the Skorokhod regulator $\sup_{s\le t} y^-(s)$
-- statement:
--   These are the one-dimensional reflection objects used throughout the paper. All paths are real functions of time $t\ge0$.
--
--   1. $f\in C^{\uparrow}_0(\mathbb R_+,\mathbb R_+)$ if $f$ is continuous and nondecreasing on $[0,\infty)$ and $f(0)=0$.
--   2. For paths $x,z$, the **complementarity condition** is
--
--   $$
--   \int_{[0,\infty)} x(t)\,dz(t) = 0 \qquad\text{with the convention } z(0-)=0 .
--   $$
--
--   Here $dz$ is the Lebesgue–Stieltjes measure of the nondecreasing, right-continuous function equal to $z$ on $[0,\infty)$ and to $0$ on $(-\infty,0)$. The condition includes the requirement that this extension is nondecreasing and right-continuous, and the value $z(0)$ is an atom at $t=0$.
--   3. The **Skorokhod regulator** of a path $y$ is $z(t)=\sup_{s\in[0,t]} y^-(s)$ with $y^-=\max(-y,0)$. The one-dimensional Skorokhod map is $\Gamma(y)=(x,z)$ with $x=y+z$.
--
--   The complementarity condition is the condition $\int_0^\infty X_i\,dL_i=0$ of (SDER) and (SDIR) and of (4.9). The regulator defines the Skorokhod map $\Gamma$ of §4.1.
--
--   **Formalization Note** The integral is a `lintegral` of $\max(x,0)$ against `StieltjesFunction.measure` of the zero-extended path, so it is never a junk value; wherever it is used, $x\ge0$ on $[0,\infty)$ holds or is assumed. The regulator is a real `sSup` of the image of $[0,t]$. For a càdlàg $y$ and $t\ge0$ this set is nonempty and bounded, so the `sSup` is the true supremum.
-- source:
--   Atar & Ichiba, Rank-Based Stochastic Differential Inclusions and Diffusion Limits for a Load Balancing Model, arXiv:2409.15121v1, p. 3, §1.1 (C↑₀); pp. 6, 8, (SDER), (SDIR); p. 11, Skorokhod map Γ and Lemma 4.2

import Mathlib

open MeasureTheory

namespace RankBasedSDI.LoadBalancing

/-!
Atar & Ichiba, arXiv:2409.15121v1, §1.1 p. 3, (SDER)/(SDIR) pp. 6–8 and §4.1 p. 11: the
one-dimensional reflection objects. Paths are `ℝ → ℝ`, used only at times `t ≥ 0`.
-/

/-- `f ∈ C↑₀(ℝ₊, ℝ₊)` (§1.1): continuous on `[0, ∞)`, nondecreasing there, and `f(0) = 0`. -/
def IsC0Up (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ici 0) ∧ MonotoneOn f (Set.Ici 0) ∧ f 0 = 0

/-- **Complementarity** `∫_{[0,∞)} x(t) dz(t) = 0` with the convention `z(0−) = 0`
(Lemma 4.2; also `∫_0^∞ X_i dL_i = 0` in (SDER), (SDIR), (4.9)). The integrator is the
Lebesgue–Stieltjes measure of `z` extended by `0` on `(−∞, 0)`, so `z(0)` is an atom at `0`.
The condition requires that this extension be a Stieltjes function (nondecreasing and
right-continuous; for `z ≥ 0` this is "`z` nondecreasing and right-continuous on `[0, ∞)`"),
and the integral of `x⁺` is a `lintegral`, so it is never a junk value. -/
def StieltjesComplementary (x z : ℝ → ℝ) : Prop :=
  ∃ G : StieltjesFunction ℝ, (∀ t : ℝ, G t = if 0 ≤ t then z t else 0) ∧
    ∫⁻ t in Set.Ici 0, ENNReal.ofReal (x t) ∂G.measure = 0

/-- The regulator of the one-dimensional Skorokhod map `Γ(y) = (x, z)` (§4.1, p. 11):
`z(t) = sup_{s ∈ [0,t]} y⁻(s)`, with `y⁻ = max(−y, 0)`. For `y ∈ D(ℝ₊, ℝ)` and `t ≥ 0` the set
is nonempty and bounded, so the real `sSup` is the true supremum. -/
noncomputable def skorokhodReg (y : ℝ → ℝ) (t : ℝ) : ℝ :=
  sSup ((fun s => max (-y s) 0) '' Set.Icc 0 t)

end RankBasedSDI.LoadBalancing


