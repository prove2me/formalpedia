-- Prove2me | Definitions.Def_GainShareOpt_StochBalance_Volterra
-- name    : GainShareOpt_StochBalance_Volterra
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:47:38.68725+00:00
-- url     : https://prove2.me/theorems/3bb095b7-1cee-4d5f-ba5e-83794024897f
-- title:
--   The Volterra operator $T_\alpha$ (75), its fixed point $y_\alpha$, the hitting time $\tau_\alpha$, the profile $g_\alpha$ and $q(\alpha)$
-- statement:
--   For $\alpha\in(1/e,1)$ and a profile $u$, the order-preserving Volterra operator (75) is
--   $$(T_\alpha u)(t)=\max\Bigl\{\frac1e,\ \max_{0\le s\le t}\frac{\alpha-1+e^{-t}+\int_0^se^{-z}u(z)\,dz}{1-t+s}\Bigr\},\qquad 0\le t<1 .$$
--   Its value at $t$ depends only on $u$ on $[0,t]$. A function $y$ is a **fixed profile** if it is continuous on $[0,1)$ and $T_\alpha y=y$ there (equivalently, on every $[0,\eta]$, $\eta<1$). $y_\alpha$ denotes a fixed profile (Lemma 13 asserts that one exists and is unique on $[0,1)$).
--
--   The hitting time $\tau_\alpha$ is the first $t\in[0,1)$ with $y_\alpha(t)=1/e$. The canonical profile is $g_\alpha(t)=y_\alpha(t)$ for $t\le\tau_\alpha$ and $g_\alpha(t)=1/e$ afterwards, and the return value is $q(\alpha)=A(g_\alpha)$.
--
--   **Formalization Note** The inner maximum is `sSup` of the image of $[0,t]$ (a maximum for continuous $u$). $y_\alpha$ is `Classical.epsilon` of the fixed-profile predicate, so its meaning rests on Lemma 13; $\tau_\alpha$ is `sInf` of the hitting set.
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), p. 50, (75); pp. 50–55, Lemmas 13, 15, 17; p. 61, (91)

import Mathlib
import Definitions.Def_GainShareOpt_StochBalance_Normalized

namespace GainShareOpt.StochBalance

/-- The Volterra operator `T_α` of (75)/(91):
`(T_α u)(t) = max{1/e, max_{0 ≤ s ≤ t} (α - 1 + e^{-t} + ∫_0^s e^{-z} u(z) dz)/(1 - t + s)}`.
The inner maximum is written as the supremum of the image of `[0, t]`. Its value at `t` depends
only on `u` on `[0, t]`, so the same formula serves every interval `[0, η]`, `η < 1`. -/
noncomputable def volterraOp (α : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  max (Real.exp (-1))
    (sSup ((fun s => (α - 1 + Real.exp (-t) + ∫ z in (0 : ℝ)..s, Real.exp (-z) * u z)
      / (1 - t + s)) '' Set.Icc 0 t))

/-- `y` is a continuous function on `[0, 1)` whose restriction to each `[0, η]`, `η < 1`, is a
fixed point of `T_α`. -/
def IsFixedProfile (α : ℝ) (y : ℝ → ℝ) : Prop :=
  ContinuousOn y (Set.Ico 0 1) ∧ ∀ t ∈ Set.Ico (0 : ℝ) 1, volterraOp α y t = y t

/-- The fixed point `y_α` of Lemma 13 (a chosen function satisfying `IsFixedProfile α`; Lemma 13
asserts it exists and is unique on `[0, 1)`). -/
noncomputable def fixedProfile (α : ℝ) : ℝ → ℝ :=
  Classical.epsilon (IsFixedProfile α)

/-- The first time `τ_α ∈ [0, 1)` at which `y_α` equals `1/e`. -/
noncomputable def hitTime (α : ℝ) : ℝ :=
  sInf {t | t ∈ Set.Ico (0 : ℝ) 1 ∧ fixedProfile α t = Real.exp (-1)}

/-- The canonical profile `g_α` (Lemma 15): `y_α` up to `τ_α`, then constantly `1/e`. -/
noncomputable def canonProfile (α : ℝ) (t : ℝ) : ℝ :=
  if t ≤ hitTime α then fixedProfile α t else Real.exp (-1)

/-- The return value `q(α) = A(g_α)` (Lemma 17, (101)). -/
noncomputable def returnValue (α : ℝ) : ℝ :=
  scoreA (canonProfile α)

end GainShareOpt.StochBalance


