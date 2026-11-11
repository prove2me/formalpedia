-- Prove2me | Definitions.Def_GainShareOpt_StochBalance_CertFunctional
-- name    : GainShareOpt_StochBalance_CertFunctional
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:47:39.986194+00:00
-- url     : https://prove2.me/theorems/e6b20903-5022-48a2-a14a-70ac3bd7c325
-- title:
--   The certificate functional $L[f]$ (44), the classes $F_0,F_1,F_2$ and $\Gamma(F)$
-- statement:
--   For a set $S\subseteq N_u$ of online neighbours of $u$, the configuration-LP coefficient is $p_u(S)=\min\{|S|p,1\}$ (the capped total assignment probability). The normalized expected dual constraint is
--   $$\frac{\mathbb E_I\bigl[\alpha_u+\sum_{v\in S}\beta_v\bigr]}{w_u\,p_u(S)} .$$
--   The **certificate functional** (44) is
--   $$L[f]=\liminf_{p\downarrow0}\ \inf_I\ \min_{u\in U,\ S\subseteq N_u,\ p_u(S)>0}\frac{\mathbb E_I[\alpha_u+\sum_{v\in S}\beta_v]}{w_u\,p_u(S)},$$
--   where for each $p$ the infimum ranges over all finite instances with that success probability (the worst case is taken before the limit).
--
--   The function classes are $F_0=C^{\uparrow}([0,\infty),[0,1])$ (continuous, non-decreasing, values in $[0,1]$), $F_1=\{f\in F_0: f(1)\le 1-1/e\}$, and $F_2=\{f\in F_1: 1-e^{-z}\le f(z)\le 1-1/e \text{ on } [0,1],\ f(z)=1-1/e \text{ for } z\ge1\}$. The optimal certificate over a class is $\Gamma(F)=\sup_{f\in F}L[f]$.
--
--   $L$ and $\Gamma$ are the quantities in the paper's main theorem (Theorem 3).
--
--   **Formalization Note** The inner $\inf_I\min_{u,S}$ is one real `sInf` over all triples $(I,u,S)$; the liminf is `Filter.liminf` along `nhdsWithin 0 (Set.Ioi 0)`; functions are `ℝ → ℝ` with the $F_0$ conditions imposed on `Set.Ici 0`; $\Gamma(F)$ is `sSup (certL '' F)`.
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), p. 22, (44); p. 6, (7)–(9); p. 3, (2)

import Mathlib
import Definitions.Def_GainShareOpt_StochBalance_Model

open Classical

namespace GainShareOpt.StochBalance

/-- The configuration-LP coefficient `p_u(S) = min{|S| p, 1}`. -/
noncomputable def capCoef {n : ℕ} (p : ℝ) (S : Finset (Fin n)) : ℝ :=
  min ((S.card : ℝ) * p) 1

/-- The normalized expected dual constraint
`E_I[α_u + Σ_{v ∈ S} β_v] / (w_u p_u(S))` of ST-BA(f) on instance `I` with success probability `p`. -/
noncomputable def constraintRatio (I : Instance) (f : ℝ → ℝ) (p : ℝ) (u : Fin I.m)
    (S : Finset (Fin I.n)) : ℝ :=
  expect I p (fun ω => (finalState I f p ω).alpha u + ∑ v ∈ S, (finalState I f p ω).beta v)
    / (I.w u * capCoef p S)

/-- For a fixed success probability `p`: the infimum over all finite instances (with at least one
edge) of the minimum over `u ∈ U`, `S ⊆ N_u` with `p_u(S) > 0` of the normalized constraint. -/
noncomputable def worstRatio (f : ℝ → ℝ) (p : ℝ) : ℝ :=
  sInf {r | ∃ (I : Instance) (u : Fin I.m) (S : Finset (Fin I.n)),
    S ⊆ I.onlineNbrs u ∧ 0 < capCoef p S ∧ r = constraintRatio I f p u S}

/-- The certificate functional (44): `L[f] = liminf_{p ↓ 0} worstRatio f p`. -/
noncomputable def certL (f : ℝ → ℝ) : ℝ :=
  Filter.liminf (fun p => worstRatio f p) (nhdsWithin 0 (Set.Ioi 0))

/-- `F0 = C↑([0, ∞), [0, 1])`: continuous non-decreasing functions `[0, ∞) → [0, 1]` (7). -/
def F0 : Set (ℝ → ℝ) :=
  {f | ContinuousOn f (Set.Ici 0) ∧ MonotoneOn f (Set.Ici 0) ∧
    ∀ z, 0 ≤ z → 0 ≤ f z ∧ f z ≤ 1}

/-- `F1 = {f ∈ F0 : f(1) ≤ 1 - 1/e}` (8). -/
def F1 : Set (ℝ → ℝ) :=
  {f | f ∈ F0 ∧ f 1 ≤ 1 - Real.exp (-1)}

/-- `F2` (9): `f ∈ F1`, `1 - e^{-z} ≤ f(z) ≤ 1 - 1/e` on `[0, 1]`, `f(z) = 1 - 1/e` for `z ≥ 1`. -/
def F2 : Set (ℝ → ℝ) :=
  {f | f ∈ F1 ∧ (∀ z ∈ Set.Icc (0 : ℝ) 1, 1 - Real.exp (-z) ≤ f z ∧ f z ≤ 1 - Real.exp (-1)) ∧
    ∀ z, 1 ≤ z → f z = 1 - Real.exp (-1)}

/-- The optimal certificate `Γ(F) = sup_{f ∈ F} L[f]` (2)/(3), with `L` the functional (44). -/
noncomputable def certCapacity (F : Set (ℝ → ℝ)) : ℝ :=
  sSup (certL '' F)

end GainShareOpt.StochBalance


