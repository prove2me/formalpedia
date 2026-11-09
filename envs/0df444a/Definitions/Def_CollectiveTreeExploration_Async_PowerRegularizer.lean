-- Prove2me | Definitions.Def_CollectiveTreeExploration_Async_PowerRegularizer
-- name    : CollectiveTreeExploration_Async_PowerRegularizer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:12:41.708623+00:00
-- url     : https://prove2.me/theorems/4015887a-1381-423b-bc70-9f9426094018
-- title:
--   The multiscale power regularizer, its fractional minimizer, and the resistive network of an elongation
-- statement:
--   This file defines the analytic objects of Section 3. All logarithms are natural.
--
--   **Parameters.** For $k\ge2$,
--   $$\varepsilon=\frac{\log(4/3)}{\log(2k)},\qquad p=1+\varepsilon .$$
--
--   **Regularizer and minimizer.** On a weighted tree $T$ the multiscale power regularizer is
--   $$\Phi_T(y)=\sum_{u\ne r}d_u\,y_u^{\,p},$$
--   and the **fractional minimizer** $y$ is a minimizer of $\Phi_T$ over all fractional configurations of mass $k$ (problem (4)). Existence, uniqueness and positivity of the minimizer are the content of Lemma 3.1; the definition makes a choice among minimizers and returns $0$ only when there is none.
--
--   **Approximate lengths and heights.** $\rho_u=d_u\,y_u^{\varepsilon}$ for $u\ne r$, and for a leaf $\ell\preceq u$, $\sum_{v\in\ell\to u}\rho_v$; the approximate height $h_u$ is this sum for the descendant leaf of smallest label (Lemma 3.4 shows that the leaf does not matter).
--
--   **Elongation.** When the leaf edge $(p_l,l)$ grows at unit rate, $\dot y$ is the derivative of the fractional minimizer with respect to $d_l$, $\dot\Phi$ the derivative of $\Phi_T(y)$, and $\|\dot y\|_\rho=\sum_{u\ne r}\rho_u|\dot y_u|$.
--
--   **Elongation network.** The general Ohm–Kirchhoff and wired-subtree resistance definitions are imported from the separate electrical-network item. Network (8) has resistances $r_u=\rho_u/y_u$ and prescribed leaf voltages $V_l=y_l^\varepsilon/\varepsilon$, $V_\ell=0$ for $\ell\ne l$.
--
--   **Formalization Note** $\dot y$ and $\dot\Phi$ use Mathlib's `deriv`, which is $0$ at a point of non-differentiability; Lemma 3.1 proves that the derivative exists. The effective resistance is an infimum of energies over unit flows.
--
--   The actual voltage of network (8) is computed from the independent Dirichlet problem with these resistances and prescribed leaf values. It is not a free potential assumed to satisfy the target identity.
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission #263 (October 2026), source.pdf sha256 54f5e43ddf9269e11a2fff4aa4b0ea62348afe16a38aba551313f43cbf3e00e0; §3.1, p.7, eqs. (2)–(4); Lemma 3.4, p.8 (ρ, h); §3.3, pp.9–10, Lemma 3.6 and network (8); electrical networks, §2.1, p.5

import Mathlib
import Definitions.Def_CollectiveTreeExploration_Async_WeightedTree
import Definitions.Def_CollectiveTreeExploration_Async_ElectricalNetwork

namespace CollectiveTreeExploration.Async

open scoped BigOperators

noncomputable section

open Classical

/-! # The multiscale power regularizer and its fractional minimizer (§3.1, p.7; §3.2–3.3, pp.8–10)

All logarithms are natural. -/

/-- `ε = log(4/3) / log(2k)` (eq. (2), p.7). -/
def eps (k : ℕ) : ℝ := Real.log (4 / 3) / Real.log (2 * (k : ℝ))

/-- The exponent `p = 1 + ε` (eq. (2), p.7). (Not to be confused with the parent `p_u`.) -/
def pexp (k : ℕ) : ℝ := 1 + eps k

namespace WTree

variable (T : WTree)

/-- The multiscale power regularizer `Φ_T(y) = ∑_{u ≠ r} d_u y_u^p` (eq. (3), p.7), with
`y_u` the mass at or below `u`. -/
def Phi (k : ℕ) (y : ℕ → ℝ) : ℝ :=
  ∑ u ∈ T.V.erase T.root, T.len u * (T.mass y u) ^ (pexp k)

/-- `y` is a minimizer of `Φ_T` over all fractional configurations of total mass `k`
(problem (4), p.7: `min Φ_T(y)` subject to `y ≥ 0`, `∑_ℓ y_ℓ = k`). -/
def IsFracMinimizer (k : ℕ) (y : ℕ → ℝ) : Prop :=
  T.IsFracConfig k y ∧ ∀ y' : ℕ → ℝ, T.IsFracConfig k y' → T.Phi k y ≤ T.Phi k y'

/-- The fractional minimizer `y = y(T)` of (4): a chosen minimizer of `Φ_T` over the fractional
configurations of mass `k`. Existence, uniqueness and positivity are the content of Lemma 3.1;
the value `0` is only a total extension for inputs with no minimizer. -/
def fracMin (k : ℕ) : ℕ → ℝ :=
  if h : ∃ y, T.IsFracMinimizer k y then Classical.choose h else fun _ => 0

/-- The approximate edge length `ρ_u = d_u y_u^ε` for the fractional minimizer `y` (Lemma 3.4,
p.8). -/
def rho (k : ℕ) (u : ℕ) : ℝ := T.len u * (T.mass (T.fracMin k) u) ^ (eps k)

/-- `∑_{v ∈ ℓ → u} ρ_v`, the approximate length of the path from a leaf `ℓ ⪯ u` up to `u`. -/
def approxHeightVia (k : ℕ) (u ℓ : ℕ) : ℝ := ∑ v ∈ T.pathVerts ℓ u, T.rho k v

/-- The approximate height `h_u = ∑_{v ∈ ℓ → u} ρ_v` of Lemma 3.4 (p.8), computed along a chosen
descendant leaf `ℓ ⪯ u` (the leaf of smallest label). That the value does not depend on the
choice is part of Lemma 3.4. -/
def hgt (k : ℕ) (u : ℕ) : ℝ :=
  if h : (T.leavesBelow u).Nonempty then T.approxHeightVia k u ((T.leavesBelow u).min' h) else 0

/-! ## Unit-rate elongation of a leaf `l` -/

/-- The derivative `ẏ_v` of the fractional minimizer with respect to the length `d_l` of the leaf
edge `(p_l, l)`, at the current length: the velocity of `y` when `l` is elongated at unit rate.
(`deriv` is `0` where no derivative exists; Lemma 3.1 proves differentiability.) Node values are
`T.mass (T.ydot k l) u`. -/
def ydot (k : ℕ) (l : ℕ) (v : ℕ) : ℝ :=
  deriv (fun L : ℝ => (T.setLen l L).fracMin k v) (T.len l)

/-- `Φ̇ = d/dt Φ_{T(t)}(y(t))` when the leaf edge `(p_l, l)` grows at unit rate. -/
def phiDot (k : ℕ) (l : ℕ) : ℝ :=
  deriv (fun L : ℝ => (T.setLen l L).Phi k ((T.setLen l L).fracMin k)) (T.len l)

/-- The instantaneous movement cost in the metric `ρ`: `‖ẏ‖_ρ = ∑_{u ≠ r} ρ_u |ẏ_u|`
(Lemma 3.8, p.10). -/
def rhoNormYdot (k : ℕ) (l : ℕ) : ℝ :=
  ∑ u ∈ T.V.erase T.root, T.rho k u * |T.mass (T.ydot k l) u|

/-- The resistances `r_u = ρ_u / y_u` of the network (8) (Lemma 3.6, p.9). -/
def netRes (k : ℕ) (u : ℕ) : ℝ := T.rho k u / T.mass (T.fracMin k) u

/-- The leaf voltages of the network (8) for the elongation of `l`: `V_l = y_l^ε / ε`, and
`V_ℓ = 0` for every other leaf. -/
def netVolt (k : ℕ) (l : ℕ) (ℓ : ℕ) : ℝ :=
  if ℓ = l then (T.fracMin k l) ^ (eps k) / eps k else 0

/-- The actual voltage of network (8), obtained by solving its Dirichlet problem. -/
def networkVoltage (k : ℕ) (l : ℕ) : ℕ → ℝ :=
  T.voltage (T.netRes k) (T.netVolt k l)

end WTree

end

end CollectiveTreeExploration.Async


