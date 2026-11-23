-- Prove2me | Definitions.Def_ThinFlowSP_Breakpoints_Supplement_FluidModel
-- name    : ThinFlowSP_Breakpoints_Supplement_FluidModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:40:47.886062+00:00
-- url     : https://prove2.me/theorems/9c1e0d3b-24b0-4365-8cb1-6bbb290e43d9
-- title:
--   §§2–3, pp. 3–4, Definition 1 — fluid queuing network, flows over time, (QD), feasibility, earliest times, dynamic equilibria
-- statement:
--   The fluid queuing model of Kaiser, §§2–3.
--
--   1. **Network.** A finite directed multigraph $G=(V,A)$ with source $s$ and sink $t\ne s$, capacities $\nu\in\mathbb R^A_{>0}$ and delays $\tau\in\mathbb R^A_{\ge0}$, with no directed cycle of zero total transit time and an $s$–$v$-path for every vertex $v$.
--   2. **Inflow rate.** A locally integrable $\nu_0:\mathbb R\to\mathbb R$, non-negative and vanishing almost everywhere on $\mathbb R_{<0}$. The distance $\ell^0_v$ is the smallest total delay of an $s$–$v$-path.
--   3. **Flow over time.** Non-negative, locally integrable arc inflow and outflow rates $f^+_a,f^-_a$ vanishing almost everywhere on $\mathbb R_{<0}$, with cumulative flows $F^\pm_a(\vartheta)=\int_0^\vartheta f^\pm_a$.
--   4. **Feasibility.** For every arc, $z_a(\vartheta)=F^+_a(\vartheta)-F^-_a(\vartheta+\tau_a)$ is the locally absolutely continuous solution of the queuing dynamics
--   $$z_a\equiv0\text{ on }\mathbb R_{\le0},\qquad \frac{dz_a}{d\vartheta}(\vartheta)=\begin{cases}[f^+_a(\vartheta)-\nu_a]_+ & z_a(\vartheta)\le0\\ f^+_a(\vartheta)-\nu_a & z_a(\vartheta)>0\end{cases}\quad\text{for a.e. }\vartheta\ge0,\tag{QD}$$
--   and strict flow conservation $\sum_{a\in\delta^+(v)}f^+_a-\sum_{a\in\delta^-(v)}f^-_a=\nu_0$ at $v=s$ and $=0$ at $v\notin\{s,t\}$ holds almost everywhere.
--   5. **Earliest times.** The queuing delay is $q_a(\vartheta)=\min\{q\ge0:F^-_a(\vartheta+\tau_a+q)\ge F^+_a(\vartheta)\}$, the exit time $T_a(\vartheta)=\vartheta+q_a(\vartheta)+\tau_a$, and $\ell_v(\vartheta)$ is the minimum over $s$–$v$-paths $P=(a_1,\dots,a_k)$ of $T_{a_k}\circ\dots\circ T_{a_1}(\vartheta)$. An arc $a=(v,w)$ is active relative to $\vartheta$ if $\ell_w(\vartheta)=T_a(\ell_v(\vartheta))$.
--   6. **Dynamic equilibrium (Definition 1).** A feasible flow over time such that for each arc $a=(v,w)$ the inflow rate $f^+_a$ vanishes almost everywhere on $\{\ell_v(\vartheta):a\text{ inactive relative to }\vartheta\in\mathbb R\}$.
--
--   These are the objects of Theorems 19, 24 and 25.
--
--   **Formalization Note** The network extends the base mission's multigraph `Net`. The path minimum defining $\ell$ is taken over walks, which gives the same value because each $T_a$ is non-decreasing with $T_a(\vartheta)\ge\vartheta$; `IsEarliestTimes` states it with `IsLeast`, so the minimum must be attained. Feasibility requires the link-equation function $F^+_a-F^-_a(\cdot+\tau_a)$ itself to solve (QD); since (QD) has a unique solution this is the paper's condition. $q_a$ is an infimum, which is the paper's minimum for feasible flows. `IsDynEqWith N ν0 fp fm ℓ` bundles a dynamic equilibrium with its earliest times function $\ell$.
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, pp. 3–4, §2 (network, inflow rate, flow over time, (QD), feasibility, q_a, T_a, ℓ, (BE), active arcs), Definition 1; Theorem 19, p. 12 (ℓ⁰)

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Network

open MeasureTheory

noncomputable section

namespace ThinFlowSP.Breakpoints.Supplement

open ThinFlowSP.Breakpoints

/-- The sub-multigraph of `G` with the same vertices, source and sink, and arc set `S`. -/
def subNet (G : Net) (S : Finset G.A) : Net where
  V := G.V
  A := {a : G.A // a ∈ S}
  tail b := G.tail b.1
  head b := G.head b.1
  s := G.s
  t := G.t

/-- `IsWalk G u p v`: the list of arcs `p = (a₁, …, a_k)` is a directed `u`–`v`-walk in `G`
(the empty list is the walk of length zero from `u` to `u`). -/
def IsWalk (G : Net) : G.V → List G.A → G.V → Prop
  | u, [], v => u = v
  | u, a :: p, v => G.tail a = u ∧ IsWalk G (G.head a) p v

/-- A network of the fluid queuing model (§2, p. 3): a finite directed multigraph `G` with
source `G.s` and sink `G.t`, arc capacities `ν` and transit times (delays) `τ`. -/
structure QNet where
  G : Net
  ν : G.A → ℝ
  τ : G.A → ℝ

/-- The standing assumptions of §2 (p. 3): the source `s` and the sink `t` of the commodity are
distinct, capacities are positive, delays are non-negative, there is no directed cycle of zero
total transit time (equivalently, as delays are non-negative, the arcs of delay `0` are
acyclic), and every vertex is reachable from `s`. -/
def QNet.Standing (N : QNet) : Prop :=
  N.G.s ≠ N.G.t ∧ (∀ a, 0 < N.ν a) ∧ (∀ a, 0 ≤ N.τ a) ∧
  IsAcyclic (subNet N.G (Finset.univ.filter fun a => N.τ a = 0)) ∧
  ∀ v, Reaches N.G N.G.s v

/-- An inflow rate (§2, p. 3): a locally integrable function `ν₀ : ℝ → ℝ` that is non-negative
almost everywhere and vanishes almost everywhere on `ℝ_{<0}`. -/
def IsInflowRate (ν0 : ℝ → ℝ) : Prop :=
  LocallyIntegrable ν0 ∧ (∀ᵐ θ, 0 ≤ ν0 θ) ∧ (∀ᵐ θ, θ < 0 → ν0 θ = 0)

/-- `ℓ⁰_v`, the shortest distance from `s` to `v` in `G` with respect to the delays `τ`
(Theorem 19, p. 12): the infimum of the total delay over all directed `s`–`v`-walks. Under
`QNet.Standing` the set is nonempty and bounded below by `0`. -/
def dist0 (N : QNet) (v : N.G.V) : ℝ :=
  sInf {c : ℝ | ∃ p : List N.G.A, IsWalk N.G N.G.s p v ∧ c = (p.map N.τ).sum}

/-- The cumulative function `F(ϑ) = ∫_0^ϑ f(θ) dθ` of a rate `f` (an interval integral, so it is
`-∫_ϑ^0 f` for `ϑ < 0`). -/
def cum (f : ℝ → ℝ) (ϑ : ℝ) : ℝ := ∫ θ in (0 : ℝ)..ϑ, f θ

/-- The queuing dynamics (QD) of an arc of capacity `νa` and inflow rate `fpa` (p. 3): `z` vanishes
on `ℝ_{≤0}`, is locally absolutely continuous (absolutely continuous on every bounded interval),
and for almost every `ϑ ≥ 0` has derivative `[fpa ϑ - νa]_+` if `z ϑ ≤ 0` and `fpa ϑ - νa` if
`z ϑ > 0`. -/
def IsQueueSolution (νa : ℝ) (fpa z : ℝ → ℝ) : Prop :=
  (∀ ϑ ≤ 0, z ϑ = 0) ∧ (∀ a b : ℝ, AbsolutelyContinuousOnInterval z a b) ∧
  ∀ᵐ ϑ, 0 ≤ ϑ → HasDerivAt z (if z ϑ ≤ 0 then max (fpa ϑ - νa) 0 else fpa ϑ - νa) ϑ

/-- A flow over time (p. 3): arc inflow rates `fp a` (`f⁺_a`) and outflow rates `fm a` (`f⁻_a`),
non-negative, locally integrable and vanishing almost everywhere on `ℝ_{<0}`. -/
def IsFlowOverTime (N : QNet) (fp fm : N.G.A → ℝ → ℝ) : Prop :=
  ∀ a, (∀ ϑ, 0 ≤ fp a ϑ) ∧ (∀ ϑ, 0 ≤ fm a ϑ) ∧
    LocallyIntegrable (fp a) ∧ LocallyIntegrable (fm a) ∧
    (∀ᵐ ϑ, ϑ < 0 → fp a ϑ = 0) ∧ (∀ᵐ ϑ, ϑ < 0 → fm a ϑ = 0)

/-- The queue length of arc `a` forced by the link equation `z_a(ϑ) = F⁺_a(ϑ) - F⁻_a(ϑ + τ_a)`
(p. 3). -/
def queueLen (N : QNet) (fp fm : N.G.A → ℝ → ℝ) (a : N.G.A) (ϑ : ℝ) : ℝ :=
  cum (fp a) ϑ - cum (fm a) (ϑ + N.τ a)

/-- Feasibility (p. 3): a flow over time such that, on every arc, the function
`ϑ ↦ F⁺_a(ϑ) - F⁻_a(ϑ + τ_a)` is the queue length `z_a`, i.e. the locally absolutely continuous
solution of (QD), and strict flow conservation holds for almost every `ϑ` at every vertex other
than the sink: `∑_{δ⁺(v)} f⁺_a(ϑ) - ∑_{δ⁻(v)} f⁻_a(ϑ)` is `ν₀(ϑ)` at `s` and `0` elsewhere. -/
def IsFeasible (N : QNet) (ν0 : ℝ → ℝ) (fp fm : N.G.A → ℝ → ℝ) : Prop :=
  IsFlowOverTime N fp fm ∧
  (∀ a, IsQueueSolution (N.ν a) (fp a) (queueLen N fp fm a)) ∧
  ∀ᵐ ϑ, ∀ v, v ≠ N.G.t →
    outflow N.G (fun a => fp a ϑ) v - inflow N.G (fun a => fm a ϑ) v =
      if v = N.G.s then ν0 ϑ else 0

/-- The queuing delay `q_a(ϑ) = min {q ≥ 0 : F⁻_a(ϑ + τ_a + q) ≥ F⁺_a(ϑ)}` (p. 4). -/
def qDelay (N : QNet) (fp fm : N.G.A → ℝ → ℝ) (a : N.G.A) (ϑ : ℝ) : ℝ :=
  sInf {q : ℝ | 0 ≤ q ∧ cum (fp a) ϑ ≤ cum (fm a) (ϑ + N.τ a + q)}

/-- The exit time `T_a(ϑ) = ϑ + q_a(ϑ) + τ_a` of a particle entering arc `a` at time `ϑ` (p. 4). -/
def exitTime (N : QNet) (fp fm : N.G.A → ℝ → ℝ) (a : N.G.A) (ϑ : ℝ) : ℝ :=
  ϑ + qDelay N fp fm a ϑ + N.τ a

/-- The arrival time `ℓ_P(ϑ) = T_{a_k} ∘ ⋯ ∘ T_{a_1}(ϑ)` at the end of the arc list
`P = (a₁, …, a_k)` for a particle entering it at time `ϑ` (p. 4). -/
def exitAlong (N : QNet) (fp fm : N.G.A → ℝ → ℝ) : List N.G.A → ℝ → ℝ
  | [], ϑ => ϑ
  | a :: p, ϑ => exitAlong N fp fm p (exitTime N fp fm a ϑ)

/-- `ℓ` is the earliest times function of the flow over time `(fp, fm)` (p. 4): for every time `ϑ`
and vertex `v`, `ℓ ϑ v` is the minimum of `ℓ_P(ϑ)` over the directed `s`–`v`-walks `P`. -/
def IsEarliestTimes (N : QNet) (fp fm : N.G.A → ℝ → ℝ) (ℓ : ℝ → N.G.V → ℝ) : Prop :=
  ∀ ϑ v, IsLeast {r : ℝ | ∃ p, IsWalk N.G N.G.s p v ∧ r = exitAlong N fp fm p ϑ} (ℓ ϑ v)

/-- Arc `a = (v, w)` is active relative to time `ϑ` (p. 4): it attains the minimum in the Bellman
equations (BE), `ℓ_w(ϑ) = T_a(ℓ_v(ϑ))`. -/
def IsActive (N : QNet) (fp fm : N.G.A → ℝ → ℝ) (ℓ : ℝ → N.G.V → ℝ) (a : N.G.A) (ϑ : ℝ) :
    Prop :=
  ℓ ϑ (N.G.head a) = exitTime N fp fm a (ℓ ϑ (N.G.tail a))

/-- Definition 1 (p. 4), with its earliest times function: `(fp, fm)` is a feasible flow over time
for the inflow rate `ν₀`, `ℓ` is its earliest times function, and for each arc `a = (v, w)` the
inflow rate `f⁺_a` vanishes almost everywhere on `{ℓ_v(ϑ) : a inactive relative to ϑ ∈ ℝ}`. -/
def IsDynEqWith (N : QNet) (ν0 : ℝ → ℝ) (fp fm : N.G.A → ℝ → ℝ) (ℓ : ℝ → N.G.V → ℝ) : Prop :=
  IsFeasible N ν0 fp fm ∧ IsEarliestTimes N fp fm ℓ ∧
  ∀ a, ∀ᵐ x, x ∈ {y : ℝ | ∃ ϑ, y = ℓ ϑ (N.G.tail a) ∧ ¬ IsActive N fp fm ℓ a ϑ} → fp a x = 0

/-- Definition 1 (p. 4): `(fp, fm)` is a dynamic equilibrium for the inflow rate `ν₀`. -/
def IsDynEq (N : QNet) (ν0 : ℝ → ℝ) (fp fm : N.G.A → ℝ → ℝ) : Prop :=
  ∃ ℓ : ℝ → N.G.V → ℝ, IsDynEqWith N ν0 fp fm ℓ

end ThinFlowSP.Breakpoints.Supplement


