-- Prove2me | Definitions.Def_SideConstrainedDTA_Existence_Setting
-- name    : SideConstrainedDTA_Existence_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:43.156736+00:00
-- url     : https://prove2.me/theorems/d002c217-4e3b-4c3f-ac05-2293a151bd14
-- title:
--   §3, §5, §7, pp. 10–45 — walk inflows Λ(Q), weak convergence, DTC equilibrium (3), deviations (17)–(18), SCDE (19), constraint set (23), deviation sets (24) and (26), penalties, assumptions (A1)–(A22)
-- statement:
--   This file fixes the dynamic traffic model of Graf and Harks and every object that the existence theorem for side-constrained dynamic equilibria refers to.
--
--   **The network.** There is a finite set $I$ of commodities, a finite set $\mathcal P$ of walks and a set $E$ of edges. Every walk $p$ belongs to one commodity, and $\mathcal P_i$ denotes the walks of commodity $i$ (these sets are disjoint). A walk $p=(v_1,\dots,v_{|p|+1})$ is described by the list of its $|p|$ edges, in order and with multiplicity. Time runs over a planning horizon $[t_0,t_f]\subseteq\mathbb R_{\ge0}$; commodity $i$ has a flow volume $Q_i\ge0$ and walk $p$ an inflow-rate bound $B_p\ge0$.
--
--   **Walk inflows.** A walk inflow assigns to every walk $p$ a rate $h_p(t)$. The feasible inflows with departure time choice form
--   $$\Lambda(Q)=\Big\{h\ \Big|\ \textstyle\sum_{p\in\mathcal P_i}\int_{t_0}^{t_f}h_p(t)\,dt=Q_i\ \forall i,\quad 0\le h_p\le B_p\ \text{a.e. on }[t_0,t_f]\Big\},$$
--   with each $h_p$ measurable and zero outside $[t_0,t_f]$. Such inflows are bounded and hence lie in $L^2([t_0,t_f])^{\mathcal P}$. The scalar product is $\langle g,h\rangle=\sum_p\int_{t_0}^{t_f}g_p(t)h_p(t)\,dt$, and a sequence $h^n$ **converges weakly** to $h$ if $\langle g,h^n\rangle\to\langle g,h\rangle$ for every $g$ with square-integrable components on $[t_0,t_f]$.
--
--   **The flow model.** The model provides an effective walk delay $\Psi_p(h,t)$, arrival times $\tau^j_p(h,t)$ (the time at which a particle entering walk $p$ at time $t$ reaches the $j$-th node of $p$, i.e. enters the $j$-th edge), edge loads $f_e(h,\theta)$ and edge capacities $c_e(\theta)$. The standing model requires $\Psi_p(h,t)\ge0$ and $\tau^j_p(h,t)\ge0$ for $h\in\Lambda(Q)$ and $t\in[t_0,t_f]$.
--
--   **Unconstrained equilibrium (3).** For a delay operator $\Phi$, $h^*\in\Lambda(Q)$ is a dynamic equilibrium with fixed flow volumes and departure time choice if for every commodity $i$ there is $\nu_i\in\mathbb R$ with, for almost all $t\in[t_0,t_f]$ and all $p\in\mathcal P_i$,
--   $$h^*_p(t)>0\Rightarrow\Phi_p(h^*,t)\le\nu_i,\qquad h^*_p(t)<B_p\Rightarrow\Phi_p(h^*,t)\ge\nu_i .$$
--
--   **Deviations and SCDE.** A deviation $(q,\gamma,\Delta)$ from walk $p$ moves the flow $\gamma$ off $p$ and the time-shifted flow $\gamma(\cdot-\Delta)$ onto $q$:
--   $$H_{p\to q}(h,\gamma,\Delta)_w(t)=h_w(t)-[w=p]\,\gamma(t)+[w=q]\,\gamma(t-\Delta).\qquad(17)$$
--   A correspondence $A_p(h)$ lists the admissible deviations. The admissible alternatives at time $t$ are
--   $$U_p(h,t)=\Big\{(q,\Delta)\in\mathcal P_i\times\mathbb R\ \Big|\ \forall\delta,\varepsilon>0\ \exists\gamma:\ 0\le\gamma\le\varepsilon,\ \operatorname{supp}\gamma\subseteq[t-\delta,t+\delta],\ \textstyle\int_{t_0}^{t_f}\gamma>0,\ (q,\gamma,\Delta)\in A_p(h)\Big\},\qquad(18)$$
--   where $i$ is the commodity of $p$ and $\gamma$ is measurable and vanishes outside $[t_0,t_f]$. Given a constraint set $S$, a flow $h^*$ is a **side-constrained dynamic equilibrium (SCDE)** w.r.t. $S$ and $A$ if $h^*\in S$ and
--   $$\Psi_p(h^*,t)\le\Psi_q(h^*,t+\Delta)\quad\text{for all }p,\ t\in[t_0,t_f],\ (q,\Delta)\in U_p(h^*,t).\qquad(19)$$
--
--   **Edge capacities.** The capacity-feasible flows are $S=\{h\in\Lambda(Q)\mid f_e(h,\theta)\le c_e(\theta)\ \forall e,\ \theta\ge0\}$ (23). The deviation set (24) (**strong LPDE**) admits $(q,\gamma,\Delta)$ with $H_{p\to q}(h,\gamma,\Delta)\in\Lambda(Q)$ such that $f_e(h,\tau^j_q(h,t))<c_e(\tau^j_q(h,t))$ for every edge $e=(v_j,v_{j+1})$ of $q$ and every $t\in\operatorname{supp}(\gamma)+\Delta$. The deviation set (26) (**strong MNSDE**) admits in addition $(q,\gamma,0)$ with $H_{p\to q}(h,\gamma,0)\in\Lambda(Q)$ for which $p$ and $q$ share a common prefix $w$, $q=w\tilde q$, and the strict inequality holds for the edges of $\tilde q$ and $t\in\operatorname{supp}\gamma$.
--
--   **Penalties.** $\xi_e(h,\theta)=\max\{0,f_e(h,\theta)-c_e(\theta)\}$, $\xi_p(h,t)=\sum_{e=(v_j,v_{j+1})\in p}\xi_e(h,\tau^j_p(h,t))$, the penalized delay $\Psi^\lambda_p=\Psi_p+\lambda\xi_p$, and the truncation $\Psi|^M_p=\min\{\Psi_p,M\}$ (Definition 5.6).
--
--   **Assumptions.** (A1) $\Phi_p(h,\cdot)$ bounded on $[t_0,t_f]$ for $h\in\Lambda(Q)$; (A2) every $\mathcal P_i$ is non-empty; (A3) $\Lambda(Q)\ne\emptyset$; (A4) $h\mapsto\Phi_p(h,\cdot)$ maps weakly convergent sequences in $\Lambda(Q)$ to $L^2$-convergent ones; (A5) $\Psi_p(h,\cdot)$ continuous on $[t_0,t_f]$ for $h\in S$; (A9) $f_e(h,0)\le c_e(0)$; (A10) for every $h\in\Lambda(Q)$ and $i$ some $p\in\mathcal P_i$ and a positive-measure $J\subseteq[t_0,t_f]$ with $h_p<B_p$ and $f_e(h,\tau^j_p(h,t))\le c_e(\tau^j_p(h,t))$ for all edges of $p$ and $t\in J$; (A11) $c_e\ge0$; (A12) $c_e$ non-decreasing; (A13) $f_e(h,\cdot)$ continuous; (A14) $f_e(h^n,\cdot)\to f_e(h,\cdot)$ uniformly along weakly convergent $h^n\to h$; (A15) the principle of causation; (A16) $\tau^j_p(h^n,\cdot)\to\tau^j_p(h,\cdot)$ uniformly; (A17) walks with a common prefix have equal arrival times along it; (A18) $\Psi_p(h,\cdot)$ continuous and $\Psi_p(h^n,\cdot)\to\Psi_p(h,\cdot)$ uniformly; (A19) $\Psi_p(h,t)\le M$ for all $h\in S$ and a.a. $t$; (A22) $c_e$ continuous on $\mathbb R_{\ge0}$.
--
--   These are the objects of Sections 3, 5 and 7 of the paper; every theorem of the mission is stated in terms of them.
--
--   **Formalization Note.** Inflows, deviations $\gamma$ and test functions are real functions (representatives), not $L^2$ classes: the bounds of $\Lambda(Q)$ hold almost everywhere, while the support and size conditions on $\gamma$ in (18), (24), (26) hold pointwise on the chosen representative (the paper's "some representative of $\gamma$", p. 33); "$t\in\operatorname{supp}(\gamma)+\Delta$" is read as $\gamma(t-\Delta)\ne0$. The node index is 0-based: `tau h p j t` is the paper's $\tau^{j+1}_p(h,t)$, and the edge `(edges p)[j]` is entered at time `tau h p j t`. (17) is read additively, also when $q=p$. The condition $H_{p\to q}(h,\gamma,\Delta)\in\Lambda(Q)$, which §7 adds implicitly to every deviation set, is written into (24) and (26). Delays are real-valued (the paper allows $+\infty$; (A1) or (A19) exclude it where used). Measurability of $\tau^j_p(h,\cdot)$ on $[t_0,t_f]$ is an added standing convention. "Converges uniformly" in (A14), (A16), (A18) and the $L^2$ convergence in (A4) are convergence to the value at the weak limit; (A9), (A13), (A14), (A15) quantify over inflows in $\Lambda(Q)$. (A17) is posed for every $h\in\Lambda(Q)$ (the paper writes $h\in S$; the proof of Theorem 7.6 applies it to infeasible flows). (A22) is from p. 45 and is not an assumption of Theorem 7.6 in the paper. Only the model with departure time choice is formalized.
-- source:
--   Graf, Harks, Side-Constrained Dynamic Traffic Equilibria, arXiv:2211.03194v3, pp. 10–45: Λ(Q) p. 10, Definition 3.1 (3) p. 10, (A1) p. 11, (A2)–(A4) and the scalar product p. 12, (17) p. 20, (18), (A5), Definition 5.1 (19) p. 21, Definition 5.6 p. 23, §7 conventions p. 33, (23), (24) p. 34, (26) p. 35, Definition 7.2 p. 36, (A9)–(A12) p. 38, (A13)–(A19) p. 39, penalties p. 40, (A22) p. 45

import Mathlib

open MeasureTheory Set Filter Topology

namespace SideConstrainedDTA.Existence

/-- §3 and §7 of Graf–Harks (arXiv:2211.03194v3), pp. 10, 33–34: a network model with
commodities `I`, walks `W` and edges `E`. Walk inflows are functions `h : W → ℝ → ℝ`
(`h p t` is the inflow rate into walk `p` at time `t`).

* `com p` is the commodity of walk `p` (so `P_i = {p | com p = i}`, disjoint by construction);
* `edges p` lists the edges of `p` in order, with multiplicity (`|p| = (edges p).length`);
* `[t0, tf]` is the planning horizon, `Q i` the flow volume of commodity `i`, `B p` the
  inflow-rate bound of walk `p`;
* `Psi h p t` is the effective walk delay `Ψ_p(h, t)`;
* `tau h p j t` is the arrival time `τ^{j+1}_p(h, t)` at the `(j+1)`-st node of `p`
  (0-based node index: `j = 0` is the start node, and the edge `(edges p)[j]` is entered at
  time `tau h p j t`);
* `f h e θ` is the edge load `f_e(h, θ)` and `c e θ` the capacity `c_e(θ)`. -/
structure Model (I W E : Type*) where
  com : W → I
  edges : W → List E
  t0 : ℝ
  tf : ℝ
  Q : I → ℝ
  B : W → ℝ
  Psi : (W → ℝ → ℝ) → W → ℝ → ℝ
  tau : (W → ℝ → ℝ) → W → ℕ → ℝ → ℝ
  f : (W → ℝ → ℝ) → E → ℝ → ℝ
  c : E → ℝ → ℝ

variable {I W E : Type*}

/-- Basic data conventions (p. 10): `0 ≤ t0 ≤ tf`, `Q_i ≥ 0`, `B_p ≥ 0`. -/
def Model.Basic (N : Model I W E) : Prop :=
  0 ≤ N.t0 ∧ N.t0 ≤ N.tf ∧ (∀ i, 0 ≤ N.Q i) ∧ ∀ p, 0 ≤ N.B p

/-- `Λ(Q)` (p. 10): measurable inflows with `0 ≤ h_p ≤ B_p` a.e. on `[t0, tf]`, zero a.e.
outside `[t0, tf]`, and `∑_{p ∈ P_i} ∫_{t0}^{tf} h_p = Q_i` for every commodity `i`. -/
def Lam [Fintype W] [DecidableEq I] (N : Model I W E) (h : W → ℝ → ℝ) : Prop :=
  (∀ p, Measurable (h p)) ∧
  (∀ p, ∀ᵐ t, (t ∈ Icc N.t0 N.tf → 0 ≤ h p t ∧ h p t ≤ N.B p) ∧
      (t ∉ Icc N.t0 N.tf → h p t = 0)) ∧
  ∀ i, ∑ p ∈ Finset.univ.filter (fun p => N.com p = i), ∫ t in Icc N.t0 N.tf, h p t = N.Q i

/-- Standing model (§3, §7): basic conventions, non-negative walk delays and arrival times on
`[t0, tf]` for inflows in `Λ(Q)`, and measurability of the arrival times `τ^j_p(h, ·)` on
`[t0, tf]` (an added convention). -/
def Model.Standing [Fintype W] [DecidableEq I] (N : Model I W E) : Prop :=
  N.Basic ∧ ∀ h, Lam N h → ∀ p,
    (∀ t ∈ Icc N.t0 N.tf, 0 ≤ N.Psi h p t) ∧
    ∀ j, j ≤ (N.edges p).length →
      Measurable (fun t : Icc N.t0 N.tf => N.tau h p j t) ∧
      ∀ t ∈ Icc N.t0 N.tf, 0 ≤ N.tau h p j t

/-- The scalar product `⟨g, h⟩ = ∑_p ∫_{t0}^{tf} g_p(t) h_p(t) dt` (p. 12). -/
noncomputable def pair [Fintype W] (N : Model I W E) (g h : W → ℝ → ℝ) : ℝ :=
  ∑ p, ∫ t in Icc N.t0 N.tf, g p t * h p t

/-- Weak convergence in `L²([t0, tf])^P` (p. 12), tested against every `g` with square
integrable components on `[t0, tf]`. -/
def WeakTendsto [Fintype W] (N : Model I W E) (hs : ℕ → W → ℝ → ℝ) (h : W → ℝ → ℝ) : Prop :=
  ∀ g : W → ℝ → ℝ, (∀ p, MemLp (g p) 2 (volume.restrict (Icc N.t0 N.tf))) →
    Tendsto (fun n => pair N g (hs n)) atTop (𝓝 (pair N g h))

/-- A weakly convergent sequence of inflows in `Λ(Q)` with its weak limit in `Λ(Q)`. -/
def WeakConvSeq [Fintype W] [DecidableEq I] (N : Model I W E) (hs : ℕ → W → ℝ → ℝ)
    (h : W → ℝ → ℝ) : Prop :=
  (∀ n, Lam N (hs n)) ∧ Lam N h ∧ WeakTendsto N hs h

/-- Definition 3.1, (3), p. 10: `h ∈ Λ(Q)` is a dynamic equilibrium with fixed flow volumes and
departure time choice for the delay operator `Φ`: for each commodity `i` there is `ν_i ∈ ℝ`
with `h_p(t) > 0 ⇒ Φ_p(h, t) ≤ ν_i` and `h_p(t) < B_p ⇒ Φ_p(h, t) ≥ ν_i` for a.a. `t ∈ [t0, tf]`
and all `p ∈ P_i`. -/
def IsDTCEq [Fintype W] [DecidableEq I] (N : Model I W E) (Φ : (W → ℝ → ℝ) → W → ℝ → ℝ)
    (h : W → ℝ → ℝ) : Prop :=
  Lam N h ∧ ∀ i, ∃ ν : ℝ, ∀ p, N.com p = i →
    ∀ᵐ t ∂(volume.restrict (Icc N.t0 N.tf)),
      (0 < h p t → Φ h p t ≤ ν) ∧ (h p t < N.B p → ν ≤ Φ h p t)

/-- (17), p. 20, read additively: `H_{p→q}(h, γ, Δ)` removes `γ` from walk `p` and adds
`γ(· − Δ)` to walk `q` (both, if `q = p`). -/
def deviate [DecidableEq W] (h : W → ℝ → ℝ) (p q : W) (γ : ℝ → ℝ) (Δ : ℝ) : W → ℝ → ℝ :=
  fun w t => h w t - (if w = p then γ t else 0) + (if w = q then γ (t - Δ) else 0)

/-- A correspondence of admissible γ-deviations: `A p h ∋ (q, γ, Δ)` (p. 20). -/
abbrev Corr (W : Type*) := W → (W → ℝ → ℝ) → Set (W × (ℝ → ℝ) × ℝ)

/-- (18), p. 21: the admissible deviations `U_p(h, t)`: pairs `(q, Δ)` with `q ∈ P_i` (the
commodity of `p`) such that for all `δ, ε > 0` there is a measurable `γ` with `0 ≤ γ ≤ ε`,
vanishing outside `[t − δ, t + δ] ∩ [t0, tf]`, with `∫_{t0}^{tf} γ > 0` and `(q, γ, Δ) ∈ A_p(h)`. -/
def admDev (N : Model I W E) (A : Corr W) (h : W → ℝ → ℝ) (p : W) (t : ℝ) : Set (W × ℝ) :=
  {x | N.com x.1 = N.com p ∧ ∀ δ > 0, ∀ ε > 0, ∃ γ : ℝ → ℝ, Measurable γ ∧
      (∀ s, 0 ≤ γ s ∧ γ s ≤ ε) ∧
      (∀ s, s ∉ Icc (t - δ) (t + δ) ∩ Icc N.t0 N.tf → γ s = 0) ∧
      0 < ∫ s in Icc N.t0 N.tf, γ s ∧ (x.1, γ, x.2) ∈ A p h}

/-- Definition 5.1, (19), p. 21: `h` is a side-constrained dynamic equilibrium (SCDE) w.r.t. the
constraint set `S`, the correspondence `A` and the delay operator `Φ`: `h ∈ S` and
`Φ_p(h, t) ≤ Φ_q(h, t + Δ)` for all `p`, all `t ∈ [t0, tf]` and all `(q, Δ) ∈ U_p(h, t)`. -/
def IsSCDE (N : Model I W E) (Φ : (W → ℝ → ℝ) → W → ℝ → ℝ) (S : (W → ℝ → ℝ) → Prop)
    (A : Corr W) (h : W → ℝ → ℝ) : Prop :=
  S h ∧ ∀ p, ∀ t ∈ Icc N.t0 N.tf, ∀ x ∈ admDev N A h p t, Φ h p t ≤ Φ h x.1 (t + x.2)

/-- (23), p. 34: the capacity-feasible inflows `S = {h ∈ Λ(Q) | f_e(h, θ) ≤ c_e(θ) ∀ e, θ ≥ 0}`. -/
def capFeasible [Fintype W] [DecidableEq I] (N : Model I W E) (h : W → ℝ → ℝ) : Prop :=
  Lam N h ∧ ∀ e θ, 0 ≤ θ → N.f h e θ ≤ N.c e θ

/-- Strict slack on the `j`-th edge (0-based) of walk `q` for a particle entering `q` at time
`s`: `f_e(h, τ) < c_e(τ)` at the time `τ = tau h q j s` it enters `e = (edges q)[j]`. -/
def slack (N : Model I W E) (h : W → ℝ → ℝ) (q : W) (j : ℕ) (s : ℝ) : Prop :=
  ∀ hj : j < (N.edges q).length,
    N.f h ((N.edges q)[j]) (N.tau h q j s) < N.c ((N.edges q)[j]) (N.tau h q j s)

/-- (24), p. 34 (strong LPDE), with the section's implicit condition `H_{p→q}(h, γ, Δ) ∈ Λ(Q)`
(p. 33): `(q, γ, Δ)` such that every edge of `q` has strict slack at every time `s` in the
support of `γ(· − Δ)` (pointwise on the representative `γ`). -/
def devLP [Fintype W] [DecidableEq W] [DecidableEq I] (N : Model I W E) : Corr W :=
  fun p h => {x | Lam N (deviate h p x.1 x.2.1 x.2.2) ∧
    ∀ s, x.2.1 (s - x.2.2) ≠ 0 → ∀ j, slack N h x.1 j s}

/-- (26), p. 35 (strong MNSDE), with the implicit condition `H_{p→q}(h, γ, Δ) ∈ Λ(Q)`: either
`Δ = 0` and, for some common prefix of `p` and `q` of `k` edges, every edge of `q` after the
prefix has strict slack at every `s` in the support of `γ`; or the condition of (24). -/
def devMNS [Fintype W] [DecidableEq W] [DecidableEq I] (N : Model I W E) : Corr W :=
  fun p h => {x | Lam N (deviate h p x.1 x.2.1 x.2.2) ∧
    ((x.2.2 = 0 ∧ ∃ k, k ≤ (N.edges p).length ∧ k ≤ (N.edges x.1).length ∧
        (N.edges p).take k = (N.edges x.1).take k ∧
        ∀ s, x.2.1 s ≠ 0 → ∀ j, k ≤ j → slack N h x.1 j s) ∨
     (∀ s, x.2.1 (s - x.2.2) ≠ 0 → ∀ j, slack N h x.1 j s))}

/-- p. 40: the edge penalty `ξ_e(h, θ) = max{0, f_e(h, θ) − c_e(θ)}`. -/
noncomputable def xi (N : Model I W E) (h : W → ℝ → ℝ) (e : E) (θ : ℝ) : ℝ :=
  max 0 (N.f h e θ - N.c e θ)

/-- p. 40: the walk penalty `ξ_p(h, t) = ∑_{e = (v_j, v_{j+1}) ∈ p} ξ_e(h, τ^j_p(h, t))`. -/
noncomputable def xiWalk (N : Model I W E) (h : W → ℝ → ℝ) (p : W) (t : ℝ) : ℝ :=
  ∑ j : Fin (N.edges p).length, xi N h ((N.edges p)[j]) (N.tau h p j t)

/-- p. 40: the penalized delay operator `Ψ^λ_p(h, t) = Ψ_p(h, t) + λ ξ_p(h, t)`. -/
noncomputable def PsiPen (N : Model I W E) (lam : ℝ) : (W → ℝ → ℝ) → W → ℝ → ℝ :=
  fun h p t => N.Psi h p t + lam * xiWalk N h p t

/-- Definition 5.6, p. 23: the truncated delay operator `Ψ|^M_p(h, t) = min{Ψ_p(h, t), M}`. -/
noncomputable def PsiTrunc (Φ : (W → ℝ → ℝ) → W → ℝ → ℝ) (M : ℝ) :
    (W → ℝ → ℝ) → W → ℝ → ℝ :=
  fun h p t => min (Φ h p t) M

/-- (A1), p. 11: for every `h ∈ Λ(Q)` and walk `p`, `Φ_p(h, ·)` is bounded on `[t0, tf]`. -/
def A1 [Fintype W] [DecidableEq I] (N : Model I W E) (Φ : (W → ℝ → ℝ) → W → ℝ → ℝ) : Prop :=
  ∀ h, Lam N h → ∀ p, ∃ C : ℝ, ∀ t ∈ Icc N.t0 N.tf, |Φ h p t| ≤ C

/-- (A2), p. 12: every `P_i` is non-empty (finiteness is `Fintype W`). -/
def A2 (N : Model I W E) : Prop := ∀ i, ∃ p, N.com p = i

/-- (A3), p. 12: `Λ(Q)` is non-empty. -/
def A3 [Fintype W] [DecidableEq I] (N : Model I W E) : Prop := ∃ h, Lam N h

/-- (A4), p. 12: `h ↦ Φ_p(h, ·)` is sequentially weak-strong continuous from `Λ(Q)` to
`L²([t0, tf])`. -/
def A4 [Fintype W] [DecidableEq I] (N : Model I W E) (Φ : (W → ℝ → ℝ) → W → ℝ → ℝ) : Prop :=
  ∀ hs h, WeakConvSeq N hs h → ∀ p,
    Tendsto (fun n => eLpNorm (Φ (hs n) p - Φ h p) 2 (volume.restrict (Icc N.t0 N.tf)))
      atTop (𝓝 0)

/-- (A5), p. 21: `Ψ_p(h, ·)` is continuous on `[t0, tf]` for every `h ∈ S` (S as in (23)). -/
def A5 [Fintype W] [DecidableEq I] (N : Model I W E) : Prop :=
  ∀ h, capFeasible N h → ∀ p, ContinuousOn (N.Psi h p) (Icc N.t0 N.tf)

/-- (A9), p. 38: `f_e(h, 0) ≤ c_e(0)`. -/
def A9 [Fintype W] [DecidableEq I] (N : Model I W E) : Prop :=
  ∀ e h, Lam N h → N.f h e 0 ≤ N.c e 0

/-- (A10), p. 38, with DTC. -/
def A10 [Fintype W] [DecidableEq I] (N : Model I W E) : Prop :=
  ∀ h, Lam N h → ∀ i, ∃ p, N.com p = i ∧ ∃ J ⊆ Icc N.t0 N.tf, MeasurableSet J ∧ 0 < volume J ∧
    ∀ t ∈ J, h p t < N.B p ∧ ∀ j (hj : j < (N.edges p).length),
      N.f h ((N.edges p)[j]) (N.tau h p j t) ≤ N.c ((N.edges p)[j]) (N.tau h p j t)

/-- (A11), p. 38: capacities are non-negative on `ℝ≥0`. -/
def A11 (N : Model I W E) : Prop := ∀ e θ, 0 ≤ θ → 0 ≤ N.c e θ

/-- (A12), p. 38: capacities are non-decreasing on `ℝ≥0`. -/
def A12 (N : Model I W E) : Prop := ∀ e, MonotoneOn (N.c e) (Ici 0)

/-- (A13), p. 39: `f_e(h, ·)` is continuous on `ℝ≥0`. -/
def A13 [Fintype W] [DecidableEq I] (N : Model I W E) : Prop :=
  ∀ e h, Lam N h → ContinuousOn (N.f h e) (Ici 0)

/-- (A14), p. 39: for a weakly convergent sequence `h^n → h`, `f_e(h^n, ·) → f_e(h, ·)`
uniformly on `ℝ≥0`. -/
def A14 [Fintype W] [DecidableEq I] (N : Model I W E) : Prop :=
  ∀ hs h, WeakConvSeq N hs h → ∀ e,
    TendstoUniformlyOn (fun n => N.f (hs n) e) (N.f h e) atTop (Ici 0)

/-- (A15), p. 39: the principle of causation. -/
def A15 [Fintype W] [DecidableEq I] (N : Model I W E) : Prop :=
  ∀ h, Lam N h → ∀ e a b, 0 ≤ a → a ≤ b → 0 ≤ N.f h e a → N.f h e a < N.f h e b →
    ∃ p j, ∃ hj : j < (N.edges p).length, (N.edges p)[j] = e ∧
      ∃ J ⊆ Icc N.t0 N.tf, MeasurableSet J ∧ 0 < volume J ∧
        ∀ t ∈ J, 0 < h p t ∧ N.tau h p j t ∈ Icc a b

/-- (A16), p. 39: for a weakly convergent sequence `h^n → h`, `τ^j_p(h^n, ·) → τ^j_p(h, ·)`
uniformly on `[t0, tf]`, for every node index `j` of `p`. -/
def A16 [Fintype W] [DecidableEq I] (N : Model I W E) : Prop :=
  ∀ hs h, WeakConvSeq N hs h → ∀ p, ∀ j ≤ (N.edges p).length,
    TendstoUniformlyOn (fun n => N.tau (hs n) p j) (N.tau h p j) atTop (Icc N.t0 N.tf)

/-- (A17), p. 39, posed for every `h ∈ Λ(Q)`: walks sharing a common prefix of `k` edges have
the same entry times into the edges of that prefix. -/
def A17 [Fintype W] [DecidableEq I] (N : Model I W E) : Prop :=
  ∀ p q k, k ≤ (N.edges p).length → k ≤ (N.edges q).length →
    (N.edges p).take k = (N.edges q).take k → ∀ h, Lam N h → ∀ j < k,
      ∀ t ∈ Icc N.t0 N.tf, N.tau h p j t = N.tau h q j t

/-- (A18), p. 39: `h ↦ Ψ(h, ·)` maps `Λ(Q)` into `C([t0, tf])^P` and is sequentially
weak-strong continuous (uniform convergence on `[t0, tf]`). -/
def A18 [Fintype W] [DecidableEq I] (N : Model I W E) : Prop :=
  (∀ h, Lam N h → ∀ p, ContinuousOn (N.Psi h p) (Icc N.t0 N.tf)) ∧
  ∀ hs h, WeakConvSeq N hs h → ∀ p,
    TendstoUniformlyOn (fun n => N.Psi (hs n) p) (N.Psi h p) atTop (Icc N.t0 N.tf)

/-- (A19), p. 39: a uniform bound `Ψ_p(h, t) ≤ M` for all `h ∈ S`, all `p` and a.a. `t`. -/
def A19 [Fintype W] [DecidableEq I] (N : Model I W E) : Prop :=
  ∃ M : ℝ, ∀ h, capFeasible N h → ∀ p,
    ∀ᵐ t ∂(volume.restrict (Icc N.t0 N.tf)), N.Psi h p t ≤ M

/-- (A22), p. 45 (added to Theorem 7.6): capacities are continuous on `ℝ≥0`. -/
def A22 (N : Model I W E) : Prop := ∀ e, ContinuousOn (N.c e) (Ici 0)

end SideConstrainedDTA.Existence


