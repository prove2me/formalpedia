-- Prove2me | Definitions.Def_SONATA_Push_Network
-- name    : SONATA_Push_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:13:08.699497+00:00
-- url     : https://prove2.me/theorems/392ecdea-62d0-4178-83e5-cf3aec0bd7c5
-- title:
--   Assumptions B′ and E, Algorithm 3, (17), (23), (75)–(78) — time-varying digraphs, push-sum SONATA runs, weighted errors, φ bounds
-- statement:
--   This file defines the network model, the push-sum version of SONATA and the weighted quantities of its analysis.
--
--   **Digraphs.** At time $\nu=0,1,\dots$ the agents communicate over a digraph $\mathcal G^\nu=(\mathcal V,\mathcal E^\nu)$, $\mathcal V=\{1,\dots,m\}$; $(i,j)\in\mathcal E^\nu$ means there is a link going from agent $i$ to agent $j$.
--
--   **Assumption B′.** The sequence $\{\mathcal G^\nu\}$ is $B$-strongly connected: there is a finite integer $B>0$ such that, for every $\nu=0,1,\dots$, the digraph with edge set $\bigcup_{t=\nu B}^{(\nu+1)B-1}\mathcal E^t$ is strongly connected.
--
--   **Assumption E.** The weight matrices $C^\nu=(c^\nu_{ij})$ satisfy, for a constant $c_\ell$ and every $\nu$:
--   1. E1: $c^\nu_{ii}\ge c_\ell>0$ for all $i$;
--   2. E2: for $j\ne i$, $c^\nu_{ij}\ge c_\ell$ if $(j,i)\in\mathcal E^\nu$, and $c^\nu_{ij}=0$ otherwise;
--   3. $C^\nu$ is column stochastic: $\mathbf 1^\top C^\nu=\mathbf 1^\top$.
--
--   **Algorithm 3 (SONATA over time-varying directed graphs).** Fix a step size $\alpha$. Start from $x_i^0\in\mathcal K$, $y_i^0=\nabla f_i(x_i^0)$, $\phi_i^0=1$. At every $\nu=0,1,\dots$ each agent $i$
--   1. computes $\hat x_i^\nu\in\mathcal K$ minimizing $\tilde f_i(x_i;x_i^\nu)+(y_i^\nu-\nabla f_i(x_i^\nu))^\top(x_i-x_i^\nu)+G(x_i)$ over $x_i\in\mathcal K$, sets $d_i^\nu=\hat x_i^\nu-x_i^\nu$ and $x_i^{\nu+1/2}=x_i^\nu+\alpha d_i^\nu$;
--   2. mixes
--   $$\phi_i^{\nu+1}=\sum_{j=1}^mc^\nu_{ij}\phi_j^\nu,\qquad x_i^{\nu+1}=\frac1{\phi_i^{\nu+1}}\sum_{j=1}^mc^\nu_{ij}\phi_j^\nu x_j^{\nu+1/2},$$
--   $$y_i^{\nu+1}=\frac1{\phi_i^{\nu+1}}\sum_{j=1}^mc^\nu_{ij}\big(\phi_j^\nu y_j^\nu+\nabla f_j(x_j^{\nu+1})-\nabla f_j(x_j^\nu)\big).$$
--
--   **Stacked and weighted quantities.** For stacked vectors $v=[v_1^\top,\dots,v_m^\top]^\top$, $\|v\|^2=\sum_i\|v_i\|^2$. With the weights $\phi^\nu$:
--   - $\bar y_\phi^\nu=\frac1m\sum_i\phi_i^\nu y_i^\nu$, $y^\nu_{\phi,\perp}=y^\nu-\mathbf 1_m\otimes\bar y^\nu_\phi$ (75); $\bar x_\phi^\nu=\frac1m\sum_i\phi_i^\nu x_i^\nu$, $x^\nu_{\phi,\perp}=x^\nu-\mathbf 1_m\otimes\bar x^\nu_\phi$ (76);
--   - $\overline{\nabla f}^\nu=\frac1m\sum_i\nabla f_i(x_i^\nu)$ (17); $\delta_i^\nu=\nabla F(x_i^\nu)-y_i^\nu$ (23);
--   - $p_\phi^\nu=\sum_i\phi_i^\nu\big(U(x_i^\nu)-U^\star\big)$ (77);
--   - $\phi_{lb}=c_\ell^{2(m-1)B}$ and $\phi_{ub}=m-c_\ell^{2(m-1)B}$ (78).
--
--   These objects are shared by the milestones and the goal theorem of the mission.
--
--   **Formalization Note** Time is 0-based: the run's equations hold for every $\nu\ge0$. A run is a relation: $\hat x_i^\nu$ is *some* minimizer of the subproblem, which the paper assumes exists. The divisions by $\phi_i^{\nu+1}$ are written as in the paper; under Assumption E these weights are positive. The edge relation is `Edges ν i j` $\Leftrightarrow(i,j)\in\mathcal E^\nu$, and strong connectivity is reachability along edges of the window union.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, pp. 10, 13–14, 28–29, Assumption B′, (17), (21)–(23), Algorithm 3 (73a)–(73d), Assumption E, (75)–(78)

import Mathlib
import Definitions.Def_SONATA_Push_Problem

namespace SONATA.Push

open scoped RealInnerProductSpace

/-- Assumption B′ (p. 10). The digraph sequence `G^ν = (V, ℰ^ν)` is given by `Edges ν i j`, meaning
`(i, j) ∈ ℰ^ν`: a link going from agent `i` to agent `j` at time `ν`. It is `B`-strongly connected:
`B > 0` and, for every `ν = 0, 1, …`, the digraph with edge set `⋃_{t = νB}^{(ν+1)B − 1} ℰ^t` is
strongly connected (every agent `j` is reachable from every agent `i` along its edges). -/
def AssumptionB' {m : ℕ} (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ) : Prop :=
  0 < B ∧ ∀ ν : ℕ, ∀ i j : Fin m,
    Relation.ReflTransGen (fun a b => ∃ t, ν * B ≤ t ∧ t < (ν + 1) * B ∧ Edges t a b) i j

/-- Assumption E (p. 28), with the constant `c_ℓ`: for every `ν`,
E1 `c^ν_ii ≥ c_ℓ > 0` for all `i`;
E2 for `j ≠ i`, `c^ν_ij ≥ c_ℓ` if `(j, i) ∈ ℰ^ν` (agent `i` receives from `j`), and `c^ν_ij = 0` otherwise;
and `C^ν` is column stochastic, `1ᵀ C^ν = 1ᵀ`. -/
def AssumptionE {m : ℕ} (Edges : ℕ → Fin m → Fin m → Prop) (C : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (cl : ℝ) : Prop :=
  0 < cl ∧ (∀ ν i, cl ≤ C ν i i) ∧
  (∀ ν i j, i ≠ j → (Edges ν j i → cl ≤ C ν i j) ∧ (¬ Edges ν j i → C ν i j = 0)) ∧
  ∀ ν j, ∑ i, C ν i j = 1

/-- The standing network hypotheses of §4: Assumptions B′ and E. -/
def NetworkHyp {m : ℕ} (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ)
    (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ) : Prop :=
  AssumptionB' Edges B ∧ AssumptionE Edges C cl

/-- The local direction `d_i^ν = x̂_i^ν − x_i^ν` of (73b), stacked over the agents. -/
def dir {m d : ℕ} (x xh : ℕ → Fin m → SONATA.Undir.E d) (ν : ℕ) : Fin m → SONATA.Undir.E d :=
  fun i => xh ν i - x ν i

/-- The half step `x_i^{ν+1/2} = x_i^ν + α d_i^ν` of (73b), stacked over the agents. -/
def xhalf {m d : ℕ} (α : ℝ) (x xh : ℕ → Fin m → SONATA.Undir.E d) (ν : ℕ) : Fin m → SONATA.Undir.E d :=
  fun i => x ν i + α • dir x xh ν i

/-- A run of SONATA over time-varying directed graphs (Algorithm 3, p. 28) with step size `α`.
Time is 0-based (iteration `ν` maps `(x^ν, y^ν, φ^ν)` to step `ν + 1`).
Data: `x_i^0 ∈ K`, `y_i^0 = ∇f_i(x_i^0)`, `φ_i^0 = 1`.
(73a): `x̂_i^ν ∈ K` minimizes `f̃_i(·; x_i^ν) + (y_i^ν − ∇f_i(x_i^ν))ᵀ(· − x_i^ν) + G` over `K`.
(73b): `x_i^{ν+1/2} = x_i^ν + α d_i^ν`.
(73c): `φ_i^{ν+1} = Σ_j c^ν_ij φ_j^ν`, `x_i^{ν+1} = (1/φ_i^{ν+1}) Σ_j c^ν_ij φ_j^ν x_j^{ν+1/2}`.
(73d): `y_i^{ν+1} = (1/φ_i^{ν+1}) Σ_j c^ν_ij (φ_j^ν y_j^ν + ∇f_j(x_j^{ν+1}) − ∇f_j(x_j^ν))`. -/
def IsRun {m d : ℕ} (K : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (G : SONATA.Undir.E d → ℝ)
    (ft : Fin m → SONATA.Undir.E d → SONATA.Undir.E d → ℝ) (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (α : ℝ)
    (x y xh : ℕ → Fin m → SONATA.Undir.E d) (φ : ℕ → Fin m → ℝ) : Prop :=
  (∀ i, x 0 i ∈ K) ∧ (∀ i, y 0 i = gradient (f i) (x 0 i)) ∧ (∀ i, φ 0 i = 1) ∧
  (∀ ν i, xh ν i ∈ K ∧
    IsMinOn (fun w => ft i w (x ν i) + ⟪y ν i - gradient (f i) (x ν i), w - x ν i⟫ + G w) K
      (xh ν i)) ∧
  (∀ ν i, φ (ν + 1) i = ∑ j, C ν i j * φ ν j) ∧
  (∀ ν i, x (ν + 1) i = (φ (ν + 1) i)⁻¹ • ∑ j, (C ν i j * φ ν j) • xhalf α x xh ν j) ∧
  (∀ ν i, y (ν + 1) i = (φ (ν + 1) i)⁻¹ • ∑ j, C ν i j •
    (φ ν j • y ν j + gradient (f j) (x (ν + 1) j) - gradient (f j) (x ν j)))

/-- The squared stacked Euclidean norm `‖v‖² = Σ_i ‖v_i‖²` of `v = [v_1ᵀ, …, v_mᵀ]ᵀ` (21). -/
noncomputable def sqn {m d : ℕ} (v : Fin m → SONATA.Undir.E d) : ℝ := ∑ i, ‖v i‖ ^ 2

/-- The `φ`-weighted average `(1/m) Σ_i φ_i v_i` of (75)–(76). -/
noncomputable def wavg {m d : ℕ} (φ : Fin m → ℝ) (v : Fin m → SONATA.Undir.E d) : SONATA.Undir.E d :=
  (1 / (m : ℝ)) • ∑ i, φ i • v i

/-- The weighted consensus error `v − 1_m ⊗ v̄_φ` of (75)–(76). -/
noncomputable def wperp {m d : ℕ} (φ : Fin m → ℝ) (v : Fin m → SONATA.Undir.E d) : Fin m → SONATA.Undir.E d :=
  fun i => v i - wavg φ v

/-- The average gradient `∇f̄ = (1/m) Σ_i ∇f_i(x_i)` of (17). -/
noncomputable def gradAvg {m d : ℕ} (f : Fin m → SONATA.Undir.E d → ℝ) (x : Fin m → SONATA.Undir.E d) : SONATA.Undir.E d :=
  (1 / (m : ℝ)) • ∑ i, gradient (f i) (x i)

/-- The tracking error `δ_i = ∇F(x_i) − y_i` of (23), stacked over the agents. -/
noncomputable def delta {m d : ℕ} (f : Fin m → SONATA.Undir.E d → ℝ) (x y : Fin m → SONATA.Undir.E d) : Fin m → SONATA.Undir.E d :=
  fun i => gradient (Fsum f) (x i) - y i

/-- The weighted optimality gap `p_φ = Σ_i φ_i (U(x_i) − U⋆)` of (77), with `U⋆ = U(x⋆)`. -/
noncomputable def pphi {m d : ℕ} (f : Fin m → SONATA.Undir.E d → ℝ) (G : SONATA.Undir.E d → ℝ) (xstar : SONATA.Undir.E d)
    (φ : Fin m → ℝ) (x : Fin m → SONATA.Undir.E d) : ℝ :=
  ∑ i, φ i * (U f G (x i) - U f G xstar)

/-- `φ_lb = c_ℓ^{2(m−1)B}` of (78). -/
noncomputable def phiLb (m B : ℕ) (cl : ℝ) : ℝ := cl ^ (2 * (m - 1) * B)

/-- `φ_ub = m − c_ℓ^{2(m−1)B}` of (78). -/
noncomputable def phiUb (m B : ℕ) (cl : ℝ) : ℝ := (m : ℝ) - cl ^ (2 * (m - 1) * B)

end SONATA.Push


