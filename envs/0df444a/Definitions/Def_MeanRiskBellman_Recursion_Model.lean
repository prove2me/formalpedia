-- Prove2me | Definitions.Def_MeanRiskBellman_Recursion_Model
-- name    : MeanRiskBellman_Recursion_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:33.982978+00:00
-- url     : https://prove2.me/theorems/75a9145e-0ea2-46f7-895c-21e0af6021c9
-- title:
--   §2, §5.2, App. B, pp. 4–13, 29–30 — mean-risk market: feasible portfolios Ψ_t, mean-risk function Γ_t, upper images P_t with (5.2), D̄_t, D̃_t
-- statement:
--   The multi-period mean-risk portfolio selection problem of Kováčová and Rudloff.
--
--   **Market** (§2.2). On the finite filtered probability space of `DynamicRisk` there are $d$ assets with an adapted discounted price process $(S_s)_{s=0,\dots,T}$, $S_s\in L_s(\mathbb R^d)$. Positions are $\psi_s\in L_s(\mathbb R^d)$, and trading constraints are closed, conditionally convex sets $\Phi_s\subseteq L_s(\mathbb R^d)$, $s=0,\dots,T-1$ (conditionally convex: $\Lambda\psi+(1-\Lambda)\phi\in\Phi_s$ for $\psi,\phi\in\Phi_s$ and $\Lambda\in L_s$, $0\le\Lambda\le1$). The risk is measured by a time consistent dynamic convex risk measure $(\rho_t)_{t\in\mathbb T}$. These are Assumption 2.2, items 1, 2, 4.
--
--   **Feasible portfolios** (p. 5). For $v_t\in L_t$,
--   $$\Psi_t(v_t)=\{(\psi_s)_{s=t,\dots,T-1}\mid S_t^\top\psi_t=v_t,\ \psi_t\in\Phi_t,\ S_s^\top\psi_{s-1}=S_s^\top\psi_s,\ \psi_s\in\Phi_s,\ s=t+1,\dots,T-1\}.$$
--
--   **Mean-risk function** (p. 7). $\Gamma_t:L_T(\mathbb R^2)\to L_t(\mathbb R^2)$, $\Gamma_t(X)=\big(-\mathbb E_t(X_1),\ \rho_t(X_2)\big)$, where $\mathbb E_t$ is the conditional expectation given $\mathcal F_t$; the terminal vector is $V_T(\psi)=(v_T,v_T)$ with $v_T=S_T^\top\psi_{T-1}$ (2.2).
--
--   **Image and upper image** (p. 9, (B.2), (5.2)). For $t<T$, the image of the feasible set of the problem $D_t(v_t)$ and its upper image are
--   $$\Gamma_t(\Psi_t(v_t))=\{\Gamma_t(V_T(\psi))\mid\psi\in\Psi_t(v_t)\},\qquad \mathcal P_t(v_t)=\operatorname{cl}\big(\Gamma_t(\Psi_t(v_t))+L_t(\mathbb R^2_+)\big),$$
--   and at $t=T$ the conventions $\Gamma_T(\Psi_T(v_T))=\{(-v_T,-v_T)\}$ (B.2) and $\mathcal P_T(v_T)=\{(-v_T,-v_T)\}+L_T(\mathbb R^2_+)$ (5.2).
--
--   **Auxiliary and one-time-step problems** (pp. 13, 29–30). For $t<T$, the feasible set $\bar\Psi_t(v_t)$ of $\bar D_t(v_t)$ consists of the pairs $(\psi_t,x)$ with $S_t^\top\psi_t=v_t$, $\psi_t\in\Phi_t$, $x\in\Gamma_{t+1}(\Psi_{t+1}(S_{t+1}^\top\psi_t))$, and its image is $\Gamma_t(\bar\Psi_t(v_t))=\{\Gamma_t(-x)\mid(\psi_t,x)\in\bar\Psi_t(v_t)\}$. The feasible set $\tilde\Psi_t(v_t)$ of $\tilde D_t(v_t)$ is the same with $x\in\mathcal P_{t+1}(S_{t+1}^\top\psi_t)$, and the upper image of $\tilde D_t(v_t)$ is $\tilde{\mathcal P}_t(v_t)=\operatorname{cl}\big(\{\Gamma_t(-x)\mid(\psi_t,x)\in\tilde\Psi_t(v_t)\}+L_t(\mathbb R^2_+)\big)$.
--
--   The upper image $\mathcal P_t(v_t)$ is the infimum of the mean-risk problem in the set-valued sense and plays the role of the value function in the set-valued Bellman principle (Theorem 5.1).
--
--   **Formalization Note.** The data are bundled in `Market` and the standing assumptions in `Market.Assumptions`. Assumption 2.2 item 3 ($\Psi_0(v_0)\neq\emptyset$) is not included: no statement of §5 uses it. Random vectors in $\mathbb R^2$ are functions $\Omega\to\mathbb R\times\mathbb R$ with the pointwise, componentwise order (this is $\le_{L_t(\mathbb R^2_+)}$), and $L_t(\mathbb R^2_+)$ is the set of $\mathcal F_t$-measurable nonnegative such functions. Closures are taken in the product topology of $\Omega\to\mathbb R\times\mathbb R$, which on a finite $\Omega$ is the topology of $L_t(\mathbb R^2)$. Strategies are sequences indexed by $\mathbb N$; only $\psi_t,\dots,\psi_{T-1}$ are constrained or read. $\mathbb E_t$ is Mathlib's conditional expectation. $\mathcal P_t$ for $t<T$ is the closure of the image of whole strategies plus the cone, not a recursive object. The value of `upperImage` for $t>T$ is a junk value never used.
-- source:
--   Kováčová & Rudloff, Time consistency of the mean-risk problem, arXiv:1806.10981v2, pp. 4–9 (§2.1–§2.4, Assumption 2.2, (2.2)), p. 13 ((5.2), problem D̃_t(v_t)), pp. 29–30 (problem D̄_t(v_t), (B.2), D̃_t(v_t))

import Mathlib
import Definitions.Def_MeanRiskBellman_Recursion_DynamicRisk

namespace MeanRiskBellman.Recursion

open MeasureTheory
open scoped Pointwise

/-- §2.1–§2.2, pp. 4–6: the data of the market model.  `P` the probability measure, `T` the horizon,
`ℱ` the filtration, `d` the number of assets, `S s : Ω → ℝ^d` the discounted prices,
`Φ s ⊆ L_s(ℝ^d)` the trading constraints (`s = 0, …, T-1`), `ρ t : L_T → L_t` the risk measure.
Indices outside the ranges the paper uses are never read. -/
structure Market (Ω : Type*) [mΩ : MeasurableSpace Ω] where
  P : Measure Ω
  T : ℕ
  ℱ : Filtration ℕ mΩ
  d : ℕ
  S : ℕ → Ω → Fin d → ℝ
  Φ : ℕ → Set (Ω → Fin d → ℝ)
  ρ : ℕ → (Ω → ℝ) → Ω → ℝ

/-- p. 5: a set `C` of random vectors is conditionally convex w.r.t. `m` if `Λ ψ + (1 - Λ) φ ∈ C`
for `ψ, φ ∈ C` and every `m`-measurable `Λ` with `0 ≤ Λ ≤ 1`. -/
def IsCondConvexSet {Ω : Type*} {d : ℕ} (m : MeasurableSpace Ω) (C : Set (Ω → Fin d → ℝ)) : Prop :=
  ∀ ψ ∈ C, ∀ φ ∈ C, ∀ Λ : Ω → ℝ, StronglyMeasurable[m] Λ → (∀ ω, 0 ≤ Λ ω ∧ Λ ω ≤ 1) →
    (fun ω => Λ ω • ψ ω + (1 - Λ ω) • φ ω) ∈ C

/-- §2.1, §2.2 and Assumption 2.2 items 1, 2, 4, pp. 4–6: the standing assumptions.
Assumption 2.2 item 3 (`Ψ_0(v_0) ≠ ∅`) is deliberately not included. -/
structure Market.Assumptions {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] (M : Market Ω) : Prop where
  /-- finite filtered probability space, `F_0` trivial, `F_T = F`, positive probabilities. -/
  space : IsFinFilteredSpace M.P M.T M.ℱ
  /-- the price process is adapted. -/
  adapted : ∀ s ≤ M.T, StronglyMeasurable[M.ℱ s] (M.S s)
  /-- `Φ_s ⊆ L_s(ℝ^d)`. -/
  Φ_meas : ∀ s < M.T, ∀ ψ ∈ M.Φ s, StronglyMeasurable[M.ℱ s] ψ
  /-- `Φ_s` is closed. -/
  Φ_closed : ∀ s < M.T, IsClosed (M.Φ s)
  /-- `Φ_s` is conditionally convex. -/
  Φ_condConvex : ∀ s < M.T, IsCondConvexSet (M.ℱ s) (M.Φ s)
  /-- `(ρ_t)_{t ∈ 𝕋}` is a dynamic convex risk measure. -/
  risk : IsDynamicConvexRiskMeasure M.P M.T M.ℱ M.ρ
  /-- `(ρ_t)_{t ∈ 𝕋}` is time consistent. -/
  timeConsistent : TimeConsistent M.T M.ρ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The portfolio value `S_s^⊤ θ` of a position `θ` at prices `S_s`. -/
def value (M : Market Ω) (s : ℕ) (θ : Ω → Fin M.d → ℝ) : Ω → ℝ :=
  fun ω => M.S s ω ⬝ᵥ θ ω

/-- p. 5: the feasible portfolios `Ψ_t(v_t)`: strategies `(ψ_s)` with `S_t^⊤ψ_t = v_t`, `ψ_t ∈ Φ_t`,
and `S_s^⊤ψ_{s-1} = S_s^⊤ψ_s`, `ψ_s ∈ Φ_s` for `s = t+1, …, T-1`.  Strategies are indexed by `ℕ`;
only `ψ_t, …, ψ_{T-1}` are constrained or read. -/
def feasible (M : Market Ω) (t : ℕ) (v : Ω → ℝ) : Set (ℕ → Ω → Fin M.d → ℝ) :=
  {ψ | value M t (ψ t) = v ∧ ψ t ∈ M.Φ t ∧
    ∀ s, t + 1 ≤ s → s ≤ M.T - 1 → value M s (ψ (s - 1)) = value M s (ψ s) ∧ ψ s ∈ M.Φ s}

/-- (2.2), p. 7: the terminal vector `V_T(ψ) = (v_T, v_T)` with `v_T = S_T^⊤ψ_{T-1}`. -/
def VT (M : Market Ω) (ψ : ℕ → Ω → Fin M.d → ℝ) : Ω → ℝ × ℝ :=
  fun ω => (value M M.T (ψ (M.T - 1)) ω, value M M.T (ψ (M.T - 1)) ω)

/-- p. 7: the mean-risk function `Γ_t(X) = (-E_t(X_1), ρ_t(X_2))`, with `E_t` the conditional
expectation given `F_t`. -/
noncomputable def Γ (M : Market Ω) (t : ℕ) (X : Ω → ℝ × ℝ) : Ω → ℝ × ℝ :=
  fun ω => (-(condExp (M.ℱ t) M.P (fun ω' => (X ω').1)) ω, M.ρ t (fun ω' => (X ω').2) ω)

/-- The ordering cone `L_t(ℝ²_+)`: `F_t`-measurable random vectors with nonnegative components. -/
def cone (M : Market Ω) (t : ℕ) : Set (Ω → ℝ × ℝ) :=
  {r | StronglyMeasurable[M.ℱ t] r ∧ 0 ≤ r}

/-- p. 9: the image `Γ_t(Ψ_t(v_t)) = {Γ_t(V_T(ψ)) | ψ ∈ Ψ_t(v_t)}` of the feasible set of `D_t(v_t)`,
for `t < T`; at `t = T` the convention (B.2), p. 30: `Γ_T(Ψ_T(v_T)) := {(-v_T, -v_T)}`. -/
noncomputable def image (M : Market Ω) (t : ℕ) (v : Ω → ℝ) : Set (Ω → ℝ × ℝ) :=
  if t < M.T then (fun ψ => Γ M t (VT M ψ)) '' feasible M t v else {fun ω => (-v ω, -v ω)}

/-- p. 9: the upper image `P_t(v_t) = cl(Γ_t(Ψ_t(v_t)) + L_t(ℝ²_+))` of `D_t(v_t)` for `t < T`;
at `t = T` the convention (5.2), p. 13: `P_T(v_T) := {(-v_T, -v_T)} + L_T(ℝ²_+)`. -/
noncomputable def upperImage (M : Market Ω) (t : ℕ) (v : Ω → ℝ) : Set (Ω → ℝ × ℝ) :=
  if t < M.T then closure (image M t v + cone M t) else image M t v + cone M t

/-- p. 29–30: the feasible set `Ψ̄_t(v_t)` of the auxiliary problem `D̄_t(v_t)`: pairs `(ψ_t, x)` with
`S_t^⊤ψ_t = v_t`, `ψ_t ∈ Φ_t`, `x ∈ Γ_{t+1}(Ψ_{t+1}(S_{t+1}^⊤ψ_t))` (with (B.2) when `t + 1 = T`). -/
def feasibleBar (M : Market Ω) (t : ℕ) (v : Ω → ℝ) :
    Set ((Ω → Fin M.d → ℝ) × (Ω → ℝ × ℝ)) :=
  {p | value M t p.1 = v ∧ p.1 ∈ M.Φ t ∧ p.2 ∈ image M (t + 1) (value M (t + 1) p.1)}

/-- p. 30: the image `Γ_t(Ψ̄_t(v_t)) = {Γ_t(-x) | (ψ_t, x) ∈ Ψ̄_t(v_t)}`. -/
noncomputable def imageBar (M : Market Ω) (t : ℕ) (v : Ω → ℝ) : Set (Ω → ℝ × ℝ) :=
  (fun p => Γ M t (-p.2)) '' feasibleBar M t v

/-- p. 13 and p. 30: the feasible set `Ψ̃_t(v_t)` of the one-time-step problem `D̃_t(v_t)`: pairs
`(ψ_t, x)` with `S_t^⊤ψ_t = v_t`, `ψ_t ∈ Φ_t`, `x ∈ P_{t+1}(S_{t+1}^⊤ψ_t)`. -/
def feasibleTilde (M : Market Ω) (t : ℕ) (v : Ω → ℝ) :
    Set ((Ω → Fin M.d → ℝ) × (Ω → ℝ × ℝ)) :=
  {p | value M t p.1 = v ∧ p.1 ∈ M.Φ t ∧ p.2 ∈ upperImage M (t + 1) (value M (t + 1) p.1)}

/-- p. 13: the upper image `P̃_t(v_t) = cl(Γ_t(Ψ̃_t(v_t)) + L_t(ℝ²_+))` of `D̃_t(v_t)`, where
`Γ_t(Ψ̃_t(v_t)) = {Γ_t(-x) | (ψ_t, x) ∈ Ψ̃_t(v_t)}`. -/
noncomputable def upperImageTilde (M : Market Ω) (t : ℕ) (v : Ω → ℝ) : Set (Ω → ℝ × ℝ) :=
  closure ((fun p => Γ M t (-p.2)) '' feasibleTilde M t v + cone M t)

end MeanRiskBellman.Recursion


