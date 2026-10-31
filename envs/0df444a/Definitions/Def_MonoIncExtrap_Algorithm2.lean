-- Prove2me | Definitions.Def_MonoIncExtrap_Algorithm2
-- name    : MonoIncExtrap_Algorithm2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:29:17.295432+00:00
-- url     : https://prove2.me/theorems/64db915b-1d6d-4eed-99c5-a70ee8a9f1c1
-- title:
--   Algorithm 2: input, the subproblem $F_k$, runs, the sets (16)–(17), and the constants (18)–(21), (75)
-- statement:
--   Algorithm 2 takes $\varepsilon>0$, $\gamma_0>0$, $z^0\in\mathrm{dom}\,B$, $0<\delta<1$, $0<\nu\le1/2$, $\eta\in[0,\nu/(1+\nu))$, $\rho_0\ge1$, $0<\tau_0\le1$, $\zeta>1$, $0<\sigma<1/\zeta$, and sets $\rho_k=\rho_0\zeta^k$, $\tau_k=\tau_0\sigma^k$. For $k=0,1,\dots$ it calls Algorithm 1 with $F\leftarrow F_k$, $\mu\leftarrow\rho_k^{-1}$, $\epsilon\leftarrow\tau_k$, $x^0=x^1\leftarrow z^k$ and the parameters $\gamma_0,\eta,\delta,\nu$, where
--   $$
--   F_k(x)=F(x)+\rho_k^{-1}(x-z^k),
--   $$
--   and outputs $z^{k+1}$. It terminates and outputs $z^{k+1}$ when
--   $$
--   \rho_k^{-1}\|z^{k+1}-z^k\|+\tau_k\le\varepsilon.
--   $$
--
--   This module defines the run predicates `IsPrefix` and `Stops`, the standing assumptions of §3 (including Assumption 1 with $\mu=0$), $\bar r_0=\|z^0-x^*\|$, $\Lambda=\rho_0\tau_0/(1-\sigma\zeta)$, the sets $\mathcal Q$ and $\widehat{\mathcal Q}$, the notion of a valid pair of Lipschitz constants of Lemma 2, and the constants $C_1,C_2,C_3,K,\bar M,\bar M_k$.
--
--   **Formalization Note** `J` is the same family in every call, since $F_k$ changes only the forward operator, and every call restarts its step size from the input $\gamma_0$. A valid pair $L_{\mathcal Q},L_{\widehat{\mathcal Q}}$ is fixed before $k$ and before the centre $z$ of $F_k$; $\widehat{\mathcal Q}$ depends on $L_{\mathcal Q}$. $\log_\zeta$ is `Real.logb`, $(C_1)_+$ is `max C1 0`, and the power in (21) is the real power.
-- source:
--   Lu & Mei, Primal-dual extrapolation methods for monotone inclusions under local Lipschitz continuity, arXiv:2206.00973v3, arXiv:2206.00973v3, Algorithm 2, p.6; (16)–(21), pp.7–8; (75), p.21

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoIncExtrap_Setting
import Definitions.Def_MonoIncExtrap_Algorithm1

open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoIncExtrap

/-! # Algorithm 2: the primal-dual extrapolation method for `μ = 0`

Z. Lu and S. Mei, arXiv:2206.00973v3, Algorithm 2, p.6, with the sets (16), (17), p.7, and the
constants (18)–(21), pp.7–8, and (75), p.21. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **The input of Algorithm 2**: `F`, a resolvent family `J` of `B`, and
`ε, γ0, δ, ν, η, ρ0, τ0, ζ, σ`, `z⁰ = z0`. arXiv:2206.00973v3, Algorithm 2, p.6. -/
structure Alg2.Input (H : Type*) where
  F : H → H
  J : ℝ → H → H
  ε : ℝ
  γ0 : ℝ
  δ : ℝ
  ν : ℝ
  η : ℝ
  ρ0 : ℝ
  τ0 : ℝ
  ζ : ℝ
  σ : ℝ
  z0 : H

/-- `F_k(x) = F(x) + ρ⁻¹(x − z)`, at `ρ = ρ_k`, `z = zᵏ`. arXiv:2206.00973v3, (14), p.6. -/
noncomputable def perturb (F : H → H) (ρ : ℝ) (z : H) : H → H :=
  fun x => F x + ρ⁻¹ • (x - z)

namespace Alg2

/-- `ρ_k = ρ0 ζ^k`. arXiv:2206.00973v3, Algorithm 2 input line, p.6. -/
noncomputable def Input.rho (I : Input H) (k : ℕ) : ℝ := I.ρ0 * I.ζ ^ k

/-- `τ_k = τ0 σ^k`. arXiv:2206.00973v3, Algorithm 2 input line, p.6. -/
noncomputable def Input.tau (I : Input H) (k : ℕ) : ℝ := I.τ0 * I.σ ^ k

/-- **The call of Algorithm 1 in outer iteration `k`.** arXiv:2206.00973v3, Algorithm 2, step 2,
p.6: "Call Algorithm 1 with `F ← F_k`, `μ ← ρ_k⁻¹`, `ϵ ← τ_k`, `x⁰ = x¹ ← zᵏ` and the parameters
`γ0, η, δ` and `ν`".

**Formalization Note.** `J` is unchanged, since `F_k` changes only the forward operator. Each call
restarts the step size from the input `γ0`. -/
noncomputable def Input.inner (I : Input H) (k : ℕ) (zk : H) : Alg1.Input H where
  F := perturb I.F (I.rho k) zk
  J := I.J
  μ := (I.rho k)⁻¹
  ε := I.tau k
  γ0 := I.γ0
  δ := I.δ
  ν := I.ν
  η := I.η
  x0 := zk

/-- Step 2 of Algorithm 2 in outer iteration `k`: the call of Algorithm 1 from `zk` terminates, with
output `zk1` and operation count `cnt`. arXiv:2206.00973v3, Algorithm 2, step 2, p.6. -/
def InnerRun (I : Input H) (k : ℕ) (zk zk1 : H) (cnt : ℕ) : Prop :=
  ∃ (x : ℕ → H) (γ : ℕ → ℝ) (n : ℕ → ℕ) (t : ℕ),
    Alg1.Stops (I.inner k zk) x γ n t ∧ zk1 = x (t + 1) ∧ cnt = Alg1.opCount n t

/-- The termination test (15): `ρ_k⁻¹‖z^{k+1} − zᵏ‖ + τ_k ≤ ε`. arXiv:2206.00973v3, (15), p.6. -/
def Input.OuterStop (I : Input H) (k : ℕ) (zk zk1 : H) : Prop :=
  (I.rho k)⁻¹ * ‖zk1 - zk‖ + I.tau k ≤ I.ε

/-- **The first `s` outer iterations of Algorithm 2** (iterations `0, …, s − 1`), generating
`z 0, …, z s` with operation counts `c 0, …, c (s − 1)`; the test (15) failed at every iteration
before the last of them. arXiv:2206.00973v3, Algorithm 2, p.6.

**Formalization Note.** The paper's `0 ≤ k ∈ 𝕂 − 1` is `k < s` here. -/
structure IsPrefix (I : Input H) (z : ℕ → H) (c : ℕ → ℕ) (s : ℕ) : Prop where
  z_zero : z 0 = I.z0
  inner : ∀ k < s, InnerRun I k (z k) (z (k + 1)) (c k)
  no_stop : ∀ k, k + 1 < s → ¬ I.OuterStop k (z k) (z (k + 1))

/-- **A terminated run of Algorithm 2**: the method stops at outer iteration `last` with output
`z (last + 1)`, after `last + 1` outer iterations. arXiv:2206.00973v3, Algorithm 2, step 3, p.6. -/
def Stops (I : Input H) (z : ℕ → H) (c : ℕ → ℕ) (last : ℕ) : Prop :=
  IsPrefix I z c (last + 1) ∧ I.OuterStop last (z last) (z (last + 1))

/-- **The standing assumptions of §3.** arXiv:2206.00973v3, Algorithm 2 input line, p.6, and §3,
pp.6–7: the parameter ranges of Algorithm 2, `z⁰ ∈ dom B`, Assumption 1 with `μ = 0`, `J` a
resolvent family of `B`, and `xstar` an arbitrary fixed solution of (1).

**Formalization Note.** The paper's "not strongly monotone" is not assumed: only Assumption 1(b)
with `μ = 0`. -/
structure Standing (B : H → Set H) (I : Input H) (xstar : H) : Prop where
  ε_pos : 0 < I.ε
  γ0_pos : 0 < I.γ0
  δ_pos : 0 < I.δ
  δ_lt_one : I.δ < 1
  ν_pos : 0 < I.ν
  ν_le : I.ν ≤ 1 / 2
  η_nonneg : 0 ≤ I.η
  η_lt : I.η < I.ν / (1 + I.ν)
  ρ0_ge : 1 ≤ I.ρ0
  τ0_pos : 0 < I.τ0
  τ0_le : I.τ0 ≤ 1
  ζ_gt : 1 < I.ζ
  σ_pos : 0 < I.σ
  σ_lt : I.σ < 1 / I.ζ
  z0_mem : I.z0 ∈ dom B
  assumption : Assumption1 I.F B 0
  resolvent : IsResolventFamily I.J B
  solution : IsSolution I.F B xstar

/-- `r̄0 = ‖z⁰ − x∗‖`. arXiv:2206.00973v3, (16), p.7. -/
noncomputable def Input.rbar (I : Input H) (xstar : H) : ℝ := ‖I.z0 - xstar‖

/-- `Λ = ρ0τ0/(1 − σζ)`. arXiv:2206.00973v3, (18), p.7. -/
noncomputable def Input.Lam (I : Input H) : ℝ := I.ρ0 * I.τ0 / (1 - I.σ * I.ζ)

/-- `Q = {x ∈ dom B : ‖x − x∗‖ ≤ (1/√(1 − 2ν²) + 1)(r̄0 + ρ0τ0/(1 − σζ))}`.
arXiv:2206.00973v3, (16), p.7. -/
noncomputable def setQ (B : H → Set H) (I : Input H) (xstar : H) : Set H :=
  ballIn B xstar
    ((1 / Real.sqrt (1 - 2 * I.ν ^ 2) + 1) *
      (I.rbar xstar + I.ρ0 * I.τ0 / (1 - I.σ * I.ζ)))

/-- `Q̂ = {x ∈ dom B : ‖x − x∗‖ ≤ ((5 + 9γ0 L)/(3√(1 − 2ν²)) + 1)(r̄0 + ρ0τ0/(1 − σζ))}`, at
`L = L_Q`. arXiv:2206.00973v3, (17), p.7. -/
noncomputable def setQhat (B : H → Set H) (I : Input H) (xstar : H) (L : ℝ) : Set H :=
  ballIn B xstar
    (((5 + 9 * I.γ0 * L) / (3 * Real.sqrt (1 - 2 * I.ν ^ 2)) + 1) *
      (I.rbar xstar + I.ρ0 * I.τ0 / (1 - I.σ * I.ζ)))

/-- **Valid Lipschitz constants of Lemma 2**: `L_Q, L_Q̂ > 0`, and for every `k` and every centre
`z`, the map `F_k = perturb F ρ_k z` is `L_Q`-Lipschitz on `Q` and `L_Q̂`-Lipschitz on the set `Q̂`
built from `L_Q`. arXiv:2206.00973v3, Lemma 2, p.7.

**Formalization Note.** "Independent of `k`": the constants are fixed before `k` and before the
centre `zᵏ`. `Q̂` depends on `L_Q`, so the two constants are a dependent pair. -/
def ValidQ (B : H → Set H) (I : Input H) (xstar : H) (LQ LQhat : ℝ) : Prop :=
  0 < LQ ∧ 0 < LQhat ∧ ∀ (k : ℕ) (z : H),
    IsLipschitzOn (perturb I.F (I.rho k) z) (setQ B I xstar) LQ ∧
      IsLipschitzOn (perturb I.F (I.rho k) z) (setQhat B I xstar LQ) LQhat

/-- `min{L_Q̂⁻¹δξ, γ0}`, the term in (18), (19), (75) of arXiv:2206.00973v3. -/
noncomputable def Input.minQ (I : Input H) (LQhat : ℝ) : ℝ :=
  Alg1.minStep LQhat I.δ (Alg1.xi I.ν I.η) I.γ0

/-- `C₁ = log((r̄0 + Λ)(8 + 12γ0 L_Q)/(3τ0√(1 − 2ν²) min{L_Q̂⁻¹δξ, γ0}))`.
arXiv:2206.00973v3, (18), p.7. -/
noncomputable def Input.C1 (I : Input H) (rbar LQ LQhat : ℝ) : ℝ :=
  Real.log ((rbar + I.Lam) * (8 + 12 * I.γ0 * LQ) /
    (3 * I.τ0 * Real.sqrt (1 - 2 * I.ν ^ 2) * I.minQ LQhat))

/-- `C₂ = ⌈log(ξ/(γ0 L_Q̂))/log δ⌉₊`. arXiv:2206.00973v3, (19), p.7. -/
noncomputable def Input.C2 (I : Input H) (LQhat : ℝ) : ℕ :=
  Alg1.ceilLog LQhat I.δ (Alg1.xi I.ν I.η) I.γ0

/-- `C₃ = 1/((ζ − 1) log(1 + (2/(ρ0(1 − η))) min{L_Q̂⁻¹δξ, γ0}))`.
arXiv:2206.00973v3, (19), p.7. -/
noncomputable def Input.C3 (I : Input H) (LQhat : ℝ) : ℝ :=
  1 / ((I.ζ - 1) * Real.log (1 + 2 / (I.ρ0 * (1 - I.η)) * I.minQ LQhat))

/-- `K = ⌈max{log_ζ((2r̄0 + 2Λ)/(ερ0)), log(2τ0/ε)/log(1/σ)}⌉₊`. arXiv:2206.00973v3, (20), p.7. -/
noncomputable def Input.Kconst (I : Input H) (rbar : ℝ) : ℕ :=
  ⌈max (Real.logb I.ζ ((2 * rbar + 2 * I.Lam) / (I.ε * I.ρ0)))
      (Real.log (2 * I.τ0 / I.ε) / Real.log (1 / I.σ))⌉₊

/-- `max{2ζ(r̄0 + Λ)/(ερ0), ζ(2τ0/ε)^{log ζ/log(1/σ)}, 1}`, which occurs twice in (21).
arXiv:2206.00973v3, (21), p.8. -/
noncomputable def Input.maxTerm (I : Input H) (rbar : ℝ) : ℝ :=
  max (2 * I.ζ * (rbar + I.Lam) / (I.ε * I.ρ0))
    (max (I.ζ * (2 * I.τ0 / I.ε) ^ (Real.log I.ζ / Real.log (1 / I.σ))) 1)

/-- `M̄ = 8 + C₂ + (8 + C₂)K + 4ζ(C₁)₊C₃ max{…} + 4ζC₃(log σ⁻¹)K max{…}`.
arXiv:2206.00973v3, (21), p.8. -/
noncomputable def Input.Mbar (I : Input H) (rbar LQ LQhat : ℝ) : ℝ :=
  8 + (I.C2 LQhat : ℝ) + (8 + (I.C2 LQhat : ℝ)) * (I.Kconst rbar : ℝ)
    + 4 * I.ζ * max (I.C1 rbar LQ LQhat) 0 * I.C3 LQhat * I.maxTerm rbar
    + 4 * I.ζ * I.C3 LQhat * Real.log I.σ⁻¹ * (I.Kconst rbar : ℝ) * I.maxTerm rbar

/-- `M̄_k = 6 + 2⌈2 log((r̄0 + Λ)(8 + 12γ0 L_Q)/(3τ_k√(1 − 2ν²) min{L_Q̂⁻¹δξ, γ0}))
/ log(1 + (2/(ρ_k(1 − η))) min{L_Q̂⁻¹δξ, γ0})⌉₊ + ⌈log(ξ/(γ0 L_Q̂))/log δ⌉₊`.
arXiv:2206.00973v3, (75), p.21. -/
noncomputable def Input.MbarK (I : Input H) (rbar LQ LQhat : ℝ) (k : ℕ) : ℕ :=
  6 + 2 * ⌈2 * Real.log ((rbar + I.Lam) * (8 + 12 * I.γ0 * LQ) /
        (3 * I.tau k * Real.sqrt (1 - 2 * I.ν ^ 2) * I.minQ LQhat)) /
      Real.log (1 + 2 / (I.rho k * (1 - I.η)) * I.minQ LQhat)⌉₊
    + Alg1.ceilLog LQhat I.δ (Alg1.xi I.ν I.η) I.γ0

end Alg2

end MonoIncExtrap


