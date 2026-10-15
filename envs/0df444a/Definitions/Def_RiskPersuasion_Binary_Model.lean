-- Prove2me | Definitions.Def_RiskPersuasion_Binary_Model
-- name    : RiskPersuasion_Binary_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:39:53.751553+00:00
-- url     : https://prove2.me/theorems/47bd1193-fcd7-47c8-a60a-ebc0b85fdfec
-- title:
--   Binary persuasion: point masses, the sets P_a, ρ̂, K₀, K₁, L₀, γ, χ, K₀₁ and Assumptions 1–3 (Sec. 2.2, 5.1, 5.2)
-- statement:
--   The model of binary persuasion with a risk-conscious receiver (Sections 2.2 and 5).
--
--   Let $\Omega$ be a finite set of states and identify a belief $\mu\in\Delta(\Omega)$ with a vector of $\mathbb R^{\Omega}$ (nonnegative entries summing to $1$). For a state $\omega$, $e_\omega$ is the point-mass belief with $e_\omega(\omega)=1$ and $e_\omega(\omega')=0$ for $\omega'\neq\omega$; following the paper, states are identified with their point masses. The receiver has two actions, $A=\{0,1\}$, and a utility $\rho(\mu,a)\in\mathbb R$ for each belief $\mu$ and action $a$; this utility need not be linear in $\mu$ (the receiver is *risk-conscious*).
--
--   1. **Optimality regions** (Eq. (1), p. 12). For $a\in A$,
--   $$P_a=\Big\{\mu\in\Delta(\Omega):\ a\in\arg\max_{a'\in A}\rho(\mu,a')\Big\}.$$
--   2. **Differential utility** (p. 22): $\hat\rho(\mu)=\rho(\mu,1)-\rho(\mu,0)$, so that $P_1=\{\mu\in\Delta(\Omega):\hat\rho(\mu)\ge 0\}$ and $P_0=\{\mu\in\Delta(\Omega):\hat\rho(\mu)\le 0\}$.
--   3. **Assumption 1** (p. 13, standing throughout the paper): $P_0$ and $P_1$ are closed subsets of $\mathbb R^{\Omega}$.
--   4. **Assumption 2** (p. 22): the set $P_1^c=\{\mu\in\Delta(\Omega):\hat\rho(\mu)<0\}$ is convex.
--   5. **Full-information sets** (pp. 22–23): $K_1=\{\omega: e_\omega\in P_1\}$, $K_0=\{\omega: e_\omega\in P_0\}$, and $L_0=K_0\setminus K_1$, the states at which action $0$ is uniquely optimal.
--   6. **Maximal mixtures** (p. 23). For $\omega_0\in L_0$ and $\omega_1\in K_1$,
--   $$\gamma(\omega_0,\omega_1)=\sup\big\{g\in[0,1]:\ g\,e_{\omega_0}+(1-g)\,e_{\omega_1}\in P_1\big\},\qquad \chi(\omega_0,\omega_1)=\gamma(\omega_0,\omega_1)\,e_{\omega_0}+\big(1-\gamma(\omega_0,\omega_1)\big)\,e_{\omega_1},$$
--   and (Eq. (9))
--   $$K_{01}=\{\chi(\omega_0,\omega_1):\ \omega_0\in L_0,\ \omega_1\in K_1\}.$$
--   7. **Assumption 3 (Monotonicity)** (p. 25), for a relation $\prec$ on $\Omega$: $\prec$ is a strict total order, and whenever $\omega\prec\omega'$, either $\omega\in K_1$, or $\omega,\omega'\in L_0$ and $\gamma(\omega,\hat\omega)>\gamma(\omega',\hat\omega)$ for every $\hat\omega\in K_1$.
--
--   These objects are shared by every statement of the mission: the sets $K_1$, $L_0$ and $K_{01}$ generate the feasible region of the linear program (10).
--
--   **Formalization Note** Beliefs are functions `Ω → ℝ` and $\Delta(\Omega)$ is Mathlib's `stdSimplex ℝ Ω`; $e_\omega$ is `Pi.single ω 1`; actions are `Fin 2`. The utility is a function `ρ : (Ω → ℝ) → Fin 2 → ℝ`; its values off the simplex are irrelevant because $P_a$ is intersected with the simplex. $P_a$ is defined from $\rho$ by Eq. (1), so $P_0\cup P_1=\Delta(\Omega)$ automatically. $K_0$, $K_1$, $L_0$ are sets of states and enter convex hulls through their images under $\omega\mapsto e_\omega$. $\gamma$ is the real `sSup` of the set above; it is only used for $\omega_0\in L_0$, $\omega_1\in K_1$, where the set contains $0$ and is bounded by $1$, so it is the paper's supremum and lies in $[0,1]$. The order $\prec$ of Assumption 3 is a relation `prec` supplied as data, not an order inherited from the type.
-- source:
--   Anunrojwong, Iyer & Lingenbrink, Persuading Risk-Conscious Agents: A Geometric Approach, arXiv:2208.03758v3, p. 12 (Eq. (1)), p. 13 (Assumption 1), p. 22 (ρ̂, Assumption 2, K₀, K₁), p. 23 (L₀, γ, χ, Eq. (9)), p. 25 (Assumption 3)

import Mathlib

namespace RiskPersuasion.Binary

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- The point-mass belief `e_ω` (p. 22): the vector of `ℝ^Ω` with a `1` at `ω` and `0` elsewhere.
The paper identifies the state `ω` with `e_ω`. -/
def e (ω : Ω) : Ω → ℝ := Pi.single ω 1

/-- Eq. (1), p. 12, for the binary action set `A = {0, 1}` (`Fin 2`): `P a` is the set of beliefs
`μ ∈ Δ(Ω)` at which `a` maximizes the receiver's utility `ρ(μ, ·)` over both actions.
Beliefs are vectors of `ℝ^Ω`; the values of `ρ` off the simplex play no role. -/
def P (ρ : (Ω → ℝ) → Fin 2 → ℝ) (a : Fin 2) : Set (Ω → ℝ) :=
  {μ | μ ∈ stdSimplex ℝ Ω ∧ ∀ a' : Fin 2, ρ μ a' ≤ ρ μ a}

/-- The receiver's differential utility `ρ̂(μ) = ρ(μ, 1) − ρ(μ, 0)` (p. 22). -/
def ρhat (ρ : (Ω → ℝ) → Fin 2 → ℝ) (μ : Ω → ℝ) : ℝ := ρ μ 1 - ρ μ 0

/-- Assumption 1 (p. 13, standing throughout the paper): for each action `a`, `P a` is closed
(in the Euclidean topology of `ℝ^Ω`). -/
def Assumption1 (ρ : (Ω → ℝ) → Fin 2 → ℝ) : Prop := ∀ a : Fin 2, IsClosed (P ρ a)

/-- Assumption 2 (p. 22): the set `P₁ᶜ = {μ ∈ Δ(Ω) : ρ̂(μ) < 0}` is convex. -/
def Assumption2 (ρ : (Ω → ℝ) → Fin 2 → ℝ) : Prop :=
  Convex ℝ {μ : Ω → ℝ | μ ∈ stdSimplex ℝ Ω ∧ ρhat ρ μ < 0}

/-- `K₁ = P₁ ∩ Ω` (p. 22): the states `ω` whose point mass `e_ω` lies in `P 1`. -/
def K1 (ρ : (Ω → ℝ) → Fin 2 → ℝ) : Set Ω := {ω | e ω ∈ P ρ 1}

/-- `K₀ = P₀ ∩ Ω` (p. 22): the states `ω` whose point mass `e_ω` lies in `P 0`. -/
def K0 (ρ : (Ω → ℝ) → Fin 2 → ℝ) : Set Ω := {ω | e ω ∈ P ρ 0}

/-- `L₀ = K₀ ∩ K₁ᶜ` (p. 23): the states at which action `0` is uniquely optimal under full
information. -/
def L0 (ρ : (Ω → ℝ) → Fin 2 → ℝ) : Set Ω := K0 ρ \ K1 ρ

/-- `γ(ω₀, ω₁) = sup {g ∈ [0, 1] : g e_{ω₀} + (1 − g) e_{ω₁} ∈ P₁}` (p. 23). The paper uses it only
for `ω₀ ∈ L₀`, `ω₁ ∈ K₁`; then the set contains `0` and is bounded by `1`, so the real `sSup` is
the paper's supremum. -/
noncomputable def γ (ρ : (Ω → ℝ) → Fin 2 → ℝ) (ω₀ ω₁ : Ω) : ℝ :=
  sSup {g : ℝ | g ∈ Set.Icc (0 : ℝ) 1 ∧ g • e ω₀ + (1 - g) • e ω₁ ∈ P ρ 1}

/-- `χ(ω₀, ω₁) = γ(ω₀, ω₁) e_{ω₀} + (1 − γ(ω₀, ω₁)) e_{ω₁}` (p. 23). -/
noncomputable def χ (ρ : (Ω → ℝ) → Fin 2 → ℝ) (ω₀ ω₁ : Ω) : Ω → ℝ :=
  γ ρ ω₀ ω₁ • e ω₀ + (1 - γ ρ ω₀ ω₁) • e ω₁

/-- Eq. (9), p. 23: `K₀₁ = {χ(ω₀, ω₁) : ω₀ ∈ L₀, ω₁ ∈ K₁}`. -/
def K01 (ρ : (Ω → ℝ) → Fin 2 → ℝ) : Set (Ω → ℝ) :=
  {x | ∃ ω₀ ∈ L0 ρ, ∃ ω₁ ∈ K1 ρ, x = χ ρ ω₀ ω₁}

/-- Assumption 3 (Monotonicity), p. 25, for a given relation `prec` (the paper's `≺`): `prec` is a
strict total order on `Ω`, and whenever `ω ≺ ω'`, either (1) `ω ∈ K₁`, or (2) `ω, ω' ∈ L₀` and
`γ(ω, ω̂) > γ(ω', ω̂)` for all `ω̂ ∈ K₁` (written `ωh`). -/
def Assumption3 (ρ : (Ω → ℝ) → Fin 2 → ℝ) (prec : Ω → Ω → Prop) : Prop :=
  IsStrictTotalOrder Ω prec ∧
    ∀ ω ω' : Ω, prec ω ω' →
      ω ∈ K1 ρ ∨ (ω ∈ L0 ρ ∧ ω' ∈ L0 ρ ∧ ∀ ωh ∈ K1 ρ, γ ρ ω' ωh < γ ρ ω ωh)

end RiskPersuasion.Binary


