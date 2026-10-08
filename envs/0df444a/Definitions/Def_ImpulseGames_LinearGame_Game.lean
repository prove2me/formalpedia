-- Prove2me | Definitions.Def_ImpulseGames_LinearGame_Game
-- name    : ImpulseGames_LinearGame_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:08:39.569215+00:00
-- url     : https://prove2.me/theorems/d51f37a0-9362-4eb3-9ef1-c78d5c848fa1
-- title:
--   The linear impulse game: strategies (Def. 2.1), controlled process (Def. 2.2), payoffs, $\Phi_x$ (Def. 2.5) and Nash equilibrium (Def. 2.6)
-- statement:
--   This file specialises the impulse game of Section 2 to the one-dimensional model of Section 4.1: state space $S=\mathbb R$, shift $\Gamma^i(y,\delta)=y+\delta$, impulse sets $Z_1=[0,\infty[$ and $Z_2=]-\infty,0]$, uncontrolled dynamics $Y^{t,\zeta}_s=\zeta+\sigma(W_s-W_t)$ for a real Brownian motion $W$.
--
--   **Strategies (Definition 2.1).** A strategy of player $i$ is a pair $\varphi_i=(\mathcal C_i,\xi_i)$ with $\mathcal C_i\subseteq\mathbb R$ open and $\xi_i:\mathbb R\to Z_i$ continuous.
--
--   **Controlled process (Definition 2.2).** Fix an initial state $x$ and a path $w$ of $W$. Set $\tilde\tau_0=0$, $x_0=x$, $\tilde X^0=Y^{0,x}$, and for $k\ge1$
--   $$\alpha^{O}_k=\inf\{s>\tilde\tau_{k-1}:\tilde X^{k-1}_s\notin O\},\qquad \tilde\tau_k=\alpha^{\mathcal C_1}_k\wedge\alpha^{\mathcal C_2}_k ,$$
--   $m_k=1$ if $\alpha^{\mathcal C_1}_k\le\alpha^{\mathcal C_2}_k$ and $m_k=2$ otherwise (player 1 has priority), $\tilde\delta_k=\xi_{m_k}(\tilde X^{k-1}_{\tilde\tau_k})\mathbb 1_{\{\tilde\tau_k<\infty\}}$, $x_k=(\tilde X^{k-1}_{\tilde\tau_k}+\tilde\delta_k)\mathbb 1_{\{\tilde\tau_k<\infty\}}$ and
--   $$\tilde X^k=\tilde X^{k-1}\mathbb 1_{[0,\tilde\tau_k[}+Y^{\tilde\tau_k,x_k}\mathbb 1_{[\tilde\tau_k,\infty[},$$
--   with $\inf\emptyset=\infty$. With $\bar k=\sup\{k:\tilde\tau_k<\infty\}$, the controlled process is $X=\tilde X^{\bar k}$ (and $\lim_k\tilde X^k$ if $\bar k=\infty$). Player $i$'s impulse control $\{(\tau_{i,k},\delta_{i,k})\}_{k\ge1}$ lists the times and impulses of the steps with $m_k=i$, followed by the tail $(\infty,0)$ (2.3).
--
--   **Payoffs (p. 13).** For $i\in\{1,2\}$ and $j\ne i$,
--   $$J^i(x;\varphi_1,\varphi_2)=\mathbb E_x\Big[\int_0^\infty e^{-\rho s}f_i(X_s)\,ds+\sum_{k\ge1}e^{-\rho\tau_{i,k}}\phi(\delta_{i,k})+\sum_{k\ge1}e^{-\rho\tau_{j,k}}\psi(\delta_{j,k})\Big],$$
--   where the tail terms ($\tau=\infty$) contribute $0$.
--
--   **Admissible pairs (Definition 2.5).** $(\varphi_1,\varphi_2)\in\Phi_x$ if, for $i=1,2$: the random variables $\int_0^\infty e^{-\rho s}|f_i|(X_s)ds$, $\sum_k e^{-\rho\tau_{i,k}}|\phi|(\delta_{i,k})$ and $\sum_k e^{-\rho\tau_{i,k}}|\psi|(\delta_{i,k})$ are in $L^1$ (2.7); $\mathbb E_x[\|X\|_\infty^p]<\infty$ for every $p\in\mathbb N$, where $\|X\|_\infty=\sup_{t\ge0}|X_t|$ (2.8); and $\tau_{i,k}\to\infty$ (2.9).
--
--   **Nash equilibrium (Definition 2.6).** $(\varphi_1^*,\varphi_2^*)\in\Phi_x$ is a Nash equilibrium if $J^1(x;\varphi_1^*,\varphi_2^*)\ge J^1(x;\varphi_1,\varphi_2^*)$ for every strategy $\varphi_1$ with $(\varphi_1,\varphi_2^*)\in\Phi_x$, and symmetrically for player 2.
--
--   **Formalization Note.** The construction is written pathwise in a path $w:\mathbb R_{\ge0}\to\mathbb R$ (`stage`, `ctrlX`), with intervention times in $[0,\infty]$ (`ℝ≥0∞`) and $e^{-\rho\cdot\infty}=0$ (`disc`). Since $S=\mathbb R$, $\tau_S=\infty$ and there is no terminal payoff. The non-accumulation assumption of Definition 2.2 is, for $S=\mathbb R$, equivalent to (2.9) for both players and is carried by $\Phi_x$; the limit `limUnder` used when $\bar k=\infty$ is only relevant on paths violating it. Integrability (2.7) is stated with the path integrals and series finite almost surely and their $\omega$-functions integrable; the signed running integral is required to be a random variable (`AEStronglyMeasurable`), which the paper takes for granted. (2.9) is read almost surely. Expectations are Bochner integrals and are only used on $\Phi_x$, where the integrand is integrable. No filtration appears: strategies are Markov feedback, so every object is a functional of $W$.
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, Definitions 2.1, 2.2, 2.4, 2.5, 2.6 (pp. 4-7), specialised in Section 4.1 (pp. 12-13)

import Mathlib
import Definitions.Def_ImpulseGames_LinearGame_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace ImpulseGames.LinearGame

/-- The two players. -/
inductive Player
  | one
  | two
  deriving DecidableEq

/-- The opponent `j ≠ i`. -/
def Player.other : Player → Player
  | .one => .two
  | .two => .one

/-- Player 1's impulses are nonnegative: `Z₁ = [0, ∞[` (p. 13). -/
def Z₁ : Set ℝ := Set.Ici 0

/-- Player 2's impulses are nonpositive: `Z₂ = ]−∞, 0]` (p. 13). -/
def Z₂ : Set ℝ := Set.Iic 0

/-- A strategy (Definition 2.1, with `S = ℝ`): a pair `(C, ξ)` where `C ⊆ ℝ` is open (the
continuation region) and `ξ : ℝ → Z` is continuous (the impulse map). -/
structure Strategy (Z : Set ℝ) where
  C : Set ℝ
  isOpen_C : IsOpen C
  ξ : ℝ → ℝ
  continuous_ξ : Continuous ξ
  mem_Z : ∀ y, ξ y ∈ Z

/-- The data of step `k` of the inductive construction of Definition 2.2, along one path:
the intervention time `τ̃ₖ ∈ [0, ∞]`, the index `mₖ` of the intervening player, the impulse
`δ̃ₖ`, the restarting point `xₖ`, and the process `X̃ᵏ` (controlled up to the `k`-th
intervention). -/
structure Stage where
  τ : ℝ≥0∞
  m : Player
  δ : ℝ
  x : ℝ
  X : ℝ≥0 → ℝ

/-- `α^O = inf {s > τ : X̃ₛ ∉ O}`, with `inf ∅ = ∞` (Definition 2.2). -/
noncomputable def exitTime (X : ℝ≥0 → ℝ) (τ : ℝ≥0∞) (O : Set ℝ) : ℝ≥0∞ :=
  ⨅ (s : ℝ≥0) (_ : τ < (s : ℝ≥0∞) ∧ X s ∉ O), (s : ℝ≥0∞)

/-- The inductive construction of Definition 2.2 along a fixed Brownian path `w`, for the model
of Section 4.1 (`S = ℝ`, so `α^S = ∞`; `Γⁱ(y, δ) = y + δ`; uncontrolled dynamics
`Y^{t,ζ}_s = ζ + σ (w_s − w_t)`). Step `0` is `τ̃₀ = 0`, `x₀ = x`, `X̃⁰ = Y^{0,x}` (its fields `m`
and `δ` are not used). Step `k + 1`:
`α^{Cᵢ} = inf {s > τ̃ₖ : X̃ᵏₛ ∉ Cᵢ}`, `τ̃ₖ₊₁ = α^{C₁} ∧ α^{C₂}`, `mₖ₊₁ = 1` if `α^{C₁} ≤ α^{C₂}`
and `2` otherwise, `δ̃ₖ₊₁ = ξ_{mₖ₊₁}(X̃ᵏ_{τ̃ₖ₊₁}) 1{τ̃ₖ₊₁ < ∞}`,
`xₖ₊₁ = (X̃ᵏ_{τ̃ₖ₊₁} + δ̃ₖ₊₁) 1{τ̃ₖ₊₁ < ∞}`, and
`X̃ᵏ⁺¹ = X̃ᵏ 1_{[0, τ̃ₖ₊₁[} + Y^{τ̃ₖ₊₁, xₖ₊₁} 1_{[τ̃ₖ₊₁, ∞[}`. -/
noncomputable def stage (M : Model) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ)
    (w : ℝ≥0 → ℝ) : ℕ → Stage
  | 0 => { τ := 0, m := .one, δ := 0, x := x, X := fun s => x + M.σ * (w s - w 0) }
  | k + 1 =>
    let S := stage M φ₁ φ₂ x w k
    let α₁ := exitTime S.X S.τ φ₁.C
    let α₂ := exitTime S.X S.τ φ₂.C
    let τ := min α₁ α₂
    let m : Player := if α₁ ≤ α₂ then .one else .two
    let pre := S.X τ.toNNReal
    let δ : ℝ := if τ < ⊤ then (match m with | .one => φ₁.ξ pre | .two => φ₂.ξ pre) else 0
    let xk : ℝ := if τ < ⊤ then pre + δ else 0
    { τ := τ, m := m, δ := δ, x := xk,
      X := fun s => if (s : ℝ≥0∞) < τ then S.X s else xk + M.σ * (w s - w τ.toNNReal) }

/-- `k̄ = sup {k ∈ ℕ ∪ {0} : τ̃ₖ < ∞}` (Definition 2.2 with `α^S = ∞`). -/
noncomputable def kbar (M : Model) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ)
    (w : ℝ≥0 → ℝ) : ℕ∞ :=
  sSup ((fun k : ℕ => (k : ℕ∞)) '' {k | (stage M φ₁ φ₂ x w k).τ < ⊤})

/-- The controlled process `X^{x;φ₁,φ₂} = X̃^{k̄}` (Definition 2.2), with
`X̃^∞ = lim_{k→∞} X̃ᵏ` when `k̄ = ∞`. -/
noncomputable def ctrlX (M : Model) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ)
    (w : ℝ≥0 → ℝ) (s : ℝ≥0) : ℝ :=
  if kbar M φ₁ φ₂ x w < ⊤ then (stage M φ₁ φ₂ x w (kbar M φ₁ φ₂ x w).toNat).X s
  else limUnder atTop (fun k => (stage M φ₁ φ₂ x w k).X s)

/-- Step `l ≥ 1` is an (actual) intervention of player `i`: `τ̃ₗ < ∞` and `mₗ = i`. -/
def intervenes (M : Model) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ) (w : ℝ≥0 → ℝ)
    (i : Player) (l : ℕ) : Prop :=
  1 ≤ l ∧ (stage M φ₁ φ₂ x w l).τ < ⊤ ∧ (stage M φ₁ φ₂ x w l).m = i

/-- `k̄ᵢ`, the number of interventions of player `i` (Definition 2.2). -/
noncomputable def kbarP (M : Model) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ)
    (w : ℝ≥0 → ℝ) (i : Player) : ℕ∞ :=
  {l | intervenes M φ₁ φ₂ x w i l}.encard

/-- `η(i, k)`, the index of the `k`-th intervention of player `i` (`k ≥ 1`). -/
noncomputable def etaIdx (M : Model) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ)
    (w : ℝ≥0 → ℝ) (i : Player) (k : ℕ) : ℕ :=
  Nat.nth (intervenes M φ₁ φ₂ x w i) (k - 1)

/-- The intervention times of player `i` (2.3): `τ_{i,k} = τ̃_{η(i,k)}` for `1 ≤ k ≤ k̄ᵢ`,
and `τ_{i,k} = τ_S = ∞` for `k > k̄ᵢ`. (Used for `k ≥ 1`.) -/
noncomputable def tauP (M : Model) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ)
    (w : ℝ≥0 → ℝ) (i : Player) (k : ℕ) : ℝ≥0∞ :=
  if (k : ℕ∞) ≤ kbarP M φ₁ φ₂ x w i then (stage M φ₁ φ₂ x w (etaIdx M φ₁ φ₂ x w i k)).τ else ⊤

/-- The impulses of player `i` (2.3): `δ_{i,k} = δ̃_{η(i,k)}` for `1 ≤ k ≤ k̄ᵢ`, and `0` for
`k > k̄ᵢ`. (Used for `k ≥ 1`.) -/
noncomputable def deltaP (M : Model) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ)
    (w : ℝ≥0 → ℝ) (i : Player) (k : ℕ) : ℝ :=
  if (k : ℕ∞) ≤ kbarP M φ₁ φ₂ x w i then (stage M φ₁ φ₂ x w (etaIdx M φ₁ φ₂ x w i k)).δ else 0

/-- Running payoffs (4.1): `f₁(y) = y − s₁`, `f₂(y) = s₂ − y`. -/
def runPay (M : Model) : Player → ℝ → ℝ
  | .one, y => y - M.s₁
  | .two, y => M.s₂ - y

/-- The intervention penalty `φᵢ(δ) = −c − λ|δ|` (p. 12). -/
noncomputable def cost (M : Model) (δ : ℝ) : ℝ := -M.c - M.lam * |δ|

/-- The opponent's gain `ψⱼ(δ) = c̃ + λ̃|δ|` (p. 12). -/
noncomputable def gain (M : Model) (δ : ℝ) : ℝ := M.ct + M.lamt * |δ|

/-- The discount factor `e^{−ρτ} 1{τ < ∞}` of an intervention time `τ ∈ [0, ∞]`. -/
noncomputable def disc (M : Model) (τ : ℝ≥0∞) : ℝ :=
  if τ < ⊤ then Real.exp (-M.ρ * τ.toReal) else 0

/-- The realized discounted running payoff `∫₀^∞ e^{−ρs} fᵢ(Xₛ) ds` along the path `w`. -/
noncomputable def runPath (M : Model) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ)
    (w : ℝ≥0 → ℝ) (i : Player) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ), Real.exp (-M.ρ * s) * runPay M i (ctrlX M φ₁ φ₂ x w s.toNNReal)

/-- The realized payoff of player `i` along the path `w` (the random variable inside the
expectation of `Jⁱ`, p. 13):
`∫₀^∞ e^{−ρs} fᵢ(Xₛ) ds + Σ_{k ≥ 1, τ_{i,k} < ∞} e^{−ρτ_{i,k}} φᵢ(δ_{i,k})
 + Σ_{k ≥ 1, τ_{j,k} < ∞} e^{−ρτ_{j,k}} ψᵢ(δ_{j,k})`, `j ≠ i`. -/
noncomputable def payoffPath (M : Model) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (x : ℝ)
    (w : ℝ≥0 → ℝ) (i : Player) : ℝ :=
  runPath M φ₁ φ₂ x w i
    + ∑' k : ℕ, disc M (tauP M φ₁ φ₂ x w i (k + 1)) * cost M (deltaP M φ₁ φ₂ x w i (k + 1))
    + ∑' k : ℕ, disc M (tauP M φ₁ φ₂ x w i.other (k + 1))
        * gain M (deltaP M φ₁ φ₂ x w i.other (k + 1))

/-- The payoff `Jⁱ(x; φ₁, φ₂) = E_x[payoffPath]` (Definition 2.4 / p. 13), the Brownian motion
`W` being evaluated pathwise. Only meaningful on `Φₓ` (see `InPhi`). -/
noncomputable def J (M : Model) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (x : ℝ) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) (i : Player) : ℝ :=
  ∫ ω, payoffPath M φ₁ φ₂ x (fun t => W t ω) i ∂P

/-- `(φ₁, φ₂) ∈ Φₓ`: the pair is `x`-admissible (Definition 2.5, with `S = ℝ`, `τ_S = ∞` and
no terminal payoff). (2.7): for each player `i` the random variables
`∫₀^∞ e^{−ρs}|fᵢ|(Xₛ) ds`, `Σ_{τ_{i,k}<∞} e^{−ρτ_{i,k}}|φᵢ|(δ_{i,k})`,
`Σ_{τ_{i,k}<∞} e^{−ρτ_{i,k}}|ψ|(δ_{i,k})` are in `L¹(P)` (the path integrals and series being
finite a.s., and the signed running integral a random variable); (2.8): `E[‖X‖^p_∞] < ∞` for every
`p ∈ ℕ`; (2.9): `τ_{i,k} → τ_S = ∞` a.s. -/
structure InPhi (M : Model) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (x : ℝ) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) : Prop where
  run_integrableOn : ∀ i, ∀ᵐ ω ∂P, MeasureTheory.IntegrableOn
    (fun s : ℝ => Real.exp (-M.ρ * s) * runPay M i (ctrlX M φ₁ φ₂ x (fun t => W t ω) s.toNNReal))
    (Set.Ioi 0)
  run_aestronglyMeasurable : ∀ i,
    AEStronglyMeasurable (fun ω => runPath M φ₁ φ₂ x (fun t => W t ω) i) P
  run_abs_integrable : ∀ i, Integrable (fun ω => ∫ s in Set.Ioi (0 : ℝ),
    Real.exp (-M.ρ * s) * |runPay M i (ctrlX M φ₁ φ₂ x (fun t => W t ω) s.toNNReal)|) P
  cost_summable : ∀ i, ∀ᵐ ω ∂P, Summable (fun k : ℕ =>
    disc M (tauP M φ₁ φ₂ x (fun t => W t ω) i (k + 1))
      * |cost M (deltaP M φ₁ φ₂ x (fun t => W t ω) i (k + 1))|)
  cost_integrable : ∀ i, Integrable (fun ω => ∑' k : ℕ,
    disc M (tauP M φ₁ φ₂ x (fun t => W t ω) i (k + 1))
      * |cost M (deltaP M φ₁ φ₂ x (fun t => W t ω) i (k + 1))|) P
  gain_summable : ∀ i, ∀ᵐ ω ∂P, Summable (fun k : ℕ =>
    disc M (tauP M φ₁ φ₂ x (fun t => W t ω) i (k + 1))
      * |gain M (deltaP M φ₁ φ₂ x (fun t => W t ω) i (k + 1))|)
  gain_integrable : ∀ i, Integrable (fun ω => ∑' k : ℕ,
    disc M (tauP M φ₁ φ₂ x (fun t => W t ω) i (k + 1))
      * |gain M (deltaP M φ₁ φ₂ x (fun t => W t ω) i (k + 1))|) P
  sup_aemeasurable :
    AEMeasurable (fun ω => ⨆ t : ℝ≥0, ENNReal.ofReal |ctrlX M φ₁ φ₂ x (fun t => W t ω) t|) P
  sup_moments : ∀ p : ℕ,
    ∫⁻ ω, (⨆ t : ℝ≥0, ENNReal.ofReal |ctrlX M φ₁ φ₂ x (fun t => W t ω) t|) ^ p ∂P < ⊤
  tau_tendsto : ∀ i, ∀ᵐ ω ∂P,
    Tendsto (fun k : ℕ => tauP M φ₁ φ₂ x (fun t => W t ω) i k) atTop (𝓝 ⊤)

/-- Nash equilibrium (Definition 2.6): `(φ₁*, φ₂*) ∈ Φₓ`, and no player gains by a unilateral
deviation to any strategy keeping the pair in `Φₓ`. -/
def IsNash (M : Model) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (x : ℝ) (φ₁ : Strategy Z₁) (φ₂ : Strategy Z₂) : Prop :=
  InPhi M P W x φ₁ φ₂ ∧
    (∀ ψ₁ : Strategy Z₁, InPhi M P W x ψ₁ φ₂ → J M P W x ψ₁ φ₂ .one ≤ J M P W x φ₁ φ₂ .one) ∧
    (∀ ψ₂ : Strategy Z₂, InPhi M P W x φ₁ ψ₂ → J M P W x φ₁ ψ₂ .two ≤ J M P W x φ₁ φ₂ .two)

end ImpulseGames.LinearGame


