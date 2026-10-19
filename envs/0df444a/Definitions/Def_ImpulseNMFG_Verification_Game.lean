-- Prove2me | Definitions.Def_ImpulseNMFG_Verification_Game
-- name    : ImpulseNMFG_Verification_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:13:58.767149+00:00
-- url     : https://prove2.me/theorems/1a47e1fc-34b5-41ec-bd79-c7818211d6cb
-- title:
--   §2.1, pp. 3–7 — N-player impulse game, controlled process, cost, admissibility and Nash equilibrium
-- statement:
--   Let $S\subseteq\mathbb R^d$ be a nonempty open set, the domain of the game. Between interventions the state follows the diffusion
--   $$
--   dY_s=b(Y_s)\,ds+\sigma(Y_s)\,dW_s,
--   $$
--   with $b$ and $\sigma$ Lipschitz on $S$ and $W$ an $M$-dimensional Brownian motion. Player $i\in\{1,\ldots,N\}$ has an impulse set $Z_i\subseteq\mathbb R^{l_i}$, a shift $\Gamma^i:S\times Z_i\to S$, a discount rate $\rho_i>0$, a running cost $f_i$, a terminal cost $h_i$, an own intervention cost $\phi_i>0$ on $S\times Z_i$, and a cost $\psi_{i,j}$ that player $i$ pays when player $j\ne i$ intervenes.
--
--   A strategy of player $i$ (Definition 2.1) is a pair $\varphi_i=(A_i,\xi_i)$ of a closed action region $A_i\subseteq\mathbb R^d$ and a continuous impulse function $\xi_i:S\to Z_i$. The controlled process $X$ (Definition 2.2) is assembled from successive solutions of the diffusion equation: the next intervention time is the first entry of the current piece into one of the action regions, the intervening player shifts the state from $y$ to $\Gamma^i(y,\xi_i(y))$, and the game ends at the exit time $\tau_S$ from $S$. This yields the intervention times and impulses $(\tau_{i,k},\xi_{i,k})_{k\ge1}$ of each player.
--
--   Player $i$ minimizes the cost (2.6)
--   $$
--   J^i(x;\varphi)=\mathbb E_x\!\left[\int_0^{\tau_S}e^{-\rho_i s}f_i(X_s)\,ds+\sum_{\tau_{i,k}<\tau_S}e^{-\rho_i\tau_{i,k}}\phi_i(X_{(\tau_{i,k})-},\xi_{i,k})+\sum_{j\ne i}\sum_{\tau_{j,k}<\tau_S}e^{-\rho_i\tau_{j,k}}\psi_{i,j}(X_{(\tau_{j,k})-},\xi_{j,k})+\mathbf 1_{\{\tau_S<\infty\}}e^{-\rho_i\tau_S}h_i(X_{\tau_S})\right].
--   $$
--   A profile is $x$-admissible, $\varphi\in\Phi_x$ (Definition 2.7), when the action regions are pairwise disjoint, the four absolute cost terms are integrable (2.7), $\mathbb E[\|X\|_\infty^p]<\infty$ for every $p\in\mathbb N$ (2.8), and $\tau_{i,k}\to\tau_S$ for every player (2.9). A profile $\varphi^*\in\Phi_x$ is a Nash equilibrium (Definition 2.8) if $J^i(x;\varphi^*)\le J^i(x;(\varphi^{*,-i},\varphi_i))$ for every player $i$ and every strategy $\varphi_i$ with $(\varphi^{*,-i},\varphi_i)\in\Phi_x$.
--
--   This definition layer provides the stochastic game, its costs and the equilibrium concept used by the verification theorem.
--
--   **Formalization Note** Each diffusion piece solves the equation in the sense of the published `SolvesFrom` (an Itô integral against $W$), on a filtration under the usual conditions for which $W$ is Brownian; the paper uses the natural filtration of $W$. A realization is a family of pieces; $\Phi_x$ asks for one admissible realization, and costs and Nash comparisons range over every admissible realization. Times lie in $[0,\infty]$ with $e^{-\rho\cdot\infty}=0$. The openness of $S$ is the paper's convention (p. 9: $V_i$ "is not defined in $\partial S$"). The printed slips are read as follows: $A_i$ is entered (not exited); the mover is the least index attaining the next intervention time; $\tau_S$ is the exit time after the last intervention; $f_i,h_i$ are scalar; the cross cost is indexed by player $j$'s intervention times; the supremum in (2.8) runs over $[0,\tau_S]$. "Provided that the right-hand side exists and is finite" (2.6) is read as almost sure integrability in time of the running cost, no accumulation of interventions at a finite $\tau_S$, and integrability of every pathwise cost. Player indices are `Fin N`, starting at $0$.
-- source:
--   Basei, Cao, Guo, Nonzero-sum stochastic games and mean-field games with impulse controls, arXiv:1901.08085v4, pp. 3–7, §2.1, Definitions 2.1, 2.2, 2.6, 2.7, 2.8 and (2.1)–(2.9)

import Mathlib
import Definitions.Def_ImpulseGames_Verification_Game
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ImpulseGames.Verification (State IsBrownianBasis SolvesFrom exitAfter disc before InL1)

namespace ImpulseNMFG.Verification

noncomputable section
open Classical

/-- Basei, Cao, Guo, Nonzero-sum stochastic games and mean-field games with impulse controls,
arXiv:1901.08085v4, pp. 3–6, §2.1. The data of the N-player cost-minimizing impulse game.
The state space and stochastic integral are inherited from the published two-player layer. -/
structure Game (N d M : ℕ) where
  b : State d → State d
  σ : State d → Matrix (Fin d) (Fin M) ℝ
  S : Set (State d)
  l : Fin N → ℕ
  Z : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (l i)))
  Γ : (i : Fin N) → State d → EuclideanSpace ℝ (Fin (l i)) → State d
  ρ : Fin N → ℝ
  f : Fin N → State d → ℝ
  h : Fin N → State d → ℝ
  φ : (i : Fin N) → State d → EuclideanSpace ℝ (Fin (l i)) → ℝ
  ψ : (i j : Fin N) → State d → EuclideanSpace ℝ (Fin (l j)) → ℝ

variable {N d M : ℕ}

abbrev Game.Imp (G : Game N d M) (i : Fin N) := EuclideanSpace ℝ (Fin (G.l i))

/-- Basei, Cao, Guo, arXiv:1901.08085v4, pp. 3–6, standing assumptions:
nonempty open S, b and σ Lipschitz on S, Γ(S × Z_i) ⊆ S, positive discount and own impulse cost.
The coefficients are extended to total functions for SolvesFrom; only their values on S matter.
Formalization Note: S is open. The page calls S "a non-empty subset", but p. 9 says that V_i
"is not defined in ∂S", i.e. S ∩ ∂S = ∅, which is openness; the C²-regularity of (ii) and the
generator in (2.13d) also need an open domain. -/
def Game.Standing (G : Game N d M) : Prop :=
  G.S.Nonempty ∧ IsOpen G.S ∧
  (∃ K : ℝ≥0, LipschitzWith K (fun y : G.S => G.b y) ∧
    ∀ p q, LipschitzWith K (fun y : G.S => G.σ y p q)) ∧
  (∀ i, ∀ y ∈ G.S, ∀ z ∈ G.Z i, G.Γ i y z ∈ G.S) ∧
  (∀ i, 0 < G.ρ i) ∧
  (∀ i, ∀ y ∈ G.S, ∀ z ∈ G.Z i, 0 < G.φ i y z)

/-- Basei, Cao, Guo, arXiv:1901.08085v4, p. 4, Definition 2.1.
A strategy has a closed action region and a continuous impulse map into Z_i. -/
def IsStrategy (G : Game N d M) (i : Fin N) (A : Set (State d))
    (ξ : State d → G.Imp i) : Prop :=
  IsClosed A ∧ (∀ y ∈ G.S, ξ y ∈ G.Z i) ∧ ContinuousOn ξ G.S

structure Profile (G : Game N d M) where
  A : Fin N → Set (State d)
  ξ : (i : Fin N) → State d → G.Imp i

def Profile.update {G : Game N d M} (π : Profile G) (i : Fin N)
    (A : Set (State d)) (ξ : State d → G.Imp i) : Profile G :=
  ⟨Function.update π.A i A, Function.update π.ξ i ξ⟩

/-- Basei, Cao, Guo, arXiv:1901.08085v4, p. 5, Definition 2.2.
A stage of the pathwise construction; mover is the least index attaining the next entry time.
Times take values in [0,∞], with ∞ for absent interventions. -/
structure Stage (N d : ℕ) where
  path : ℝ≥0 → State d
  time : ℝ≥0∞
  exitS : ℝ≥0∞
  mover : Fin N
  pre : State d
  post : State d

variable [NeZero N]

/-- The least player whose action region is entered at the next intervention time. -/
def mover (G : Game N d M) (π : Profile G) (Q : Stage N d) : Fin N :=
  sInf {i : Fin N | exitAfter Q.path Q.time (π.A i)ᶜ =
    ⨅ j : Fin N, exitAfter Q.path Q.time (π.A j)ᶜ}

/-- Definition 2.2, inductive stages from diffusion pieces. The entry time into A_i
is the exit time from its complement. -/
def stage (G : Game N d M) (x : State d) (π : Profile G)
    (y : ℕ → ℝ≥0 → State d) : ℕ → Stage N d
  | 0 => ⟨y 0, 0, ⊤, 0, x, x⟩
  | n + 1 =>
    let Q := stage G x π y n
    let τ := ⨅ i : Fin N, exitAfter Q.path Q.time (π.A i)ᶜ
    let m := mover G π Q
    let pre := Q.path τ.toNNReal
    { path := fun s => if (s : ℝ≥0∞) < τ then Q.path s else y (n + 1) s
      time := τ
      exitS := exitAfter Q.path Q.time G.S
      mover := m
      pre := pre
      post := if τ < ⊤ then G.Γ m pre (π.ξ m pre) else 0 }

section Path
variable (G : Game N d M) (x : State d) (π : Profile G) (y : ℕ → ℝ≥0 → State d)

def alive (n : ℕ) : Prop :=
  ∀ h ≤ n, (stage G x π y h).time < (stage G x π y h).exitS

def kbar : ℕ∞ := ⨆ (n : ℕ) (_ : alive G x π y n), (n : ℕ∞)

/-- τ_S = α^S_{k̄+1} at finite k̄, correcting the page's off-by-one subscript. -/
def exitTime : ℝ≥0∞ :=
  if kbar G x π y = ⊤ then ⨆ n, (stage G x π y n).exitS
  else (stage G x π y ((kbar G x π y).toNat + 1)).exitS

def ctrl (s : ℝ≥0) : State d :=
  if kbar G x π y = ⊤ then limUnder atTop (fun n => (stage G x π y n).path s)
  else (stage G x π y (kbar G x π y).toNat).path s

def count (i : Fin N) (l : ℕ) : ℕ :=
  ((Finset.Icc 1 l).filter (fun h => (stage G x π y h).mover = i)).card

def kbarI (i : Fin N) : ℕ∞ :=
  ⨆ (l : ℕ) (_ : (l : ℕ∞) ≤ kbar G x π y), (count G x π y i l : ℕ∞)

def eta (i : Fin N) (n : ℕ) : ℕ := sInf {l | count G x π y i l = n}

def interTime (i : Fin N) (n : ℕ) : ℝ≥0∞ :=
  if (n : ℕ∞) ≤ kbarI G x π y i then (stage G x π y (eta G x π y i n)).time
  else exitTime G x π y

def preState (i : Fin N) (n : ℕ) : State d :=
  (stage G x π y (eta G x π y i n)).pre

def impulse (i : Fin N) (n : ℕ) : G.Imp i :=
  if (n : ℕ∞) ≤ kbarI G x π y i then π.ξ i (preState G x π y i n) else 0

def interventionTimes : Set ℝ≥0∞ :=
  {t | ∃ i n, 1 ≤ n ∧ interTime G x π y i n < exitTime G x π y ∧
    t = interTime G x π y i n}

/-- Basei, Cao, Guo, arXiv:1901.08085v4, p. 6, (2.6), pathwise cost.
Cross costs use player j's times and impulses. The expectation is defined separately. -/
def pathCost (i : Fin N) : ℝ :=
  (∫ s in before (exitTime G x π y),
      Real.exp (-G.ρ i * s) * G.f i (ctrl G x π y s.toNNReal)) +
  (∑' n : ℕ, if 1 ≤ n ∧ interTime G x π y i n < exitTime G x π y then
      disc (G.ρ i) (interTime G x π y i n) *
        G.φ i (preState G x π y i n) (impulse G x π y i n) else 0) +
  (∑ j ∈ Finset.univ.erase i, ∑' n : ℕ,
    if 1 ≤ n ∧ interTime G x π y j n < exitTime G x π y then
      disc (G.ρ i) (interTime G x π y j n) *
        G.ψ i j (preState G x π y j n) (impulse G x π y j n) else 0) +
  (if exitTime G x π y < ⊤ then
      disc (G.ρ i) (exitTime G x π y) *
        G.h i (ctrl G x π y (exitTime G x π y).toNNReal) else 0)

/-- The four absolute cost variables in (2.7). -/
def runningAbs (i : Fin N) : ℝ≥0∞ :=
  ∫⁻ s in before (exitTime G x π y),
    ENNReal.ofReal (Real.exp (-G.ρ i * s) * |G.f i (ctrl G x π y s.toNNReal)|)

def terminalAbs (i : Fin N) : ℝ≥0∞ :=
  ENNReal.ofReal (disc (G.ρ i) (exitTime G x π y) *
    |G.h i (ctrl G x π y (exitTime G x π y).toNNReal)|)

def ownAbs (i : Fin N) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (if 1 ≤ n ∧ interTime G x π y i n < exitTime G x π y then
    disc (G.ρ i) (interTime G x π y i n) *
      |G.φ i (preState G x π y i n) (impulse G x π y i n)| else 0)

def crossAbs (i j : Fin N) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (if 1 ≤ n ∧ interTime G x π y j n < exitTime G x π y then
    disc (G.ρ i) (interTime G x π y j n) *
      |G.ψ i j (preState G x π y j n) (impulse G x π y j n)| else 0)

/-- Supremum of the path norm at finite times before or at τ_S, the operational reading of (2.8). -/
def supNorm : ℝ≥0∞ :=
  ⨆ (s : ℝ≥0) (_ : (s : ℝ≥0∞) ≤ exitTime G x π y),
    (‖ctrl G x π y s‖₊ : ℝ≥0∞)
end Path

def pathOf {Ω : Type*} (Y : ℕ → ℝ≥0 → Ω → State d) (ω : Ω) :
    ℕ → ℝ≥0 → State d := fun n s => Y n s ω

section Random
variable {Ω : Type*} [m : MeasurableSpace Ω]

/-- Definition 2.2: every live diffusion piece solves (2.1) against the same Brownian motion,
and on infinitely many stages the intervention times do not accumulate before exit. -/
def IsRealization (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m)
    (W : ℝ≥0 → Ω → (Fin M → ℝ)) (G : Game N d M) (x : State d)
    (π : Profile G) (Y : ℕ → ℝ≥0 → Ω → State d) : Prop :=
  (∀ n, SolvesFrom P 𝔽 W G.b G.σ
    (fun ω => if alive G x π (pathOf Y ω) n then (stage G x π (pathOf Y ω) n).time else ⊤)
    (fun ω => (stage G x π (pathOf Y ω) n).post) (Y n)) ∧
  (∀ ω, kbar G x π (pathOf Y ω) = ⊤ →
    Tendsto (fun n => (stage G x π (pathOf Y ω) n).time) atTop
      (𝓝 (⨆ n, (stage G x π (pathOf Y ω) n).exitS)))

/-- Definition 2.7, p. 7: strategy, disjointness, realization, (2.7)–(2.9), and
well-defined finite cost. The moment supremum stops at τ_S, as used in (2.22).
"Provided that the right-hand side exists and is finite" (Definition 2.6, p. 6) is read as:
a.s. the running-cost integrand is Lebesgue integrable in time on [0, τ_S), a.s. no
accumulation of interventions at a finite τ_S, and every pathwise cost is integrable in ω. -/
def IsAdmissible (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m)
    (W : ℝ≥0 → Ω → (Fin M → ℝ)) (G : Game N d M) (x : State d)
    (π : Profile G) (Y : ℕ → ℝ≥0 → Ω → State d) : Prop :=
  (∀ i, IsStrategy G i (π.A i) (π.ξ i)) ∧
  (∀ i j, i ≠ j → Disjoint (π.A i) (π.A j)) ∧
  IsRealization P 𝔽 W G x π Y ∧
  (∀ i, ∀ᵐ ω ∂P, MeasureTheory.IntegrableOn
    (fun s : ℝ => Real.exp (-G.ρ i * s) * G.f i (ctrl G x π (pathOf Y ω) s.toNNReal))
    (before (exitTime G x π (pathOf Y ω)))) ∧
  (∀ i, InL1 P (fun ω => runningAbs G x π (pathOf Y ω) i) ∧
    InL1 P (fun ω => terminalAbs G x π (pathOf Y ω) i) ∧
    InL1 P (fun ω => ownAbs G x π (pathOf Y ω) i)) ∧
  (∀ i j, i ≠ j → InL1 P (fun ω => crossAbs G x π (pathOf Y ω) i j)) ∧
  (∀ p : ℕ, AEMeasurable (fun ω => supNorm G x π (pathOf Y ω) ^ p) P ∧
    ∫⁻ ω, supNorm G x π (pathOf Y ω) ^ p ∂P < ⊤) ∧
  (∀ i, ∀ᵐ ω ∂P, Tendsto (fun n => interTime G x π (pathOf Y ω) i n) atTop
    (𝓝 (exitTime G x π (pathOf Y ω)))) ∧
  (∀ᵐ ω ∂P, kbar G x π (pathOf Y ω) = ⊤ → exitTime G x π (pathOf Y ω) = ⊤) ∧
  (∀ i, Integrable (fun ω => pathCost G x π (pathOf Y ω) i) P)

def InPhi (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m)
    (W : ℝ≥0 → Ω → (Fin M → ℝ)) (G : Game N d M) (x : State d)
    (π : Profile G) : Prop := ∃ Y, IsAdmissible P 𝔽 W G x π Y

def cost (P : Measure Ω) (G : Game N d M) (x : State d) (π : Profile G)
    (Y : ℕ → ℝ≥0 → Ω → State d) (i : Fin N) : ℝ :=
  ∫ ω, pathCost G x π (pathOf Y ω) i ∂P

/-- Basei, Cao, Guo, arXiv:1901.08085v4, p. 7, Definition 2.8.
Costs are minimized. Every admissible unilateral deviation and every admissible realization
is compared. -/
def IsNash (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m)
    (W : ℝ≥0 → Ω → (Fin M → ℝ)) (G : Game N d M) (x : State d)
    (π : Profile G) : Prop :=
  InPhi P 𝔽 W G x π ∧
  ∀ (i : Fin N) (A : Set (State d)) (ξ : State d → G.Imp i)
    (Y Y' : ℕ → ℝ≥0 → Ω → State d),
    IsAdmissible P 𝔽 W G x (π.update i A ξ) Y →
    IsAdmissible P 𝔽 W G x π Y' →
    cost P G x π Y' i ≤ cost P G x (π.update i A ξ) Y i
end Random

end
end ImpulseNMFG.Verification


