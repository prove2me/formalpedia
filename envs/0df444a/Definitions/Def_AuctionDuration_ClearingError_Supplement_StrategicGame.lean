-- Prove2me | Definitions.Def_AuctionDuration_ClearingError_Supplement_StrategicGame
-- name    : AuctionDuration_ClearingError_Supplement_StrategicGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:47:34.981913+00:00
-- url     : https://prove2.me/theorems/eeca1a59-7836-467e-85e4-5c8a046b31e4
-- title:
--   Appendix C.1 — quadratic game, full lattice Hamiltonians and viscosity solution class
-- statement:
--   Let $x=(x_a,x_b)\in\mathbb N^2$. The players minimize actual expected terminal costs under the controlled law:
--   $$
--   g^a(x)=x_a(x_a-x_b),\qquad g^b(x)=x_b(x_b-x_a),\qquad V^{i,x}_h(a,b)=E^{P^{a,b}}[g^i(x+X_h)].
--   $$
--   A deterministic measurable feedback induces a predictable control by evaluation at $(t,x+X_{t-})$. Nash optimality requires both attained least costs among every predictable unilateral deviation, for every initial count pair. Integrability and the probability property of the likelihood law are defined separately and asserted by the theorem targets.
--
--   On the entire infinite lattice define $D_iU(t,x)=U(t,x+e_i)-U(t,x)$. The bang-bang selector takes $\lambda_-$ at positive own marginal cost, $\lambda_+$ at negative marginal cost, and a threshold at zero. For the paper's positive index $m=n+1$, the smoothed selector equals $\lambda_+$ on $z\le-1/m$, $\lambda_-$ on $z\ge1/m$, and $m(\lambda_--\lambda_+)z/2+(\lambda_++\lambda_-)/2$ in between. With $\Phi_m(z)=\max(\min(z,m),-m)$,
--   $$
--   H^{*,m}(z_1,z_2,\widetilde z)=\Phi_m(z_1\lambda^m(z_1))+\Phi_m(z_2)\lambda^m(\widetilde z).
--   $$
--   The coupled system uses $(D_aV^a,D_bV^a,D_bV^b)$ for a and $(D_bV^b,D_aV^b,D_aV^a)$ for b, with both terminal costs. A viscosity solution is defined by smooth time test functions at each lattice site, with the actual nonlocal differences of the solution itself. Solutions are continuous in time and have uniform polynomial growth in the count state. This independently specifies the PDE target rather than defining it by an assumed BSDE solution.
--
--   **Formalization Note** All cost subtractions are real. Backward viscosity tests encode $-\partial_tV-H=0$, with one-sided tests at time zero; uniqueness is equality on $[0,h]\times\mathbb N^2$. The growth class is the class in the p.28 representation and pp.29–30 estimates. Feedbacks extend by the lower intensity after the horizon. This extension excludes no admissible strategy on the game interval.
-- source:
--   Jusselin, Mastrolia & Rosenbaum, Optimal auction duration: a price formation viewpoint, arXiv:1906.01713v3, https://arxiv.org/abs/1906.01713v3, pp.12–13,(6)–(7); pp.24–26,(D),(L),(S^n); pp.28–30, representation and growth estimates

import Mathlib
import Definitions.Def_AuctionDuration_ClearingError_Supplement_Canonical

noncomputable section

namespace AuctionDuration.ClearingError.Supplement

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal NNReal

abbrev State := Fin 2 → ℕ
abbrev ValueField := ℝ → State → ℝ
abbrev ValuePair := Fin 2 → ValueField

/-- Terminal quadratic costs; subtraction takes place in the reals. -/
def terminalCost (i : Fin 2) (x : State) : ℝ :=
  if i = 0 then (x 0 : ℝ) * ((x 0 : ℝ) - (x 1 : ℝ))
  else (x 1 : ℝ) * ((x 1 : ℝ) - (x 0 : ℝ))

/-- Deterministic initial counts are added to the zero-start canonical process. -/
def terminalPayoff (G : Game) (i : Fin 2) (x : State) (ω : Sample) : ℝ :=
  terminalCost i (fun j => x j + X (Real.toNNReal G.h) ω j)

/-- Actual expected cost under the likelihood-defined controlled law. -/
def Game.cost (G : Game) (i : Fin 2) (x : State) (a b : Process) : ℝ :=
  ∫ ω, terminalPayoff G i x ω ∂(G.law a b)

/-- The costs and controlled probabilities must be genuine; this is asserted by
our targets, never assumed as an existence shortcut. -/
def Game.WellDefined (G : Game) : Prop :=
  ∀ a b, G.Admissible a → G.Admissible b →
    IsProbabilityMeasure (G.law a b) ∧
    ∀ i x, Integrable (terminalPayoff G i x) (G.law a b)

/-- A feedback is used on pre-jump counts. Its harmless extension after h is
constant, leaving the entire predictable deviation class available. -/
def Game.liftFeedback (G : Game) (f : ValueField) (x : State) : Process :=
  fun t ω => if (t : ℝ) ≤ G.h then
    f t (fun i => x i + preX t ω i) else G.lower

def Game.MeasurableField (G : Game) (f : ValueField) : Prop :=
  Measurable (fun p : Icc (0 : ℝ) G.h × State => f p.1 p.2)

/-- A deterministic measurable feedback whose induced controls are admissible
from every starting state. -/
def Game.Feedback (G : Game) (f : ValueField) : Prop :=
  G.MeasurableField f ∧
  (∀ s ∈ Icc (0 : ℝ) G.h, ∀ x, f s x ∈ Icc G.lower G.upper) ∧
  ∀ x, G.Admissible (G.liftFeedback f x)

/-- Both infima are attained, over ALL predictable unilateral deviations.
IsLeast states attainment and the lower-bound property without a default real infimum. -/
def Game.IsNash (G : Game) (fa fb : ValueField) : Prop :=
  G.Feedback fa ∧ G.Feedback fb ∧ ∀ x : State,
    IsLeast {c : ℝ | ∃ a : Process, G.Admissible a ∧
      c = G.cost 0 x a (G.liftFeedback fb x)}
      (G.cost 0 x (G.liftFeedback fa x) (G.liftFeedback fb x)) ∧
    IsLeast {c : ℝ | ∃ b : Process, G.Admissible b ∧
      c = G.cost 1 x (G.liftFeedback fa x) b}
      (G.cost 1 x (G.liftFeedback fa x) (G.liftFeedback fb x))

/-- The exact forward differences of (D), on the whole infinite lattice. -/
def D (i : Fin 2) (U : ValueField) (s : ℝ) (x : State) : ℝ :=
  U s (Function.update x i (x i + 1)) - U s x

def other (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

/-- Selector (L), including the threshold on the zero set. -/
def Game.selector (G : Game) (z θ : ℝ) : ℝ :=
  if 0 < z then G.lower else if z < 0 then G.upper else θ

/-- Hamiltonians on p.24. -/
def Game.hamiltonian (G : Game) (zOwn zOther zOpponent θ : ℝ) : ℝ :=
  zOwn * G.selector zOwn G.lower + zOther * G.selector zOpponent θ

/-- n=0 denotes the paper's first POSITIVE index n=1 throughout this module. -/
def Game.smooth (G : Game) (n : ℕ) (z : ℝ) : ℝ :=
  if z ≤ -1 / (n + 1 : ℝ) then G.upper else
  if 1 / (n + 1 : ℝ) ≤ z then G.lower else
  (n + 1 : ℝ) * (G.lower - G.upper) / 2 * z + (G.upper + G.lower) / 2

def clamp (n : ℕ) (z : ℝ) : ℝ := max (min z (n + 1 : ℝ)) (-(n + 1 : ℝ))

/-- Both clamp placements are exactly those on p.25. -/
def Game.smoothH (G : Game) (n : ℕ) (zOwn zOther zOpponent : ℝ) : ℝ :=
  clamp n (zOwn * G.smooth n zOwn) + clamp n zOther * G.smooth n zOpponent

/-- Reversing the coordinates in Player b's equation is essential. -/
def Game.generator (G : Game) (n : ℕ) (V : ValuePair) (i : Fin 2)
    (s : ℝ) (x : State) : ℝ :=
  G.smoothH n (D i (V i) s x) (D (other i) (V i) s x)
    (D (other i) (V (other i)) s x)

/-- Continuous-in-time polynomial-growth class used in the representation on
p.28 and the estimates on pp.29-30; the lattice itself is not truncated. -/
def Game.GrowthClass (G : Game) (V : ValuePair) : Prop :=
  (∀ i x, ContinuousOn (fun s => V i s x) (Icc (0 : ℝ) G.h)) ∧
  ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ i s, s ∈ Icc (0 : ℝ) G.h → ∀ x,
    |V i s x| ≤ C * (1 + ((x 0 : ℝ) + (x 1 : ℝ)) ^ d)

/-- Time-test-function viscosity formulation for the backward terminal equation
-∂s V-H=0. Test functions touch one component at a fixed lattice site; the
nonlocal differences are those of V itself, never of the time test function.
The one-sided tests at s=0 use the same backward sign as interior tests. -/
def Game.ViscositySolution (G : Game) (n : ℕ) (V : ValuePair) : Prop :=
  G.GrowthClass V ∧
  (∀ i x, V i G.h x = terminalCost i x) ∧
  ∀ i x s, s ∈ Ico (0 : ℝ) G.h → ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ →
    (IsLocalMaxOn (fun t => V i t x - φ t) (Icc (0 : ℝ) G.h) s →
      0 ≤ deriv φ s + G.generator n V i s x) ∧
    (IsLocalMinOn (fun t => V i t x - φ t) (Icc (0 : ℝ) G.h) s →
      deriv φ s + G.generator n V i s x ≤ 0)

/-- Equality of the two solution components on their actual time domain. -/
def Game.SameValues (G : Game) (V U : ValuePair) : Prop :=
  ∀ i s, s ∈ Icc (0 : ℝ) G.h → ∀ x, V i s x = U i s x

/-- The Markov controls determined by limiting values and threshold fields. -/
def Game.limitFeedback (G : Game) (V θ : ValuePair) (i : Fin 2) : ValueField :=
  fun s x => G.selector (D i (V i) s x) (θ i s x)

end AuctionDuration.ClearingError.Supplement


