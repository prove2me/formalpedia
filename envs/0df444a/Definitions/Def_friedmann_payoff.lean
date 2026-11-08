-- Prove2me | Definitions.Def_friedmann_payoff
-- name    : friedmann_payoff
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T17:10:24.84435+00:00
-- url     : https://prove2.me/theorems/bb7c15dd-aea7-4b7a-80a2-56923bdd1d74
-- title:
--   Rational payoff and stopping stochastic game models
-- statement:
--   Rational discounted Bellman values, the specified parity-to-payoff reduction, stopping stochastic absorption equations, and the corresponding local and global update rules. Validity predicates require total arenas, a discount in (0,1), or almost-sure absorption as appropriate.
-- source:
--   Friedmann, LMCS2011, §9; https://arxiv.org/abs/1106.0778

import Definitions.Def_friedmann_parity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

open Matrix

namespace FriedmannScalar

open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]

/- A common interface for the actual payoff models below. Every instance in a
mission target is constructed from a concrete game, not supplied as a hypothesis.
-/
structure Model (V : Type) where
  maxNode : V → Prop
  action : V → V → Prop
  maxLegal : (V → V) → Prop
  minLegal : (V → V) → Prop
  payoff : (V → V) → (V → V) → V → ℚ

noncomputable def value (M : Model V) (σ : V → V) (v : V) : ℚ := by
  classical
  exact if h : ∃ a : ℚ,
      (∃ τ, M.minLegal τ ∧ M.payoff σ τ v = a) ∧
        ∀ τ, M.minLegal τ → a ≤ M.payoff σ τ v
    then Classical.choose h else 0

def Improving (M : Model V) (σ : V → V) (v w : V) : Prop :=
  M.maxNode v ∧ M.action v w ∧ value M σ (σ v) < value M σ w

def Improvable (M : Model V) (σ : V → V) : Prop := ∃ v w, Improving M σ v w

def Allowed (M : Model V) (σ σ' : V → V) : Prop :=
  M.maxLegal σ' ∧ ∀ v, M.maxNode v → value M σ (σ v) ≤ value M σ (σ' v)

def Improvement (M : Model V) (σ σ' : V → V) : Prop :=
  Allowed M σ σ' ∧ (Improvable M σ →
    ∃ v, M.maxNode v ∧ value M σ (σ v) < value M σ (σ' v))

def LocalStep (M : Model V) (σ σ' : V → V) : Prop :=
  Improvement M σ σ' ∧ ∀ v w, M.maxNode v → M.action v w →
    value M σ w ≤ value M σ (σ' v)

def GlobalStep (M : Model V) (σ σ' : V → V) : Prop :=
  Improvement M σ σ' ∧ ∀ ρ, Allowed M σ ρ → ∀ v, value M ρ v ≤ value M σ' v

def CompleteRun (M : Model V) (step : (V → V) → (V → V) → Prop)
    (ι : V → V) (T : ℕ) (run : ℕ → (V → V)) : Prop :=
  run 0 = ι ∧ (∀ t, t ≤ T → M.maxLegal (run t)) ∧
    (∀ t, t < T → Improvable M (run t) ∧ step (run t) (run (t + 1))) ∧
    ¬ Improvable M (run T)

def HardInstance (M : Model V) (ι : V → V)
    (step : (V → V) → (V → V) → Prop) (iterations : ℕ) : Prop :=
  M.maxLegal ι ∧ (∃ T run, CompleteRun M step ι T run) ∧
    ∀ T run, CompleteRun M step ι T run → iterations ≤ T

def rule (M : Model V) (global : Bool) : (V → V) → (V → V) → Prop :=
  if global then GlobalStep M else LocalStep M

end FriedmannScalar

namespace FriedmannDiscounted

open scoped BigOperators

structure Game (V : Type) where
  arena : FriedmannParity.Game V
  reward : V → ℚ
  discount : ℚ

variable {V : Type} [Fintype V] [DecidableEq V]

def WellFormed (G : Game V) : Prop :=
  (∀ v, ∃ w, G.arena.edge v w) ∧ 0 < G.discount ∧ G.discount < 1

noncomputable def transition (G : Game V) (σ τ : V → V) : Matrix V V ℚ := by
  classical
  exact fun v w => if (if G.arena.owner v = false then σ v else τ v) = w then 1 else 0

/- Exact rational solution of x = r + βPx. For 0 < β < 1 the matrix is
nonsingular, and this is the infinite discounted sum of the actual play. -/
noncomputable def playValue (G : Game V) (σ τ : V → V) : V → ℚ :=
  (1 - G.discount • transition G σ τ)⁻¹ *ᵥ G.reward

noncomputable def model (G : Game V) : FriedmannScalar.Model V where
  maxNode v := G.arena.owner v = false
  action := G.arena.edge
  maxLegal := FriedmannParity.Legal G.arena false
  minLegal := FriedmannParity.Legal G.arena true
  payoff := playValue G

noncomputable def induced (G : FriedmannParity.Game V) : Game V := by
  classical
  let r : V → ℚ := fun v => (-(Fintype.card V : ℚ)) ^ G.priority v
  let maxReward : ℕ := Finset.univ.sup (fun v => (Fintype.card V) ^ G.priority v)
  exact ⟨G, r, 1 - 1 / (4 * (Fintype.card V : ℚ) ^ 3 * (maxReward : ℚ))⟩

def Exponential : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ global : Bool, ∀ n : ℕ, 0 < n →
    ∃ N : ℕ, ∃ G : Game (Fin N), ∃ ι : Fin N → Fin N,
      WellFormed G ∧ FriedmannParity.edgeCount G.arena ≤ C * n ∧
      FriedmannScalar.HardInstance (model G) ι
        (FriedmannScalar.rule (model G) global) (2 ^ n)

/- Mean-payoff policy iteration in this paper is run through its specified
discounted reduction. A direct mean-reward-only strict-switch algorithm is not
silently substituted, since it can stall at a nonoptimal strategy. -/
def ExponentialMeanViaReduction : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ global : Bool, ∀ n : ℕ, 0 < n →
    ∃ N : ℕ, ∃ G : FriedmannParity.Game (Fin N), ∃ ι : Fin N → Fin N,
      FriedmannParity.WellFormed G ∧ FriedmannParity.edgeCount G ≤ C * n ∧
      WellFormed (induced G) ∧
      FriedmannScalar.HardInstance (model (induced G)) ι
        (FriedmannScalar.rule (model (induced G)) global) (2 ^ n)

end FriedmannDiscounted

namespace FriedmannStochastic

open scoped BigOperators

/- Roles 0 and 1 are Max and Min; role 2 is a random vertex. The two terminals
are excluded from these decision sets by explicit tests in every definition. -/
structure Game (V : Type) where
  role : V → Fin 3
  edge : V → V → Prop
  probability : V → V → ℚ
  win : V
  lose : V

variable {V : Type} [Fintype V] [DecidableEq V]

def Decision (G : Game V) (p : Fin 3) (v : V) : Prop :=
  v ≠ G.win ∧ v ≠ G.lose ∧ G.role v = p

def Legal (G : Game V) (p : Fin 3) (σ : V → V) : Prop :=
  ∀ v, Decision G p v → G.edge v (σ v)

noncomputable def transition (G : Game V) (σ τ : V → V) : Matrix V V ℚ := by
  classical
  exact fun v w => if v = G.win ∨ v = G.lose then 0
    else if G.role v = 0 then (if σ v = w then 1 else 0)
    else if G.role v = 1 then (if τ v = w then 1 else 0)
    else G.probability v w

def WellFormed (G : Game V) : Prop :=
  G.win ≠ G.lose ∧
  (∀ v, v ≠ G.win → v ≠ G.lose → ∃ w, G.edge v w) ∧
  (∀ w, ¬ G.edge G.win w ∧ ¬ G.edge G.lose w) ∧
  (∀ v w, Decision G 2 v → 0 ≤ G.probability v w ∧
    (¬ G.edge v w → G.probability v w = 0)) ∧
  (∀ v, Decision G 2 v → ∑ w, G.probability v w = 1) ∧
  ∀ σ τ, Legal G 0 σ → Legal G 1 τ → ∀ v,
    Relation.ReflTransGen (fun a b => 0 < transition G σ τ a b) v G.win ∨
    Relation.ReflTransGen (fun a b => 0 < transition G σ τ a b) v G.lose

/- Absorption probabilities, obtained from the finite transient transition
matrix. Almost-sure halting in WellFormed makes I-P nonsingular. -/
noncomputable def playValue (G : Game V) (σ τ : V → V) : V → ℚ := by
  classical
  exact (1 - transition G σ τ)⁻¹ *ᵥ (fun v => if v = G.win then 1 else 0)

noncomputable def model (G : Game V) : FriedmannScalar.Model V where
  maxNode := Decision G 0
  action := G.edge
  maxLegal := Legal G 0
  minLegal := Legal G 1
  payoff := playValue G

noncomputable def edgeCount (G : Game V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : V × V => G.edge e.1 e.2)).card

def Exponential : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ global : Bool, ∀ n : ℕ, 0 < n →
    ∃ N : ℕ, ∃ G : Game (Fin N), ∃ ι : Fin N → Fin N,
      WellFormed G ∧ edgeCount G ≤ C * n ∧
      FriedmannScalar.HardInstance (model G) ι
        (FriedmannScalar.rule (model G) global) (2 ^ n)

end FriedmannStochastic


