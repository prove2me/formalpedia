-- Prove2me | Definitions.Def_friedmann_parity
-- name    : friedmann_parity
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-02T05:10:09.657942+00:00
-- url     : https://prove2.me/theorems/0c93926b-a5e4-4c33-9714-4dcddf1748b1
-- title:
--   Finite parity games and deterministic strategy improvement
-- statement:
--   Finite positional parity games, ultimately periodic plays, three-component valuations, minima over legal counterstrategies, local and global improvement, completed executions, and constrained lower-bound propositions. No witness family or long execution is assumed.
-- source:
--   Friedmann, LMCS2011, §§2–8; https://arxiv.org/abs/1106.0778

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

/-!
Finite parity games and the Vöge–Jurdziński valuation, as in Friedmann,
LMCS 2011, §§2–4. `false` denotes player 0. Functions representing strategies
are ignored at the other player's vertices. Definitions contain no open proofs.
-/
namespace FriedmannParity

structure Game (V : Type) where
  owner : V → Bool
  priority : V → ℕ
  edge : V → V → Prop

variable {V : Type} [Fintype V] [DecidableEq V]

def WellFormed (G : Game V) : Prop :=
  (∀ v, ∃ w, G.edge v w) ∧ Function.Injective G.priority

def Legal (G : Game V) (player : Bool) (σ : V → V) : Prop :=
  ∀ v, G.owner v = player → G.edge v (σ v)

def play (G : Game V) (σ τ : V → V) (v : V) : ℕ → V :=
  fun t => (fun w => if G.owner w = false then σ w else τ w)^[t] v

noncomputable def recurring (π : ℕ → V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∀ t, ∃ k, t ≤ k ∧ π k = v)

structure Valuation (V : Type) where
  cyclePriority : ℕ
  path : Finset V
  length : ℕ
  deriving DecidableEq

/- The finite orbit always has a recurring vertex. Thus `sup` and the least index have
their ordinary intended meanings on finite games; the valuation milestone makes
this obligation explicit. Empty V has no starting vertex. -/
noncomputable def playValue (G : Game V) (σ τ : V → V) (v : V) : Valuation V := by
  classical
  let π := play G σ τ v
  let p := (recurring π).sup G.priority
  let w := if h : ∃ w, w ∈ recurring π ∧ G.priority w = p
    then Classical.choose h else v
  let k := if h : ∃ k : ℕ, π k = w then Nat.find h else 0
  exact ⟨p, ((Finset.range k).image π).filter (fun w => p < G.priority w), k⟩

def reward (p : ℕ) : ℤ := if p % 2 = 0 then (p : ℤ) else -(p : ℤ)

def SetLT (G : Game V) (A B : Finset V) : Prop :=
  ∃ w, w ∈ (A \ B) ∪ (B \ A) ∧
    (∀ u ∈ (A \ B) ∪ (B \ A), G.priority u ≤ G.priority w) ∧
    ((G.priority w % 2 = 0 ∧ w ∈ B) ∨ (G.priority w % 2 = 1 ∧ w ∈ A))

def ValueLT (G : Game V) (a b : Valuation V) : Prop :=
  reward a.cyclePriority < reward b.cyclePriority ∨
  (a.cyclePriority = b.cyclePriority ∧ SetLT G a.path b.path) ∨
  (a.cyclePriority = b.cyclePriority ∧ a.path = b.path ∧
    ((a.cyclePriority % 2 = 1 ∧ a.length < b.length) ∨
      (a.cyclePriority % 2 = 0 ∧ b.length < a.length)))

def ValueLE (G : Game V) (a b : Valuation V) : Prop := a = b ∨ ValueLT G a b

def IsMinimum (G : Game V) (σ : V → V) (v : V) (a : Valuation V) : Prop :=
  (∃ τ, Legal G true τ ∧ playValue G σ τ v = a) ∧
  ∀ τ, Legal G true τ → ValueLE G a (playValue G σ τ v)

/- A constrained minimum of actual legal counterstrategy valuations, never an
arbitrary valuation parameter. The fallback is irrelevant once existence is
proved for the finite, total, injective-priority model. -/
noncomputable def value (G : Game V) (σ : V → V) (v : V) : Valuation V :=
  by
    classical
    exact if h : ∃ a, IsMinimum G σ v a then Classical.choose h else ⟨0, ∅, 0⟩

def OptimalCounterstrategy (G : Game V) (σ τ : V → V) : Prop :=
  Legal G true τ ∧ ∀ v τ', Legal G true τ' →
    ValueLE G (playValue G σ τ v) (playValue G σ τ' v)

def Improving (G : Game V) (σ : V → V) (v w : V) : Prop :=
  G.owner v = false ∧ G.edge v w ∧
    ValueLT G (value G σ (σ v)) (value G σ w)

def Improvable (G : Game V) (σ : V → V) : Prop := ∃ v w, Improving G σ v w

def Allowed (G : Game V) (σ σ' : V → V) : Prop :=
  Legal G false σ' ∧ ∀ v, G.owner v = false →
    ValueLE G (value G σ (σ v)) (value G σ (σ' v))

def Improvement (G : Game V) (σ σ' : V → V) : Prop :=
  Allowed G σ σ' ∧
    (Improvable G σ → ∃ v, G.owner v = false ∧
      ValueLT G (value G σ (σ v)) (value G σ (σ' v)))

def LocalStep (G : Game V) (σ σ' : V → V) : Prop :=
  Improvement G σ σ' ∧ ∀ v w, G.owner v = false → G.edge v w →
    ValueLE G (value G σ w) (value G σ (σ' v))

def GlobalStep (G : Game V) (σ σ' : V → V) : Prop :=
  Improvement G σ σ' ∧ ∀ ρ, Allowed G σ ρ → ∀ v,
    ValueLE G (value G ρ v) (value G σ' v)

def CompleteRun (G : Game V) (step : (V → V) → (V → V) → Prop)
    (ι : V → V) (T : ℕ) (run : ℕ → (V → V)) : Prop :=
  run 0 = ι ∧ (∀ t, t ≤ T → Legal G false (run t)) ∧
    (∀ t, t < T → Improvable G (run t) ∧ step (run t) (run (t + 1))) ∧
    ¬ Improvable G (run T)

noncomputable def edgeCount (G : Game V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : V × V => G.edge e.1 e.2)).card

def HardInstance (G : Game V) (ι : V → V)
    (step : (V → V) → (V → V) → Prop) (iterations : ℕ) : Prop :=
  WellFormed G ∧ Legal G false ι ∧
    (∃ T run, CompleteRun G step ι T run) ∧
    ∀ T run, CompleteRun G step ι T run → iterations ≤ T

/- Both families, including their size bound, are conclusions to be proved.
No field or hypothesis supplies a long execution. The constant is uniform in n.
Size is edges, as in the source, rather than vertices or numeric bit length. -/
def ExponentialLocal : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n →
    ∃ N : ℕ, ∃ G : Game (Fin N), ∃ ι : Fin N → Fin N,
      edgeCount G ≤ C * n ∧
      (∀ v, G.priority v ≤ C * n) ∧ HardInstance G ι (LocalStep G) (2 ^ n)

def ExponentialGlobal : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n →
    ∃ N : ℕ, ∃ G : Game (Fin N), ∃ ι : Fin N → Fin N,
      edgeCount G ≤ C * n ∧
      (∀ v, G.priority v ≤ C * n) ∧ HardInstance G ι (GlobalStep G) (2 ^ n)

def Binary (G : Game V) : Prop :=
  ∀ v, ∃ a b, ∀ w, G.edge v w → w = a ∨ w = b

def ExponentialBinary : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ global : Bool, ∀ n : ℕ, 0 < n →
    ∃ N : ℕ, ∃ G : Game (Fin N), ∃ ι : Fin N → Fin N,
      Binary G ∧ edgeCount G ≤ C * n ∧
      (∀ v, G.priority v ≤ C * n) ∧
      HardInstance G ι (if global then GlobalStep G else LocalStep G) (2 ^ n)

def Wins (G : Game V) (player : Bool) (σ : V → V) (v : V) : Prop :=
  Legal G player σ ∧ ∀ τ, Legal G (!player) τ →
    (if player = false then (playValue G σ τ v).cyclePriority % 2 = 0
      else (playValue G τ σ v).cyclePriority % 2 = 1)

def WinningRegion (G : Game V) (player : Bool) : Set V :=
  {v | ∃ σ, Wins G player σ v}

def IsSinkGame (G : Game V) (ι : V → V) (sink : V) : Prop :=
  WellFormed G ∧ Legal G false ι ∧
    G.edge sink sink ∧ G.priority sink = 1 ∧
    (∀ v, v ≠ sink → 1 < G.priority v) ∧
    (∀ v, Relation.ReflTransGen G.edge v sink) ∧
    ∀ σ, Legal G false σ →
      (∀ v, ValueLE G (value G ι v) (value G σ v)) →
      ∀ v, (value G σ v).cyclePriority = 1

end FriedmannParity


