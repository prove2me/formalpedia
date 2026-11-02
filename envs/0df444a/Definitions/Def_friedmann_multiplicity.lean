-- Prove2me | Definitions.Def_friedmann_multiplicity
-- name    : friedmann_multiplicity
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-02T05:10:21.610209+00:00
-- url     : https://prove2.me/theorems/5f01719c-ebb2-4fda-8b0e-95108285e67b
-- title:
--   Parity-game valuations with repeated priorities
-- statement:
--   Priority-occurrence-count ordering of parity-game play valuations, constrained minimum over legal opponent strategies, and improving switches. Repeated priorities are allowed; the minimum fallback is an explicit validity obligation.
-- source:
--   Avis and Friedmann, Mathematical Programming2017, §2.2; https://arxiv.org/abs/1305.3944

import Definitions.Def_friedmann_parity

set_option autoImplicit false

/-! The repeated-priority valuation of Avis–Friedmann §2.2. Unlike the
injective-priority specialization, this compares PRIORITY OCCURRENCE COUNTS,
not which tied vertex happens to be selected from a symmetric difference. -/
namespace FriedmannMultiplicity

open FriedmannParity

variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def count (G : Game V) (A : Finset V) (p : ℕ) : ℕ := by
  classical
  exact (A.filter (fun v => G.priority v = p)).card

def SetLT (G : Game V) (A B : Finset V) : Prop :=
  ∃ p : ℕ, count G A p ≠ count G B p ∧
    (∀ q : ℕ, p < q → count G A q = count G B q) ∧
    ((p % 2 = 0 ∧ count G A p < count G B p) ∨
      (p % 2 = 1 ∧ count G B p < count G A p))

def SetEquivalent (G : Game V) (A B : Finset V) : Prop :=
  ∀ p, count G A p = count G B p

def ValueLT (G : Game V) (a b : Valuation V) : Prop :=
  reward a.cyclePriority < reward b.cyclePriority ∨
  (a.cyclePriority = b.cyclePriority ∧ SetLT G a.path b.path) ∨
  (a.cyclePriority = b.cyclePriority ∧ SetEquivalent G a.path b.path ∧
    ((a.cyclePriority % 2 = 1 ∧ a.length < b.length) ∨
      (a.cyclePriority % 2 = 0 ∧ b.length < a.length)))

/-- Equivalent paths may consist of different vertices with identical counts. -/
def ValueLE (G : Game V) (a b : Valuation V) : Prop := ¬ValueLT G b a

def IsMinimum (G : Game V) (σ : V → V) (v : V) (a : Valuation V) : Prop :=
  (∃ τ, Legal G true τ ∧ playValue G σ τ v = a) ∧
  ∀ τ, Legal G true τ → ValueLE G a (playValue G σ τ v)

noncomputable def value (G : Game V) (σ : V → V) (v : V) : Valuation V := by
  classical
  exact if h : ∃ a, IsMinimum G σ v a then Classical.choose h else ⟨0, ∅, 0⟩

def Improving (G : Game V) (σ : V → V) (v w : V) : Prop :=
  G.owner v = false ∧ G.edge v w ∧
    ValueLT G (value G σ (σ v)) (value G σ w)

def Improvable (G : Game V) (σ : V → V) : Prop := ∃ v w, Improving G σ v w

end FriedmannMultiplicity


