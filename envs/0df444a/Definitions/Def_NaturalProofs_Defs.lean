-- Prove2me | Definitions.Def_NaturalProofs_Defs
-- name    : NaturalProofs_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:18:06.063206+00:00
-- url     : https://prove2.me/theorems/ed71b040-c70d-4755-8577-8d62641d74ec
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from zzyzek / NaturalProof-Lean contributors's pinned NaturalProof-Lean development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Defs.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace NaturalProofs
inductive Wire (α : Type) where
  | input (a : α)
  | const (b : Bool)
  | gate (i : ℕ)
inductive Gate (α : Type) where
  | not (w : Wire α)
  | and (w₁ w₂ : Wire α)
  | or (w₁ w₂ : Wire α)
def Wire.eval {α : Type} (x : α → Bool) (vals : List Bool) : Wire α → Bool
  | .input a => x a
  | .const b => b
  | .gate i => vals.getD i false
def Gate.eval {α : Type} (x : α → Bool) (vals : List Bool) : Gate α → Bool
  | .not w => !(w.eval x vals)
  | .and w₁ w₂ => w₁.eval x vals && w₂.eval x vals
  | .or w₁ w₂ => w₁.eval x vals || w₂.eval x vals
def evalGates {α : Type} (x : α → Bool) (gs : List (Gate α)) : List Bool :=
  gs.foldl (fun vals g => vals ++ [g.eval x vals]) []
structure Circuit (α : Type) where
  gates : List (Gate α)
  output : Wire α
def Circuit.size {α : Type} (C : Circuit α) : ℕ := C.gates.length
def Circuit.eval {α : Type} (C : Circuit α) (x : α → Bool) : Bool :=
  C.output.eval x (evalGates x C.gates)
abbrev BoolFn (n : ℕ) := (Fin n → Bool) → Bool
abbrev Property := (n : ℕ) → Set (BoolFn n)
def Constructive (C : Property) : Prop :=
  ∃ c n₀ : ℕ, ∀ n ≥ n₀, ∃ D : Circuit (Fin n → Bool),
    D.size ≤ 2 ^ (c * n) ∧ ∀ f : BoolFn n, D.eval f = true ↔ f ∈ C n
open Classical in
/-- Largeness: `C n` contains at least a `2 ^ (-O(n))` fraction of all `2 ^ (2 ^ n)` Boolean
functions of `n` variables. -/
def Large (C : Property) : Prop :=
  ∃ c n₀ : ℕ, ∀ n ≥ n₀,
    2 ^ (2 ^ n) ≤ (Finset.univ.filter (fun f : BoolFn n => f ∈ C n)).card * 2 ^ (c * n)
def IsNatural (C : Property) : Prop :=
  ∃ C' : Property, (∀ n, C' n ⊆ C n) ∧ Constructive C' ∧ Large C'
def UsefulAgainstPPoly (C : Property) : Prop :=
  ∀ d : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ f ∈ C n, ∀ D : Circuit (Fin n), D.eval = f → n ^ d < D.size
def GenInPPoly (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool) : Prop :=
  ∃ c : ℕ, ∀ k (j : Fin (2 * k)), ∃ D : Circuit (Fin k),
    D.size ≤ k ^ c + c ∧ ∀ x, D.eval x = G k x j
def HardnessAtLeast (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool) (k : ℕ) (T : ℝ) :
    Prop :=
  ∀ (S : ℕ) (D : Circuit (Fin (2 * k))), 0 < S → D.size ≤ S →
    (1 : ℝ) / S ≤
      |((Finset.univ.filter (fun x : Fin k → Bool => D.eval (G k x) = true)).card : ℝ) / 2 ^ k -
        ((Finset.univ.filter (fun y : Fin (2 * k) → Bool => D.eval y = true)).card : ℝ) /
          2 ^ (2 * k)| →
    T ≤ S
end NaturalProofs


