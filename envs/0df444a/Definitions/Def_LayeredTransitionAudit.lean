-- Prove2me | Definitions.Def_LayeredTransitionAudit
-- name    : LayeredTransitionAudit
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T20:53:48.398912+00:00
-- url     : https://prove2.me/theorems/a05ad6d9-fc46-5530-a50f-5fc4bc6dfd8e
-- title:
--   Layered certificates for deterministic transition diagrams
-- statement:
--   A layered transition diagram reads one symbol per layer from a finite allowed set and updates its state deterministically. A certificate lists a set of states in each layer, contains the initial state in layer zero, contains all allowed successors in the next layer, and satisfies a terminal condition. Two diagrams reading the same symbols in the same order can be combined by taking pairs of states.
-- source:
--   The finite-automata product construction and forward reachability in a layered graph.

import Mathlib

set_option autoImplicit false

namespace LayeredTransitionAudit

variable {Q A : Type*} [DecidableEq Q]

def successor (allowed : ℕ → Finset A) (step : ℕ → Q → A → Q)
    (i : ℕ) (states : Finset Q) : Finset Q :=
  states.biUnion fun q => (allowed i).image (step i q)

def reachable (allowed : ℕ → Finset A) (step : ℕ → Q → A → Q) (root : Q) :
    ℕ → Finset Q
  | 0 => {root}
  | i + 1 => successor allowed step i (reachable allowed step root i)

def acceptsWord (allowed : ℕ → Finset A) : ℕ → List A → Prop
  | _, [] => True
  | i, a :: tail => a ∈ allowed i ∧ acceptsWord allowed (i + 1) tail

def run (step : ℕ → Q → A → Q) : ℕ → Q → List A → Q
  | _, q, [] => q
  | i, q, a :: tail => run step (i + 1) (step i q a) tail

def ClosedLayers (allowed : ℕ → Finset A) (step : ℕ → Q → A → Q)
    (root : Q) (width : ℕ) (layers : ℕ → Finset Q) (valid : Q → Prop) : Prop :=
  root ∈ layers 0 ∧
  (∀ i < width, successor allowed step i (layers i) ⊆ layers (i + 1)) ∧
  ∀ q ∈ layers width, valid q

/-- Membership tests compare explicit states in adjacent layers. The
list loops do not enumerate the words represented by those layers. -/
def verify (allowed : ℕ → List A) (step : ℕ → Q → A → Q)
    (root : Q) (width : ℕ) (layers : ℕ → List Q) (valid : Q → Bool) : Bool :=
  decide (root ∈ layers 0) &&
  (List.range width).all (fun i =>
    (layers i).all (fun q =>
      (allowed i).all (fun a => decide (step i q a ∈ layers (i + 1))))) &&
  (layers width).all valid

section Product

variable {Left Right : Type*}

def productStep (left : ℕ → Left → A → Left) (right : ℕ → Right → A → Right)
    (i : ℕ) (states : Left × Right) (a : A) : Left × Right :=
  (left i states.1 a, right i states.2 a)

end Product

end LayeredTransitionAudit


