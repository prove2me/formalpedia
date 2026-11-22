-- Prove2me | Definitions.Def_GJKKL_Statement
-- name    : GJKKL_Statement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:30:15.172544+00:00
-- url     : https://prove2.me/theorems/8fec3178-329d-4e58-9bda-4d9c747523aa
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Juan Pablo Traverso Gianini and CDR III contributors's pinned Counting matchings in regular graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Statement.lean

module
public import Definitions.Def_RequestProject_Pseudorandom_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GJKKL
open Finset Pseudorandom
variable {V : Type*} [DecidableEq V]
open Classical in
/-- The matchings of `H` with exactly `m` edges, as a finset of sets of edges. -/
noncomputable def matchingsOfSize (H : Finset (Finset V)) (m : ℕ) : Finset (Finset (Finset V)) :=
  H.powerset.filter (fun M => IsMatching M ∧ M.card = m)
def TargetStatement : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ d₀ : ℝ, ∀ d : ℝ, d₀ ≤ d →
        ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V)),
          IsUniform H k →
          (Fintype.card V : ℝ) ≤ Real.exp (d ^ (ε ^ 3)) →
          (∀ v : V, (1 - d ^ (-ε)) * d ≤ (degree H v : ℝ)) →
          (∀ v : V, (degree H v : ℝ) ≤ d) →
          (∀ u v : V, u ≠ v → (codegree H u v : ℝ) ≤ d ^ (1 - ε)) →
          ∀ m : ℕ, (m : ℝ) ≤ (1 - d ^ (-(ε ^ 3))) * (Fintype.card V : ℝ) / k →
            ((1 - d ^ (-(ε ^ 4))) * d / Real.exp ((k : ℝ) - 1)) ^ m ≤
              ((matchingsOfSize H m).card : ℝ)
end GJKKL


