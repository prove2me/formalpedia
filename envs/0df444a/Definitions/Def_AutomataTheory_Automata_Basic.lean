-- Prove2me | Definitions.Def_AutomataTheory_Automata_Basic
-- name    : AutomataTheory_Automata_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:10:55.467839+00:00
-- url     : https://prove2.me/theorems/cc37a351-6ef5-4f60-ae0f-0888eee01390
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean

import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Filter Stream'
namespace Automata
section AutomataDefinition
class NA (A : Type) where
  State : Type
  init : Set State
  next : State → A → Set State
end AutomataDefinition
section AutomataFiniteRuns
variable {A : Type}
def NA.FinRun (M : NA A) (n : ℕ) (as : Stream' A) (ss : Stream' M.State) :=
  ss 0 ∈ M.init ∧ ∀ k < n, ss (k + 1) ∈ M.next (ss k) (as k)
def NA.FinAccept (M : NA A) (acc : Set M.State) (n : ℕ) (as : Stream' A) :=
  ∃ ss : Stream' M.State, M.FinRun n as ss ∧ ss n ∈ acc
def NA.AcceptedLang (M : NA A) (acc : Set M.State) : Set (List A) :=
  { al | ∃ n as, M.FinAccept acc n as ∧ as.extract 0 n = al }
def NA.FinRun' (M : NA A) (n : ℕ) (as : Fin n → A) (ss : Fin (n + 1) → M.State) :=
  ss 0 ∈ M.init ∧ ∀ k : Fin n, ss k.succ ∈ M.next (ss k.castSucc) (as k)
def NA.FinAccept' (M : NA A) (acc : Set M.State) (n : ℕ) (as : Fin n → A) :=
  ∃ ss : Fin (n + 1) → M.State, M.FinRun' n as ss ∧ ss ⟨n, by omega⟩ ∈ acc
variable {M : NA A} {acc : Set M.State}
end AutomataFiniteRuns
section AutomataInfiniteRuns
variable {A : Type}
def NA.InfRun (M : NA A) (as : Stream' A) (ss : Stream' M.State) :=
  ss 0 ∈ M.init ∧ ∀ k : ℕ, ss (k + 1) ∈ M.next (ss k) (as k)
def NA.BuchiAccept (M : NA A) (acc : Set M.State) (as : Stream' A) :=
  ∃ ss : Stream' M.State, M.InfRun as ss ∧ ∃ᶠ k in atTop, ss k ∈ acc
def NA.MullerAccept (M : NA A) (accSet : Set (Set M.State)) (as : Stream' A) :=
  ∃ ss : Stream' M.State, M.InfRun as ss ∧ ∃ acc ∈ accSet, ∀ s, s ∈ acc ↔ (∃ᶠ k in atTop, ss k = s)
def NA.RabinAccept (M : NA A) (accPairs : Set (Set M.State × Set M.State)) (as : Stream' A) :=
  ∃ ss : Stream' M.State, M.InfRun as ss ∧ ∃ pair ∈ accPairs, (∃ᶠ k in atTop, ss k ∈ pair.1) ∧ (∀ᶠ k in atTop, ss k ∉ pair.2)
def NA.StreettAccept (M : NA A) (accPairs : Set (Set M.State × Set M.State)) (as : Stream' A) :=
  ∃ ss : Stream' M.State, M.InfRun as ss ∧ ∀ pair ∈ accPairs, (∃ᶠ k in atTop, ss k ∈ pair.1) → (∃ᶠ k in atTop, ss k ∈ pair.2)
def NA.AcceptedOmegaLang (M : NA A) (acc : Set M.State) : Set (Stream' A) :=
  { as | M.BuchiAccept acc as }
end AutomataInfiniteRuns
section AutomataBasicResults
variable {A : Type} {M : NA A}
end AutomataBasicResults


