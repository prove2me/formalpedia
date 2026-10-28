-- Prove2me | Definitions.Def_RuntimeTransfer
-- name    : RuntimeTransfer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T10:52:51.819021+00:00
-- url     : https://prove2.me/theorems/223b91d8-cf1c-46eb-b421-c57ff8b69b49
-- title:
--   Oracle programs with explicit cost semantics
-- statement:
--   Defines terminating adaptive oracle programs, explicit local-work charges, execution as an answer/cost pair, the specification-selected value and budget, query counts, local overhead, query-size bounds, sequential composition, query expansion, and an eventual big-O predicate for natural-valued functions. Arbitrary functions and returned values carry no implicit evaluation charge. This is a relative oracle-cost semantics; it does not certify machine runtimes or computability of those functions.
-- source:
--   General runtime transfer and its Fourier/packing applications, companion proof note for this mission, 24 October 2026. Original cost-semantics formulation of standard substitution principles; not a claimed new complexity bound.

import Mathlib.Data.Nat.Basic

set_option autoImplicit false

namespace RuntimeTransfer

/-- A finite, possibly adaptive oracle computation. Local work is explicitly charged
with `work`; this is an oracle cost semantics, not a Turing-machine compiler. -/
inductive Program (Q A R : Type) where
  | done : R → Program Q A R
  | work : ℕ → Program Q A R → Program Q A R
  | query : Q → (A → Program Q A R) → Program Q A R

def Program.run {Q A R : Type} (oracle : Q → A × ℕ) : Program Q A R → R × ℕ
  | .done r => (r, 0)
  | .work c p => let z := p.run oracle; (z.1, c + z.2)
  | .query q next => let a := oracle q; let z := (next a.1).run oracle;
      (z.1, a.2 + z.2)

def Program.value {Q A R : Type} (spec : Q → A) : Program Q A R → R
  | .done r => r
  | .work _ p => p.value spec
  | .query q next => (next (spec q)).value spec

def Program.budget {Q A R : Type} (spec : Q → A) (bound : Q → ℕ) :
    Program Q A R → ℕ
  | .done _ => 0
  | .work c p => c + p.budget spec bound
  | .query q next => bound q + (next (spec q)).budget spec bound

def Program.calls {Q A R : Type} (spec : Q → A) : Program Q A R → ℕ
  | .done _ => 0
  | .work _ p => p.calls spec
  | .query q next => 1 + (next (spec q)).calls spec

def Program.overhead {Q A R : Type} (spec : Q → A) : Program Q A R → ℕ
  | .done _ => 0
  | .work c p => c + p.overhead spec
  | .query q next => (next (spec q)).overhead spec

/-- Only queries on the execution path selected by the specification are bounded. -/
def Program.QueriesBounded {Q A R : Type} (spec : Q → A) (size : Q → ℕ)
    (s : ℕ) : Program Q A R → Prop
  | .done _ => True
  | .work _ p => p.QueriesBounded spec size s
  | .query q next => size q ≤ s ∧ (next (spec q)).QueriesBounded spec size s

def Program.bind {Q A R S : Type} (p : Program Q A R)
    (f : R → Program Q A S) : Program Q A S :=
  match p with
  | .done r => f r
  | .work c next => .work c (next.bind f)
  | .query q next => .query q (fun a => (next a).bind f)

/-- Replace every outer query by a finite inner oracle computation. -/
def Program.expand {Q A R Q' A' : Type} (p : Program Q A R)
    (inner : Q → Program Q' A' A) : Program Q' A' R :=
  match p with
  | .done r => .done r
  | .work c next => .work c (next.expand inner)
  | .query q next => (inner q).bind (fun a => (next a).expand inner)

/-- Standard Big-O for natural-valued functions, with a positive integral constant. -/
def BigOBound (f g : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∃ N : ℕ, ∀ n, N ≤ n → f n ≤ C * g n

end RuntimeTransfer


