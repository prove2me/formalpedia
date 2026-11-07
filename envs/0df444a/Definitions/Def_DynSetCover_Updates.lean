-- Prove2me | Definitions.Def_DynSetCover_Updates
-- name    : DynSetCover_Updates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:48.786338+00:00
-- url     : https://prove2.me/theorems/031761fa-1622-4d5e-9cc3-99e72912506e
-- title:
--   §1 — updates, active sets $A_t$ and valid update sequences
-- statement:
--   In fully dynamic set cover the set of **active** elements changes over time: each update inserts one element into the active set or deletes one element from it. For an update sequence $\sigma=(\sigma_1,\sigma_2,\dots)$, the active set $A_t$ after the first $t$ updates is obtained from $A_0=\emptyset$ by applying them in order. The sequence is **valid** if every insertion inserts an inactive element and every deletion deletes an active one.
--
--   Each update also has an input word: $2e$ for inserting $e$ and $2e+1$ for deleting $e$.
--
--   **Formalization Note** $A_t$ is computed by folding the first $t$ updates over $\emptyset$.
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), §1, p.1 (PDF 3); A_t and n_t, p.2 (PDF 4)

import Mathlib

namespace DynSetCover

/-- **Updates of fully dynamic set cover** (Paul, Solomon, STOC 2027 submission, sha256
a671756b…, §1, p.1 (PDF 3)): "Each update inserts one element into the active set or deletes
one element from it." -/
inductive Upd (u : ℕ) where
  | ins (e : Fin u)
  | del (e : Fin u)
  deriving DecidableEq

namespace Upd

variable {u : ℕ}

/-- The effect of an update on the active set. -/
def apply : Upd u → Finset (Fin u) → Finset (Fin u)
  | ins e, A => insert e A
  | del e, A => A.erase e

/-- An update is valid for the active set `A` if it inserts an inactive element or deletes an
active one. -/
def ValidAt : Upd u → Finset (Fin u) → Prop
  | ins e, A => e ∉ A
  | del e, A => e ∈ A

/-- The input word of an update: `2e` for inserting `e`, `2e + 1` for deleting `e`.

**Formalization Note.** One word per update, so that a word-RAM reads an update in one step
(§7, p.56). -/
def word : Upd u → ℕ
  | ins e => 2 * (e : ℕ)
  | del e => 2 * (e : ℕ) + 1

/-- Whether the update is an insertion (arrival). -/
def isIns : Upd u → Bool
  | ins _ => true
  | del _ => false

end Upd

/-- `A_t`, the active set after the first `t` updates of `σ`, with `A_0 = ∅` (p.2). -/
def active {u : ℕ} (σ : List (Upd u)) (t : ℕ) : Finset (Fin u) :=
  (σ.take t).foldl (fun A x => x.apply A) ∅

/-- A valid update sequence: every insertion is of an inactive element and every deletion of
an active one. -/
def Valid {u : ℕ} (σ : List (Upd u)) : Prop :=
  ∀ t (h : t < σ.length), (σ[t]).ValidAt (active σ t)

end DynSetCover


