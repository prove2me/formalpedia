-- Prove2me | Definitions.Def_Monotonicity_Theorem_DiscTower
-- name    : Monotonicity_Theorem_DiscTower
-- status  : Definition
-- author  : @Tamas Fulop
-- created : 2026-09-14T21:33:42.567877+00:00
-- url     : https://prove2.me/theorems/8843480d-c07a-4251-b6a3-db03047087ef
-- title:
--   Discontinuity-matrix index maps
-- statement:
--   The coordinate index maps selecting graph, epsilon, delta, and bad-point slots out of flattened tuples, plus the point-as-lambda identity.
-- source:
--   van den Dries, Tame Topology and O-Minimal Structures, Ch. 3

import Definitions.Def_Monotonicity_Theorem_Framework
import Mathlib.Tactic.FinCases

open Monotonicity_Theorem

-- Points are determined by coordinates.
theorem ptLam {R : Type} (x : Power R 1) : x = fun _ => Power.coord1 x := by
  funext k
  have hk : k.val = 0 := by
    have := k.isLt
    omega
  have ek : k = (⟨0, by decide⟩ : Fin 1) := Fin.ext hk
  rw [ek]
  rfl

-- Index maps for the discontinuity matrix (wide layout, arity 8).
-- Slots: 0:x, 1:w0, 2:e1, 3:e2, 4:d1, 5:d2, 6:y, 7:q.
def dIx : Fin 1 → Fin 8 := fun _ => ⟨0, by decide⟩
def dGy : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨6, by decide⟩ else ⟨7, by decide⟩
def dD1y : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨4, by decide⟩ else ⟨6, by decide⟩
def dYD2 : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨6, by decide⟩ else ⟨5, by decide⟩
def dE1q : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨2, by decide⟩ else ⟨7, by decide⟩
def dQe2 : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨7, by decide⟩ else ⟨3, by decide⟩
-- Delta maps at arity 6 (tuple x,w0,e1,e2,d1,d2).
def dD1x6 : Fin 2 → Fin 6 := fun j => if _ : j.val = 0 then ⟨4, by decide⟩ else ⟨0, by decide⟩
def dXD26 : Fin 2 → Fin 6 := fun j => if _ : j.val = 0 then ⟨0, by decide⟩ else ⟨5, by decide⟩
-- Graph/epsilon maps at arity 4 (tuple x,w0,e1,e2).
def dGx4 : Fin 2 → Fin 4 := fun j => if _ : j.val = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩
def dE1w4 : Fin 2 → Fin 4 := fun j => if _ : j.val = 0 then ⟨2, by decide⟩ else ⟨1, by decide⟩
def dWe24 : Fin 2 → Fin 4 := fun j => if _ : j.val = 0 then ⟨1, by decide⟩ else ⟨3, by decide⟩


