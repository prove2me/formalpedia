-- Prove2me | Definitions.Def_BKAR_Interpolation
-- name    : BKAR_Interpolation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:14:57.044119+00:00
-- url     : https://prove2.me/theorems/a25d009f-21dc-4627-a345-d6cfb1915c4c
-- title:
--   Interpolation
-- statement:
--   Definitions and structural lemmas for Interpolation, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Theorems.Thm_BKAR_Forest_EdgeExtension_mem_old_of_mem_of_ne
import Theorems.Thm_BKAR_Forest_empty_edges

set_option autoImplicit false
namespace BKAR
variable {V : Type*} [DecidableEq V]
def constantConfig (t : ℝ) : Edge V → ℝ :=
  fun _ => t
def zeroConfig : Edge V → ℝ :=
  constantConfig 0
def oneConfig : Edge V → ℝ :=
  constantConfig 1
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
abbrev EdgeParam (F : Forest V) : Type _ :=
  { e : Edge V // e ∈ F.edges }
def emptyParam : (Forest.empty V).EdgeParam → ℝ :=
  fun e => False.elim (by
    have he : e.val ∈ (∅ : Finset (Edge V)) := by
      rw [← Forest.empty_edges V]
      exact e.property
    exact Finset.notMem_empty e.val he)
def paramValue (F : Forest V) (u : F.EdgeParam → ℝ) (e : Edge V) : ℝ :=
  if he : e ∈ F.edges then u ⟨e, he⟩ else 1
def pathMinAux (F : Forest V) (u : F.EdgeParam → ℝ) :
    ℝ → List (Edge V) → ℝ
  | a, [] => a
  | a, e :: γ => F.pathMinAux u (min a (F.paramValue u e)) γ
def pathMin (F : Forest V) (u : F.EdgeParam → ℝ) : List (Edge V) → ℝ
  | [] => 1
  | e :: γ => F.pathMinAux u (F.paramValue u e) γ
noncomputable def standardInterp (F : Forest V) (u : F.EdgeParam → ℝ) :
    Edge V → ℝ :=
  fun e =>
    if h : F.inSameComponent e.left e.right then
      F.pathMin u (F.pathInF e.left e.right h)
    else
      0
noncomputable def interpWithFill (F : Forest V) (u : F.EdgeParam → ℝ)
    (t : ℝ) : Edge V → ℝ :=
  fun e =>
    if h : F.inSameComponent e.left e.right then
      F.pathMin u (F.pathInF e.left e.right h)
    else
      t
namespace EdgeExtension
variable {F F' : Forest V} {e₀ : Edge V}
def extendParam (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) (s : ℝ) : F'.EdgeParam → ℝ :=
  fun e =>
    if he : e.val = e₀ then
      s
    else
      u ⟨e.val, h.mem_old_of_mem_of_ne e.property he⟩
end EdgeExtension
end Forest
end BKAR


