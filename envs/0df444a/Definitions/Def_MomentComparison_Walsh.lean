-- Prove2me | Definitions.Def_MomentComparison_Walsh
-- name    : MomentComparison_Walsh
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:11:09.424076+00:00
-- url     : https://prove2.me/theorems/26f0a75f-fc41-48ee-b973-4cd27cf85ab7
-- title:
--   Walsh
-- statement:
--   Definitions and structural lemmas for Walsh, from XinyuanXie-hub (XinyuanXie-hub/MomentComparison; see pinned Apache-2.0 LICENSE)'s pinned Sharp two-sided bounds on the moment comparison constant Cstar development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Walsh.lean

module
public import Definitions.Def_MomentComparison_Basic
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open scoped BigOperators symmDiff
namespace MomentComparison
open Finset
@[expose] def cubeSign {n : ℕ} (x : Cube n) (i : Fin n) : ℝ := if x i then 1 else -1
@[expose] def walsh {n : ℕ} (s : Finset (Fin n)) (x : Cube n) : ℝ := ∏ i ∈ s, cubeSign x i
def flip {n : ℕ} (i : Fin n) (x : Cube n) : Cube n :=
  Function.update x i (!x i)
@[expose] noncomputable def walshLayer (n m : ℕ) (x : Cube n) : ℝ :=
  ∑ s ∈ (univ : Finset (Fin n)).powersetCard m, walsh s x
@[expose] def walshPairCount (n m : ℕ) (T : Finset (Fin n)) : ℕ :=
  let u := (univ : Finset (Fin n)).powersetCard m
  ((u ×ˢ u).filter (fun st => st.1 ∆ st.2 = T)).card
end MomentComparison


