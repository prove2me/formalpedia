-- Prove2me | Definitions.Def_Erdos266_Algorithm
-- name    : Erdos266_Algorithm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:46:35.667359+00:00
-- url     : https://prove2.me/theorems/76dcba77-726e-43c6-8d5a-285ce2ff0a5b
-- title:
--   Algorithm
-- statement:
--   Definitions and structural lemmas for Algorithm, from Ben Keene (benkeene/erdos266; Challenge statement adapted under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Erdos Problem 266: Kovac-Tao disproof of Stolarsky's conjecture on shifted Ahmes series development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Theorems.Thm_Erdos266_growth_eventually
public import Theorems.Thm_Erdos266_lattice_lemma

set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace Erdos266
open Finset
noncomputable def εL (d : ℕ) : ℝ := (lattice_lemma d).choose
noncomputable def DL (d : ℕ) : ℝ := (lattice_lemma d).choose_spec.choose
lemma εL_pos (d : ℕ) : 0 < εL d := (lattice_lemma d).choose_spec.choose_spec.1
lemma one_le_DL (d : ℕ) : 1 ≤ DL d := (lattice_lemma d).choose_spec.choose_spec.2.2.1
lemma DL_pos (d : ℕ) : 0 < DL d := lt_of_lt_of_le one_pos (one_le_DL d)
noncomputable def εA : ℕ → ℝ
  | 0 => εL 0
  | d + 1 => min (εA d) (εL (d + 1))
lemma εA_pos (d : ℕ) : 0 < εA d := by
  induction d with
  | zero => exact εL_pos 0
  | succ d ih => exact lt_min ih (εL_pos (d + 1))
noncomputable def mseq : ℕ → ℕ
  | 0 => 2
  | d + 1 => max (mseq d + 1)
      (growth_eventually (d + 1) (DL (d + 1)) (εA (d + 2)) (DL_pos (d + 1))
        (εA_pos (d + 2))).choose
noncomputable def dOf (k : ℕ) : ℕ := Nat.findGreatest (fun d => mseq d ≤ k) k
noncomputable def blockAnchor (i l : ℕ) : ℝ :=
  ∑ j ∈ range (dOf l), f i (((j + 1) * bigN l : ℕ) : ℝ)
noncomputable def tailAnchor (i k : ℕ) : ℝ := ∑' l : ℕ, blockAnchor i (k + l)
end Erdos266


