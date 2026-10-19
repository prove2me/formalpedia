-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_DetypingDecider
-- name    : MIPRE_Foundations_CL_DetypingDecider
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:50:39.00643+00:00
-- url     : https://prove2.me/theorems/77a3c271-a6c9-4548-9773-19d6dd090e87
-- title:
--   Definitions of DetypingDecider: Acceptance and global answer bounds for the detyping compiler
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.DetypingDecider` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Acceptance and global answer bounds for the detyping compiler
--
--   **Definitions** (1): `MIPRE.CL.Detyping.DeciderProgram.verifier` (The executable sampler and decider form a normal-form ambient verifier.).
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `accepts_iff`, `decisionStage_accepts_direct`, `decisionStage_accepts_indirect`, `prog_accepts_iff_stage`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.DetypingDecider` (`MIPRE/Foundations/CL/DetypingDecider.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 48 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingDecider.lean; blueprint lem:detype-executable-decider

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingDecider.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderProg
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_encode_injective
import Theorems.Thm_MIPRE_CL_Detyping_DeciderProgram_decisionStage_direct
import Theorems.Thm_MIPRE_CL_Detyping_DeciderProgram_decisionStage_halts
import Theorems.Thm_MIPRE_CL_Detyping_DeciderProgram_decisionStage_indirect
import Theorems.Thm_MIPRE_CL_Detyping_DeciderProgram_post_apply
import Theorems.Thm_MIPRE_CL_Detyping_DeciderProgram_prog_runs
import Theorems.Thm_MIPRE_CL_Detyping_DeciderProgram_route_context
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode

/-! # Acceptance and global answer bounds for the detyping compiler -/

noncomputable section

namespace MIPRE.CL.Detyping.DeciderProgram

open Cost Cost.PolyTimeFun Program

variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)

theorem decisionStage_accepts_direct (c r : Data) (h : route E c = (false, r)) :
    (∃ time, (decisionStage E D).Runs c (encode true) time) ↔ r = encode true := by
  obtain ⟨t, ht⟩ := decisionStage_direct E D c r h
  constructor
  · rintro ⟨time, hr⟩
    exact (ht.deterministic hr).1
  · rintro rfl
    exact ⟨t, ht⟩

theorem decisionStage_accepts_indirect (c arg ctx : Data)
    (h : route E c = (true, .cons arg ctx)) (hD : Halts D.prog arg) :
    (∃ time, (decisionStage E D).Runs c (encode true) time) ↔
      ∃ time, D.prog.Runs arg (encode true) time := by
  obtain ⟨r, time, hr⟩ := hD
  obtain ⟨t, ht⟩ := decisionStage_indirect E D c arg ctx r time h hr
  constructor
  · rintro ⟨t', ht'⟩
    have he := (ht.deterministic ht').1
    have he' : r = encode true := by
      rw [post_apply] at he
      exact of_decide_eq_true (encode_injective he)
    exact ⟨time, he' ▸ hr⟩
  · rintro ⟨time', hr'⟩
    have he := (hr.deterministic hr').1
    refine ⟨t, ?_⟩
    simpa [post_apply, he] using ht

/-- A raw-input acceptance law: the executable preliminary stages merely supply
their verified dimension and cutoffs to the final router. -/
theorem prog_accepts_iff_stage (hD : D.Total) (input : Data) :
    (∃ time, (prog E S D C).Runs input (encode true) time) ↔
      ∃ time, (decisionStage E D).Runs
        (context input (S.dim (readNat (treeHead input)))
          (C.inner (readNat (treeHead input))) (C.outer (readNat (treeHead input))))
        (encode true) time := by
  obtain ⟨r, t, ht⟩ := decisionStage_halts E D hD
    (context input (S.dim (readNat (treeHead input)))
      (C.inner (readNat (treeHead input))) (C.outer (readNat (treeHead input))))
  obtain ⟨tp, hp⟩ := prog_runs E S D C input r t ht
  constructor
  · rintro ⟨time, hr⟩
    have he := (hp.deterministic hr).1
    exact ⟨t, he ▸ ht⟩
  · rintro ⟨time, hr⟩
    exact prog_runs E S D C input (encode true) time hr

/-- Exact typed-input acceptance. Nonedges accept within the global cutoff;
genuine edges retain the source's inner cutoff and the unchanged answers. -/
theorem accepts_iff (hD : D.Total) (n : ℕ) (x y a b : BitStr) :
    (decider E S D C).Accepts n x y a b ↔
      x.length = graphDim T + S.dim n ∧ y.length = graphDim T + S.dim n ∧
      a.length ≤ C.outer n ∧ b.length ≤ C.outer n ∧
      match selectedEdge E (graphOfBits x) (graphOfBits y) with
      | none => True
      | some uv => a.length ≤ C.inner n ∧ b.length ≤ C.inner n ∧
          D.Accepts n uv.1 (x.drop (graphDim T)) uv.2 (y.drop (graphDim T)) a b := by
  change (∃ time, (prog E S D C).Runs (encode (n, x, y, a, b)) (encode true) time) ↔ _
  rw [prog_accepts_iff_stage E S D C hD]
  have hn : readNat (treeHead (encode (n, x, y, a, b))) = n := by
    simp only [encode_prod, treeHead_cons, readNat_encode]
  rw [hn]
  have hroute := route_context E n (S.dim n) (C.inner n) (C.outer n) x y a b
  by_cases hlength : x.length = graphDim T + S.dim n ∧
      y.length = graphDim T + S.dim n ∧ a.length ≤ C.outer n ∧ b.length ≤ C.outer n
  · rw [if_pos hlength] at hroute
    cases he : selectedEdge E (graphOfBits x) (graphOfBits y) with
    | none =>
      simp only [he] at hroute
      rw [decisionStage_accepts_direct E D _ _ hroute]
      simp [hlength.1, hlength.2.1, hlength.2.2.1, hlength.2.2.2]
    | some uv =>
      simp only [he] at hroute
      by_cases hinner : a.length ≤ C.inner n ∧ b.length ≤ C.inner n
      · rw [if_pos hinner] at hroute
        rw [decisionStage_accepts_indirect E D _ _ _ hroute (hD n _)]
        simp [hlength.1, hlength.2.1, hlength.2.2.1, hlength.2.2.2,
          hinner.1, hinner.2, TypedDecider.Accepts]
      · rw [if_neg hinner] at hroute
        rw [decisionStage_accepts_direct E D _ _ hroute]
        simp [hlength.1, hlength.2.1, hlength.2.2.1, hlength.2.2.2]
        intro ha hb
        exact False.elim (hinner ⟨ha, hb⟩)
  · rw [if_neg hlength] at hroute
    rw [decisionStage_accepts_direct E D _ _ hroute]
    constructor
    · intro h
      have hf : false = true := encode_injective h
      cases hf
    · intro h
      exact False.elim (hlength ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)

/-- The executable sampler and decider form a normal-form ambient verifier. -/
def verifier (hℓ : 0 < ℓ) (hD : D.Total) : MIPRE.Verifier (ℓ + 2) where
  sampler := Detyping.sampler E S hℓ
  decider := decider E S D C
  accepts_length n x y a b h := by
    have h' := (accepts_iff E S D C hD n x y a b).mp h
    exact ⟨h'.1, h'.2.1⟩

end MIPRE.CL.Detyping.DeciderProgram


