-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
-- name    : MIPRE_Foundations_CL_DetypingProgSampler
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:25:05.807794+00:00
-- url     : https://prove2.me/theorems/3730675f-fa46-4299-a0ea-5ebc1d0ad543
-- title:
--   Definitions of DetypingProgSampler: The actual detyping sampler A fixed finite graph and an arbitrary typed sampler compile to an ordinary sampler with two…
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.DetypingProgSampler` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The actual detyping sampler. A fixed finite graph and an arbitrary typed sampler compile to an ordinary sampler with two additional levels. The construction includes a closed ambient program, all query correctness clauses and halting on every malformed query.
--
--   **Definitions** (2): `MIPRE.CL.Detyping.sampler` (Detyping as a genuine ambient sampler, with two additional CL levels.); `MIPRE.CL.Detyping.samplerProg`.
--
--   **Embedded lemmas** (8): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `samplerProg_closed`, `samplerProg_dimension`, `samplerProg_factor`, `samplerProg_halts`, `samplerProg_linear`, `samplerProg_marginal`, `run_call`, `run_direct`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.DetypingProgSampler` (`MIPRE/Foundations/CL/DetypingProgSampler.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 35 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingProgSampler.lean; blueprint lem:detype-functional-sampler

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingProgSampler.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
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
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Theorems.Thm_MIPRE_CL_CLFun_factorOfPrefix_zeroOn
import Theorems.Thm_MIPRE_CL_CLFun_mapOfPrefix_zeroOn
import Theorems.Thm_MIPRE_CL_Detyping_Program_content_length
import Theorems.Thm_MIPRE_CL_Detyping_Program_pad_content
import Theorems.Thm_MIPRE_CL_Detyping_Program_post_dimension
import Theorems.Thm_MIPRE_CL_Detyping_Program_post_prefix
import Theorems.Thm_MIPRE_CL_Detyping_Program_route_dimension
import Theorems.Thm_MIPRE_CL_Detyping_Program_route_factor_early
import Theorems.Thm_MIPRE_CL_Detyping_Program_route_factor_late
import Theorems.Thm_MIPRE_CL_Detyping_Program_route_linear_early
import Theorems.Thm_MIPRE_CL_Detyping_Program_route_linear_late
import Theorems.Thm_MIPRE_CL_Detyping_Program_route_marginal_early
import Theorems.Thm_MIPRE_CL_Detyping_Program_route_marginal_late
import Theorems.Thm_MIPRE_CL_Detyping_Program_route_preserves
import Theorems.Thm_MIPRE_CL_Detyping_graphOfBits_take_eq
import Theorems.Thm_MIPRE_CL_Detyping_numbered_exactlyOn
import Theorems.Thm_MIPRE_CL_Detyping_numbered_factor_content
import Theorems.Thm_MIPRE_CL_Detyping_numbered_factor_graph
import Theorems.Thm_MIPRE_CL_Detyping_numbered_linear_content
import Theorems.Thm_MIPRE_CL_Detyping_numbered_linear_graph
import Theorems.Thm_MIPRE_CL_Detyping_numbered_marginal_content
import Theorems.Thm_MIPRE_CL_Detyping_numbered_marginal_graph
import Theorems.Thm_MIPRE_CL_Detyping_numbered_selected_prefix
import Theorems.Thm_MIPRE_CL_Detyping_toBits_zero
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_closed
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_direct
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_halts
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_indirect

/-! # The actual detyping sampler

A fixed finite graph and an arbitrary typed sampler compile to an ordinary
sampler with two additional levels. The construction includes a closed ambient
program, all query correctness clauses and halting on every malformed query.
-/

noncomputable section

namespace MIPRE.CL.Detyping

open Cost Program

variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T] {ℓ : ℕ}
variable (E : T → T → Prop) [DecidableRel E] (S : TypedSampler ℓ T)

def samplerProg : Prog := Prog.routeOneCall (route E) S.prog (post (graphDim T))

theorem samplerProg_closed : (samplerProg E S).WellScoped 1 :=
  Prog.routeOneCall_closed _ S.closed _

theorem samplerProg_halts (n : ℕ) (q : Data) :
    Halts (samplerProg E S) (.cons (encode n) q) :=
  Prog.routeOneCall_halts _ S.closed _ n q (S.halts n) (route_preserves E n q)

theorem run_direct (n : ℕ) (q : Sampler.Query) (out : BitStr)
    (h : route E (encode (n, q)) = directResult out) :
    ∃ time, (samplerProg E S).Runs (encode (n, q)) (encode out) time :=
  Prog.routeOneCall_direct _ _ _ _ _ h

theorem run_call (n : ℕ) (q : Sampler.Query) (sub : TypedSampler.Query T)
    (preBits out : BitStr) (time : ℕ)
    (h : route E (encode (n, q)) = callResult (encode (n, sub)) (withPrefix preBits))
    (hr : S.prog.Runs (encode (n, sub)) (encode out) time) :
    ∃ t, (samplerProg E S).Runs (encode (n, q)) (encode (preBits ++ out)) t := by
  obtain ⟨t, ht⟩ := Prog.routeOneCall_indirect (route E) S.closed (post (graphDim T))
    _ _ _ _ time h hr
  exact ⟨t, by simpa only [post_prefix, samplerProg] using ht⟩

theorem samplerProg_dimension (n : ℕ) :
    ∃ time, (samplerProg E S).Runs (encode (n, Sampler.Query.dimension))
      (encode (graphDim T + S.dim n)) time := by
  obtain ⟨time, hr⟩ := S.runs_dimension n
  obtain ⟨t, ht⟩ := Prog.routeOneCall_indirect (route E) S.closed (post (graphDim T))
    _ _ _ _ time (route_dimension E n) hr
  exact ⟨t, by simpa only [post_dimension, Nat.add_comm, samplerProg] using ht⟩

theorem samplerProg_marginal (hℓ : 0 < ℓ) (n : ℕ) (w : Player) (j : ℕ) (z : BitStr)
    (hj : 1 ≤ j) (hj' : j ≤ ℓ + 2) (hz : z.length = graphDim T + S.dim n) :
    ∃ time, (samplerProg E S).Runs (encode (n, Sampler.Query.marginal w j z))
      (encode (toBits (((numbered E w (S.cl n w)).truncate j).eval
        (ofBits (graphDim T + S.dim n) z)))) time := by
  by_cases he : j ≤ 2
  · rw [numbered_marginal_graph E w _ j he z hz, graphOfBits_take_eq]
    apply run_direct E S
    rw [route_marginal_early E n w j z hj he, pad_content false z hz]
  · obtain ⟨r, rfl⟩ : ∃ r, j = r + 2 := ⟨j - 2, by omega⟩
    rw [numbered_marginal_content E w _ (S.cl_exactlyOn n w) hℓ r z hz, graphOfBits_take_eq]
    have hroute := route_marginal_late E n w (r + 2) z (by omega)
    cases ht : select E w.toBool (graphOfBits z) with
    | none =>
      simp only [selected, CLFun.eval_truncate_zeroOn, toBits_zero]
      apply run_direct E S
      simpa only [ht, pad_content false z hz] using hroute
    | some t =>
      simp only [selected]
      obtain ⟨time, hr⟩ := S.runs_marginal n w t r (content (graphDim T) z)
        (by omega) (by omega) (content_length z hz)
      exact run_call E S n _ _ _ _ time (by simpa only [ht, Nat.add_sub_cancel] using hroute) hr

theorem samplerProg_linear (hℓ : 0 < ℓ) (n : ℕ) (w : Player) (j : ℕ) (u y : BitStr)
    (hj : 1 ≤ j) (hj' : j ≤ ℓ + 2)
    (hu : ∃ x, u = toBits (((numbered E w (S.cl n w)).truncate (j - 1)).eval x))
    (hy : y.length = graphDim T + S.dim n) :
    ∃ time, (samplerProg E S).Runs (encode (n, Sampler.Query.linear w j u y))
      (encode (toBits ((numbered E w (S.cl n w)).mapOfPrefix (j - 1)
        (ofBits (graphDim T + S.dim n) u) (ofBits (graphDim T + S.dim n) y)))) time := by
  have huLen : u.length = graphDim T + S.dim n := by
    obtain ⟨x, rfl⟩ := hu
    exact length_toBits _
  by_cases he : j ≤ 2
  · rw [numbered_linear_graph E w _ (j - 1) (by omega) u y huLen hy,
      graphOfBits_take_eq, graphOfBits_take_eq]
    apply run_direct E S
    rw [route_linear_early E n w j u y hj he, pad_content false y hy]
  · obtain ⟨r, rfl⟩ : ∃ r, j = r + 3 := ⟨j - 3, by omega⟩
    have hi : r + 3 - 1 = r + 2 := by omega
    have hi' : r + 3 - 2 = r + 1 := by omega
    rw [hi, numbered_linear_content E w _ r u y huLen hy, graphOfBits_take_eq]
    have hroute := route_linear_late E n w (r + 3) u y (by omega)
    cases ht : select E w.toBool (graphOfBits u) with
    | none =>
      simp only [selected, CLFun.mapOfPrefix_zeroOn, LinearMap.zero_apply, toBits_zero]
      apply run_direct E S
      simpa only [ht, pad_content false y hy] using hroute
    | some t =>
      simp only [selected]
      have hp := numbered_selected_prefix E w (S.cl n w) (S.cl_exactlyOn n w) hℓ
        (r + 1) (by omega) u ((show r + 3 - 1 = r + 1 + 1 by omega) ▸ hu)
        (by simpa only [graphOfBits_take_eq] using ht)
      obtain ⟨time, hr⟩ := S.runs_linear n w t (r + 1)
        (content (graphDim T) u) (content (graphDim T) y) (by omega) (by omega)
        hp (content_length y hy)
      simpa only [Nat.add_sub_cancel, content] using
        run_call E S n _ _ _ _ time (by simpa only [ht, hi'] using hroute) hr

theorem samplerProg_factor (hℓ : 0 < ℓ) (n : ℕ) (w : Player) (j : ℕ) (u : BitStr)
    (hj : 1 ≤ j) (hj' : j ≤ ℓ + 2)
    (hu : ∃ x, u = toBits (((numbered E w (S.cl n w)).truncate (j - 1)).eval x)) :
    ∃ time, (samplerProg E S).Runs (encode (n, Sampler.Query.factor w j u))
      (encode (indicatorBits ((numbered E w (S.cl n w)).factorOfPrefix (j - 1)
        (ofBits (graphDim T + S.dim n) u)))) time := by
  have huLen : u.length = graphDim T + S.dim n := by
    obtain ⟨x, rfl⟩ := hu
    exact length_toBits _
  by_cases he : j ≤ 2
  · rw [numbered_factor_graph E w _ (j - 1) (by omega) u huLen, graphOfBits_take_eq]
    apply run_direct E S
    rw [route_factor_early E n w j u hj he, pad_content false u huLen]
  · obtain ⟨r, rfl⟩ : ∃ r, j = r + 3 := ⟨j - 3, by omega⟩
    have hi : r + 3 - 1 = r + 2 := by omega
    have hi' : r + 3 - 2 = r + 1 := by omega
    rw [hi, numbered_factor_content E w _ r u huLen, graphOfBits_take_eq]
    have hroute := route_factor_late E n w (r + 3) u (by omega)
    cases ht : select E w.toBool (graphOfBits u) with
    | none =>
      simp only [ht] at hroute
      rw [pad_content _ u huLen] at hroute
      have hℓ' : ℓ ≠ 0 := by omega
      cases r with
      | zero =>
        simpa [ht, selected, CLFun.factorOfPrefix_zeroOn, hℓ', indicatorBits] using
          run_direct E S n _ _ hroute
      | succ r =>
        simpa [ht, selected, CLFun.factorOfPrefix_zeroOn, hℓ', indicatorBits] using
          run_direct E S n _ _ hroute
    | some t =>
      simp only [selected]
      have hp := numbered_selected_prefix E w (S.cl n w) (S.cl_exactlyOn n w) hℓ
        (r + 1) (by omega) u ((show r + 3 - 1 = r + 1 + 1 by omega) ▸ hu)
        (by simpa only [graphOfBits_take_eq] using ht)
      obtain ⟨time, hr⟩ := S.runs_factor n w t (r + 1) (content (graphDim T) u)
        (by omega) (by omega) hp
      simpa only [Nat.add_sub_cancel, content] using
        run_call E S n _ _ _ _ time (by simpa only [ht, hi'] using hroute) hr

/-- Detyping as a genuine ambient sampler, with two additional CL levels. -/
def sampler (hℓ : 0 < ℓ) : Sampler (ℓ + 2) where
  prog := samplerProg E S
  closed := samplerProg_closed E S
  dim n := graphDim T + S.dim n
  cl n w := numbered E w (S.cl n w)
  cl_exactlyOn n w := numbered_exactlyOn E w _ (S.cl_exactlyOn n w) hℓ
  runs_dimension := samplerProg_dimension E S
  runs_marginal := samplerProg_marginal E S hℓ
  runs_linear := samplerProg_linear E S hℓ
  runs_factor := samplerProg_factor E S hℓ
  halts := samplerProg_halts E S

end MIPRE.CL.Detyping


