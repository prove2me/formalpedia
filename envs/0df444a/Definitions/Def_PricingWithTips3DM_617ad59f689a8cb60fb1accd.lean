-- Prove2me | Definitions.Def_PricingWithTips3DM_617ad59f689a8cb60fb1accd
-- name    : PricingWithTips3DM_617ad59f689a8cb60fb1accd
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T06:49:29.567897+00:00
-- url     : https://prove2.me/theorems/b8dc321e-cfe0-444b-a660-33411f8f396f
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.QueryNormalizer.Runtime
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_595ff4c6c4b40a2ae697a626
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Query normalization: polynomial runtime

The fixed controller has linear cost in the serialized query stream.  After
the shared reversal pass, it computes the semantic map that puts every
undirected edge into increasing endpoint order.
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer

open PolyBuilder

/-- Normalizing one unary edge record costs at most ten times its physical
encoding length. -/
theorem rowSteps_le_encoding (edge : Nat × Nat) :
    rowSteps edge ≤ 10 * (encodeCliqueEdge edge).length := by
  rcases edge with ⟨left, right⟩
  simp only [rowSteps, encodeCliqueEdge_length]
  have hmin : Nat.min left right ≤ left + right :=
    (Nat.min_le_left left right).trans (Nat.le_add_right left right)
  omega

/-- Accumulated row cost is linear in the complete canonical query stream. -/
theorem rowsSteps_le_encoding (edges : List (Nat × Nat)) :
    rowsSteps edges ≤ 10 * (edges.flatMap encodeCliqueEdge).length := by
  induction edges with
  | nil => simp [rowsSteps]
  | cons edge edges ih =>
      have hrow := rowSteps_le_encoding edge
      have hsteps : rowsSteps (edge :: edges) =
          rowSteps edge + rowsSteps edges := by
        simp [rowsSteps]
      rw [hsteps, List.flatMap_cons, List.length_append]
      omega

/-- The reverse-output run, including final control transitions, has a fixed
linear upper envelope in the input length. -/
theorem revSteps_le_input (edges : List (Nat × Nat)) :
    revSteps edges ≤ 12 * ((edges.flatMap encodeCliqueEdge).length + 1) := by
  have hrows := rowsSteps_le_encoding edges
  simp only [revSteps]
  omega

/-- Compiled reverse-output query normalizer. -/
noncomputable def rev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge) id
      (fun edges => (encodeNormalizedQueries edges).reverse) where
  tm := compile revProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 12 * (Polynomial.X + 1)
  outputsFun := fun edges => by
    have builderRun := revRun edges
    have compiledRun := compile_evalsToInTime revProgram builderRun
    have machineRun : EvalsToInTime
        (compile revProgram).step
        (_root_.Turing.initList (compile revProgram)
          (edges.flatMap encodeCliqueEdge))
        (some (_root_.Turing.haltList (compile revProgram)
          (encodeNormalizedQueries edges).reverse))
        (revSteps edges) := by
      convert compiledRun using 1 <;>
        simp only [encodeCfg_initialCfg, encodeCfg_haltCfg] <;> rfl
    have htime := revSteps_le_input edges
    have polynomialBound : revSteps edges ≤
        (12 * (Polynomial.X + 1)).eval
          (edges.flatMap encodeCliqueEdge).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_one,
        Polynomial.eval_ofNat] using htime
    have boundedRun : EvalsToInTime
        (compile revProgram).step
        (_root_.Turing.initList (compile revProgram)
          (edges.flatMap encodeCliqueEdge))
        (some (_root_.Turing.haltList (compile revProgram)
          (encodeNormalizedQueries edges).reverse))
        ((12 * (Polynomial.X + 1)).eval
          (edges.flatMap encodeCliqueEdge).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans polynomialBound⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward-order serialization obtained by composing with the reusable
reversal controller. -/
noncomputable def queries_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge) id
      encodeNormalizedQueries := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      rev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := CliqueSym))
  simpa [Function.comp_def] using Classical.choice composed

/-- The physical output of the controller is precisely the canonical encoder
applied to the semantic list of normalized edges. -/
theorem encodeNormalizedQueries_eq_map (edges : List (Nat × Nat)) :
    encodeNormalizedQueries edges =
      (edges.map normalizeQuery).flatMap encodeCliqueEdge := by
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
      simp [encodeNormalizedQueries, Function.comp_def,
        encodeNormalizedQueries] at ih ⊢
      exact ih

/-- Polynomial-time computability exposed at the semantic list boundary. -/
noncomputable def normalizer_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge)
      (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge)
      (List.map normalizeQuery) := by
  let queries := queries_computableInPolyTime
  exact
    { tm := queries.tm
      inputAlphabet := queries.inputAlphabet
      outputAlphabet := queries.outputAlphabet
      time := queries.time
      outputsFun := fun edges => by
        simpa [encodeNormalizedQueries_eq_map] using queries.outputsFun edges }

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer


