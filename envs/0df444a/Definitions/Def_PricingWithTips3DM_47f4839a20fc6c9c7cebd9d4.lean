-- Prove2me | Definitions.Def_PricingWithTips3DM_47f4839a20fc6c9c7cebd9d4
-- name    : PricingWithTips3DM_47f4839a20fc6c9c7cebd9d4
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:45:26.379317+00:00
-- url     : https://prove2.me/theorems/a9f509f6-40fc-4332-882d-1589bddd2b34
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameValueMarkedRows
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_a379488bf4a9c826d3fac0e5
import Definitions.Def_PricingWithTips3DM_645fa74d60687a6229a5303d
import Definitions.Def_PricingWithTips3DM_c74718a616769e19e5aa2ff6
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Marked rows for individual unary values

Two aligned views are useful for pointwise unary addition.  A full row keeps
the value's ordinary separator; a tick-only row drops that separator.  Their
row-wise concatenation therefore represents addition without a bespoke
arithmetic controller.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

private theorem valueMarkedRows_encodeUnaryFrame_frameEnd_free
    (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  rw [encodeUnaryFrame, List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, _, hblock⟩
  simp [encodeUnaryFrameBlock] at hblock
  rcases hblock with ⟨_, rfl⟩ | rfl <;> decide

/-- One complete unary block, including its ordinary separator, per row. -/
def unaryFrameFullValueMarkedRows
    (values : List Nat) : UnaryFrameMarkedRowFamily :=
  { rows := values.map fun value => encodeUnaryFrame [value]
    frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨value, _, rfl⟩
      exact valueMarkedRows_encodeUnaryFrame_frameEnd_free _ symbol hsymbol }

/-- Only the unary ticks of one value per row. -/
def unaryFrameTickValueMarkedRows
    (values : List Nat) : UnaryFrameMarkedRowFamily :=
  { rows := values.map fun value => List.replicate value .tick
    frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨value, _, rfl⟩
      have : symbol = UnaryFrameSym.tick := by
        have hs : value ≠ 0 ∧ symbol = UnaryFrameSym.tick := by
          simpa only [List.mem_replicate] using hsymbol
        exact hs.2
      subst symbol
      decide }

@[simp] theorem unaryFrameFullValueMarkedRows_length (values : List Nat) :
    (unaryFrameFullValueMarkedRows values).rows.length = values.length := by
  simp [unaryFrameFullValueMarkedRows]

@[simp] theorem unaryFrameTickValueMarkedRows_length (values : List Nat) :
    (unaryFrameTickValueMarkedRows values).rows.length = values.length := by
  simp [unaryFrameTickValueMarkedRows]

/-- Marking every ordinary unary field yields the full-row encoding. -/
theorem markUnaryFrameSingleFieldRows_encode (values : List Nat) :
    markUnaryFrameFixedFieldRows 1 (encodeUnaryFrame values) =
      encodeUnaryFrameMarkedRowFamily
        (unaryFrameFullValueMarkedRows values) := by
  have hflatten :
      (values.map fun value => [value]).flatten = values := by
    induction values with
    | nil => rfl
    | cons value rest ih => simp [ih]
  have hmark := markUnaryFrameFixedFieldRows_encode 1 (by omega)
    (values.map fun value => [value]) (by
      intro row hrow
      rw [List.mem_map] at hrow
      rcases hrow with ⟨value, _, rfl⟩
      rfl)
  rw [hflatten] at hmark
  rw [hmark]
  unfold encodeUnaryFrameFixedFieldMarkedRows
    encodeUnaryFrameMarkedRowFamily
  dsimp only [unaryFrameFullValueMarkedRows]
  rw [List.flatMap_map, List.flatMap_map]

private theorem delimiterCycle_singleFrameEnd (values : List Nat) :
    encodeUnaryFrameWithDelimiterCycle [.frameEnd] (by simp) values =
      encodeUnaryFrameMarkedRowFamily
        (unaryFrameTickValueMarkedRows values) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [encodeUnaryFrameWithDelimiterCycle,
        encodeUnaryFrameWithDelimiterCycleFrom,
        encodeUnaryFrameMarkedRowFamily,
        unaryFrameTickValueMarkedRows, List.map_cons, List.flatMap_cons]
      rw [show unaryFrameDelimiterNext [.frameEnd] (by simp)
          ⟨0, by simp⟩ = ⟨0, by simp⟩ by apply Fin.ext; rfl]
      change List.replicate value .tick ++ [.frameEnd] ++
          encodeUnaryFrameWithDelimiterCycle [.frameEnd] (by simp) rest =
        (List.replicate value .tick ++ [.frameEnd]) ++
          (rest.map fun item => List.replicate item .tick).flatMap
            (fun row => row ++ [.frameEnd])
      rw [ih]
      rfl

/-- Replacing every ordinary separator by `frameEnd` yields tick-only rows. -/
theorem delimitUnaryFrameValuesAsTickRows (values : List Nat) :
    rewriteUnaryFrameDelimiters [.frameEnd] (by simp)
        (encodeUnaryFrame values) =
      encodeUnaryFrameMarkedRowFamily
        (unaryFrameTickValueMarkedRows values) := by
  rw [rewriteUnaryFrameDelimiters_encodeUnaryFrame]
  exact delimiterCycle_singleFrameEnd values

/-- Row-wise concatenation of tick-only addends with complete unary values is
pointwise natural-number addition. -/
theorem concatUnaryFrameTickFullRows_ofFn {count : Nat}
    (addend value : Fin count → Nat) :
    concatUnaryFrameMarkedRows
        (unaryFrameTickValueMarkedRows (List.ofFn addend)).rows
        (unaryFrameFullValueMarkedRows (List.ofFn value)).rows =
      List.ofFn fun index => encodeUnaryFrame [addend index + value index] := by
  change concatUnaryFrameMarkedRows
      ((List.ofFn addend).map fun item => List.replicate item .tick)
      ((List.ofFn value).map fun item => encodeUnaryFrame [item]) = _
  rw [List.map_ofFn, List.map_ofFn]
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
      simp only [concatUnaryFrameMarkedRows]
      congr 1
      · simp only [encodeUnaryFrame, encodeUnaryFrameBlock,
          List.flatMap_cons, List.flatMap_nil, List.append_nil]
        change List.replicate (addend 0) UnaryFrameSym.tick ++
            (List.replicate (value 0) UnaryFrameSym.tick ++
              [UnaryFrameSym.separator]) = _
        rw [← List.append_assoc, ← List.replicate_add]
      · exact ih (fun index => addend index.succ)
          (fun index => value index.succ)

end CLRS.Chapter34.Turing.PolyBuilder


