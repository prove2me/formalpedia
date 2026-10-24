-- Prove2me | Definitions.Def_PricingWithTips3DM_498bba7a490a84d9a63ab0be
-- name    : PricingWithTips3DM_498bba7a490a84d9a63ab0be
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:31:17.443749+00:00
-- url     : https://prove2.me/theorems/b96c4a99-a309-4f5e-9ff9-91f9b12fd6f7
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding.Length
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_324d2af57942969ab022525f
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Size bounds for general CLIQUE encodings

The exact encoder formula and the successful-decoder bound connect unary graph
fields to physical input length.  These facts feed certificate and machine
polynomial bounds.
-/

namespace CLRS
namespace Chapter34

/-- Total physical cost of a list of unary edge records. -/
def cliqueEdgesEncodingLength (edges : List (Nat × Nat)) : Nat :=
  (edges.map fun edge => edge.1 + edge.2 + 3).sum

/-- Flat-mapping the edge encoder has exactly the recorded aggregate cost. -/
theorem flatMap_encodeCliqueEdge_length (edges : List (Nat × Nat)) :
    (edges.flatMap encodeCliqueEdge).length = cliqueEdgesEncodingLength edges := by
  induction edges with
  | nil => simp [cliqueEdgesEncodingLength]
  | cons edge edges ih =>
      simp [cliqueEdgesEncodingLength, ih, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

/-- Exact physical length of the canonical graph-plus-{lit}`k` encoding. -/
theorem encodeCliqueInstance_length (I : CliqueInstance) :
    (encodeCliqueInstance I).length =
      I.vertexCount + I.targetSize + 3 + cliqueEdgesEncodingLength I.edges := by
  simp only [encodeCliqueInstance, List.length_cons, prependCliqueTicks_length]
  rw [flatMap_encodeCliqueEdge_length]
  omega

/-- Unary-prefix parsing partitions the input into its tick count and suffix. -/
theorem consumeCliqueTicks_length (input : List CliqueSym) :
    (consumeCliqueTicks input).1 + (consumeCliqueTicks input).2.length =
      input.length := by
  induction input with
  | nil => rfl
  | cons symbol rest ih =>
      cases symbol <;>
        simp only [consumeCliqueTicks, List.length_cons, Nat.zero_add]
      all_goals omega

/-- Successful instance parsing forces both unary header fields, plus the three
mandatory structural markers, to fit in the physical input. -/
theorem decodeCliqueInstance_fields_le_length {input : List CliqueSym}
    {I : CliqueInstance} (hdecode : decodeCliqueInstance input = some I) :
    I.vertexCount + I.targetSize + 3 ≤ input.length := by
  cases input with
  | nil => simp [decodeCliqueInstance] at hdecode
  | cons symbol rest =>
      cases symbol with
      | instanceMark =>
          generalize hvertex : consumeCliqueTicks rest = vertexField
          rcases vertexField with ⟨vertexCount, vertexSuffix⟩
          cases vertexSuffix with
          | nil => simp [decodeCliqueInstance, hvertex] at hdecode
          | cons separator afterVertices =>
              cases separator with
              | fieldSep =>
                  generalize htarget : consumeCliqueTicks afterVertices = targetField
                  rcases targetField with ⟨targetSize, targetSuffix⟩
                  cases targetSuffix with
                  | nil => simp [decodeCliqueInstance, hvertex, htarget] at hdecode
                  | cons separator edgeInput =>
                      cases separator with
                      | fieldSep =>
                          generalize hedge : decodeCliqueEdges edgeInput = edgeResult
                          cases edgeResult with
                          | none =>
                              simp [decodeCliqueInstance, hvertex, htarget, hedge] at hdecode
                          | some edges =>
                              simp [decodeCliqueInstance, hvertex, htarget, hedge] at hdecode
                              cases hdecode
                              have hv := consumeCliqueTicks_length rest
                              have ht := consumeCliqueTicks_length afterVertices
                              rw [hvertex] at hv
                              rw [htarget] at ht
                              simp only [List.length_cons] at hv ht ⊢
                              omega
                      | _ => simp [decodeCliqueInstance, hvertex, htarget] at hdecode
              | _ => simp [decodeCliqueInstance, hvertex] at hdecode
      | _ => simp [decodeCliqueInstance] at hdecode

end Chapter34
end CLRS


