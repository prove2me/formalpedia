-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
-- name    : LIDT_MIPStarRE_LDT_Basic_DiagonalLine
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:47:51.090555+00:00
-- url     : https://prove2.me/theorems/2ed7cfe4-2c08-4fdd-9a33-7a328bf78852
-- title:
--   LIDT definitions: LDT / Basic / DiagonalLine
-- statement:
--   This bundle sets up affine diagonal lines in the finite-field point space. It provides canonical representatives, direction normalization, rebasing, and successor-slice embedding.
--
--   Principal definitions:
--   - `DiagonalLine`: a line represented by a base point and direction vector.
--   - `pointAt`: evaluates the affine parameterization.
--   - `nonzeroDirectionSupport`: records the nonzero coordinates of a direction.
--   - `firstNonzeroCoord?`: selects the least supported coordinate when one exists.
--   - `normalizeDirection`: scales a nonzero direction so its first supported coordinate is one.
--   - `throughPointDirection`: constructs the canonical line through a point and direction.
--   - `sampleParameter`: returns the canonical parameter of the point.
--   - `rebaseAt`: changes the base point to a selected point on the line.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/DiagonalLine.lean#L20-L191

-- Generated from MIPStarRE/LDT/Basic/DiagonalLine.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Mathlib

namespace LIDT

/-!
# Diagonal lines for the low individual degree test

Diagonal-line geometry and rebasing operations.

## References

- `references/ldt-paper/test_definition.tex`
- `blueprint/src/chapter/ch02_test.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT

/-- A genuinely affine diagonal line in `F_q^m`. -/
structure DiagonalLine (params : Parameters) where
  base : Point params
  direction : Point params

deriving instance DecidableEq, Inhabited for DiagonalLine

namespace DiagonalLine

/-- The canonical affine parameterization `t ↦ base + t · direction`. -/
def pointAt {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) : Fq params → Point params :=
  fun t => addPoint ℓ.base (smulPoint t ℓ.direction)

/-- The support of the nonzero coordinates of a direction vector. -/
noncomputable def nonzeroDirectionSupport {params : Parameters} [FieldModel params.q]
    (v : Point params) : Finset (Fin params.m) :=
  Finset.univ.filter fun i => v i ≠ zeroCoord

/-- The least nonzero coordinate of a direction vector, when one exists. -/
noncomputable def firstNonzeroCoord? {params : Parameters} [FieldModel params.q]
    (v : Point params) : Option (Fin params.m) :=
  open Classical in
  let s := nonzeroDirectionSupport (params := params) v
  if hs : s.Nonempty then some (s.min' hs) else none

/-- Normalize a direction vector so its first nonzero coordinate becomes `1`. -/
noncomputable def normalizeDirection {params : Parameters} [FieldModel params.q]
    (v : Point params) : Point params :=
  open Classical in
  match firstNonzeroCoord? (params := params) v with
    | none => zeroPoint
    | some i => smulPoint (invCoord (v i)) v

/-- Canonical geometric diagonal line through `u` in direction `v`.

For nonzero `v`, we normalize by the first nonzero coordinate and shift the
base point so that this pivot coordinate is `0`. The degenerate `v = 0` case is
kept as the singleton line through `u`. -/
noncomputable def throughPointDirection {params : Parameters} [FieldModel params.q]
    (u v : Point params) : DiagonalLine params :=
  open Classical in
  match firstNonzeroCoord? (params := params) v with
    | none => { base := u, direction := zeroPoint }
    | some i =>
        let w := normalizeDirection (params := params) v
        let t := u i
        { base := fun j => subCoord (u j) (mulCoord t (w j))
          direction := w }

/-- Affine parameter of the sampled point on the canonical diagonal line through
`u` in direction `v`. -/
noncomputable def sampleParameter {params : Parameters} [FieldModel params.q]
    (u v : Point params) : Fq params :=
  open Classical in
  match firstNonzeroCoord? (params := params) v with
    | none => zeroCoord
    | some i => u i

@[simp] theorem throughPoint_pointAt_sampleParameter {params : Parameters}
    [FieldModel params.q] (u : Point params) (i : Fin params.m) :
    (AxisParallelLine.throughPoint (params := params) u i).pointAt
        (AxisParallelLine.sampleParameter (params := params) u i) = u := by
  funext j
  by_cases h : j = i
  · subst h
    unfold AxisParallelLine.pointAt AxisParallelLine.throughPoint
    simp [AxisParallelLine.sampleParameter, addCoord, zeroCoord]
  · simp [AxisParallelLine.throughPoint, AxisParallelLine.pointAt, h]

@[simp] theorem throughPointDirection_pointAt_sampleParameter {params : Parameters}
    [FieldModel params.q] (u v : Point params) :
    (DiagonalLine.throughPointDirection (params := params) u v).pointAt
        (DiagonalLine.sampleParameter (params := params) u v) = u := by
  classical
  unfold DiagonalLine.throughPointDirection DiagonalLine.sampleParameter
  split
  · funext j
    simp [DiagonalLine.pointAt, addPoint, smulPoint, zeroPoint,
      zeroCoord, addCoord, mulCoord]
  · rename_i i
    funext j
    simp [DiagonalLine.pointAt, addPoint, smulPoint, subCoord, addCoord, mulCoord]

/-- Rebase a diagonal line so that the old point `ℓ.pointAt t` becomes the new base point. -/
def rebaseAt {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t : Fq params) : DiagonalLine params where
  base := ℓ.pointAt t
  direction := ℓ.direction

@[simp] theorem rebaseAt_pointAt_zero {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t : Fq params) :
    (rebaseAt ℓ t).pointAt zeroCoord = ℓ.pointAt t := by
  ext i
  simp [rebaseAt, pointAt, addPoint, smulPoint, addCoord, mulCoord, zeroCoord]

theorem rebaseAt_pointAt {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t s : Fq params) :
    (rebaseAt ℓ t).pointAt s = ℓ.pointAt (addCoord t s) := by
  ext i
  simp only [pointAt, addPoint, addCoord, rebaseAt, smulPoint, mulCoord, decode_encodeScalar]
  rw [← encode_decodeScalar (ℓ.base i)]
  congr 1
  ring_nf

@[simp] theorem rebaseAt_zero {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) :
    rebaseAt ℓ zeroCoord = ℓ := by
  cases ℓ with
  | mk base direction =>
      change
        ({ base :=
             ({ base := base, direction := direction } : DiagonalLine params).pointAt zeroCoord,
           direction := direction } : DiagonalLine params) =
        ({ base := base, direction := direction } : DiagonalLine params)
      congr
      funext i
      simp [pointAt, addPoint, smulPoint, addCoord, mulCoord, zeroCoord]

theorem rebaseAt_rebase {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t s : Fq params) :
    rebaseAt (rebaseAt ℓ t) s = rebaseAt ℓ (addCoord t s) := by
  cases ℓ with
  | mk base direction =>
      change
        ({ base :=
             (rebaseAt
               ({ base := base, direction := direction } : DiagonalLine params) t).pointAt s,
           direction := direction } : DiagonalLine params) =
        ({ base :=
             ({ base := base, direction := direction } : DiagonalLine params).pointAt
               (addCoord t s),
           direction := direction } : DiagonalLine params)
      exact congrArg
        (fun b => ({ base := b, direction := direction } : DiagonalLine params))
        (rebaseAt_pointAt { base := base, direction := direction } t s)

/-- Embed a diagonal line into the slice at height `x`, keeping the new coordinate fixed. -/
def appendAtHeight (params : Parameters) [FieldModel params.q]
    (ℓ : DiagonalLine params) (x : Fq params) : DiagonalLine params.next where
  base := appendPoint params ℓ.base x
  direction := appendPoint params ℓ.direction zeroCoord

@[simp] theorem appendAtHeight_rebaseAt {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t x : Fq params) :
    appendAtHeight params (rebaseAt ℓ t) x =
      rebaseAt (appendAtHeight params ℓ x) t := by
  cases ℓ with
  | mk base direction =>
      change
        ({ base := appendPoint params (addPoint base (smulPoint t direction)) x,
           direction := appendPoint params direction zeroCoord } : DiagonalLine params.next) =
        ({ base := addPoint (appendPoint params base x)
             (smulPoint t (appendPoint params direction zeroCoord)),
           direction := appendPoint params direction zeroCoord } : DiagonalLine params.next)
      congr
      funext i
      by_cases hi : i.1 < params.m
      · simp only [appendPoint, addPoint, smulPoint, addCoord, mulCoord, hi, ↓reduceDIte]
        rfl
      · simp only [appendPoint, hi, ↓reduceDIte, addPoint, addCoord, smulPoint, mulCoord,
          zeroCoord, decode_encodeScalar]
        rw [← encode_decodeScalar x]
        congr 1
        calc
          decodeScalar x = decodeScalar x + decodeScalar t * (0 : Scalar params) := by ring
          _ = decodeScalar (encodeScalar (decodeScalar x)) +
                decodeScalar t * decodeScalar (encodeScalar 0) := by
              rw [show decodeScalar (encodeScalar (decodeScalar x)) = decodeScalar x from
                  decode_encodeScalar (decodeScalar x),
                show decodeScalar (encodeScalar (0 : Scalar params)) = (0 : Scalar params) from
                  decode_encodeScalar (0 : Scalar params)]

end DiagonalLine

end MIPStarRE.LDT

end

end LIDT


