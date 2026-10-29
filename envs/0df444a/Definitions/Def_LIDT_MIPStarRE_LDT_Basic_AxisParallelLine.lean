-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
-- name    : LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:46:57.062172+00:00
-- url     : https://prove2.me/theorems/34ec2728-bf2f-440e-b3c4-75384ce561cf
-- title:
--   LIDT definitions: LDT / Basic / AxisParallelLine
-- statement:
--   This bundle sets up affine axis-parallel lines in the finite-field point space. It provides the canonical line through a sampled point, rebasing operations, and the embedding of a line into a successor slice used by axis tests and induction.
--
--   Principal definitions:
--   - `AxisParallelLine`: A line is a base point in $\mathbb{F}_q^m$ together with a coordinate direction.
--   - `pointAt`: Evaluates the line at $t$ by adding $t$ in its selected coordinate and leaving the other coordinates fixed.
--   - `throughPoint`: Chooses the canonical representative of the axis-parallel line through $u$ in direction $i$, with zero in the moving coordinate.
--   - `sampleParameter`: The parameter of $u$ on the canonical line in direction $i$, namely its $i$th coordinate.
--   - `rebaseAt`: Makes the point at parameter $t$ the new base while preserving the direction.
--   - `appendAtHeight`: Embeds a line in $\mathbb{F}_q^m$ into the height-$x$ slice of $\mathbb{F}_q^{m+1}$ and embeds its direction among the old coordinates.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/AxisParallelLine.lean#L22-L150

-- Generated from MIPStarRE/LDT/Basic/AxisParallelLine.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Mathlib

namespace LIDT

/-!
# Axis-parallel lines for the low individual degree test

Axis-parallel line geometry on top of the core parameter infrastructure:
`AxisParallelLine` records a base point and a coordinate direction, with
canonical parameterization, rebasing, and slice-embedding operations.

## References

- `references/ldt-paper/test_definition.tex`
- `blueprint/src/chapter/ch02_test.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT

/-- A genuinely axis-parallel affine line in `F_q^m`. -/
structure AxisParallelLine (params : Parameters) where
  base : Point params
  direction : Fin params.m

deriving instance DecidableEq, Inhabited for AxisParallelLine

namespace AxisParallelLine

/-- The canonical affine parameterization `t ↦ base + t e_i`. -/
def pointAt {params : Parameters} [FieldModel params.q]
    (ℓ : AxisParallelLine params) : Fq params → Point params :=
  fun t i =>
    if i = ℓ.direction then
      addCoord (ℓ.base i) t
    else
      ℓ.base i

/-- Canonical geometric axis-parallel line through `u` in direction `i`.

The representative stores zero in the moving coordinate, so all points on the
same geometric line map to the same `AxisParallelLine`. -/
def throughPoint {params : Parameters} [FieldModel params.q]
    (u : Point params) (i : Fin params.m) : AxisParallelLine params where
  base := fun j => if j = i then zeroCoord else u j
  direction := i

/-- Affine parameter of the sampled point on the canonical axis-parallel line
through `u` in direction `i`. -/
def sampleParameter {params : Parameters} [FieldModel params.q]
    (u : Point params) (i : Fin params.m) : Fq params :=
  u i

/-- Rebase an axis-parallel line so that the old point `ℓ.pointAt t`
becomes the new base point. -/
def rebaseAt {params : Parameters} [FieldModel params.q]
    (ℓ : AxisParallelLine params) (t : Fq params) : AxisParallelLine params where
  base := ℓ.pointAt t
  direction := ℓ.direction

@[simp] theorem rebaseAt_pointAt_zero {params : Parameters} [FieldModel params.q]
    (ℓ : AxisParallelLine params) (t : Fq params) :
    (rebaseAt ℓ t).pointAt zeroCoord = ℓ.pointAt t := by
  ext i
  simp [rebaseAt, pointAt, addCoord, zeroCoord]

@[simp] theorem rebaseAt_zero {params : Parameters} [FieldModel params.q]
    (ℓ : AxisParallelLine params) :
    rebaseAt ℓ zeroCoord = ℓ := by
  cases ℓ with
  | mk base direction =>
      change
        ({ base :=
             ({ base := base, direction := direction } : AxisParallelLine params).pointAt zeroCoord,
           direction := direction } : AxisParallelLine params) =
        ({ base := base, direction := direction } : AxisParallelLine params)
      congr
      funext i
      simp [pointAt, addCoord, zeroCoord]

@[simp] theorem rebaseAt_direction {params : Parameters} [FieldModel params.q]
    (ℓ : AxisParallelLine params) (t : Fq params) :
    (rebaseAt ℓ t).direction = ℓ.direction :=
  rfl

/-- The canonical affine parameterization of `throughPoint u i` at parameter
`sampleParameter u i = u i` returns the original point `u`. -/
@[simp] theorem throughPoint_pointAt_sampleParameter {params : Parameters}
    [FieldModel params.q] (u : Point params) (i : Fin params.m) :
    (throughPoint (params := params) u i).pointAt
        (sampleParameter (params := params) u i) = u := by
  ext j
  by_cases h : j = i
  · subst h
    simp [throughPoint, pointAt, sampleParameter, addCoord, zeroCoord]
  · simp [throughPoint, pointAt, h]

/-- Rebasing the canonical line `throughPoint u i` at its sample parameter yields
the axis-parallel line with base `u` and direction `i`. -/
@[simp] theorem rebaseAt_throughPoint_sampleParameter {params : Parameters}
    [FieldModel params.q] (u : Point params) (i : Fin params.m) :
    rebaseAt (throughPoint (params := params) u i)
        (sampleParameter (params := params) u i) =
      { base := u, direction := i } := by
  change
    ({ base :=
        (throughPoint (params := params) u i).pointAt
          (sampleParameter (params := params) u i)
       direction := i } : AxisParallelLine params) =
      { base := u, direction := i }
  congr
  exact throughPoint_pointAt_sampleParameter u i

/-- Embed an axis-parallel line into the slice at height `x`. -/
def appendAtHeight (params : Parameters)
    (ℓ : AxisParallelLine params) (x : Fq params) : AxisParallelLine params.next where
  base := appendPoint params ℓ.base x
  direction := embedCoord params ℓ.direction

@[simp] theorem appendAtHeight_rebaseAt {params : Parameters} [FieldModel params.q]
    (ℓ : AxisParallelLine params) (t x : Fq params) :
    appendAtHeight params (rebaseAt ℓ t) x =
      rebaseAt (appendAtHeight params ℓ x) t := by
  cases ℓ with
  | mk base direction =>
      change
        ({ base :=
             appendPoint params
               (({ base := base, direction := direction } : AxisParallelLine params).pointAt t) x,
           direction := embedCoord params direction } : AxisParallelLine params.next) =
        ({ base :=
             ({ base := appendPoint params base x,
                direction := embedCoord params direction } :
                AxisParallelLine params.next).pointAt t,
           direction := embedCoord params direction } : AxisParallelLine params.next)
      congr
      funext i
      by_cases hdir : i = embedCoord params direction
      · subst i
        simp [appendPoint, pointAt, embedCoord]
        rfl
      · by_cases hi : i.1 < params.m
        · have hdir' : (⟨i.1, hi⟩ : Fin params.m) ≠ direction := by
            intro h
            apply hdir
            apply Fin.ext
            simpa [embedCoord] using congrArg Fin.val h
          simp [appendPoint, pointAt, hi, hdir, hdir']
        · simp [appendPoint, pointAt, hi, hdir]

end AxisParallelLine

end MIPStarRE.LDT

end

end LIDT


