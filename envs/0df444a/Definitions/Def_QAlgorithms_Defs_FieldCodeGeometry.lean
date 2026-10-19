-- Prove2me | Definitions.Def_QAlgorithms_Defs_FieldCodeGeometry
-- name    : QAlgorithms_Defs_FieldCodeGeometry
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:17:58.681162+00:00
-- url     : https://prove2.me/theorems/6303b784-5531-4f53-982e-5f067ee125f1
-- title:
--   FieldCodeGeometry
-- statement:
--   FieldCodeGeometry
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\FieldCodeGeometry.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.FieldCodes

/-- Matrix-specified code ker H; 0903.0566 p.4, 1504.00822 p.4, 2610.02145 p.9. -/
def parityCheckCode {F R I : Type*} [Field F] [Fintype I]
    (H : Matrix R I F) : Submodule F (I → F) :=
  LinearMap.ker H.mulVecLin

/-- Constructed dual of an encoder image, ker Bᵀ; 2607.28120 p.2 (1), 2605.10666 pp.5–6. -/
def dualOfEncoder {F R I : Type*} [Field F] [Fintype R]
    (B : Matrix R I F) : Submodule F (R → F) :=
  parityCheckCode B.transpose

/-- Nonzero-word minimum, infinity for the zero code; 2607.28120 pp.2,17;
2610.02145 pp.9–11. A tuple is one coordinate. -/
def minimumDistance {F V I : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype I] (C : Submodule F (I → V)) : ℕ∞ :=
  ⨅ x ∈ C, ⨅ (_ : x ≠ 0), (hammingNorm x : ℕ∞)

/-- Ordinary bilinear field dual; 2607.16541 p.9, 2607.14650 p.19, 2610.02145 p.9. -/
def dual {F I : Type*} [Field F] [Fintype I]
    (C : Submodule F (I → F)) : Submodule F (I → F) where
  carrier := {y | ∀ x ∈ C, x ⬝ᵥ y = 0}
  add_mem' := by
    intro x y hx hy c hc
    rw [dotProduct_add, hx c hc, hy c hc, add_zero]
  zero_mem' := by intro c _; exact dotProduct_zero c
  smul_mem' := by
    intro a x hx c hc
    rw [dotProduct_smul, hx c hc, smul_zero]

/-- Actual row span, including redundant rows; 1504.00822 pp.2,6, 2306.12470 p.6. -/
def rowSpace {F R I : Type*} [Field F] (H : Matrix R I F) : Submodule F (I → F) :=
  Submodule.span F (Set.range H)

example {F R I : Type*} [Field F] [Fintype I] (H : Matrix R I F) (x : I → F) :
    x ∈ parityCheckCode H ↔ H.mulVec x = 0 := Iff.rfl

example {F V I : Type*} [Field F] [AddCommGroup V] [Module F V] [Fintype I] :
    minimumDistance (⊥ : Submodule F (I → V)) = ⊤ := by simp [minimumDistance]

example {F : Type*} [Field F] [Fintype F] :
    minimumDistance (⊤ : Submodule F (Fin 0 → F)) = ⊤ := by
  have : (⊤ : Submodule F (Fin 0 → F)) = ⊥ := Subsingleton.elim _ _
  rw [this]
  simp [minimumDistance]


end QAlgorithms.FieldCodes


