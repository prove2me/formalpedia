-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_FactorOneOfDiscrete
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_FactorOneOfDiscrete
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:18:57.411965+00:00
-- url     : https://prove2.me/theorems/8247995f-fa33-4628-b7ad-66bac8319cc2
-- title:
--   Factor One Of Discrete
-- statement:
--   Definitions and structural lemmas for Factor One Of Discrete, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/FactorOneOfDiscrete.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeNGLQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiscreteHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal
namespace PI.NglqJacSplitW
section Mod
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  [LocallyCompactSpace F]
end Mod
def rmul {E : Type} [CommRing E] (n m : ℕ) (A : Matrix (Fin m) (Fin m) E) :
    Matrix (Fin n) (Fin m) E →ₗ[E] Matrix (Fin n) (Fin m) E where
  toFun X := X * A
  map_add' X Y := Matrix.add_mul X Y A
  map_smul' c X := Matrix.smul_mul c X A
def lmulM {E : Type} [CommRing E] (m : ℕ) (B : Matrix (Fin m) (Fin m) E) :
    Matrix (Fin m) (Fin m) E →ₗ[E] Matrix (Fin m) (Fin m) E where
  toFun H := B * H
  map_add' X Y := Matrix.mul_add B X Y
  map_smul' c X := Matrix.mul_smul B c X
def pairEquiv (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] (n m : ℕ) :
    (Matrix (Fin n) (Fin m) F × Matrix (Fin n) (Fin m) F) ≃L[F]
      ((Fin n × Fin m) ⊕ (Fin n × Fin m) → F) where
  toFun X i := Sum.elim (fun p => X.1 p.1 p.2) (fun p => X.2 p.1 p.2) i
  invFun v := (Matrix.of fun a b => v (Sum.inl (a, b)), Matrix.of fun a b => v (Sum.inr (a, b)))
  map_add' X Y := by ext i; rcases i with p | p <;> rfl
  map_smul' c X := by ext i; rcases i with p | p <;> rfl
  left_inv X := by ext <;> rfl
  right_inv v := by ext i; rcases i with p | p <;> rfl
  continuous_toFun := by
    refine continuous_pi fun i => ?_
    rcases i with p | p
    · exact (continuous_fst.matrix_elem p.1 p.2)
    · exact (continuous_snd.matrix_elem p.1 p.2)
  continuous_invFun := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_pi fun a => continuous_pi fun b => continuous_apply (Sum.inl (a, b))
    · exact continuous_pi fun a => continuous_pi fun b => continuous_apply (Sum.inr (a, b))
def sqEquiv (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] (m : ℕ) :
    Matrix (Fin m) (Fin m) F ≃L[F] (Fin m × Fin m → F) where
  toFun X p := X p.1 p.2
  invFun v := Matrix.of fun a b => v (a, b)
  map_add' X Y := rfl
  map_smul' c X := rfl
  left_inv X := rfl
  right_inv v := rfl
  continuous_toFun := continuous_pi fun p => continuous_id.matrix_elem p.1 p.2
  continuous_invFun := continuous_pi fun a => continuous_pi fun b => continuous_apply (a, b)
end PI.NglqJacSplitW


