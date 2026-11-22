-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandDA
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandDA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:53.000894+00:00
-- url     : https://prove2.me/theorems/3ac95591-66bb-4ea0-a38b-f22fc7473c4e
-- title:
--   Mass Land DA
-- statement:
--   Definitions and structural lemmas for Mass Land DA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandDA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Polynomial
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.QuadAdj
variable {F : Type*} [Field F] (c : F)
theorem monic_pol : (X ^ 2 - C c : F[X]).Monic := monic_X_pow_sub_C c two_ne_zero
theorem natDegree_pol : (X ^ 2 - C c : F[X]).natDegree = 2 := natDegree_X_pow_sub_C
theorem root_mul_root :
    AdjoinRoot.root (X ^ 2 - C c) * AdjoinRoot.root (X ^ 2 - C c) = AdjoinRoot.of (X ^ 2 - C c) c := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C c)
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  linear_combination h
instance finite_adj : Module.Finite F (AdjoinRoot (X ^ 2 - C c)) := (monic_pol c).finite_adjoinRoot
theorem finrank_adj : finrank F (AdjoinRoot (X ^ 2 - C c)) = 2 := by
  rw [(AdjoinRoot.powerBasis' (monic_pol c)).finrank, AdjoinRoot.powerBasis'_dim, natDegree_pol]
def conjHom : AdjoinRoot (X ^ 2 - C c) →ₐ[F] AdjoinRoot (X ^ 2 - C c) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId F _) (-AdjoinRoot.root _) (by
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    have h := root_mul_root c
    show (-AdjoinRoot.root _) ^ 2 - AdjoinRoot.of _ c = 0
    linear_combination h)
theorem conjHom_root : conjHom c (AdjoinRoot.root _) = -AdjoinRoot.root _ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _
def conj : AdjoinRoot (X ^ 2 - C c) ≃ₐ[F] AdjoinRoot (X ^ 2 - C c) :=
  AlgEquiv.ofAlgHom (conjHom c) (conjHom c)
    (AdjoinRoot.algHom_ext (by
      rw [AlgHom.comp_apply, conjHom_root, map_neg, conjHom_root, neg_neg, AlgHom.id_apply]))
    (AdjoinRoot.algHom_ext (by
      rw [AlgHom.comp_apply, conjHom_root, map_neg, conjHom_root, neg_neg, AlgHom.id_apply]))
section
variable [Fact (Irreducible (X ^ 2 - C c : F[X]))]
variable [CharZero F]
instance isGalois_adj : IsGalois F (AdjoinRoot (X ^ 2 - C c)) := by
  have : Algebra.IsQuadraticExtension F (AdjoinRoot (X ^ 2 - C c)) := ⟨finrank_adj c⟩
  infer_instance
end
end Formalism.HermitianLattices.Ext.L3.QuadAdj


