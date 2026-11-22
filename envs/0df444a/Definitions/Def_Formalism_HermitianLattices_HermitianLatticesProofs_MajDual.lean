-- Prove2me | Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajDual
-- name    : Formalism_HermitianLattices_HermitianLatticesProofs_MajDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:44.190815+00:00
-- url     : https://prove2.me/theorems/c3fe18cd-d011-4879-bb83-81450b89f3bf
-- title:
--   Maj Dual
-- statement:
--   Definitions and structural lemmas for Maj Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajDual.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
namespace Formalism.HermitianLatticesTheory
section
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
lemma majDual_jW_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) p :
    jW h b X w p = sgnAt h b X p.1 p.2.1 * w p := rfl
end
section
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
end
section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
abbrev majDualI (K : Type) [Field K] [NumberField K] :
    FractionalIdeal (RingOfIntegers K)⁰ K :=
  FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (RingOfIntegers K)⁰ K)
end
section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
end
section
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
def majDualJ (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) :
    EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) where
  toFun := jW h b X
  map_add' := by
    intro u w; ext p; simp only [majDual_jW_apply, PiLp.add_apply]; ring
  map_smul' := by
    intro c u; ext p; simp only [majDual_jW_apply, PiLp.smul_apply, smul_eq_mul,
      RingHom.id_apply]; ring
variable [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
end
end Formalism.HermitianLatticesTheory


