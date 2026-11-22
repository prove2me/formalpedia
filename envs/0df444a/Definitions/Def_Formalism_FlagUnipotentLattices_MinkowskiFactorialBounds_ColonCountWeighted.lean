-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:50.371543+00:00
-- url     : https://prove2.me/theorems/f3e2b22b-b8ef-4994-aa6e-25d7f2efa91e
-- title:
--   Colon Count Weighted
-- statement:
--   Definitions and structural lemmas for Colon Count Weighted, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
namespace Formalism.HermitianLatticeCounting.P
namespace DualLatticeIndexBis
end DualLatticeIndexBis
namespace DualLatticeIndexBis
end DualLatticeIndexBis
namespace DualLatticeIndexBis
end DualLatticeIndexBis
namespace DualLatticeIndexBis
end DualLatticeIndexBis
namespace DualLatticeIndexBis
end DualLatticeIndexBis
namespace DualLatticeIndexBis
end DualLatticeIndexBis
namespace DualLatticeIndexBis
end DualLatticeIndexBis
namespace DualLatticeIndexBis
section Dual
variable {E U : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup U] [Module E U]
  [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U] [Module ℚ U] [IsScalarTower ℚ E U]
noncomputable def trForm (h : U →ₗ[E] U →ₗ⋆[E] E) : U →ₗ[ℚ] U →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ E (h x y))
    (fun x x' y => by simp only [map_add, LinearMap.add_apply])
    (fun q x y => by
      rw [← algebraMap_smul E q x, map_smul, LinearMap.smul_apply, smul_eq_mul, ← Algebra.smul_def, map_smul])
    (fun x y y' => by simp only [map_add])
    (fun q x y => by
      rw [← algebraMap_smul E q y, LinearMap.map_smulₛₗ, RingHom.map_rat_algebraMap, smul_eq_mul,
        ← Algebra.smul_def, map_smul])
end Dual
end DualLatticeIndexBis
end Formalism.HermitianLatticeCounting.P


