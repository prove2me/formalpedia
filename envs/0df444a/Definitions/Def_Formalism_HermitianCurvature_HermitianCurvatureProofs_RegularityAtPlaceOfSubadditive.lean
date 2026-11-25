-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularityAtPlaceOfSubadditive
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularityAtPlaceOfSubadditive
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:42:37.55997+00:00
-- url     : https://prove2.me/theorems/04441fde-9bb3-41f2-9838-eb78051cda45
-- title:
--   Regularity At Place Of Subadditive
-- statement:
--   Definitions and structural lemmas for Regularity At Place Of Subadditive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.TBBx4
open MeasureTheory Filter Topology Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB
open scoped ENNReal ComplexConjugate
noncomputable section
section hs
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
end hs
section place
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
end place
section norm
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
def fpm (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : B.Mat P.k P.r → (Wq →L[ℂ] Wq)) (p₀ : ℕ) :
    B.Mat P.k P.r → (Wq →L[ℂ] Wp) :=
  fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (A g)
end norm
section reg
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
end reg
section iter
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
def mulD (r : ℕ) : Module.End ℂ ((Fin (r + 1) → ℂ) → (Wq →L[ℂ] Wp)) where
  toFun x := fun c => (D.ptMatN (bigPt r c) (r + 1)).det • x c
  map_add' x y := by
    funext c
    simp [smul_add]
  map_smul' z x := by
    funext c
    simp only [Pi.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _
end iter
end
end Formalism.FourierDecayAlt.P.TBBx4
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants
end Formalism.FourierDecayAlt.P


