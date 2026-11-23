-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MeasurableSetBallSet
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MeasurableSetBallSet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:11.207898+00:00
-- url     : https://prove2.me/theorems/1ba5f753-9ff0-4271-bfc6-88c67179c723
-- title:
--   Measurable Set Ball Set
-- statement:
--   Definitions and structural lemmas for Measurable Set Ball Set, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MeasurableSetBallSet.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscreteTopologyOfZsmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VolumeNormSqLeOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FundamentalDomainPiBasis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthBasisMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CovolumeIntegerLatticeEq
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


set_option autoImplicit false
open NumberField NumberField.mixedEmbedding MeasureTheory Module Pointwise
open scoped Classical
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.BallD
open BallB BallC
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
def emb (b : Basis (Fin (finrank K V)) K V) : V →+ (Fin (finrank K V) → mixedSpace K) where
  toFun x := fun i => mixedEmbedding K (b.repr x i)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp
def lat (b : Basis (Fin (finrank K V)) K V) (L : Submodule (𝓞 K) V) :
    Submodule ℤ (Fin (finrank K V) → mixedSpace K) :=
  AddSubgroup.toIntSubmodule (L.toAddSubgroup.map (emb b))
def ballSet [IsEmpty {w : InfinitePlace K // w.IsReal}] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (b : Basis (Fin (finrank K V)) K V) : Set (Fin (finrank K V) → mixedSpace K) :=
  (psi K (Fin (finrank K V))) ⁻¹' Set.pi Set.univ fun w =>
    ell fun i => (w.1.embedding (h (b i) (b i))).re
variable [IsEmpty {w : InfinitePlace K // w.IsReal}] {h : V →ₗ⋆[K] V →ₗ[K] K}
  {b : Basis (Fin (finrank K V)) K V}
end Formalism.HermitianLattices.Ext.L3.BallD


