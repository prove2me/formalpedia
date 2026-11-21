-- Prove2me | Definitions.Def_RiemannMasullo_AdeleFundamentalDomain
-- name    : RiemannMasullo_AdeleFundamentalDomain
-- status  : Definition
-- author  : @dga471
-- created : 2026-11-20T23:14:40.425858+00:00
-- url     : https://prove2.me/theorems/65fdfa0d-6ded-49cb-8e24-821258fce3de
-- title:
--   Fundamental parallelepiped in the adeles of a number field
-- statement:
--   The infinite domain is the half-open parallelepiped determined by the real basis from an integral basis. The adelic domain also requires integrality at every finite place.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2.lean#L36-L57

import Mathlib
import Definitions.Def_RiemannMasullo_AdelicExtensions

noncomputable section
namespace RiemannMasullo
open Function NumberField IsDedekindDomain Topology
open InfinitePlace.Completion
open scoped Classical NNRat NNReal NumberField.AdeleRing Pointwise
variable (F : Type*) [Field F] [NumberField F]
variable {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))
def infiniteAdeleFundamentalDomain : Set (InfiniteAdeleRing F) :=
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let e := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  (InfiniteAdeleRing.ringEquiv_mixedSpace F) ⁻¹'
    ZSpan.fundamentalDomain ((b.map e).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F))
def adeleFundamentalDomain : Set 𝔸[F] :=
  {a | a.1 ∈ infiniteAdeleFundamentalDomain F b ∧ a ∈ integralAdelesOutside F ∅}
end RiemannMasullo


