-- Prove2me | Definitions.Def_N25_LocalFiveIntegralPoints
-- name    : N25_LocalFiveIntegralPoints
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:02:07.76421+00:00
-- url     : https://prove2.me/theorems/5495837e-92d1-4107-9cbb-eaa34e98ad4e
-- title:
--   Integral sections and reduction at $5$
-- statement:
--   Packages a covering of the rational points of an abelian model by integral sections of a Néron model, together with the additive reduction map to the residue field and its identity-fibre kernel. This is a technical carrier for establishing finite-index divisibility of the local point group.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_LocalFiveArithmetic
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GoodReductionJacobian NeronModelInfra

noncomputable section
local instance instL_N25_LocalFiveIntegralPoints_bfd51b : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace N25.LocalFive

/-- Integral sections of a Néron model covering the points for the supplied rational law. -/
structure IntegralPointCover
    {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of ℚ)}
    (L : RelativeGroupLaw ℚ f) (hc : L.IsCommutative) where
  N : Scheme.{0}
  g : N ⟶ Spec (CommRingCat.of R5)
  law : RelativeGroupLaw R5 g
  comm : law.IsCommutative
  model : NeronModelPropertyBundle R5 ℚ_[5] g
  toLocal : law.AlgPoints comm R5 →+ L.AlgPoints hc ℚ_[5]
  onto : Function.Surjective toLocal

/-- Reduction of integral sections to the residue field. -/
noncomputable def reductionHom
    {N : Scheme.{0}} {g : N ⟶ Spec (CommRingCat.of R5)}
    (L : RelativeGroupLaw R5 g) (hc : L.IsCommutative) :
    L.AlgPoints hc R5 →+ L.AlgPoints hc k5 :=
  RelativeGroupLaw.AlgPoints.map (L := L) (hc := hc)
    (IsScalarTower.toAlgHom R5 R5 k5)

/-- Integral points reducing to the identity. -/
abbrev reductionKernel
    {N : Scheme.{0}} {g : N ⟶ Spec (CommRingCat.of R5)}
    (L : RelativeGroupLaw R5 g) (hc : L.IsCommutative) :
    AddSubgroup (L.AlgPoints hc R5) := (reductionHom L hc).ker
end N25.LocalFive


