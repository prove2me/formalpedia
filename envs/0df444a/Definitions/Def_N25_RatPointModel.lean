-- Prove2me | Definitions.Def_N25_RatPointModel
-- name    : N25_RatPointModel
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:05:44.256396+00:00
-- url     : https://prove2.me/theorems/63267591-a8e9-4a4b-81b9-43332b66dce8
-- title:
--   A rational abelian point model across completions
-- statement:
--   Packages an abelian group of geometric points over an algebraic closure of the rationals, its arithmetic Galois action, rational and $5$-adic fixed-point groups, and points over an algebraic closure of the $5$-adic field, together with additive maps induced by the completion embedding. This technical carrier keeps the group law and Galois equivariance available when comparing global and local points.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2
import Definitions.Def_GaloisRep_CompletionBridge
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory AlgebraicGeometry GoodReductionJacobian
namespace N25

/-- A rational abelian model retaining its law and its arithmetic point action. -/
structure RatPointModel where
  B : Scheme.{0}
  f : B ⟶ Spec (CommRingCat.of ℚ)
  G : RelativeGroupLaw ℚ f
  comm : G.IsCommutative
  abelian : AbelianSchemePropertyBundle ℚ f
  pts : J ≃+ G.AlgPoints comm (AlgebraicClosure ℚ)
  equivariant : ∀ (σ : Gal) (x : J), pts (σ • x) = σ • pts x

local instance instL_N25_RatPointModel_bfd51b : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance instL_N25_RatPointModel_3dbe1c : IsScalarTower ℚ ℚ_[5] (PadicAlgCl 5) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

abbrev RatPointModel.Bar (D : RatPointModel) : Type :=
  D.G.AlgPoints D.comm (AlgebraicClosure ℚ)
abbrev RatPointModel.Local (D : RatPointModel) : Type :=
  D.G.AlgPoints D.comm ℚ_[5]
abbrev RatPointModel.Omega (D : RatPointModel) : Type :=
  D.G.AlgPoints D.comm (PadicAlgCl 5)

/-- Extend a geometric point through the prescribed completion embedding. -/
noncomputable def RatPointModel.barMap (D : RatPointModel) : D.Bar →+ D.Omega :=
  RelativeGroupLaw.AlgPoints.map (L := D.G) (hc := D.comm) (padicEmbedding 5)

/-- Extend a local rational point to the local algebraic closure. -/
noncomputable def RatPointModel.localMap (D : RatPointModel) : D.Local →+ D.Omega :=
  RelativeGroupLaw.AlgPoints.map (L := D.G) (hc := D.comm)
    (IsScalarTower.toAlgHom ℚ ℚ_[5] (PadicAlgCl 5))
end N25


