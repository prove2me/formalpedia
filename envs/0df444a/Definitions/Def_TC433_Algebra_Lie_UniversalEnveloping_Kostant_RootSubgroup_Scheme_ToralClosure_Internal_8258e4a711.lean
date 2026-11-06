-- Prove2me | Definitions.Def_TC433_Algebra_Lie_UniversalEnveloping_Kostant_RootSubgroup_Scheme_ToralClosure_Internal_8258e4a711
-- name    : TC433_Algebra_Lie_UniversalEnveloping_Kostant_RootSubgroup_Scheme_ToralClosure_Internal_8258e4a711
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:40:06.735481+00:00
-- url     : https://prove2.me/theorems/8489b99c-b405-482c-85d7-957b8bac41eb
-- title:
--   TauCeti: Algebra / Lie / UniversalEnveloping / Kostant / RootSubgroup / Scheme / ToralClosure / Internal
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Internal for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Lie/UniversalEnveloping/Kostant/RootSubgroup/Scheme/ToralClosure/Internal.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_Algebra_AlgebraicGroup_GeneralLinear_Weight_Torus_e30f327bba
public import Definitions.Def_TC433_Algebra_Lie_UniversalEnveloping_Kostant_RootSubgroup_Scheme_Generated_Basic_f975ec660c

/-!
# Internal generator family for Kostant toral closures

This module contains the shared implementation of the coordinate-map family used to construct
both the full Kostant toral closure and its selected-root subsystems. It is internal plumbing;
public users should use the characterized defining ideals and factorization maps instead.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra.ToralClosure.Internal

universe u v w

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {J : Type v} {kappa : Type} [Finite kappa]
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : kappa → L)
variable (rho : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, rho u m ∈ M)
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (wt : Fin n → kappa → ℤ)

/-- The coordinate Hopf algebra receiving a root-subgroup or weight-torus generator map. -/
noncomputable abbrev kostantToralGeneratorCodomain (j : Sum J Unit) :
    _root_.CommHopfAlgCat ℤ :=
  match j with
  | .inl _ => AdditiveGroup.coordinateHopfAlgebra ℤ
  | .inr _ => (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup kappa)).obj

/-- The family consisting of reindexed root-subgroup coordinate maps and the weight-torus map. -/
noncomputable def kostantToralGeneratorMap (r : J → I)
    (hnilJ : ∀ j, IsNilpotent
      (rho (_root_.UniversalEnvelopingAlgebra.ι ℚ (e (r j))))) (j : Sum J Unit) :
    GeneralLinear.coordinateHopfAlgebra ℤ n ⟶
      kostantToralGeneratorCodomain (kappa := kappa) j :=
  match j with
  | .inl i => kostantRootSubgroupCoordinateMap e h rho M hM (r i) (hnilJ i) b
  | .inr _ => GeneralLinear.weightTorusCoordinateMap wt

/-- A root-indexed member of the internal generator family is its represented root-subgroup
coordinate map. -/
@[simp]
theorem kostantToralGeneratorMap_inl (r : J → I)
    (hnilJ : ∀ j, IsNilpotent
      (rho (_root_.UniversalEnvelopingAlgebra.ι ℚ (e (r j))))) (j : J) :
    kostantToralGeneratorMap e h rho M hM b wt r hnilJ (.inl j) =
      kostantRootSubgroupCoordinateMap e h rho M hM (r j) (hnilJ j) b := by
  rfl

/-- The final member of the internal generator family is the represented weight-torus coordinate
map. -/
@[simp]
theorem kostantToralGeneratorMap_inr (r : J → I)
    (hnilJ : ∀ j, IsNilpotent
      (rho (_root_.UniversalEnvelopingAlgebra.ι ℚ (e (r j))))) :
    kostantToralGeneratorMap e h rho M hM b wt r hnilJ (.inr ()) =
      GeneralLinear.weightTorusCoordinateMap wt := by
  rfl

/-- The common kernel of a subtype-indexed generator family can be written using its root and
torus branches without exposing the implementation of the family itself. -/
theorem commonKernelHopfIdeal_kostantToralGeneratorMap_subtype (S : Set I)
    (hnilS : ∀ i : S, IsNilpotent
      (rho (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i.1)))) :
    CommHopfAlgCat.commonKernelHopfIdeal
        (kostantToralGeneratorMap e h rho M hM b wt Subtype.val hnilS) =
      CommHopfAlgCat.commonKernelHopfIdeal
        ((fun j : Sum S Unit =>
          match j with
          | .inl i => kostantRootSubgroupCoordinateMap e h rho M hM i.1 (hnilS i) b
          | .inr _ => GeneralLinear.weightTorusCoordinateMap (R := ℤ) wt) :
          (j : Sum S Unit) → GeneralLinear.coordinateHopfAlgebra ℤ n ⟶
            match j with
            | .inl _ => AdditiveGroup.coordinateHopfAlgebra ℤ
            | .inr _ =>
                (DiagonalizableGroup.coordinateRing ℤ
                  (SplitTorus.characterGroup kappa)).obj) := by
  unfold kostantToralGeneratorMap kostantToralGeneratorCodomain
  congr 1
  · funext j
    rcases j with i | ⟨⟩ <;> rfl
  · apply Function.hfunext rfl
    intro j j' hj
    cases hj
    rcases j with i | ⟨⟩ <;> rfl

end TauCeti.UniversalEnvelopingAlgebra.ToralClosure.Internal


