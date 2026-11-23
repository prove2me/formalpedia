-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:06:33.132794+00:00
-- url     : https://prove2.me/theorems/4393bb56-449a-48b6-93d1-9d2811c7bb30
-- title:
--   Is Precomplete Of Basis
-- statement:
--   Definitions and structural lemmas for Is Precomplete Of Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/IsPrecompleteOfBasis.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_SemistableCompleteSplit
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Tower
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open IsLocalRing Polynomial
namespace ReciprocityTheory.ChartRestriction.G.Semi
namespace Nb
section Coord
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
end Coord
section Step
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable (f : V[X]) (hf : f.Monic) (hg : Irreducible (f.map (residue V)))
include hf hg
lemma quot_isField : IsField (AdjoinRoot f ⧸ (maximalIdeal V).map (AdjoinRoot.of f)) := by
  haveI : Fact (Irreducible (f.map (residue V))) := ⟨hg⟩
  have e := (AdjoinRoot.quotEquivQuotMap f (maximalIdeal V)).toRingEquiv
  first
  | exact MulEquiv.isField (Field.toIsField (AdjoinRoot (f.map (residue V)))) e.toMulEquiv
  | exact MulEquiv.isField (Field.toIsField (AdjoinRoot (f.map (residue V)))) e.symm.toMulEquiv
lemma J_max : ((maximalIdeal V).map (algebraMap V (AdjoinRoot f))).IsMaximal := by
  rw [AdjoinRoot.algebraMap_eq]
  exact Ideal.Quotient.maximal_of_isField _ (quot_isField f hf hg)
lemma maxEq [IsLocalRing (AdjoinRoot f)] :
    maximalIdeal (AdjoinRoot f) = (maximalIdeal V).map (algebraMap V (AdjoinRoot f)) := by
  exact (IsLocalRing.eq_maximalIdeal (J_max f hf hg)).symm
lemma locHom [IsLocalRing (AdjoinRoot f)] : IsLocalHom (algebraMap V (AdjoinRoot f)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have hm : a ∈ maximalIdeal V := (IsLocalRing.mem_maximalIdeal a).mpr (mem_nonunits_iff.mpr h)
  have h2 : algebraMap V (AdjoinRoot f) a ∈ maximalIdeal (AdjoinRoot f) := by
    rw [maxEq f hf hg]
    exact Ideal.mem_map_of_mem _ hm
  exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h2) ha
noncomputable def resEquiv [IsLocalRing (AdjoinRoot f)] :
    ResidueField (AdjoinRoot f) ≃+* AdjoinRoot (f.map (residue V)) :=
  (Ideal.quotEquivOfEq (maxEq f hf hg)).trans
    (AdjoinRoot.quotEquivQuotMap f (maximalIdeal V)).toRingEquiv
end Step
section Main
end Main
end Nb
end ReciprocityTheory.ChartRestriction.G.Semi


