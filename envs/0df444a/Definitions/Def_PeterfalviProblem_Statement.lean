-- Prove2me | Definitions.Def_PeterfalviProblem_Statement
-- name    : PeterfalviProblem_Statement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-27T04:56:00.820351+00:00
-- url     : https://prove2.me/theorems/306e1021-ac48-5e5d-ab67-b1a6de70c4c0
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Yawara Ishida (yawara/peterfalvi-problem; see pinned Apache-2.0 LICENSE and source headers)'s pinned Resolution of Péterfalvi problem for p = 3 and SL(2, 2^q) witness for p = 2 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Statement.lean

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.Norm.Defs
set_option autoImplicit false
namespace PeterfalviProblem
variable (p q : ℕ) [Fact p.Prime]
abbrev additiveFieldGroup := Multiplicative (GaloisField p q)
noncomputable def normOneUnits : Subgroup (GaloisField p q)ˣ :=
  (Units.map (Algebra.norm (ZMod p) (S := GaloisField p q))).ker
noncomputable def normOneMulAction : normOneUnits p q →* MulAut (additiveFieldGroup p q) :=
  (MulAutMultiplicative (GaloisField p q)).symm.toMonoidHom.comp
    ((AddAut.mulLeft : (GaloisField p q)ˣ →* Multiplicative (AddAut (GaloisField p q))).comp
      (normOneUnits p q).subtype)
abbrev normOneFrobeniusGroup :=
  additiveFieldGroup p q ⋊[normOneMulAction p q] normOneUnits p q
noncomputable def normOneFrobeniusComplement : Subgroup (normOneFrobeniusGroup p q) :=
  (SemidirectProduct.inr : normOneUnits p q →* normOneFrobeniusGroup p q).range
noncomputable def primeLine : Subgroup (normOneFrobeniusGroup p q) :=
  (AddSubgroup.toSubgroup (algebraMap (ZMod p) (GaloisField p q)).toAddMonoidHom.range).map
    (SemidirectProduct.inl : additiveFieldGroup p q →* normOneFrobeniusGroup p q)
def HypothesisB (G : Type*) [Group G] : Prop :=
  ∃ σ : normOneFrobeniusGroup p q →* G, Function.Injective σ ∧
    ∃ Q : Subgroup G, Finite Q ∧ IsMulCommutative Q ∧ ¬ p ∣ Nat.card Q ∧
      ∃ y ∈ Q,
        (primeLine p q).map σ ≤ Subgroup.normalizer (Q : Set G) ∧
        (primeLine p q).map ((MulAut.conj y⁻¹).toMonoidHom.comp σ) ≤
          Subgroup.normalizer ((normOneFrobeniusComplement p q).map σ : Set G)
end PeterfalviProblem


