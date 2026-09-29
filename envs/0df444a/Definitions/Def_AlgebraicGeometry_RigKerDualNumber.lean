-- Prove2me | Definitions.Def_AlgebraicGeometry_RigKerDualNumber
-- name    : AlgebraicGeometry_RigKerDualNumber
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/4405c8e3-aa44-5da9-a77c-a73d7e2d48af
-- title:
--   Dual-number reduction and the rigidified relative Picard kernel
-- statement:
--   Fix a commutative ring $R$ and an $R$-algebra $A$, and write $A[\varepsilon] = A \oplus A\varepsilon$ for `DualNumber A`. The first group of declarations introduces `dualNumberReduction R A`, the morphism $\operatorname{Spec} A \to \operatorname{Spec} A[\varepsilon]$ obtained by applying `Spec.map` to the $R$-algebra projection $A[\varepsilon] \to A$, $a + b\varepsilon \mapsto a$ (Mathlib's `TrivSqZeroExt.fstHom R A A`); `dualNumberReduction_comp_specMap` records that it is compatible with the structure morphisms to $\operatorname{Spec} R$, and `dualNumberReductionOver` packages it as a morphism over $\operatorname{Spec} R$. Next, `dualNumberReduction_catches_geometric_points` states that for a field $k$ every morphism $s : \operatorname{Spec} k \to \operatorname{Spec} A[\varepsilon]$ factors as $s_0$ followed by the reduction; the proof uses only that $\varepsilon$ is nilpotent and $k$ has no nonzero nilpotents, not that $k$ is algebraically closed.
--
--   The second group fixes an $R$-scheme $c : C \to \operatorname{Spec} R$ with a section $\varepsilon$ of $c$ over $\operatorname{Spec} R$. `RigKerDualNumber.Carrier c ε A` is the subtype of those rigidified line bundles $M$ on $C \times_R \operatorname{Spec} A[\varepsilon]$ (invertible modules with a rigidification along $\varepsilon$) for which there exists an isomorphism of the underlying module of $M$ pulled back along the dual-number reduction with the unit module on $C \times_R \operatorname{Spec} A$; the condition is the propositional `Nonempty` of such an isomorphism, and it concerns the underlying modules only, ignoring rigidifications. `RigKerDualNumber c ε A` is the quotient of this carrier by the relation inherited from isomorphism of underlying modules. Tensor product of representatives and the unit bundle stay inside the carrier (`tensor_mem`, `unit_mem`), which yields a multiplication `RigKerDualNumber.mul` and a distinguished element `RigKerDualNumber.one` on the quotient; no group structure is registered here.
--
--   Finally, given a designation $D$ (a scheme with a structure morphism to $\operatorname{Spec} R$ and a zero section) together with data `h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D` — a Poincaré bundle on $C \times_R D$ satisfying the fibrewise algebraic-equivalence-to-zero condition, the universal property classifying such bundles by unique morphisms to $D$, and triviality along the zero section — `RepresentsRelSubPic.kerPointsToRigKer` sends a point $x$ of $D$ over $\operatorname{Spec} A[\varepsilon]$ whose composite with the reduction is the underlying morphism of the identity section of the induced relative group law at $\operatorname{Spec} A$, to the class of the pullback $x^{*}\mathcal{P}$.
--
--   **Relation to Mathlib.** The dual numbers $A[\varepsilon]$ and the projection to $A$ are Mathlib's `DualNumber` and `TrivSqZeroExt.fstHom`; the rigidified relative Picard functor, its sub-functor conditions and the dual-number kernel constructed here are the project's own notions, with no Mathlib counterpart.
--
--   **Where it is used.** These definitions belong to the infrastructure for the relative Picard functor and its representing scheme used for Jacobians of modular curves: the dual-number kernel is the object through which points of the representing scheme lying above the identity over $\operatorname{Spec} A$ are compared with deformations of line bundles, i.e. with the tangent space of the relative $\operatorname{Pic}^{0}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RigKerDualNumber.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian

namespace AlgebraicGeometry.RelPicard

section Thickening

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

abbrev dualNumberReduction : Spec (.of A) ⟶ Spec (.of (DualNumber A)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R A A).toRingHom)

theorem dualNumberReduction_comp_specMap :
    dualNumberReduction R A ≫ Scheme.TwoAffineOpenCover.specMap R (DualNumber A)
      = Scheme.TwoAffineOpenCover.specMap R A := by
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber A))) =
    Spec.map (CommRingCat.ofHom (algebraMap R A))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  try exact (TrivSqZeroExt.fstHom R A A).comp_algebraMap

abbrev dualNumberReductionOver :
    SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R A) (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)) :=
  ⟨dualNumberReduction R A, dualNumberReduction_comp_specMap R A⟩

theorem dualNumberReduction_catches_geometric_points
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ Spec (.of (DualNumber A))) :
    ∃ s₀ : Spec (.of k) ⟶ Spec (.of A), s₀ ≫ dualNumberReduction R A = s := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  have hε : φ.hom DualNumber.eps = 0 := by
    have h2 : φ.hom DualNumber.eps * φ.hom DualNumber.eps = 0 := by
      rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
    exact mul_self_eq_zero.mp h2
  let φ₀ : A →+* k := φ.hom.comp (algebraMap A (DualNumber A))
  refine ⟨Spec.map (CommRingCat.ofHom φ₀), ?_⟩
  change Spec.map _ ≫ Spec.map _ = Spec.map φ
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
  refine DualNumber.ringHom_ext ?_ ?_
  · ext a
    simp only [φ₀, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      TrivSqZeroExt.fstHom_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl]
  · simp only [φ₀, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      TrivSqZeroExt.fstHom_apply, DualNumber.fst_eps, map_zero, hε]

end Thickening

section Kernel

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
variable (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
variable (A : Type u) [CommRing A] [Algebra R A]

def RigKerDualNumber.Carrier : Type (u + 1) :=
  { M : RigidifiedLineBundle c ε (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)) //
      Nonempty ((M.pullbackAlong (dualNumberReductionOver R A)).L ≅
        (RigidifiedLineBundle.unit (c := c) (ε := ε) (Scheme.TwoAffineOpenCover.specMap R A)).L) }

instance RigKerDualNumber.setoid : Setoid (RigKerDualNumber.Carrier c ε A) :=
  (RigidifiedLineBundle.setoid (c := c) (ε := ε) (Scheme.TwoAffineOpenCover.specMap R (DualNumber A))).comap
    Subtype.val

def RigKerDualNumber : Type (u + 1) := Quotient (RigKerDualNumber.setoid c ε A)

theorem RigKerDualNumber.tensor_mem (M N : RigKerDualNumber.Carrier c ε A) :
    Nonempty (((M.1.tensor N.1).pullbackAlong (dualNumberReductionOver R A)).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) (Scheme.TwoAffineOpenCover.specMap R A)).L) :=
  ⟨(RigidifiedLineBundle.nonempty_tensor_pullbackAlong_iso (dualNumberReductionOver R A) M.1 N.1).some ≪≫
    (M.2.some ⊗ᵢ N.2.some) ≪≫ λ_ _⟩

theorem RigKerDualNumber.unit_mem :
    Nonempty (((RigidifiedLineBundle.unit (c := c) (ε := ε)
        (Scheme.TwoAffineOpenCover.specMap R (DualNumber A))).pullbackAlong (dualNumberReductionOver R A)).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) (Scheme.TwoAffineOpenCover.specMap R A)).L) :=
  ⟨Scheme.Modules.pullbackUnitIso _⟩

def RigKerDualNumber.mul : RigKerDualNumber c ε A → RigKerDualNumber c ε A → RigKerDualNumber c ε A :=
  Quotient.map₂ (fun M N => ⟨M.1.tensor N.1, RigKerDualNumber.tensor_mem c ε A M N⟩)
    (fun _ _ hM _ _ hN => RigidifiedLineBundle.tensor_congr hM hN)

def RigKerDualNumber.one : RigKerDualNumber c ε A :=
  Quotient.mk _ ⟨RigidifiedLineBundle.unit (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)),
    RigKerDualNumber.unit_mem c ε A⟩

end Kernel

section KerPoints

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} {D : RelativePic0Designation R c}

noncomputable def RepresentsRelSubPic.kerPointsToRigKer (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (A : Type u) [CommRing A] [Algebra R A] :
    letI L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h
    { x : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)) D.toBase //
        dualNumberReduction R A ≫ x.1 = (L.one (Scheme.TwoAffineOpenCover.specMap R A)).1 } →
      RigKerDualNumber c ε A :=
  fun x => Quotient.mk _ ⟨h.poincare.pullbackAlong x.1, by
    letI := RepresentsRelSubPic.grpObj (P := algEquivZeroGroupCut c ε) h
    letI := (algEquivZeroGroupCut c ε).commGroupObj (Opposite.op (Over.mk (Scheme.TwoAffineOpenCover.specMap R A)))
    have h1 := congrArg Subtype.val
      (RepresentsRelSubPic.homEquiv_one (P := algEquivZeroGroupCut c ε) h (Over.mk (Scheme.TwoAffineOpenCover.specMap R A)))
    have one_iso : Nonempty ((h.poincare.pullbackAlong
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one (Scheme.TwoAffineOpenCover.specMap R A))).L ≅
          (RigidifiedLineBundle.unit (c := c) (ε := ε) (Scheme.TwoAffineOpenCover.specMap R A)).L) :=
      Quotient.exact h1
    have hx : GoodReductionJacobian.schemeHomOverComp (dualNumberReduction R A)
        (dualNumberReduction_comp_specMap R A) x.1 =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one (Scheme.TwoAffineOpenCover.specMap R A) :=
      Subtype.ext x.2
    rw [← hx] at one_iso
    exact ⟨h.poincare.pullbackAlongPullbackAlongIso x.1 (dualNumberReductionOver R A) ≪≫ one_iso.some⟩⟩

end KerPoints

end AlgebraicGeometry.RelPicard

end


