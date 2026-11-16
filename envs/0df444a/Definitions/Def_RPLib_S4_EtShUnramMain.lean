-- Prove2me | Definitions.Def_RPLib_S4_EtShUnramMain
-- name    : RPLib_S4_EtShUnramMain
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:38:23.28253+00:00
-- url     : https://prove2.me/theorems/2fb4a182-f726-4000-a036-f45fd04665d3
-- title:
--   The generic Galois representation of a lisse sheaf is unramified
-- statement:
--   Let $A$ be an integrally closed domain with fraction field $K$ and $F$ a lisse etale sheaf of $\Lambda$-modules on $\mathrm{Spec}\,A$. The Galois representation on the generic stalk $F_{\bar\eta}$ is trivial on the kernel of $\mathrm{Gal}(\kappa(\eta)^{\mathrm{sep}}/\kappa(\eta)) \to \pi_1(\mathrm{Spec}\,A)$. Equivalently, the fixed field $L_0$ of its (open) kernel is a finite Galois extension of $K$ whose copy in $\overline K$ is unramified over $A$: an inertia element lifts to an automorphism of the separable closure that fixes a chart point of $F$, hence fixes $L_0$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. Grothendieck, Revetements etales et groupe fondamental (SGA 1), Lecture Notes in Math. 224, Springer (1971), Expose V, Section 8; J. S. Milne, Etale Cohomology, Princeton University Press (1980)

import Mathlib
import Definitions.Def_RPLib_S4_EtShPlumb
import Definitions.Def_RPLib_S4_EtShInertiaLift2
import Definitions.Def_RPLib_S4_EtShUnramKer

/-!
# S4-EtSheaves, O10c part 5: the generic Galois representation of a lisse sheaf is unramified

For a lisse `F` on `Spec A` (`A` an integrally closed domain with fraction field `K`), the Galois
representation on the generic stalk `F_η̄` is trivial on the kernel of `Gal(κ(η)^sep/κ(η)) → π₁(Spec A)`
(`galRep_unram`). The fixed field `L0` of its (open) kernel is a finite Galois extension of `K`; its copy
in `K̄` is unramified over `A` (`unram`): an inertia element lifts (`InertiaLift.exists_inertia_lift`) to an
automorphism fixing a chart point (`Plumb.exists_chart`), hence `L0`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtSheaves.UnramMain

open GenBr

attribute [local instance] genAlg genAlgSep genTower Plumb.genAlgA

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

theorem fracIso_algebraMap' (a : A) : fracIso A K (algebraMap A K a) = Plumb.toGen A a := by
  show (Scheme.Spec.residueFieldIso (CommRingCat.of A) (genPt A)).inv.hom
    (IsLocalization.algEquiv (nonZeroDivisors A) K (⊥ : Ideal A).ResidueField (algebraMap A K a)) = _
  rw [AlgEquiv.commutes]
  rfl

theorem tower : IsScalarTower A K (SeparableClosure (genField A)) :=
  IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap (genField A) (SeparableClosure (genField A)) (Plumb.toGen A a) =
      algebraMap (genField A) (SeparableClosure (genField A)) (fracIso A K (algebraMap A K a))
    rw [fracIso_algebraMap'])

theorem isGaloisK : IsGalois K (SeparableClosure (genField A)) :=
  IsGalois.of_equiv_equiv (F := genField A) (E := SeparableClosure (genField A)) (f := (fracIso A K).symm)
    (g := RingEquiv.refl _) (RingHom.ext fun x => by
      show algebraMap (genField A) (SeparableClosure (genField A)) (fracIso A K ((fracIso A K).symm x)) =
        algebraMap (genField A) (SeparableClosure (genField A)) x
      rw [RingEquiv.apply_symm_apply])

attribute [local instance] tower isGaloisK

/-- An automorphism of `κ(η)^sep` over `K` is one over `κ(η) ≅ K`. -/
def toGal (τ : SeparableClosure (genField A) ≃ₐ[K] SeparableClosure (genField A)) : Gal (genPt A) :=
  AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) (fun x => by
    obtain ⟨y, rfl⟩ := (fracIso A K).surjective x
    exact τ.commutes y)

variable {Λ : Type} [CommRing Λ] (F : EtSh Λ (Spec (CommRingCat.of A)))

/-- The fixed field of the kernel of the generic Galois representation. -/
def L0 : IntermediateField (genField A) (SeparableClosure (genField A)) :=
  IntermediateField.fixedField (galRep Λ F (genPt A)).ker

theorem fixingSubgroup_L0 (hF : IsLisse Λ F) : (L0 A F).fixingSubgroup = (galRep Λ F (genPt A)).ker :=
  InfiniteGalois.fixingSubgroup_fixedField
    ⟨(galRep Λ F (genPt A)).ker, Subgroup.isClosed_of_isOpen _ (isOpen_ker_galRep hF _)⟩

theorem finiteDimensional_L0 (hF : IsLisse Λ F) : FiniteDimensional (genField A) (L0 A F) :=
  (InfiniteGalois.isOpen_iff_finite _).mp (by
    rw [fixingSubgroup_L0 A F hF]
    exact isOpen_ker_galRep hF _)

theorem isGalois_L0 (hF : IsLisse Λ F) : IsGalois (genField A) (L0 A F) :=
  (InfiniteGalois.normal_iff_isGalois _).mp (by
    rw [fixingSubgroup_L0 A F hF]
    infer_instance)

theorem finK (hF : IsLisse Λ F) : FiniteDimensional K (L0 A F) := by
  have := finiteDimensional_L0 A F hF
  have : Module.Finite K (genField A) := Module.Finite.of_surjective (Algebra.linearMap K (genField A))
    (fun y => ⟨(fracIso A K).symm y, (fracIso A K).apply_symm_apply y⟩)
  exact Module.Finite.trans (genField A) (L0 A F)

/-- `K`-copies of `L0` are finite over `K` (with the `K`-module structure of the `K`-algebra `L0`). -/
theorem finRange (hF : IsLisse Λ F) (j : L0 A F →ₐ[K] AlgebraicClosure K) : FiniteDimensional K j.fieldRange := by
  have := finiteDimensional_L0 A F hF
  have : Module.Finite K (genField A) := Module.Finite.of_surjective (Algebra.linearMap K (genField A))
    (fun y => ⟨(fracIso A K).symm y, (fracIso A K).apply_symm_apply y⟩)
  letI : Module K (L0 A F) := Algebra.toModule
  letI : IsScalarTower K (genField A) (L0 A F) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Module.Finite K (L0 A F) := Module.Finite.trans (genField A) (L0 A F)
  exact Module.Finite.equiv j.equivFieldRange.toLinearEquiv

theorem galK (hF : IsLisse Λ F) : IsGalois K (L0 A F) := by
  have := isGalois_L0 A F hF
  exact IsGalois.of_equiv_equiv (F := genField A) (E := L0 A F) (f := (fracIso A K).symm)
    (g := RingEquiv.refl _) (RingHom.ext fun x => by
      rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply K (genField A) (L0 A F)]
      exact congrArg (algebraMap (genField A) (L0 A F)) ((fracIso A K).apply_symm_apply x))

/-- Any `K`-copy `L` of `L0` inside `K̄` is unramified over `A`. -/
theorem unram [IsIntegrallyClosed A] (hF : IsLisse Λ F) (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [IsGalois K L] (e0 : L0 A F ≃ₐ[K] L) : IsUnramifiedSub A K L := by
  intro Q hQ
  have := hQ
  have : IsFractionRing (integralClosure A L) L :=
    integralClosure.isFractionRing_of_finite_extension (A := A) K L
  have : IsIntegrallyClosed (integralClosure A L) := integralClosure.isIntegrallyClosedOfFiniteExtension K
  rw [eq_bot_iff]
  intro τ hτ
  rw [Subgroup.mem_bot]
  let τB : integralClosure A L ≃ₐ[A] integralClosure A L :=
    AlgEquiv.ofRingEquiv (f := MulSemiringAction.toRingEquiv _ (integralClosure A L) τ) (fun a =>
      Subtype.ext (by
        show τ (algebraMap A L a) = algebraMap A L a
        rw [IsScalarTower.algebraMap_apply A K L]
        exact τ.commutes _))
  obtain ⟨R', _, _, P0, u, hu, hcomp, H⟩ :=
    Plumb.exists_chart A F hF ⟨Q.comap (algebraMap A (integralClosure A L)), inferInstance⟩
  have := hu
  obtain ⟨ψ, ι, τ', hψ, hι⟩ := InertiaLift.exists_inertia_lift P0 τ τB (fun _ => rfl) Q
    (fun b => AddSubgroup.mem_inertia.mp hτ b) u hcomp (SeparableClosure (genField A))
  have hN : toGal A K τ' ∈ (L0 A F).fixingSubgroup := by
    rw [fixingSubgroup_L0 A F hF]
    exact MonoidHom.mem_ker.mpr (H ψ (toGal A K τ') hψ)
  have hx : ∀ x, τ x = x := by
    intro x
    have hmem : ι x ∈ L0 A F := by
      obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp
        (mem_fieldRange_of_normal ι (((L0 A F).val.restrictScalars K).comp e0.symm.toAlgHom) x)
      rw [← hy]
      exact (e0.symm y).2
    apply ι.toRingHom.injective
    show ι (τ x) = ι x
    rw [← hι x]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hN (ι x) hmem
  exact AlgEquiv.ext hx

/-- **HEADLINE (O10c).** For lisse `F` on `Spec A` (`A` integrally closed), the Galois representation on the
generic stalk `F_η̄` factors through `π₁(Spec A)`: it is trivial on the kernel of `genToPi1`. -/
theorem galRep_unram [IsIntegrallyClosed A] (hF : IsLisse Λ F) (σ : Gal (genPt A))
    (hσ : genToPi1 A K σ = 1) : galRep Λ F (genPt A) σ = LinearMap.id := by
  have := finiteDimensional_L0 A F hF
  have := isGalois_L0 A F hF
  have := finK A K F hF
  have := galK A K F hF
  let j : L0 A F →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let e0 := j.equivFieldRange
  have : FiniteDimensional K j.fieldRange := finRange A K F hF j
  have : IsGalois K j.fieldRange := IsGalois.of_algEquiv e0
  have hmem : j.fieldRange ∈ unramSet A K := ⟨inferInstance, inferInstance, unram A K F hF j.fieldRange e0⟩
  have hle : j.fieldRange ≤ maxUnram A K := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hmem
  have hker : σ ∈ (galRep Λ F (genPt A)).ker := by
    rw [← fixingSubgroup_L0 A F hF, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    obtain ⟨z, hz⟩ := AlgHom.mem_fieldRange.mp (mem_fieldRange_of_normal
      (((L0 A F).val.restrictScalars K).comp e0.symm.toAlgHom)
      ((emb A K (SeparableClosure (genField A))).comp (IntermediateField.inclusion hle)) (e0 ⟨y, hy⟩))
    have h2 : ((e0.symm (e0 ⟨y, hy⟩) : L0 A F) : SeparableClosure (genField A)) = y := by
      rw [AlgEquiv.symm_apply_apply]
    have hz' : genEmb A K (IntermediateField.inclusion hle z) = y := hz.trans h2
    rw [← hz']
    exact (genToPi1_eq_one_iff A K σ).mp hσ _
  exact MonoidHom.mem_ker.mp hker

end RamanujanPetersson.EtSheaves.UnramMain


