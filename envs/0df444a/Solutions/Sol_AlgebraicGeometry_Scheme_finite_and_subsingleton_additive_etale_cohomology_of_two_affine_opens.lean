-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.finite_and_subsingleton_additive_etale_cohomology_of_two_affine_opens
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-26T09:51:49.432426+00:00
-- url     : https://prove2.me/submissions/be0b609f-65d6-480b-9982-3fb701765508

import Definitions.Def_AlgebraicGeometry_EtaleAdditiveStructureSheaf
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isProper
import Theorems.Thm_AlgebraicGeometry_Scheme_smallEtale_additive_cohomology_equiv_orderedCech

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SmallEtaleAdditive (sheaf cohomologyModule)

namespace PhilipponEtaleAdditiveFiniteness

universe u

/-- Cohomology of the additive étale sheaf on a proper scheme over a field
is finite-dimensional with its natural scalar action. -/
theorem finite_additive_cohomology (K : Type u) [Field K] {X : Scheme.{u}}
    (r : X ⟶ Spec (.of K)) [IsProper r] (q : ℕ) :
    @Module.Finite K ((sheaf X).H q) _ _ (cohomologyModule r q) := by
  classical
  let := QuasiCompact.compactSpace_of_compactSpace r
  let V := X.affineCover.finiteSubcover
  let : LinearOrder V.I₀ := LinearOrder.lift' (Fintype.equivFin V.I₀) (Fintype.equivFin V.I₀).injective
  let U : X.OrderedAffineCover :=
    { ι := V.I₀
      U i := (V.f i).opensRange
      isAffineOpen i := isAffineOpen_opensRange (V.f i)
      iSup_eq_top := V.iSup_opensRange }
  let : ∀ n : ℕ, Module K ((sheaf X).H n) := fun n => cohomologyModule r n
  have h := OModulePresheaf.cechFinite_unit_of_isProper r U
  obtain ⟨e₀, e⟩ := Scheme.smallEtale_additive_cohomology_equiv_orderedCech K r U
  cases q with
  | zero =>
    let := h.1
    exact Module.Finite.equiv e₀.some.symm
  | succ n =>
    let := h.2 n
    exact Module.Finite.equiv (e n).some.symm

end PhilipponEtaleAdditiveFiniteness

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SmallEtaleAdditive (sheaf cohomologyModule)

namespace PhilipponEtaleTwoAffineAdditiveComparison

universe u

/-- A separated scheme over a field covered by two affine opens has no additive
étale cohomology in degrees above one. -/
theorem subsingleton_additive_cohomology {K : Type u} [Field K] {X : Scheme.{u}}
    (r : X ⟶ Spec (.of K)) [IsSeparated r] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ⊔ V = ⊤) (n : ℕ) :
    Subsingleton ((sheaf X).H (n + 2)) := by
  let W (i : ULift.{u} (Fin 2)) : X.Opens := if i.down = 0 then U else V
  let C : X.OrderedAffineCover :=
    { ι := ULift.{u} (Fin 2)
      U := W
      isAffineOpen i := by dsimp [W]; split <;> assumption
      iSup_eq_top := top_unique (by
        rw [← h]
        exact sup_le (by simpa [W] using le_iSup W ⟨0⟩) (by simpa [W] using le_iSup W ⟨1⟩)) }
  let : IsEmpty (C.Idx (n + 1 + 1)) := ⟨fun s => by
    have hc := Fintype.card_le_of_injective s.val s.property.injective
    change Fintype.card (Fin (n + 1 + 1 + 1)) ≤ Fintype.card (ULift.{u} (Fin 2)) at hc
    simp only [Fintype.card_fin, Fintype.card_ulift] at hc
    omega⟩
  let F := OModulePresheaf.unit r
  let : Subsingleton (F.cochain C (n + 1 + 1)) := inferInstance
  let : Subsingleton (F.HSucc C (n + 1)) := Quot.Subsingleton
  let : ∀ q : ℕ, Module K ((sheaf X).H q) := fun q => cohomologyModule r q
  let e := ((Scheme.smallEtale_additive_cohomology_equiv_orderedCech K r C).2 (n + 1)).some
  exact e.injective.subsingleton


end PhilipponEtaleTwoAffineAdditiveComparison

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (K : Type u) [Field K] {X : Scheme.{u}} (r : X ⟶ Spec (.of K)) [IsProper r]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ⊔ V = ⊤) :
    (∀ q : ℕ, @Module.Finite K ((PhilipponEtaleAdditiveStructureSheaf.sheaf X).H q)
      _ _ (PhilipponEtaleAdditiveStructureSheaf.cohomologyModule r q)) ∧
    ∀ q : ℕ, Subsingleton ((PhilipponEtaleAdditiveStructureSheaf.sheaf X).H (q + 2)) := by
  exact ⟨
    PhilipponEtaleAdditiveFiniteness.finite_additive_cohomology K r,
    PhilipponEtaleTwoAffineAdditiveComparison.subsingleton_additive_cohomology r U V hU hV h⟩

end

end
