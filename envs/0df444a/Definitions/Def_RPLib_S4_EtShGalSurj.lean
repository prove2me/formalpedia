-- Prove2me | Definitions.Def_RPLib_S4_EtShGalSurj
-- name    : RPLib_S4_EtShGalSurj
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:50:39.010959+00:00
-- url     : https://prove2.me/theorems/22ae2115-fabb-4f44-afe5-c88cfc71afe0
-- title:
--   Every finite continuous $\pi_1$-representation is the generic fibre of a lisse sheaf
-- statement:
--   Let $A$ be a domain with fraction field $K$ and $\pi_1 = \mathrm{Gal}(K_U/K)$. For a finite Galois $L \subseteq K_U$ unramified over $A$, restriction $\pi_1 \to \mathrm{Gal}(L/K)$ is onto with open kernel, and every open subgroup of $\pi_1$ contains such a kernel. A representation of $\pi_1$ whose kernel contains $\ker(\pi_1 \to \mathrm{Gal}(L/K))$ factors through $\mathrm{Gal}(L/K)$. Main result: a representation of $\pi_1$ on a finite $\Lambda$-module with open kernel is, up to equivariant isomorphism, the Galois representation on the generic stalk $(F_V)_{\bar\eta}$ of the lisse sheaf $F_V$ attached to it.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. Grothendieck, Revetements etales et groupe fondamental (SGA 1), Lecture Notes in Math. 224, Springer (1971), Expose V, Section 8; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter I, Section 5

import Mathlib
import Definitions.Def_RPLib_S4_EtShGalGen

/-!
# S4-EtSheaves, part O10e(i): every finite continuous `π₁`-representation is the generic fibre of a lisse sheaf

For `π₁ = Pi1 A K = Gal(K_U/K)` and a finite unramified Galois `L ⊆ K_U` with cover `C = coverOf L`:
* `resL_surjective`, `isOpen_ker_resL`: restriction `resL : π₁ ↠ Gal(L/K)` is onto with open kernel;
* `exists_resL_ker_le`: every open subgroup of `π₁` contains `ker resL` for some such `L`;
* `factorRep`: a representation `ρ'` of `π₁` with `ker resL ≤ ker ρ'` factors as `ρ ∘ resL` (`factorRep_resL`);
* `isOpen_ker_piRep`: for every `G`-module `V`, the `π₁`-representation `ρ ∘ resL` has open kernel;
* **`exists_lisse_of_rep`**: a representation of `π₁` on a finite `Λ`-module with open kernel is, up to
  isomorphism of the stalk, the Galois representation on the generic stalk `(F_V)_η̄` of the lisse sheaf `F_V`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtSheaves.TorSec

open GenBr

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin
  GalCover.grp GalCover.fG GalCover.act GalCover.gal genAlg genAlgSep genTower

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] [IsNoetherianRing A]

theorem resL_surjective (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K) :
    Function.Surjective (resL A K L hL) := by
  haveI := hL.2.1
  letI : Algebra L (maxUnram A K) := (IntermediateField.inclusion (le_maxUnram A K L hL)).toAlgebra
  haveI : IsScalarTower K L (maxUnram A K) :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (le_maxUnram A K L hL))
  exact AlgEquiv.restrictNormalHom_surjective (maxUnram A K)

/-- `σ ∈ ker resL` iff `σ` fixes the image of `L`. -/
theorem resL_eq_one_of_fix (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K)
    (σ : Pi1 A K) (h : ∀ y : L, σ (IntermediateField.inclusion (le_maxUnram A K L hL) y) =
      IntermediateField.inclusion (le_maxUnram A K L hL) y) :
    resL A K L hL σ = 1 := by
  show (show L ≃ₐ[K] L from resL A K L hL σ) = 1
  refine AlgEquiv.ext fun y => ?_
  rw [AlgEquiv.one_apply]
  exact Subtype.ext (congrArg (fun z : maxUnram A K => (z : AlgebraicClosure K))
    ((resL_spec A K L hL σ y).trans (h y)))

theorem fix_of_resL_eq_one (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K)
    (σ : Pi1 A K) (hσ : resL A K L hL σ = 1) (y : L) :
    σ (IntermediateField.inclusion (le_maxUnram A K L hL) y) =
      IntermediateField.inclusion (le_maxUnram A K L hL) y := by
  have h1 : (show L ≃ₐ[K] L from resL A K L hL σ) = 1 := hσ
  rw [← resL_spec A K L hL σ y, h1, AlgEquiv.one_apply]

/-- `ker (π₁ ↠ Gal(L/K))` is open: it contains the fixing group of the finite extension `L ⊆ K_U`. -/
theorem isOpen_ker_resL (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K) :
    IsOpen ((resL A K L hL).ker : Set (Pi1 A K)) := by
  haveI := hL.1
  haveI : FiniteDimensional K (IntermediateField.restrict (le_maxUnram A K L hL)) :=
    (IntermediateField.restrictAlgEquiv (le_maxUnram A K L hL)).toLinearEquiv.finiteDimensional
  refine Subgroup.isOpen_mono (H₁ := (IntermediateField.restrict (le_maxUnram A K L hL)).fixingSubgroup) ?_
    (IntermediateField.fixingSubgroup_isOpen _)
  intro σ hσ
  rw [MonoidHom.mem_ker]
  refine resL_eq_one_of_fix A K L hL σ fun y => ?_
  exact (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ _
    ((IntermediateField.mem_restrict (le_maxUnram A K L hL) _).2 y.2)

/-- **Every open subgroup of `π₁` contains `ker (π₁ ↠ Gal(L/K))` for a finite unramified Galois `L`.** -/
theorem exists_resL_ker_le (N : Subgroup (Pi1 A K)) (hN : IsOpen (N : Set (Pi1 A K))) :
    ∃ (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K), (resL A K L hL).ker ≤ N := by
  classical
  obtain ⟨E, hE, hEN⟩ :=
    (krullTopology_mem_nhds_one_iff K (maxUnram A K) N).mp (hN.mem_nhds N.one_mem)
  have hfg : E.FG := by
    apply IntermediateField.fg_of_fg_toSubalgebra
    apply Subalgebra.fg_of_fg_toSubmodule
    exact (Submodule.fg_iff_finiteDimensional _).mpr hE
  obtain ⟨t, htfin, hadj⟩ := IntermediateField.fg_def.mp hfg
  obtain ⟨L, hL, hle⟩ := exists_unramSet_of_finite A K
    (htfin.toFinset.image (fun x : maxUnram A K => (x : AlgebraicClosure K))) (by
      intro x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
      exact y.2)
  refine ⟨L, hL, ?_⟩
  intro σ hσ
  have hσ' : resL A K L hL σ = 1 := MonoidHom.mem_ker.mp hσ
  apply hEN
  have hgen : ∀ x ∈ t, σ x = x := by
    intro x hx
    have hxL : (x : AlgebraicClosure K) ∈ L := by
      apply hle
      apply IntermediateField.subset_adjoin
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, htfin.mem_toFinset.mpr hx, rfl⟩)
    have hx' : x = IntermediateField.inclusion (le_maxUnram A K L hL) ⟨x, hxL⟩ := Subtype.ext rfl
    rw [hx']
    exact fix_of_resL_eq_one A K L hL σ hσ' ⟨x, hxL⟩
  have hEfix : E ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    rw [← hadj, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih => rw [zpow_add_one, AlgEquiv.mul_apply, hgen x hx, ih (Subgroup.zpow_mem_zpowers σ _)]
    | pred n ih =>
      have hinv : σ⁻¹ x = x := by
        conv_lhs => rw [← hgen x hx]
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
      rw [zpow_sub_one, AlgEquiv.mul_apply, hinv, ih (Subgroup.zpow_mem_zpowers σ _)]
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixedField_iff _ _).mp (hEfix hx) σ (Subgroup.mem_zpowers σ)

variable {A K} (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K)
variable (Λ : Type) [CommRing Λ] {V : Type} [AddCommGroup V] [Module Λ V]

/-- A representation of `π₁` killed by `ker resL` descends to `Gal(L/K)`. -/
def factorRep (ρ' : Representation Λ (Pi1 A K) V) (hk : (resL A K L hL).ker ≤ ρ'.ker) :
    Representation Λ (coverOf A K L hL).G V :=
  (QuotientGroup.lift (resL A K L hL).ker ρ' hk).comp
    (QuotientGroup.quotientKerEquivOfSurjective (resL A K L hL) (resL_surjective A K L hL)).symm.toMonoidHom

theorem factorRep_resL (ρ' : Representation Λ (Pi1 A K) V) (hk : (resL A K L hL).ker ≤ ρ'.ker)
    (σ : Pi1 A K) : factorRep L hL Λ ρ' hk (resL A K L hL σ) = ρ' σ := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective (resL A K L hL) (resL_surjective A K L hL)).symm
      (resL A K L hL σ) = (σ : Pi1 A K ⧸ (resL A K L hL).ker) :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  simp only [factorRep, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h]
  rfl

theorem factorRep_comp (ρ' : Representation Λ (Pi1 A K) V) (hk : (resL A K L hL).ker ≤ ρ'.ker) :
    (factorRep L hL Λ ρ' hk).comp (resL A K L hL) = ρ' :=
  MonoidHom.ext (factorRep_resL L hL Λ ρ' hk)

/-- The `π₁`-representation of `F_V` at the generic point: `ρ ∘ resL`. -/
abbrev piRep (ρ : Representation Λ (coverOf A K L hL).G V) : Representation Λ (Pi1 A K) V :=
  ρ.comp (resL A K L hL)

theorem isOpen_ker_piRep (ρ : Representation Λ (coverOf A K L hL).G V) :
    IsOpen ((piRep L hL Λ ρ).ker : Set (Pi1 A K)) :=
  Subgroup.isOpen_mono (fun σ hσ => by
      rw [MonoidHom.mem_ker] at hσ ⊢
      rw [MonoidHom.comp_apply, hσ, map_one])
    (isOpen_ker_resL A K L hL)

/-- The Galois representation on the generic stalk of `F_V` is `piRep ∘ genToPi1`. -/
theorem stalkFVGen_piRep (ρ : Representation Λ (coverOf A K L hL).G V) (σ : Gal (genPt A))
    (w : stalk Λ (FV (coverOf A K L hL) Λ ρ) (genPt A)) :
    (stalkFVAt Λ ρ (geomPtAt (genPt A)) (lGen A K L hL) (hlGen A K L hL)).hom.hom
        (galRep Λ (FV (coverOf A K L hL) Λ ρ) (genPt A) σ w) =
      piRep L hL Λ ρ (genToPi1 A K σ)
        ((stalkFVAt Λ ρ (geomPtAt (genPt A)) (lGen A K L hL) (hlGen A K L hL)).hom.hom w) :=
  stalkFVGen_galRep A K L hL Λ ρ σ w

variable (A K)

/-- **Essential surjectivity at the generic fibre.** A representation `ρ'` of `π₁ = Pi1 A K` on a finite
`Λ`-module `V` with open kernel factors as `ρ ∘ resL` through a finite unramified Galois `Gal(L/K)`, the sheaf
`F_V` of `coverOf L` is lisse, and its generic stalk is `V` with Galois action `ρ' ∘ genToPi1`. -/
theorem exists_lisse_of_rep [Module.Finite Λ V] (ρ' : Representation Λ (Pi1 A K) V)
    (hρ : IsOpen (ρ'.ker : Set (Pi1 A K))) :
    ∃ (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K)
      (ρ : Representation Λ (coverOf A K L hL).G V),
      piRep L hL Λ ρ = ρ' ∧ IsLisse Λ (FV (coverOf A K L hL) Λ ρ) ∧
      ∃ e : stalk Λ (FV (coverOf A K L hL) Λ ρ) (genPt A) ≅ ModuleCat.of Λ V,
        ∀ (σ : Gal (genPt A)) (w : stalk Λ (FV (coverOf A K L hL) Λ ρ) (genPt A)),
          e.hom.hom (galRep Λ (FV (coverOf A K L hL) Λ ρ) (genPt A) σ w) =
            ρ' (genToPi1 A K σ) (e.hom.hom w) := by
  obtain ⟨L, hL, hk⟩ := exists_resL_ker_le A K ρ'.ker hρ
  refine ⟨L, hL, factorRep L hL Λ ρ' hk, factorRep_comp L hL Λ ρ' hk, isLisse_FV Λ _,
    stalkFVAt Λ _ (geomPtAt (genPt A)) (lGen A K L hL) (hlGen A K L hL), fun σ w => ?_⟩
  rw [stalkFVGen_galRep, factorRep_resL]

end RamanujanPetersson.EtSheaves.TorSec


