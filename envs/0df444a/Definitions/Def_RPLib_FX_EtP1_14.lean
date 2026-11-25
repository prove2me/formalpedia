-- Prove2me | Definitions.Def_RPLib_FX_EtP1_14
-- name    : RPLib_FX_EtP1_14
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T05:24:47.53901+00:00
-- url     : https://prove2.me/theorems/0ab7f117-aa88-559d-bf28-a75b748a1803
-- title:
--   Étale cohomology of the projective line, library file 14 of 34
-- statement:
--   File 14 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtSheaves_SpecPt`: S4-EtSheaves, part 29: geometric points of the spectrum of a field
--   * `S4.Def_RP_EtSheaves_SkyG`: S4-EtSheaves, part 28: the sheaf of equivariant maps on the fibres of a point
--   * `S4.Def_RP_EtSheaves_SpecEq`: S4-EtSheaves, part 30: Galois descent over a field
--   * `S4.Def_RP_EtSheaves_SpecHom`: S4-EtSheaves, part 31: morphisms of sheaves over a field are equivariant stalk maps
--   * `S4.Def_RP_Kummer_Gal`: S4-Kummer, part 1: Kummer characters for a subgroup of a Galois group (generic field theory)
--   * `S4.Def_RP_EtCompact_FibPt`: S4-EtCompact, part 48: fibre points of the generic geometric point (F4b of plan v5)
--   * `S4.Def_RP_EtCompact_GenFrac`: S4-EtCompact, part 49: the generic point as an `A`-algebra (F4c of plan v5)
--   * `S4.Def_RP_EtCompact_Obs`: S4-EtCompact, part 50: the Galois obstruction of a lift (F5 of plan v5)
--   * `S4.Def_RP_EtCompact_GalLift`: S4-EtCompact, part 44: lifting sections over a field point through Galois-fixed stalk elements (GM1)
--   * `S4.Def_RP_EtCompact_KumEt`: S4-EtCompact, part 43: Kummer covers and local factorisation (curve core v4, algebra bricks LT/LF)
--   * `S4.Def_RP_EtCompact_LT`: S4-EtCompact, part 51: local triviality of Kummer-unit obstructions (F6 of plan v5)
--   * `S4.Def_RP_EtCompact_Supp`: S4-EtCompact, part 52: global sections of `Λ`-morphisms and where they vanish (F7a of plan v5)
--   * `S4.Def_RP_EtCompact_KCe`: S4-EtCompact, part 53: the Kummer condition for elements (F7b of plan v5)
--   * `S4.Def_RP_EtCompact_Twist`: S4-EtCompact, part 45: every Galois character is an obstruction (P2 of curve core v4)
--   * `S4.Def_RP_EtCompact_SgUnit`: S4-EtCompact, part 42: `Λ_U ≅ g_*Λ_η` at the generic point (K5)
--   * `S4.Def_RP_EtCompact_GlobQ`: S4-EtCompact, part 54: the global Kummer section at a closed point (F7c of plan v5)
--   * `S4.Def_RP_EtCompact_LerayG`: S4-EtCompact, part 40: a two-row Leray argument for `g_*` (CC4, formal part)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_13

/-!
# Étale cohomology of the projective line, library file 14 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtSheaves_SpecPt`: S4-EtSheaves, part 29: geometric points of the spectrum of a field
* `S4.Def_RP_EtSheaves_SkyG`: S4-EtSheaves, part 28: the sheaf of equivariant maps on the fibres of a point
* `S4.Def_RP_EtSheaves_SpecEq`: S4-EtSheaves, part 30: Galois descent over a field
* `S4.Def_RP_EtSheaves_SpecHom`: S4-EtSheaves, part 31: morphisms of sheaves over a field are equivariant stalk maps
* `S4.Def_RP_Kummer_Gal`: S4-Kummer, part 1: Kummer characters for a subgroup of a Galois group (generic field theory)
* `S4.Def_RP_EtCompact_FibPt`: S4-EtCompact, part 48: fibre points of the generic geometric point (F4b of plan v5)
* `S4.Def_RP_EtCompact_GenFrac`: S4-EtCompact, part 49: the generic point as an `A`-algebra (F4c of plan v5)
* `S4.Def_RP_EtCompact_Obs`: S4-EtCompact, part 50: the Galois obstruction of a lift (F5 of plan v5)
* `S4.Def_RP_EtCompact_GalLift`: S4-EtCompact, part 44: lifting sections over a field point through Galois-fixed stalk elements (GM1)
* `S4.Def_RP_EtCompact_KumEt`: S4-EtCompact, part 43: Kummer covers and local factorisation (curve core v4, algebra bricks LT/LF)
* `S4.Def_RP_EtCompact_LT`: S4-EtCompact, part 51: local triviality of Kummer-unit obstructions (F6 of plan v5)
* `S4.Def_RP_EtCompact_Supp`: S4-EtCompact, part 52: global sections of `Λ`-morphisms and where they vanish (F7a of plan v5)
* `S4.Def_RP_EtCompact_KCe`: S4-EtCompact, part 53: the Kummer condition for elements (F7b of plan v5)
* `S4.Def_RP_EtCompact_Twist`: S4-EtCompact, part 45: every Galois character is an obstruction (P2 of curve core v4)
* `S4.Def_RP_EtCompact_SgUnit`: S4-EtCompact, part 42: `Λ_U ≅ g_*Λ_η` at the generic point (K5)
* `S4.Def_RP_EtCompact_GlobQ`: S4-EtCompact, part 54: the global Kummer section at a closed point (F7c of plan v5)
* `S4.Def_RP_EtCompact_LerayG`: S4-EtCompact, part 40: a two-row Leray argument for `g_*` (CC4, formal part)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtSheaves_SpecPt =====
section

/-!
# S4-EtSheaves, part 29: geometric points of the spectrum of a field

Let `X` be a scheme with `X.fromSpecResidueField x0` an isomorphism ("`X = Spec κ(x0)`"), `Ω` the separable closure
of `κ(x0)` and `Γ = Gal(Ω/κ(x0))`, acting on the fibre functor of `geomPtAt x0` by `a ↦ Spec σ ≫ a` (`galAct`).
For an etale `X`-scheme `Spec R` with `R` a field, `Γ` acts transitively on the fibre (`fiber_transitive`: lifts are
`κ(x0)`-embeddings `R → Ω`, which differ by an automorphism of the normal extension `Ω`). Every fibre element over `U`
comes from the residue-field object `Spec κ(u) → U` (`exists_nbhd`), and a finite subextension `E ⊆ Ω` gives the
etale object `specObj E` whose base point `specPt E` is fixed only by the fixing subgroup of `E`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

theorem galAct_mul {X : Scheme.{u}} (x : X) (σ τ : Gal x) (U : X.Etale) (a : (geomPtAt x).point.fiber.obj U) :
    (galAct x (σ * τ)).app U a = (galAct x σ).app U ((galAct x τ).app U a) := by
  refine fiber_ext _ ?_
  rw [galAct_left, galAct_left, galAct_left, galSpec_mul]
  exact Category.assoc _ _ _

theorem galAct_one {X : Scheme.{u}} (x : X) (U : X.Etale) (a : (geomPtAt x).point.fiber.obj U) :
    (galAct x 1).app U a = a := by
  refine fiber_ext _ ?_
  rw [galAct_left, galSpec_one]
  exact Category.id_comp _

variable {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)]

/-- A lift `Spec ψ` of `geomPtAt x0` through `Spec φ ≫ (Spec κ(x0) ≅ X)` is a `κ(x0)`-embedding: `φ ≫ ψ = ι`. -/
theorem lift_eq {R : CommRingCat.{u}} (φ : X.residueField x0 ⟶ R)
    (ψ : R ⟶ CommRingCat.of (SeparableClosure (X.residueField x0)))
    (h : Spec.map ψ ≫ Spec.map φ ≫ X.fromSpecResidueField x0 = (geomPtAt x0).pt) :
    φ ≫ ψ = CommRingCat.ofHom (algebraMap (X.residueField x0) (SeparableClosure (X.residueField x0))) := by
  apply Spec.map_injective
  apply (cancel_mono (X.fromSpecResidueField x0)).1
  rw [Spec.map_comp, Category.assoc]
  exact h

/-- **Transitivity**: `Gal(Ω/κ(x0))` acts transitively on the fibre of an etale `Spec R → X`, `R` a field. -/
theorem fiber_transitive {L : Type u} [Field L] (h : Spec (CommRingCat.of L) ⟶ X) (hh : Etale h)
    (b₁ b₂ : (geomPtAt x0).point.fiber.obj (MorphismProperty.Over.mk ⊤ h hh)) :
    ∃ σ : Gal x0, (galAct x0 σ).app _ b₁ = b₂ := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (h ≫ inv (X.fromSpecResidueField x0))
  have hφ' : Spec.map φ ≫ X.fromSpecResidueField x0 = h := by
    rw [hφ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  obtain ⟨ψ₁, hψ₁⟩ : ∃ ψ : CommRingCat.of L ⟶ CommRingCat.of (SeparableClosure (X.residueField x0)),
      Spec.map ψ = ((geomPtAt x0).liftOf b₁).left := Spec.map_surjective _
  obtain ⟨ψ₂, hψ₂⟩ : ∃ ψ : CommRingCat.of L ⟶ CommRingCat.of (SeparableClosure (X.residueField x0)),
      Spec.map ψ = ((geomPtAt x0).liftOf b₂).left := Spec.map_surjective _
  have e₁ := lift_eq x0 φ ψ₁ (by
    rw [hφ']; exact (congrArg (· ≫ h) hψ₁).trans (Over.w ((geomPtAt x0).liftOf b₁)))
  have e₂ := lift_eq x0 φ ψ₂ (by
    rw [hφ']; exact (congrArg (· ≫ h) hψ₂).trans (Over.w ((geomPtAt x0).liftOf b₂)))
  obtain ⟨σ, hσ⟩ := exists_algEquiv_comp (K := X.residueField x0) (L := L)
    (Ω := SeparableClosure (X.residueField x0)) φ.hom ψ₁.hom ψ₂.hom
    (congrArg CommRingCat.Hom.hom e₁) (congrArg CommRingCat.Hom.hom e₂)
  have key : galSpec x0 σ ≫ Spec.map ψ₁ = Spec.map ψ₂ := by
    rw [galSpec, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun t => hσ t))
  exact ⟨σ, fiber_ext _ ((congrArg (galSpec x0 σ ≫ ·) hψ₁).symm.trans (key.trans hψ₂))⟩

include x0 in
theorem etale_res (U : X.Etale) (u : U.left) : Etale (U.left.fromSpecResidueField u ≫ U.hom) := by
  haveI := isIso_fromSpecResidueField x0 (U.hom.base u)
  haveI := etale_residueFieldMap U.hom u
  have e : U.left.fromSpecResidueField u ≫ U.hom =
      Spec.map (U.hom.residueFieldMap u) ≫ X.fromSpecResidueField (U.hom.base u) :=
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (f := U.hom) (x := u)).symm
  rw [e]
  infer_instance

/-- **Residue-field neighbourhoods**: every fibre element `a` over `U` is the image of a fibre element `b` of an etale
`V ⟶ U` (namely `Spec κ(u) → U`) on whose fibre the Galois group acts transitively. -/
theorem exists_nbhd (U : X.Etale) (a : (geomPtAt x0).point.fiber.obj U) :
    ∃ (V : X.Etale) (g : V ⟶ U) (b : (geomPtAt x0).point.fiber.obj V),
      (geomPtAt x0).point.fiber.map g b = a ∧
      ∀ b' : (geomPtAt x0).point.fiber.obj V, ∃ σ : Gal x0, (galAct x0 σ).app V b = b' := by
  obtain ⟨⟨u, φ⟩, hp⟩ :=
    (Scheme.SpecToEquivOfField (geomPtAt x0).Ω U.left).symm.surjective ((geomPtAt x0).liftOf a).left
  have hp' : Spec.map φ ≫ U.left.fromSpecResidueField u = ((geomPtAt x0).liftOf a).left := hp
  have hw : Spec.map φ ≫ (U.left.fromSpecResidueField u ≫ U.hom) = (geomPtAt x0).pt := by
    rw [← Category.assoc, hp']
    exact Over.w ((geomPtAt x0).liftOf a)
  let V : X.Etale := MorphismProperty.Over.mk ⊤ (U.left.fromSpecResidueField u ≫ U.hom) (etale_res x0 U u)
  let g : V ⟶ U := MorphismProperty.Over.homMk (U.left.fromSpecResidueField u) rfl trivial
  let b : (geomPtAt x0).point.fiber.obj V :=
    (Over.homMk (Spec.map φ) hw : CategoryTheory.Over.mk (geomPtAt x0).pt ⟶ (Scheme.Etale.forget X).obj V)
  refine ⟨V, g, b, fiber_ext _ hp', fun b' =>
    fiber_transitive x0 (L := U.left.residueField u) (U.left.fromSpecResidueField u ≫ U.hom) (etale_res x0 U u) b b'⟩

variable (E : IntermediateField (X.residueField x0) (SeparableClosure (X.residueField x0)))
  [FiniteDimensional (X.residueField x0) E]

/-- The etale `X`-scheme `Spec E` of a finite subextension `E` of `Ω/κ(x0)`. -/
def specObj : X.Etale :=
  MorphismProperty.Over.mk ⊤ (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x0) E)) ≫
    X.fromSpecResidueField x0) (etale_specObj x0 E)

theorem specPt_w : Spec.map (CommRingCat.ofHom (E.val : E →+* SeparableClosure (X.residueField x0))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x0) E)) ≫ X.fromSpecResidueField x0 =
      (geomPtAt x0).pt := by
  have e : CommRingCat.ofHom (algebraMap (X.residueField x0) E) ≫
      CommRingCat.ofHom (E.val : E →+* SeparableClosure (X.residueField x0)) =
      CommRingCat.ofHom (algebraMap (X.residueField x0) (SeparableClosure (X.residueField x0))) := by
    ext r
    rfl
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ X.fromSpecResidueField x0) ((Spec.map_comp _ _).symm.trans (congrArg Spec.map e)))

/-- The base point of `specObj E`: the inclusion `E ⊆ Ω`. -/
def specPt : (geomPtAt x0).point.fiber.obj (specObj x0 E) :=
  (Over.homMk (Spec.map (CommRingCat.ofHom (E.val : E →+* SeparableClosure (X.residueField x0))))
    (specPt_w x0 E) : CategoryTheory.Over.mk (geomPtAt x0).pt ⟶ (Scheme.Etale.forget X).obj (specObj x0 E))

/-- The stabilizer of the base point `specPt E` lies in the fixing subgroup of `E`. -/
theorem mem_fixingSubgroup_of_galAct {σ : Gal x0} (h : (galAct x0 σ).app _ (specPt x0 E) = specPt x0 E) :
    σ ∈ E.fixingSubgroup := by
  have h1 := congrArg (fun a => ((geomPtAt x0).liftOf a).left) h
  change galSpec x0 σ ≫ Spec.map (CommRingCat.ofHom (E.val : E →+* SeparableClosure (X.residueField x0))) =
    Spec.map (CommRingCat.ofHom (E.val : E →+* SeparableClosure (X.residueField x0))) at h1
  rw [galSpec, ← Spec.map_comp] at h1
  have h2 := Spec.map_injective h1
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro t ht
  exact congrArg (fun g => g.hom ⟨t, ht⟩) h2

/-- Transitivity on the fibre of `specObj E`. -/
theorem specObj_transitive (b : (geomPtAt x0).point.fiber.obj (specObj x0 E)) :
    ∃ σ : Gal x0, (galAct x0 σ).app _ (specPt x0 E) = b :=
  fiber_transitive x0 (L := E) _ (etale_specObj x0 E) (specPt x0 E) b

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_SkyG =====
section

/-!
# S4-EtSheaves, part 28: the sheaf of equivariant maps on the fibres of a point

For a point `Φ` of the small etale site of `X`, a family `act σ` of endomorphisms of its fibre functor and a family
`ρ σ` of linear endomorphisms of a module `M`, the maps `β : Φ.fiber.obj U → M` with `β (act σ a) = ρ σ (β a)` form a
sheaf `skyG` (glued along the jointly surjective fibres of a covering, well defined because `Φ.fiber.Elements` is
cofiltered). Evaluation at a fibre element gives `evG : (skyG)_Φ ⟶ M`, and a sheaf whose germs are equivariant maps to
`skyG` by `unitG` with `evG ∘ (unitG)_Φ = id`. Used for Galois descent over a field (O9).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {X : Scheme.{u}} (Φ : GrothendieckTopology.Point.{u} (Scheme.smallEtaleTopology X)) {Γ : Type u}
  (act : Γ → (Φ.fiber ⟶ Φ.fiber)) (Λ : Type u) [CommRing Λ] {M : Type u} [AddCommGroup M] [Module Λ M]
  (ρ : Γ → (M →ₗ[Λ] M))

/-- Equivariant maps on the fibre over `U`. -/
def eqSub (U : X.Etale) : Submodule Λ (Φ.fiber.obj U → M) where
  carrier := {β | ∀ (σ : Γ) (a : Φ.fiber.obj U), β ((act σ).app U a) = ρ σ (β a)}
  add_mem' {β γ} hβ hγ σ a := by
    simp only [Set.mem_setOf_eq] at hβ hγ
    simp only [Pi.add_apply, hβ σ a, hγ σ a, map_add]
  zero_mem' σ a := by simp
  smul_mem' c β hβ σ a := by
    simp only [Set.mem_setOf_eq] at hβ
    simp only [Pi.smul_apply, hβ σ a, map_smul]

theorem mem_eqSub {U : X.Etale} (β : Φ.fiber.obj U → M) :
    β ∈ eqSub Φ act Λ ρ U ↔ ∀ (σ : Γ) (a : Φ.fiber.obj U), β ((act σ).app U a) = ρ σ (β a) := Iff.rfl

/-- Restriction of equivariant maps along `f : U ⟶ V`. -/
def eqRes {U V : X.Etale} (f : U ⟶ V) : eqSub Φ act Λ ρ V →ₗ[Λ] eqSub Φ act Λ ρ U where
  toFun β := ⟨β.1 ∘ Φ.fiber.map f, (mem_eqSub Φ act Λ ρ _).2 fun σ a => by
    change β.1 (Φ.fiber.map f ((act σ).app U a)) = ρ σ (β.1 (Φ.fiber.map f a))
    rw [← NatTrans.naturality_apply]
    exact (mem_eqSub Φ act Λ ρ _).1 β.2 σ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The presheaf of equivariant maps. -/
def skyPre : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ where
  obj U := ModuleCat.of Λ (eqSub Φ act Λ ρ U.unop)
  map f := ModuleCat.ofHom (eqRes Φ act Λ ρ f.unop)
  map_id U := ModuleCat.hom_ext (LinearMap.ext fun β => Subtype.ext (funext fun a =>
    congrArg β.1 (FunctorToTypes.map_id_apply Φ.fiber a)))
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext fun β => Subtype.ext (funext fun a =>
    congrArg β.1 (FunctorToTypes.map_comp_apply Φ.fiber g.unop f.unop a)))

theorem isSheaf_skyPre : Presheaf.IsSheaf (Scheme.smallEtaleTopology X) (skyPre Φ act Λ ρ) := by
  refine Presheaf.isSheaf_of_isSheaf_comp _ _ (forget (ModuleCat.{u} Λ) ⋙ uliftFunctor.{u + 1, u})
    ((isSheaf_iff_isSheaf_of_type (J := Scheme.smallEtaleTopology X)
      (P := skyPre Φ act Λ ρ ⋙ forget (ModuleCat.{u} Λ) ⋙ uliftFunctor.{u + 1, u})).2 ?_)
  intro U R hR x hx
  have W : ∀ {V₁ V₂ : X.Etale} (f₁ : V₁ ⟶ U) (f₂ : V₂ ⟶ U) (h₁ : R f₁) (h₂ : R f₂)
      (b₁ : Φ.fiber.obj V₁) (b₂ : Φ.fiber.obj V₂), Φ.fiber.map f₁ b₁ = Φ.fiber.map f₂ b₂ →
        (x f₁ h₁).down.1 b₁ = (x f₂ h₂).down.1 b₂ := by
    intro V₁ V₂ f₁ f₂ h₁ h₂ b₁ b₂ e
    let e₁ : Φ.fiber.elementsMk V₁ b₁ ⟶ Φ.fiber.elementsMk U (Φ.fiber.map f₂ b₂) :=
      CategoryOfElements.homMk _ _ f₁ e
    let e₂ : Φ.fiber.elementsMk V₂ b₂ ⟶ Φ.fiber.elementsMk U (Φ.fiber.map f₂ b₂) :=
      CategoryOfElements.homMk _ _ f₂ rfl
    obtain ⟨w, g₁, g₂, hg⟩ := IsCofiltered.cospan e₁ e₂
    have hv : g₁.1 ≫ f₁ = g₂.1 ≫ f₂ := congrArg Subtype.val hg
    have hc := congrArg (fun t => t.down.1 w.2) (hx g₁.1 g₂.1 h₁ h₂ hv)
    change (x f₁ h₁).down.1 (Φ.fiber.map g₁.1 w.2) = (x f₂ h₂).down.1 (Φ.fiber.map g₂.1 w.2) at hc
    rwa [g₁.2, g₂.2] at hc
  choose V f hf b hb using fun a : Φ.fiber.obj U => Φ.jointly_surjective R hR a
  let β : Φ.fiber.obj U → M := fun a => (x (f a) (hf a)).down.1 (b a)
  have hβ : ∀ {V' : X.Etale} (g : V' ⟶ U) (hg : R g) (c : Φ.fiber.obj V'),
      β (Φ.fiber.map g c) = (x g hg).down.1 c := fun g hg c => W (f _) g (hf _) hg (b _) c (hb _)
  have hmem : β ∈ eqSub Φ act Λ ρ U := (mem_eqSub Φ act Λ ρ _).2 fun σ a => by
    have e1 : (act σ).app U a = Φ.fiber.map (f a) ((act σ).app (V a) (b a)) := by
      rw [← NatTrans.naturality_apply, hb a]
    rw [e1, hβ (f a) (hf a)]
    exact (mem_eqSub Φ act Λ ρ _).1 (x (f a) (hf a)).down.2 σ _
  refine ⟨ULift.up ⟨β, hmem⟩, fun Y g hg => ?_, fun t ht => ?_⟩
  · apply ULift.ext
    apply Subtype.ext
    funext c
    exact hβ g hg c
  · apply ULift.ext
    apply Subtype.ext
    funext a
    change t.down.1 a = β a
    calc t.down.1 a = t.down.1 (Φ.fiber.map (f a) (b a)) := by rw [hb a]
      _ = (x (f a) (hf a)).down.1 (b a) := congrArg (fun t => t.down.1 (b a)) (ht (f a) (hf a))

/-- **The sheaf of equivariant maps** `U ↦ {β : Φ.fiber.obj U → M | β ∘ act σ = ρ σ ∘ β}`. -/
def skyG : EtSh Λ X := ⟨skyPre Φ act Λ ρ, isSheaf_skyPre Φ act Λ ρ⟩

/-- Evaluation at a fibre element. -/
def evAt (U : X.Etale) (a : Φ.fiber.obj U) : eqSub Φ act Λ ρ U →ₗ[Λ] M where
  toFun β := β.1 a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation on the fibre: `germ_a β ↦ β a`. -/
def evG : Φ.sheafFiber.obj (skyG Φ act Λ ρ) ⟶ ModuleCat.of Λ M :=
  Φ.presheafFiberDesc (P := skyPre Φ act Λ ρ) (fun U a => ModuleCat.ofHom (evAt Φ act Λ ρ U a))
    (fun _ _ _ _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

theorem germ_evG (U : X.Etale) (a : Φ.fiber.obj U) :
    Φ.toPresheafFiber U a (skyPre Φ act Λ ρ) ≫ evG Φ act Λ ρ = ModuleCat.ofHom (evAt Φ act Λ ρ U a) :=
  Φ.toPresheafFiber_presheafFiberDesc _ _ U a

theorem evG_germ (U : X.Etale) (a : Φ.fiber.obj U) (β : eqSub Φ act Λ ρ U) :
    (evG Φ act Λ ρ).hom ((Φ.toPresheafFiber U a (skyPre Φ act Λ ρ)).hom β) = β.1 a :=
  congrArg (fun g => g.hom β) (germ_evG Φ act Λ ρ U a)

section Unit

variable (F : EtSh Λ X)
  (ρF : Γ → ((Φ.sheafFiber (A := ModuleCat.{u} Λ)).obj F →ₗ[Λ] (Φ.sheafFiber (A := ModuleCat.{u} Λ)).obj F))
  (hF : ∀ (σ : Γ) (U : X.Etale) (a : Φ.fiber.obj U) (z : F.obj.obj (op U)),
    (Φ.toPresheafFiber U ((act σ).app U a) F.obj).hom z = ρF σ ((Φ.toPresheafFiber U a F.obj).hom z))

/-- Germs of a section, as an equivariant map. -/
def germAt (U : X.Etale) : F.obj.obj (op U) →ₗ[Λ] eqSub Φ act Λ ρF U where
  toFun z := ⟨fun a => (Φ.toPresheafFiber U a F.obj).hom z, (mem_eqSub Φ act Λ ρF _).2 fun σ a => hF σ U a z⟩
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => map_smul _ _ _)

/-- **The unit** `F ⟶ skyG(F_Φ)`: a section goes to its germs. -/
def unitG : F ⟶ skyG Φ act Λ ρF :=
  ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom (germAt Φ act Λ F ρF hF U.unop)
      naturality := fun U V f => ModuleCat.hom_ext (LinearMap.ext fun z => Subtype.ext (funext fun a =>
        congrArg (fun g => g.hom z) (Φ.toPresheafFiber_w f.unop a F.obj))) }

/-- `evG ∘ (unitG)_Φ = id`: the germ of the germ map is evaluation. -/
theorem unitG_evG_apply (v : (Φ.sheafFiber (A := ModuleCat.{u} Λ)).obj F) :
    (evG Φ act Λ ρF).hom ((Φ.sheafFiber.map (unitG Φ act Λ F ρF hF)).hom v) = v := by
  obtain ⟨U, a, z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := F.obj) v
  change (evG Φ act Λ ρF).hom ((Φ.toPresheafFiber U a F.obj ≫
    Φ.presheafFiber.map (unitG Φ act Λ F ρF hF).hom).hom z) = _
  rw [Φ.toPresheafFiber_naturality]
  exact evG_germ Φ act Λ ρF U a _

end Unit

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_SpecEq =====
section

/-!
# S4-EtSheaves, part 30: Galois descent over a field

For `X` with `X.fromSpecResidueField x0` an isomorphism, evaluation `evG` on the stalk of the sheaf of
`Gal(Ω/κ(x0))`-equivariant maps is injective (`evG_injective`: an equivariant map vanishing at one point of a
residue-field neighbourhood vanishes on its whole, transitive, fibre). Hence the descent unit
`descUnit F : F ⟶ skyG(F_x̄)` (a section goes to its germs) is an isomorphism (`isIso_descUnit`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] (Λ : Type u) [CommRing Λ]

section Ev

variable {M : Type u} [AddCommGroup M] [Module Λ M] (ρ : Gal x0 → (M →ₗ[Λ] M))

/-- **Over a field, evaluation on the stalk of the sheaf of equivariant maps is injective.** -/
theorem evG_injective : Function.Injective (evG (geomPtAt x0).point (galAct x0) Λ ρ).hom := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  obtain ⟨U, a, β, rfl⟩ := (geomPtAt x0).point.toPresheafFiber_jointly_surjective
    (P := skyPre (geomPtAt x0).point (galAct x0) Λ ρ) w
  have hw' : β.1 a = 0 := (evG_germ _ _ Λ ρ U a β).symm.trans hw
  obtain ⟨V, g, b, hb, htr⟩ := exists_nbhd x0 U a
  have hz : ((skyPre (geomPtAt x0).point (galAct x0) Λ ρ).map g.op).hom β = 0 := by
    apply Subtype.ext
    funext b'
    obtain ⟨σ, rfl⟩ := htr b'
    change β.1 ((geomPtAt x0).point.fiber.map g ((galAct x0 σ).app V b)) = 0
    rw [← NatTrans.naturality_apply, hb, (mem_eqSub _ _ _ _ _).1 β.2 σ a, hw', map_zero]
  rw [← hb, ← (geomPtAt x0).point.toPresheafFiber_w g b]
  change ((geomPtAt x0).point.toPresheafFiber V b (skyPre (geomPtAt x0).point (galAct x0) Λ ρ)).hom
    (((skyPre (geomPtAt x0).point (galAct x0) Λ ρ).map g.op).hom β) = 0
  rw [hz, map_zero]

end Ev

variable (F : EtSh Λ X)

/-- `σ ∈ Gal(Ω/κ(x))` moves germs along `galAct`. -/
theorem galRep_germ (x : X) (σ : Gal x) (U : X.Etale) (a : (geomPtAt x).point.fiber.obj U)
    (z : F.obj.obj (op U)) :
    ((geomPtAt x).point.toPresheafFiber U ((galAct x σ).app U a) F.obj).hom z =
      galRep Λ F x σ (((geomPtAt x).point.toPresheafFiber U a F.obj).hom z) :=
  (GeomPt.stalkAut_toPresheafFiber (geomPtAt x) Λ (galSpec x σ) (galSpec_comp x σ) F U a z).symm

/-- **The Galois descent unit** `F ⟶ skyG(F_x̄)`: a section goes to its (equivariant) germs. -/
def descUnit : F ⟶ skyG (geomPtAt x0).point (galAct x0) Λ (fun σ => galRep Λ F x0 σ) :=
  unitG (geomPtAt x0).point (galAct x0) Λ F (fun σ => galRep Λ F x0 σ) (galRep_germ Λ F x0)

/-- **Galois descent over a field**: `F ≅ skyG(F_x̄)`. -/
theorem isIso_descUnit : IsIso (descUnit x0 Λ F) := by
  haveI := subsingleton_of_isIso x0
  rw [isIso_iff_stalk Λ]
  intro x
  rw [Subsingleton.elim x x0]
  have hinj := evG_injective x0 Λ (fun σ => galRep Λ F x0 σ)
  have hl := unitG_evG_apply (geomPtAt x0).point (galAct x0) Λ F (fun σ => galRep Λ F x0 σ)
    (galRep_germ Λ F x0)
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨Function.LeftInverse.injective hl, fun w => ⟨_, hinj (hl _)⟩⟩

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_SpecHom =====
section

/-!
# S4-EtSheaves, part 31: morphisms of sheaves over a field are equivariant stalk maps

An equivariant linear map `f : M → N` gives a morphism `skyMap f : skyG(M) ⟶ skyG(N)` of sheaves of equivariant maps
(post-composition), compatible with evaluation (`skyMap_evG_apply`). Over a field (`X ≅ Spec κ(x0)`) the descent unit
is natural (`descUnit_natural`), its inverse on stalks is evaluation (`inv_descUnit_apply`), and taking stalks is a
bijection from sheaf morphisms `F ⟶ G` onto `Gal(Ω/κ(x0))`-equivariant maps `F_x̄ → G_x̄` (`specField_homEquiv`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

section Map

variable {X : Scheme.{u}} (Φ : GrothendieckTopology.Point.{u} (Scheme.smallEtaleTopology X)) {Γ : Type u}
  (act : Γ → (Φ.fiber ⟶ Φ.fiber)) (Λ : Type u) [CommRing Λ] {M N : Type u} [AddCommGroup M] [Module Λ M]
  [AddCommGroup N] [Module Λ N] (ρ : Γ → (M →ₗ[Λ] M)) (ρN : Γ → (N →ₗ[Λ] N)) (f : M →ₗ[Λ] N)
  (hf : ∀ σ : Γ, f ∘ₗ ρ σ = ρN σ ∘ₗ f)

/-- Post-composition with an equivariant `f` on equivariant maps over `U`. -/
def eqMap (U : X.Etale) : eqSub Φ act Λ ρ U →ₗ[Λ] eqSub Φ act Λ ρN U where
  toFun β := ⟨f ∘ β.1, (mem_eqSub Φ act Λ ρN _).2 fun σ a => by
    change f (β.1 ((act σ).app U a)) = ρN σ (f (β.1 a))
    rw [(mem_eqSub Φ act Λ ρ _).1 β.2 σ a]
    exact LinearMap.congr_fun (hf σ) (β.1 a)⟩
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => map_smul _ _ _)

/-- **Functoriality of `skyG`** in equivariant maps `f : M → N`. -/
def skyMap : skyG Φ act Λ ρ ⟶ skyG Φ act Λ ρN :=
  ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom (eqMap Φ act Λ ρ ρN f hf U.unop)
      naturality := fun _ _ _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl) }

/-- `evG ∘ (skyMap f)_Φ = f ∘ evG`. -/
theorem skyMap_evG_apply (v : (Φ.sheafFiber (A := ModuleCat.{u} Λ)).obj (skyG Φ act Λ ρ)) :
    (evG Φ act Λ ρN).hom ((Φ.sheafFiber.map (skyMap Φ act Λ ρ ρN f hf)).hom v) =
      f ((evG Φ act Λ ρ).hom v) := by
  obtain ⟨U, a, β, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := (skyG Φ act Λ ρ).obj) v
  change (evG Φ act Λ ρN).hom ((Φ.toPresheafFiber U a (skyG Φ act Λ ρ).obj ≫
    Φ.presheafFiber.map (skyMap Φ act Λ ρ ρN f hf).hom).hom β) = _
  rw [Φ.toPresheafFiber_naturality]
  refine (evG_germ Φ act Λ ρN U a _).trans ?_
  exact congrArg f (evG_germ Φ act Λ ρ U a β).symm

end Map

variable {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] (Λ : Type u) [CommRing Λ]

instance isIso_descUnit' (F : EtSh Λ X) : IsIso (descUnit x0 Λ F) := isIso_descUnit x0 Λ F

omit [IsIso (X.fromSpecResidueField x0)] in
/-- `evG ∘ (descUnit F)_x̄ = id`. -/
theorem descUnit_evG (F : EtSh Λ X) (v : stalk Λ F x0) :
    (evG (geomPtAt x0).point (galAct x0) Λ (fun σ => galRep Λ F x0 σ)).hom
      ((((geomPtAt x0).stalkF Λ).map (descUnit x0 Λ F)).hom v) = v :=
  unitG_evG_apply (geomPtAt x0).point (galAct x0) Λ F (fun σ => galRep Λ F x0 σ) (galRep_germ Λ F x0) v

/-- On stalks, the inverse of the descent unit is evaluation. -/
theorem inv_descUnit_apply (F : EtSh Λ X)
    (w : ((geomPtAt x0).stalkF Λ).obj (skyG (geomPtAt x0).point (galAct x0) Λ (fun σ => galRep Λ F x0 σ))) :
    (((geomPtAt x0).stalkF Λ).map (inv (descUnit x0 Λ F))).hom w =
      (evG (geomPtAt x0).point (galAct x0) Λ (fun σ => galRep Λ F x0 σ)).hom w := by
  have e : ((geomPtAt x0).stalkF Λ).map (inv (descUnit x0 Λ F)) ≫
      ((geomPtAt x0).stalkF Λ).map (descUnit x0 Λ F) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
  have h1 : (((geomPtAt x0).stalkF Λ).map (descUnit x0 Λ F)).hom
      ((((geomPtAt x0).stalkF Λ).map (inv (descUnit x0 Λ F))).hom w) = w :=
    congrArg (fun g => g.hom w) e
  have hl := descUnit_evG x0 Λ F ((((geomPtAt x0).stalkF Λ).map (inv (descUnit x0 Λ F))).hom w)
  rw [h1] at hl
  exact hl.symm

/-- **Naturality of the descent unit**: `φ ≫ descUnit G = descUnit F ≫ skyMap φ_x̄`. -/
theorem descUnit_natural {F G : EtSh Λ X} (φ : F ⟶ G) :
    φ ≫ descUnit x0 Λ G = descUnit x0 Λ F ≫ skyMap (geomPtAt x0).point (galAct x0) Λ
      (fun σ => galRep Λ F x0 σ) (fun σ => galRep Λ G x0 σ) (((geomPtAt x0).stalkF Λ).map φ).hom
      (galRep_natural Λ φ x0) := by
  have := subsingleton_of_isIso x0
  refine hom_ext_stalk Λ fun x => ?_
  rw [Subsingleton.elim x x0, Functor.map_comp, Functor.map_comp]
  refine ModuleCat.hom_ext (LinearMap.ext fun v => ?_)
  have hinj := evG_injective x0 Λ (fun σ => galRep Λ G x0 σ)
  apply hinj
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [descUnit_evG]
  refine Eq.trans ?_ (skyMap_evG_apply (geomPtAt x0).point (galAct x0) Λ _ _ _ _ _).symm
  exact congrArg _ (descUnit_evG x0 Λ F v).symm

/-- **Sheaves over a field, full faithfulness**: morphisms `F ⟶ G` are the `Gal(Ω/κ(x0))`-equivariant maps
`F_x̄ → G_x̄` of stalks. -/
def specField_homEquiv (F G : EtSh Λ X) :
    (F ⟶ G) ≃ {f : stalk Λ F x0 →ₗ[Λ] stalk Λ G x0 //
      ∀ σ : Gal x0, f ∘ₗ galRep Λ F x0 σ = galRep Λ G x0 σ ∘ₗ f} where
  toFun φ := ⟨(((geomPtAt x0).stalkF Λ).map φ).hom, galRep_natural Λ φ x0⟩
  invFun f := descUnit x0 Λ F ≫ skyMap (geomPtAt x0).point (galAct x0) Λ
    (fun σ => galRep Λ F x0 σ) (fun σ => galRep Λ G x0 σ) f.1 f.2 ≫ inv (descUnit x0 Λ G)
  left_inv φ := by
    change descUnit x0 Λ F ≫ skyMap (geomPtAt x0).point (galAct x0) Λ
      (fun σ => galRep Λ F x0 σ) (fun σ => galRep Λ G x0 σ) (((geomPtAt x0).stalkF Λ).map φ).hom
      (galRep_natural Λ φ x0) ≫ inv (descUnit x0 Λ G) = φ
    rw [← Category.assoc, ← descUnit_natural, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  right_inv f := by
    apply Subtype.ext
    refine LinearMap.ext fun v => ?_
    change (((geomPtAt x0).stalkF Λ).map (descUnit x0 Λ F ≫ skyMap (geomPtAt x0).point (galAct x0) Λ
      (fun σ => galRep Λ F x0 σ) (fun σ => galRep Λ G x0 σ) f.1 f.2 ≫ inv (descUnit x0 Λ G))).hom v = f.1 v
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [inv_descUnit_apply]
    refine (skyMap_evG_apply (geomPtAt x0).point (galAct x0) Λ _ _ _ _ _).trans ?_
    exact congrArg f.1 (descUnit_evG x0 Λ F v)

theorem specField_homEquiv_apply (F G : EtSh Λ X) (φ : F ⟶ G) :
    (specField_homEquiv x0 Λ F G φ).1 = (((geomPtAt x0).stalkF Λ).map φ).hom := rfl

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_Kummer_Gal =====
section

/-!
# S4-Kummer, part 1: Kummer characters for a subgroup of a Galois group (generic field theory)

Setting: fields `K ⊆ E`, ANY subgroup `Γ ≤ Gal(E/K)` (later `π₁(U ⊗ F̄) ≤ π₁(U)`, with `E = K_U`), `N ≠ 0` and a
primitive `N`-th root of unity `ζ ∈ E` fixed by `Γ`.

* `epow ζ k = ζ ^ k` for `k : ZMod N`, `dlog` its inverse on `μ_N`;
* `rad Γ N`: the Kummer radicals, units `α` with `α ^ N` fixed by `Γ`;
* `kchar hζ α : Γ → ZMod N`, `σ α = ζ ^ (kchar α σ) α` (`kchar_spec`);
* `kchar_mul` / `kchar_mul_left`: additive in `σ` and in `α`; `kchar_eq_zero_iff`: `kchar α = 0 ↔ Γ fixes α`;
* `isLocallyConstant_kchar` (`E/K` integral, Krull topology);
* `exists_kchar_eq`: EVERY locally constant additive character `Γ → ZMod N` is a Kummer character (Hilbert 90 at a
  finite level, by Dedekind's independence of the finitely many `K`-embeddings `L₁ → E`; no normality needed);
* `kchar_conj`: equivariance, `kchar (φ α) σ = w * kchar α (φ⁻¹ σ φ)` when `φ ζ = ζ ^ w` and `φ` normalises `Γ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

noncomputable section

/-! ## Powers of `ζ` indexed by `ZMod N` and the discrete logarithm -/

section DLog

variable {E : Type} [Field E] {N : ℕ} [NeZero N] {ζ : E}

end DLog

/-! ## Kummer radicals and Kummer characters -/

section Radicals

variable {K E : Type} [Field K] [Field E] [Algebra K E] (Γ : Subgroup (E ≃ₐ[K] E)) (N : ℕ)

theorem fixUnits_le_rad : fixUnits Γ ≤ rad Γ N := by
  intro α hα σ hσ
  rw [map_pow, hα σ hσ]

variable {Γ N}

variable [NeZero N] {ζ : E} (hζ : IsPrimitiveRoot ζ N)

variable (hζΓ : ∀ σ ∈ Γ, σ ζ = ζ)
include hζΓ

/-- `kchar α` is a homomorphism `Γ → ZMod N`. -/
theorem kchar_mul {α : Eˣ} (hα : α ∈ rad Γ N) (σ τ : Γ) :
    kchar hζ α (σ * τ) = kchar hζ α σ + kchar hζ α τ := by
  rw [kchar_eq_iff hζ hα, epow_add hζ]
  have e : ((σ * τ : Γ) : E ≃ₐ[K] E) (α : E) = (σ : E ≃ₐ[K] E) ((τ : E ≃ₐ[K] E) (α : E)) := rfl
  rw [e, kchar_spec hζ hα τ, map_mul, kchar_spec hζ hα σ, map_epow (hζΓ σ σ.2)]
  ring

theorem kchar_one {α : Eˣ} (hα : α ∈ rad Γ N) : kchar hζ α (1 : Γ) = 0 := by
  have h := kchar_mul hζ hζΓ hα 1 1
  rw [mul_one] at h
  linear_combination -h

end Radicals

section Radicals2

variable {K E : Type} [Field K] [Field E] [Algebra K E] {Γ : Subgroup (E ≃ₐ[K] E)} {N : ℕ} [NeZero N]
  {ζ : E} (hζ : IsPrimitiveRoot ζ N)

/-- `kchar` is additive in the radical. -/
theorem kchar_mul_left {α β : Eˣ} (hα : α ∈ rad Γ N) (hβ : β ∈ rad Γ N) (σ : Γ) :
    kchar hζ (α * β) σ = kchar hζ α σ + kchar hζ β σ := by
  rw [kchar_eq_iff hζ ((rad Γ N).mul_mem hα hβ), epow_add hζ, Units.val_mul, map_mul, kchar_spec hζ hα σ,
    kchar_spec hζ hβ σ]
  ring

theorem kchar_of_fix {α : Eˣ} (hα : α ∈ fixUnits Γ) (σ : Γ) : kchar hζ α σ = 0 :=
  (kchar_eq_zero_iff hζ (fixUnits_le_rad Γ N hα)).2 hα σ

/-- For `E/K` integral, `σ ↦ σ x` is locally constant on `Gal(E/K)` (Krull topology). -/
theorem isLocallyConstant_apply [Algebra.IsIntegral K E] (x : E) :
    IsLocallyConstant (fun σ : E ≃ₐ[K] E => σ x) := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro y
  rw [isOpen_iff_mem_nhds]
  intro σ₀ hσ₀
  have hσ₀' : σ₀ x = y := hσ₀
  have hS : IsOpen (MulAction.stabilizer (E ≃ₐ[K] E) x : Set (E ≃ₐ[K] E)) := stabilizer_isOpen_of_isIntegral x
  have hT : IsOpen ((fun τ => σ₀ * τ) '' (MulAction.stabilizer (E ≃ₐ[K] E) x : Set (E ≃ₐ[K] E))) :=
    isOpenMap_mul_left σ₀ _ hS
  refine Filter.mem_of_superset (hT.mem_nhds ⟨1, (MulAction.stabilizer (E ≃ₐ[K] E) x).one_mem, mul_one σ₀⟩) ?_
  rintro _ ⟨τ, hτ, rfl⟩
  have hτ' : τ x = x := hτ
  show (σ₀ * τ) x = y
  rw [AlgEquiv.mul_apply, hτ', hσ₀']

theorem isLocallyConstant_kchar [Algebra.IsIntegral K E] (α : Eˣ) : IsLocallyConstant (kchar hζ (Γ := Γ) α) := by
  have h1 : IsLocallyConstant (fun σ : Γ => (σ : E ≃ₐ[K] E) (α : E)) :=
    (isLocallyConstant_apply (α : E)).comp_continuous continuous_subtype_val
  exact h1.comp (fun y => dlog hζ (y / α))

/-! ## Surjectivity: every locally constant character is a Kummer character (Hilbert 90) -/

end Radicals2

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_EtCompact_FibPt =====
section

/-!
# S4-EtCompact, part 48: fibre points of the generic geometric point (F4b of plan v5)

`x : X`, `x̄ = geomPtAt x` with `Ω = κ(x)^sep`, `W : X.Etale`, `a` a point of the fibre of `x̄` over `W`.

* `exists_conj`: two embeddings of a field `L/F` into a normal `Ω/F` are conjugate under `Gal(Ω/F)`;
* **`exists_galAct_eq`**: if `W` has a single point, `Gal x` acts transitively on the fibre over `W`
  (a fibre point is a point `u ∈ W` and a `κ(x)`-embedding `κ(u) → Ω`, `SpecToEquivOfField`);
* for `W = g^* V` (`g : X ⟶ U`) and `e : V ⟶ Spec B` a monomorphism: `phi x g V e a : B →+* Ω`, the ring map of
  `Spec Ω → W → V → Spec B`; `phi_galAct`: `phi (σ a) = σ ∘ phi a`; **`galAct_eq_of_phi`**: `σ ∘ phi a = phi a`
  implies `σ a = a`; `phi_comp`: on `B`'s structure map, `phi a` is the ring map of `Spec Ω → X → U = Spec A`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.FibPt

open RamanujanPetersson.EtSheaves

/-- Two embeddings of a field into a normal extension are conjugate. -/
theorem exists_conj {F L Ω : Type*} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Normal F Ω]
    (f f' : L →ₐ[F] Ω) : ∃ τ : Ω ≃ₐ[F] Ω, ∀ t, τ (f t) = f' t := by
  let χ : f.fieldRange ≃ₐ[F] f'.fieldRange := f.equivFieldRange.symm.trans f'.equivFieldRange
  refine ⟨χ.liftNormal Ω, fun t => ?_⟩
  have h := AlgEquiv.liftNormal_commutes χ Ω (f.equivFieldRange t)
  have e2 : χ (f.equivFieldRange t) = f'.equivFieldRange t := by
    simp only [χ, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  rw [e2] at h
  exact h

variable {X : Scheme.{u}} (x : X)

/-- **Transitivity**: over an etale `W` with a single point, `Gal x` acts transitively on the fibre of `x̄`. -/
theorem exists_galAct_eq {W : X.Etale} [Subsingleton W.left] (a a' : (geomPtAt x).point.fiber.obj W) :
    ∃ τ : Gal x, (galAct x τ).app W a = a' := by
  obtain ⟨⟨u, φ⟩, hp⟩ :=
    (Scheme.SpecToEquivOfField (geomPtAt x).Ω W.left).symm.surjective ((geomPtAt x).liftOf a).left
  obtain ⟨⟨u', φ'⟩, hp'⟩ :=
    (Scheme.SpecToEquivOfField (geomPtAt x).Ω W.left).symm.surjective ((geomPtAt x).liftOf a').left
  obtain rfl : u = u' := Subsingleton.elim _ _
  have hpA : Spec.map φ ≫ W.left.fromSpecResidueField u = ((geomPtAt x).liftOf a).left := hp
  have hpB : Spec.map φ' ≫ W.left.fromSpecResidueField u = ((geomPtAt x).liftOf a').left := hp'
  have hwA : ((geomPtAt x).liftOf a).left ≫ W.hom = (geomPtAt x).pt := Over.w ((geomPtAt x).liftOf a)
  have hwB : ((geomPtAt x).liftOf a').left ≫ W.hom = (geomPtAt x).pt := Over.w ((geomPtAt x).liftOf a')
  have keyA : (Scheme.SpecToEquivOfField (geomPtAt x).Ω X).symm
      ⟨W.hom.base u, W.hom.residueFieldMap u ≫ φ⟩ = (geomPtAt x).pt := by
    change Spec.map (W.hom.residueFieldMap u ≫ φ) ≫ X.fromSpecResidueField (W.hom.base u) = _
    rw [Spec.map_comp, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Category.assoc]
    exact (congrArg (· ≫ W.hom) hpA).trans hwA
  have keyB : (Scheme.SpecToEquivOfField (geomPtAt x).Ω X).symm
      ⟨W.hom.base u, W.hom.residueFieldMap u ≫ φ'⟩ = (geomPtAt x).pt := by
    change Spec.map (W.hom.residueFieldMap u ≫ φ') ≫ X.fromSpecResidueField (W.hom.base u) = _
    rw [Spec.map_comp, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Category.assoc]
    exact (congrArg (· ≫ W.hom) hpB).trans hwB
  have hpt : (Scheme.SpecToEquivOfField (geomPtAt x).Ω X) (geomPtAt x).pt =
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) (SeparableClosure (X.residueField x)))⟩ :=
    (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).apply_symm_apply _
  have k2A : (⟨W.hom.base u, W.hom.residueFieldMap u ≫ φ⟩ :
      Σ y : X, X.residueField y ⟶ CommRingCat.of (geomPtAt x).Ω) =
      (Scheme.SpecToEquivOfField (geomPtAt x).Ω X) (geomPtAt x).pt := by
    rw [← keyA, Equiv.apply_symm_apply]
  have k2B : (⟨W.hom.base u, W.hom.residueFieldMap u ≫ φ'⟩ :
      Σ y : X, X.residueField y ⟶ CommRingCat.of (geomPtAt x).Ω) =
      (Scheme.SpecToEquivOfField (geomPtAt x).Ω X) (geomPtAt x).pt := by
    rw [← keyB, Equiv.apply_symm_apply]
  have k3A := k2A.trans hpt
  have k3B := k2B.trans hpt
  obtain ⟨e, -⟩ := Scheme.SpecToEquivOfField_eq_iff.1 k3A
  have e' : W.hom.base u = x := e
  subst e'
  have hA : W.hom.residueFieldMap u ≫ φ = CommRingCat.ofHom (algebraMap (X.residueField (W.hom.base u))
      (SeparableClosure (X.residueField (W.hom.base u)))) := eq_of_heq (Sigma.mk.inj_iff.mp k3A).2
  have hB : W.hom.residueFieldMap u ≫ φ' = CommRingCat.ofHom (algebraMap (X.residueField (W.hom.base u))
      (SeparableClosure (X.residueField (W.hom.base u)))) := eq_of_heq (Sigma.mk.inj_iff.mp k3B).2
  let _ : Algebra (X.residueField (W.hom.base u)) (W.left.residueField u) :=
    (W.hom.residueFieldMap u).hom.toAlgebra
  let f : W.left.residueField u →ₐ[X.residueField (W.hom.base u)]
      SeparableClosure (X.residueField (W.hom.base u)) :=
    { toRingHom := φ.hom
      commutes' := fun r => congrArg (fun g => g.hom r) hA }
  let f' : W.left.residueField u →ₐ[X.residueField (W.hom.base u)]
      SeparableClosure (X.residueField (W.hom.base u)) :=
    { toRingHom := φ'.hom
      commutes' := fun r => congrArg (fun g => g.hom r) hB }
  obtain ⟨τ, hτ⟩ := exists_conj f f'
  refine ⟨τ, fiber_ext _ ?_⟩
  rw [galAct_left, ← hpA, ← hpB]
  have hc : φ ≫ CommRingCat.ofHom (τ : SeparableClosure (X.residueField (W.hom.base u)) →+*
      SeparableClosure (X.residueField (W.hom.base u))) = φ' := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    exact hτ t
  have hS : galSpec (W.hom.base u) τ ≫ Spec.map φ = Spec.map φ' :=
    (Spec.map_comp φ _).symm.trans (congrArg Spec.map hc)
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ W.left.fromSpecResidueField u) hS)

section Phi

variable {U : Scheme.{u}} (g : X ⟶ U) (V : U.Etale) {B : CommRingCat.{u}} (e : V.left ⟶ Spec B)

/-- The ring map `B → Ω` of `Spec Ω → g^* V → V → Spec B` at a fibre point `a`. -/
def phi (a : (geomPtAt x).point.fiber.obj ((etPull g).obj V)) : B ⟶ CommRingCat.of (geomPtAt x).Ω :=
  Spec.preimage (((geomPtAt x).liftOf a).left ≫ pullback.fst V.hom g ≫ e)

theorem map_phi (a : (geomPtAt x).point.fiber.obj ((etPull g).obj V)) :
    Spec.map (phi x g V e a) = ((geomPtAt x).liftOf a).left ≫ pullback.fst V.hom g ≫ e :=
  Spec.map_preimage _

/-- `phi (σ a) = σ ∘ phi a`. -/
theorem phi_galAct (σ : Gal x) (a : (geomPtAt x).point.fiber.obj ((etPull g).obj V)) :
    phi x g V e ((galAct x σ).app _ a) =
      phi x g V e a ≫ CommRingCat.ofHom (σ : SeparableClosure (X.residueField x) →+*
        SeparableClosure (X.residueField x)) := by
  apply Spec.map_injective
  refine (map_phi x g V e _).trans ?_
  refine (congrArg (· ≫ pullback.fst V.hom g ≫ e) (galAct_left x σ _ a)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (galSpec x σ ≫ ·) (map_phi x g V e a).symm).trans ?_
  exact Spec.map_comp _ _ |>.symm

theorem phi_galAct_apply (σ : Gal x) (a : (geomPtAt x).point.fiber.obj ((etPull g).obj V)) (c : B) :
    (phi x g V e ((galAct x σ).app _ a)).hom c = σ ((phi x g V e a).hom c) :=
  congrArg (fun f => f.hom c) (phi_galAct x g V e σ a)

/-- `galSpec σ ≫ L = L` for a lift `L` whose ring map to `B` is fixed by `σ`. -/
theorem galSpec_comp_eq [Mono e] (σ : Gal x) (L : Spec (CommRingCat.of (geomPtAt x).Ω) ⟶ pullback V.hom g)
    (hw : L ≫ pullback.snd V.hom g = (geomPtAt x).pt)
    (hc : Spec.preimage (L ≫ pullback.fst V.hom g ≫ e) ≫ CommRingCat.ofHom (σ : SeparableClosure
      (X.residueField x) →+* SeparableClosure (X.residueField x)) = Spec.preimage (L ≫ pullback.fst V.hom g ≫ e)) :
    galSpec x σ ≫ L = L := by
  have h1 : ((galSpec x σ ≫ L) ≫ pullback.fst V.hom g) ≫ e = (L ≫ pullback.fst V.hom g) ≫ e :=
    ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).trans
      ((congrArg (galSpec x σ ≫ ·) (Spec.map_preimage (L ≫ pullback.fst V.hom g ≫ e)).symm).trans
        ((Spec.map_comp _ _).symm.trans ((congrArg Spec.map hc).trans
          ((Spec.map_preimage _).trans (Category.assoc _ _ _).symm))))
  refine pullback.hom_ext ((cancel_mono e).1 h1) ?_
  exact (Category.assoc _ _ _).trans ((congrArg (galSpec x σ ≫ ·) hw).trans ((galSpec_comp x σ).trans hw.symm))

/-- **Stabiliser**: if `σ ∘ phi a = phi a` (and `e` is a monomorphism) then `σ` fixes `a`. -/
theorem galAct_eq_of_phi [Mono e] (σ : Gal x) (a : (geomPtAt x).point.fiber.obj ((etPull g).obj V))
    (h : ∀ c, σ ((phi x g V e a).hom c) = (phi x g V e a).hom c) : (galAct x σ).app _ a = a := by
  have hc : phi x g V e a ≫ CommRingCat.ofHom (σ : SeparableClosure (X.residueField x) →+*
      SeparableClosure (X.residueField x)) = phi x g V e a := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    exact h t
  exact fiber_ext _ ((galAct_left x σ _ a).trans
    (galSpec_comp_eq x g V e σ _ (Over.w ((geomPtAt x).liftOf a)) hc))

end Phi

/-- On the structure map of `B`, the ring map of a lift is the ring map of `Spec Ω → X → U = Spec A`. -/
theorem preimage_comp {B A : CommRingCat.{u}} {g : X ⟶ Spec A} {V : (Spec A).Etale} {e : V.left ⟶ Spec B}
    (φB : A ⟶ B) (he : e ≫ Spec.map φB = V.hom) (L : Spec (CommRingCat.of (geomPtAt x).Ω) ⟶ pullback V.hom g)
    (hw : L ≫ pullback.snd V.hom g = (geomPtAt x).pt) :
    φB ≫ Spec.preimage (L ≫ pullback.fst V.hom g ≫ e) = Spec.preimage ((geomPtAt x).pt ≫ g) := by
  apply Spec.map_injective
  refine (Spec.map_comp _ _).trans ?_
  refine (congrArg (· ≫ Spec.map φB) (Spec.map_preimage _)).trans ?_
  refine ((Category.assoc _ _ _).trans (congrArg (L ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (pullback.fst V.hom g ≫ ·) he)))).trans ?_
  refine (congrArg (L ≫ ·) pullback.condition).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ g) hw).trans ?_
  exact (Spec.map_preimage _).symm

theorem phi_comp {B A : CommRingCat.{u}} {g : X ⟶ Spec A} {V : (Spec A).Etale} {e : V.left ⟶ Spec B}
    (φB : A ⟶ B) (he : e ≫ Spec.map φB = V.hom) (a : (geomPtAt x).point.fiber.obj ((etPull g).obj V)) :
    φB ≫ phi x g V e a = Spec.preimage ((geomPtAt x).pt ≫ g) :=
  preimage_comp x φB he _ (Over.w ((geomPtAt x).liftOf a))

end RamanujanPetersson.EtCompact.FibPt

end

end

-- ===== S4.Def_RP_EtCompact_GenFrac =====
section

/-!
# S4-EtCompact, part 49: the generic point as an `A`-algebra (F4c of plan v5)

`A` a domain, `η` the generic point of `U = Spec A`, `Y = Spec κ(η)` with its point `x0 = ptOf η`,
`g : Y ⟶ U` (`= SgUnit.gη A`), `κ0 = κ(x0)`, `Ω = κ0^sep`.

* `botIso A : (⊥ : Ideal A).ResidueField ≃+* κ0`; instances `Algebra A κ0`, **`IsFractionRing A κ0`**,
  `Algebra A Ω`, `IsScalarTower A κ0 Ω`;
* `map_ptResidueIso_hom`, **`map_algebraMap`**: `Spec (A → κ0) = (Y → κ(x0)) ≫ g`;
* **`preimage_pt`**: the ring map of `x̄ ≫ g : Spec Ω → U` is `algebraMap A Ω`;
* **`phiA A V e he a : B →ₐ[A] Ω`**: `FibPt.phi` at a fibre point of `g^* V` as an `A`-algebra map.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.GenFrac

open RamanujanPetersson.EtSheaves

theorem map_ptResidueIso_hom {Y : Scheme.{0}} (y : Y) :
    Spec.map (ptResidueIso y).hom = (Spec (Y.residueField y)).fromSpecResidueField (ptOf y) :=
  Spec.fullyFaithful.map_preimage _

variable (A : Type) [CommRing A] [IsDomain A]

/-- The generic point inclusion `g : Spec κ(η) ⟶ Spec A`. -/
abbrev gen : Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)) ⟶ Spec (CommRingCat.of A) :=
  (Spec (CommRingCat.of A)).fromSpecResidueField (GenBr.genPt A)

/-- The point of `Y = Spec κ(η)`. -/
abbrev x0 : Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)) := ptOf (GenBr.genPt A)

/-- `κ(x0)`. -/
abbrev κ0 : CommRingCat.{0} := (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A))).residueField (x0 A)

/-- `(⊥ : Ideal A).ResidueField ≅ κ(x0)`. -/
def botIso : (⊥ : Ideal A).ResidueField ≃+* κ0 A :=
  ((Scheme.Spec.residueFieldIso (CommRingCat.of A) (GenBr.genPt A)).symm ≪≫
    ptResidueIso (GenBr.genPt A)).commRingCatIsoToRingEquiv

instance algK : Algebra A (κ0 A) :=
  ((botIso A).toRingHom.comp (algebraMap A (⊥ : Ideal A).ResidueField)).toAlgebra

theorem algebraMap_κ0 (r : A) : algebraMap A (κ0 A) r = botIso A (algebraMap A (⊥ : Ideal A).ResidueField r) := rfl

instance isFractionRing_κ0 : IsFractionRing A (κ0 A) :=
  IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors A)
    { botIso A with commutes' := fun _ => rfl }

instance algΩ : Algebra A (SeparableClosure (κ0 A)) :=
  ((algebraMap (κ0 A) (SeparableClosure (κ0 A))).comp (algebraMap A (κ0 A))).toAlgebra

instance towerΩ : IsScalarTower A (κ0 A) (SeparableClosure (κ0 A)) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem ofHom_algebraMap_κ0 : CommRingCat.ofHom (algebraMap A (κ0 A)) =
    CommRingCat.ofHom (algebraMap A (⊥ : Ideal A).ResidueField) ≫
      (Scheme.Spec.residueFieldIso (CommRingCat.of A) (GenBr.genPt A)).inv ≫ (ptResidueIso (GenBr.genPt A)).hom := by
  rfl

/-- `Spec (A → κ(x0)) = (Spec κ(x0) → Y) ≫ g`. -/
theorem map_algebraMap : Spec.map (CommRingCat.ofHom (algebraMap A (κ0 A))) =
    (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A))).fromSpecResidueField (x0 A) ≫ gen A := by
  refine (congrArg Spec.map (ofHom_algebraMap_κ0 A)).trans <|
    ((Spec.map_comp _ _).trans (congrArg (· ≫ _) (Spec.map_comp _ _))).trans <|
      (Category.assoc _ _ _).trans <| congrArg₂ (· ≫ ·) (map_ptResidueIso_hom _) ?_
  exact Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (R := CommRingCat.of A)
    (x := (⊥ : PrimeSpectrum A))

/-- The ring map of `x̄ ≫ g : Spec Ω → Spec A` is `algebraMap A Ω`. -/
theorem preimage_pt : Spec.preimage ((geomPtAt (x0 A)).pt ≫ gen A) =
    CommRingCat.ofHom (algebraMap A (SeparableClosure (κ0 A))) := by
  apply Spec.map_injective
  rw [Spec.map_preimage]
  have e1 : (geomPtAt (x0 A)).pt = Spec.map (CommRingCat.ofHom (algebraMap (κ0 A) (SeparableClosure (κ0 A)))) ≫
      (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A))).fromSpecResidueField (x0 A) := rfl
  have e2 : CommRingCat.ofHom (algebraMap A (SeparableClosure (κ0 A))) =
      CommRingCat.ofHom (algebraMap A (κ0 A)) ≫ CommRingCat.ofHom (algebraMap (κ0 A) (SeparableClosure (κ0 A))) :=
    rfl
  exact (congrArg (· ≫ gen A) e1).trans <| (Category.assoc _ _ _).trans <|
    (congrArg (Spec.map (CommRingCat.ofHom (algebraMap (κ0 A) (SeparableClosure (κ0 A)))) ≫ ·)
      (map_algebraMap A).symm).trans <| (Spec.map_comp _ _).symm.trans (congrArg Spec.map e2.symm)

/-- `FibPt.phi` at a fibre point of `g^* V` as an `A`-algebra map `B →ₐ[A] Ω`. -/
def phiA {B : Type} [CommRing B] [Algebra A B] (V : (Spec (CommRingCat.of A)).Etale)
    (e : V.left ⟶ Spec (CommRingCat.of B)) (he : e ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = V.hom)
    (a : (geomPtAt (x0 A)).point.fiber.obj ((etPull (gen A)).obj V)) : B →ₐ[A] SeparableClosure (κ0 A) :=
  { toRingHom := (FibPt.phi (x0 A) (gen A) V e a).hom
    commutes' := fun r => congrArg (fun f => f.hom r)
      ((FibPt.phi_comp (x0 A) (CommRingCat.ofHom (algebraMap A B)) he a).trans (preimage_pt A)) }

theorem phiA_apply {B : Type} [CommRing B] [Algebra A B] (V : (Spec (CommRingCat.of A)).Etale)
    (e : V.left ⟶ Spec (CommRingCat.of B)) (he : e ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = V.hom)
    (a : (geomPtAt (x0 A)).point.fiber.obj ((etPull (gen A)).obj V)) (c : B) :
    phiA A V e he a c = (FibPt.phi (x0 A) (gen A) V e a).hom c := rfl

end RamanujanPetersson.EtCompact.GenFrac

end

end

-- ===== S4.Def_RP_EtCompact_Obs =====
section

/-!
# S4-EtCompact, part 50: the Galois obstruction of a lift (F5 of plan v5)

`ρ` a representation of a group `G` on `MI`, `ι : MN → MI` injective with `G` acting trivially on its image,
`m ∈ MI`. For `σ` with `σ m - m ∈ ι(MN)` (e.g. `σ` fixes the image of `m` in `MI / ι(MN)`):

* `obs ρ ι m σ := ι⁻¹(σ m - m)`; `obs_spec`, `adm_of` (from exactness), `obs_mul` (additive on the admissible
  subgroup), `obs_eq_zero_of_fix`, `fix_of_obs_eq_zero`, `obs_add_ι` (independent of the lift `m`), `obs_conj`
  (conjugation by `τ` and `τ m`);
* **`isLocallyConstant_obs`**, **`finite_range_obs`**: for a topological `G`, `m` with an open stabiliser `H` and a
  subgroup `Γ` of admissible elements, `σ ↦ obs m σ` on `Γ` is locally constant, with finite range if `G` is compact.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtCompact.Obs

variable {Λ : Type*} [CommRing Λ] {G : Type*} [Group G]
  {MN MI MQ : Type*} [AddCommGroup MN] [Module Λ MN] [AddCommGroup MI] [Module Λ MI]
  [AddCommGroup MQ] [Module Λ MQ]
  (ρ : Representation Λ G MI) (ι : MN →ₗ[Λ] MI)

open Classical in
/-- The obstruction `σ ↦ ι⁻¹(σ m - m)` (zero when `σ m - m ∉ ι(MN)`). -/
def obs (m : MI) (σ : G) : MN := if h : ∃ n, ι n = ρ σ m - m then h.choose else 0

variable {ρ ι}

theorem obs_spec {m : MI} {σ : G} (h : ∃ n, ι n = ρ σ m - m) : ι (obs ρ ι m σ) = ρ σ m - m := by
  unfold obs
  rw [dif_pos h]
  exact h.choose_spec

theorem adm_of {p : MI →ₗ[Λ] MQ} (hex : ∀ y, p y = 0 → ∃ x, ι x = y) {m : MI} {σ : G}
    (h : p (ρ σ m) = p m) : ∃ n, ι n = ρ σ m - m :=
  hex _ (by rw [map_sub, h, sub_self])

variable (hι : Function.Injective ι) (hN : ∀ (σ : G) (n : MN), ρ σ (ι n) = ι n)
include hι

theorem obs_eq_of {m : MI} {σ : G} {n : MN} (h : ι n = ρ σ m - m) : obs ρ ι m σ = n :=
  hι ((obs_spec ⟨n, h⟩).trans h.symm)

theorem obs_eq_zero_of_fix {m : MI} {σ : G} (h : ρ σ m = m) : obs ρ ι m σ = 0 :=
  obs_eq_of hι (by rw [map_zero, h, sub_self])

omit hι in
theorem fix_of_obs_eq_zero {m : MI} {σ : G} (h : ∃ n, ι n = ρ σ m - m) (h0 : obs ρ ι m σ = 0) :
    ρ σ m = m := by
  have := obs_spec h
  rw [h0, map_zero] at this
  exact (sub_eq_zero.mp this.symm)

include hN

theorem adm_mul {m : MI} {σ τ : G} (hσ : ∃ n, ι n = ρ σ m - m) (hτ : ∃ n, ι n = ρ τ m - m) :
    ι (obs ρ ι m σ + obs ρ ι m τ) = ρ (σ * τ) m - m := by
  rw [map_add, obs_spec hσ, map_mul, Module.End.mul_apply]
  have h2 : ρ τ m = m + ι (obs ρ ι m τ) := by rw [obs_spec hτ]; abel
  rw [h2, map_add, hN]
  abel

theorem obs_mul {m : MI} {σ τ : G} (hσ : ∃ n, ι n = ρ σ m - m) (hτ : ∃ n, ι n = ρ τ m - m) :
    obs ρ ι m (σ * τ) = obs ρ ι m σ + obs ρ ι m τ :=
  obs_eq_of hι (adm_mul hι hN hσ hτ)

theorem obs_conj {m : MI} {σ : G} (τ : G) (h : ∃ n, ι n = ρ σ m - m) :
    obs ρ ι (ρ τ m) (τ * σ * τ⁻¹) = obs ρ ι m σ :=
  obs_eq_of hι (by
    rw [← hN τ, obs_spec h, map_sub, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      ← Module.End.mul_apply (ρ τ⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply])

section Top

variable [TopologicalSpace G] [IsTopologicalGroup G] {m : MI} (Γ : Subgroup G)
  (hΓ : ∀ σ ∈ Γ, ∃ n, ι n = ρ σ m - m) {H : Subgroup G} (hHo : IsOpen (H : Set G))
  (hH : ∀ σ ∈ H, ρ σ m = m)
include hΓ hH

theorem obs_mul_of_mem {σ τ : G} (hσ : σ ∈ Γ) (hτ : τ ∈ Γ) (hτH : τ ∈ H) :
    obs ρ ι m (σ * τ) = obs ρ ι m σ := by
  rw [obs_mul hι hN (hΓ σ hσ) (hΓ τ hτ), obs_eq_zero_of_fix hι (hH τ hτH), add_zero]

include hHo in
/-- The obstruction is locally constant on `Γ`. -/
theorem isLocallyConstant_obs : IsLocallyConstant (fun σ : Γ => obs ρ ι m (σ : G)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro σ
  have ho : IsOpen {τ : Γ | (σ : G)⁻¹ * (τ : G) ∈ H} :=
    hHo.preimage ((continuous_const.mul continuous_subtype_val))
  have hmem : σ ∈ {τ : Γ | (σ : G)⁻¹ * (τ : G) ∈ H} := by
    show (σ : G)⁻¹ * σ ∈ H
    rw [inv_mul_cancel]
    exact H.one_mem
  filter_upwards [ho.mem_nhds hmem] with τ hτ
  have e : (τ : G) = σ * ((σ : G)⁻¹ * τ) := by group
  show obs ρ ι m (τ : G) = obs ρ ι m (σ : G)
  rw [e]
  exact obs_mul_of_mem hι hN Γ hΓ hH σ.2 (Γ.mul_mem (Γ.inv_mem σ.2) τ.2) hτ

include hHo in
/-- The obstruction has finite range on `Γ` when `G` is compact. -/
theorem finite_range_obs [CompactSpace G] : (Set.range (fun σ : Γ => obs ρ ι m (σ : G))).Finite := by
  classical
  have : Finite (G ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  let f : G ⧸ H → MN := fun c =>
    if h : ∃ σ : Γ, (QuotientGroup.mk (σ : G) : G ⧸ H) = c then obs ρ ι m (h.choose : G) else 0
  refine (Set.finite_range f).subset ?_
  rintro _ ⟨σ, rfl⟩
  refine ⟨QuotientGroup.mk (σ : G), ?_⟩
  have h : ∃ τ : Γ, (QuotientGroup.mk (τ : G) : G ⧸ H) = QuotientGroup.mk (σ : G) := ⟨σ, rfl⟩
  show (if h : ∃ τ : Γ, (QuotientGroup.mk (τ : G) : G ⧸ H) = QuotientGroup.mk (σ : G) then
    obs ρ ι m (h.choose : G) else 0) = obs ρ ι m (σ : G)
  rw [dif_pos h]
  have hc := QuotientGroup.eq.mp h.choose_spec
  have := obs_mul_of_mem hι hN Γ hΓ hH h.choose.2 (Γ.mul_mem (Γ.inv_mem h.choose.2) σ.2) hc
  rw [show (h.choose : G) * ((h.choose : G)⁻¹ * σ) = σ by group] at this
  exact this.symm

end Top

end RamanujanPetersson.EtCompact.Obs

end

end

-- ===== S4.Def_RP_EtCompact_GalLift =====
section

/-!
# S4-EtCompact, part 44: lifting sections over a field point through Galois-fixed stalk elements (GM1)

`X` with `X.fromSpecResidueField x0` an isomorphism ("`X = Spec κ(x0)`"), `p : F ⟶ G`, `W : X.Etale`.

* `orbSetoid x0 W`: the orbit relation of `Gal x0` on the fibre of `x̄ = geomPtAt x0` over `W`;
* `inv_app_apply`, `app_injective_of_isIso`: sections and isomorphisms of étale sheaves;
* **`exists_lift_of_fixed`**: a section `q ∈ G(W)` comes from `F(W)` as soon as every germ `q_a` (`a` in the fibre
  over `W`) is the image of a stalk element of `F` fixed by the stabiliser of `a`. Proof: choose orbit
  representatives to build an equivariant map on the fibre, then descend with `descUnit` (`descUnit_natural`).
-/

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.GalLift

open RamanujanPetersson.EtSheaves

section Iso

variable {X : Scheme.{u}} {Λ : Type u} [CommRing Λ]

theorem inv_app_apply {F G : EtSh Λ X} (φ : F ⟶ G) [IsIso φ] (W : X.Etale) (y : G.obj.obj (op W)) :
    (φ.hom.app (op W)).hom (((inv φ).hom.app (op W)).hom y) = y :=
  congrArg (fun t => (t.hom.app (op W)).hom y) (IsIso.inv_hom_id φ)

theorem app_injective_of_isIso {F G : EtSh Λ X} (φ : F ⟶ G) [IsIso φ] (W : X.Etale) :
    Function.Injective (φ.hom.app (op W)).hom := fun y z h => by
  have hy := congrArg (fun t => (t.hom.app (op W)).hom y) (IsIso.hom_inv_id φ)
  have hz := congrArg (fun t => (t.hom.app (op W)).hom z) (IsIso.hom_inv_id φ)
  exact hy.symm.trans ((congrArg ((inv φ).hom.app (op W)).hom h).trans hz)

end Iso

variable {X : Scheme.{u}} (x0 : X)

/-- The orbit relation of `Gal x0` on the fibre over `W`. -/
def orbSetoid (W : X.Etale) : Setoid ((geomPtAt x0).point.fiber.obj W) where
  r a b := ∃ σ : Gal x0, (galAct x0 σ).app W a = b
  iseqv := ⟨fun a => ⟨1, galAct_one x0 W a⟩,
    fun {a b} ⟨σ, h⟩ => ⟨σ⁻¹, by rw [← h, ← galAct_mul, inv_mul_cancel, galAct_one]⟩,
    fun {a b c} ⟨σ, h⟩ ⟨τ, h'⟩ => ⟨τ * σ, by rw [galAct_mul, h, h']⟩⟩

variable [IsIso (X.fromSpecResidueField x0)] {Λ : Type u} [CommRing Λ] {F G : EtSh Λ X} (p : F ⟶ G)

/-- **Lifting over a field point (GM1)**: `q ∈ G(W)` comes from `F(W)` when every germ `q_a` is the image of a
stalk element of `F` fixed by the stabiliser of `a`. -/
theorem exists_lift_of_fixed (W : X.Etale) (q : G.obj.obj (op W))
    (h : ∀ a : (geomPtAt x0).point.fiber.obj W, ∃ m : stalk Λ F x0,
      (∀ σ : Gal x0, (galAct x0 σ).app W a = a → galRep Λ F x0 σ m = m) ∧
      (((geomPtAt x0).stalkF Λ).map p).hom m = ((geomPtAt x0).point.toPresheafFiber W a G.obj).hom q) :
    ∃ f : F.obj.obj (op W), (p.hom.app (op W)).hom f = q := by
  classical
  let S := orbSetoid x0 W
  let rep : (geomPtAt x0).point.fiber.obj W → (geomPtAt x0).point.fiber.obj W :=
    fun a => (Quotient.mk S a).out
  have hrep : ∀ a, ∃ σ : Gal x0, (galAct x0 σ).app W (rep a) = a := fun a => Quotient.mk_out (s := S) a
  have hrep_eq : ∀ (τ : Gal x0) a, rep ((galAct x0 τ).app W a) = rep a := fun τ a =>
    congrArg Quotient.out (Quotient.sound (s := S)
      ⟨τ⁻¹, by rw [← galAct_mul, inv_mul_cancel, galAct_one]⟩)
  let sg : (geomPtAt x0).point.fiber.obj W → Gal x0 := fun a => (hrep a).choose
  have hsg : ∀ a, (galAct x0 (sg a)).app W (rep a) = a := fun a => (hrep a).choose_spec
  let m0 : (geomPtAt x0).point.fiber.obj W → stalk Λ F x0 := fun a => (h (rep a)).choose
  have hm0fix : ∀ a (σ : Gal x0), (galAct x0 σ).app W (rep a) = rep a → galRep Λ F x0 σ (m0 a) = m0 a :=
    fun a => (h (rep a)).choose_spec.1
  have hm0 : ∀ a, (((geomPtAt x0).stalkF Λ).map p).hom (m0 a) =
      ((geomPtAt x0).point.toPresheafFiber W (rep a) G.obj).hom q := fun a => (h (rep a)).choose_spec.2
  have hm0eq : ∀ (τ : Gal x0) a, m0 ((galAct x0 τ).app W a) = m0 a := fun τ a => by
    show (h (rep ((galAct x0 τ).app W a))).choose = (h (rep a)).choose
    rw [hrep_eq τ a]
  let β : (geomPtAt x0).point.fiber.obj W → stalk Λ F x0 := fun a => galRep Λ F x0 (sg a) (m0 a)
  have hβ : β ∈ eqSub (geomPtAt x0).point (galAct x0) Λ (fun σ => galRep Λ F x0 σ) W := by
    rw [mem_eqSub]
    intro τ a
    show galRep Λ F x0 (sg ((galAct x0 τ).app W a)) (m0 ((galAct x0 τ).app W a)) =
      galRep Λ F x0 τ (galRep Λ F x0 (sg a) (m0 a))
    rw [hm0eq]
    have h1 : (galAct x0 (sg ((galAct x0 τ).app W a))).app W (rep a) = (galAct x0 τ).app W a := by
      rw [← hrep_eq τ a]; exact hsg _
    have h2 : (galAct x0 τ).app W a = (galAct x0 (τ * sg a)).app W (rep a) := by rw [galAct_mul, hsg a]
    have hst : (galAct x0 ((τ * sg a)⁻¹ * sg ((galAct x0 τ).app W a))).app W (rep a) = rep a := by
      rw [galAct_mul, h1, h2, ← galAct_mul, inv_mul_cancel, galAct_one]
    have hfix := hm0fix a _ hst
    calc galRep Λ F x0 (sg ((galAct x0 τ).app W a)) (m0 a)
        = galRep Λ F x0 (τ * sg a) (galRep Λ F x0 ((τ * sg a)⁻¹ * sg ((galAct x0 τ).app W a)) (m0 a)) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = galRep Λ F x0 τ (galRep Λ F x0 (sg a) (m0 a)) := by
          rw [hfix, map_mul, Module.End.mul_apply]
  refine ⟨((inv (descUnit x0 Λ F)).hom.app (op W)).hom ⟨β, hβ⟩, ?_⟩
  apply app_injective_of_isIso (descUnit x0 Λ G) W
  have hn := congrArg (fun t => (t.hom.app (op W)).hom (((inv (descUnit x0 Λ F)).hom.app (op W)).hom ⟨β, hβ⟩))
    (descUnit_natural x0 Λ p)
  refine hn.trans ?_
  refine Subtype.ext (funext fun a => ?_)
  show (((geomPtAt x0).stalkF Λ).map p).hom
      ((((descUnit x0 Λ F).hom.app (op W)).hom (((inv (descUnit x0 Λ F)).hom.app (op W)).hom ⟨β, hβ⟩)).1 a) =
    ((geomPtAt x0).point.toPresheafFiber W a G.obj).hom q
  have e2 : (((descUnit x0 Λ F).hom.app (op W)).hom
      (((inv (descUnit x0 Λ F)).hom.app (op W)).hom ⟨β, hβ⟩)).1 a = β a :=
    congrArg (fun z => z.1 a) (inv_app_apply (descUnit x0 Λ F) W ⟨β, hβ⟩)
  refine (congrArg (((geomPtAt x0).stalkF Λ).map p).hom e2).trans ?_
  show (((geomPtAt x0).stalkF Λ).map p).hom (galRep Λ F x0 (sg a) (m0 a)) = _
  have hnat := LinearMap.congr_fun (galRep_natural Λ p x0 (sg a)) (m0 a)
  simp only [LinearMap.comp_apply] at hnat
  rw [hnat, hm0, ← galRep_germ, hsg a]

end RamanujanPetersson.EtCompact.GalLift

end

end

-- ===== S4.Def_RP_EtCompact_KumEt =====
section

/-!
# S4-EtCompact, part 43: Kummer covers and local factorisation (curve core v4, algebra bricks LT/LF)

* `kumPoly N u = X^N - C u`, `kumPair hN0 hN hu : StandardEtalePair B` (`g = 1`), `kumEquiv`:
  its ring is `B[T]/(T^N - u)`;
* **`etale_kum`**: `B[T]/(T^N - u)` is étale over `B` when `N` and `u` are units of `B`;
* **`comap_surjective_kum`**: its prime spectrum maps onto that of `B` (free of rank `N`, faithfully flat);
* `root_pow_kum`: `T^N = u`;
* **`exists_mul_eq_unit_mul_pow`** (LF): `B` a noetherian domain, formally unramified and essentially of finite
  type over `A`, `w` a prime of `B` over the principal prime `(π)` of `A`, `π ≠ 0` in `B`: every `a ≠ 0` of `B`
  satisfies `s * a = v * π^n` with `s, v ∉ w`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtCompact.KumEt

section Kummer

variable {B : Type*} [CommRing B]

/-- The Kummer polynomial `X^N - u`. -/
def kumPoly (N : ℕ) (u : B) : B[X] := X ^ N - C u

theorem kumPoly_monic {N : ℕ} (hN0 : N ≠ 0) (u : B) : (kumPoly N u).Monic :=
  monic_X_pow_sub_C u hN0

/-- The standard étale pair `(X^N - u, 1)` for units `N`, `u`. -/
def kumPair {N : ℕ} (hN0 : N ≠ 0) (hN : IsUnit (N : B)) {u : B} (hu : IsUnit u) :
    StandardEtalePair B where
  f := kumPoly N u
  monic_f := kumPoly_monic hN0 u
  g := 1
  cond := by
    obtain ⟨v, hv⟩ := hN.mul hu
    refine ⟨C (↑v⁻¹ : B) * X, -C ((N : B) * ↑v⁻¹), 0, ?_⟩
    have hd : derivative (kumPoly N u) = C (N : B) * X ^ (N - 1) := by
      simp [kumPoly, derivative_X_pow]
    have hX : X ^ (N - 1) * X = (X : B[X]) ^ N := pow_sub_one_mul hN0 X
    have hw : (N : B) * u * ↑v⁻¹ = 1 := by rw [← hv]; exact Units.mul_inv v
    rw [hd, pow_zero]
    calc C (N : B) * X ^ (N - 1) * (C (↑v⁻¹ : B) * X) + kumPoly N u * -C ((N : B) * ↑v⁻¹)
        = C ((N : B) * u * ↑v⁻¹) + C ((N : B) * ↑v⁻¹) * (X ^ (N - 1) * X - X ^ N) := by
          simp only [kumPoly, map_mul]; ring
      _ = 1 := by rw [hX, hw, sub_self, mul_zero, add_zero, map_one]

/-- The ring of `kumPair` is `B[T]/(T^N - u)`. -/
def kumEquiv {N : ℕ} (hN0 : N ≠ 0) (hN : IsUnit (N : B)) {u : B} (hu : IsUnit u) :
    (kumPair hN0 hN hu).Ring ≃ₐ[B] AdjoinRoot (kumPoly N u) :=
  (kumPair hN0 hN hu).equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnits (AdjoinRoot (kumPair hN0 hN hu).f)
      (Submonoid.powers (AdjoinRoot.mk (kumPair hN0 hN hu).f (kumPair hN0 hN hu).g))
      (S := Localization.Away (AdjoinRoot.mk (kumPair hN0 hN hu).f (kumPair hN0 hN hu).g))
      (by
        rintro _ ⟨n, rfl⟩
        show IsUnit ((AdjoinRoot.mk (kumPoly N u) 1) ^ n)
        rw [map_one, one_pow]
        exact isUnit_one)).restrictScalars B).symm

/-- **The Kummer cover is étale**: `B[T]/(T^N - u)` is étale over `B` for units `N`, `u`. -/
theorem etale_kum {N : ℕ} (hN0 : N ≠ 0) (hN : IsUnit (N : B)) {u : B} (hu : IsUnit u) :
    Algebra.Etale B (AdjoinRoot (kumPoly N u)) :=
  Algebra.Etale.of_equiv (kumEquiv hN0 hN hu)

/-- `T^N = u` in `B[T]/(T^N - u)`. -/
theorem root_pow_kum (N : ℕ) (u : B) :
    AdjoinRoot.root (kumPoly N u) ^ N = algebraMap B (AdjoinRoot (kumPoly N u)) u := by
  have h : AdjoinRoot.mk (kumPoly N u) (X ^ N - C u) = 0 := AdjoinRoot.mk_self
  rwa [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero, ← AdjoinRoot.algebraMap_eq] at h

/-- **The Kummer cover is surjective** on prime spectra. -/
theorem comap_surjective_kum {N : ℕ} (hN0 : N ≠ 0) (u : B) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap B (AdjoinRoot (kumPoly N u)))) := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · intro p
    exact (p.isPrime.ne_top (Subsingleton.elim _ _)).elim
  · have hm := kumPoly_monic hN0 u
    have : Module.Free B (AdjoinRoot (kumPoly N u)) := hm.free_adjoinRoot
    have hne : kumPoly N u ≠ 1 := by
      intro h
      have := congrArg natDegree h
      rw [kumPoly, natDegree_X_pow_sub_C, natDegree_one] at this
      exact hN0 this
    have : Nontrivial (AdjoinRoot (kumPoly N u)) :=
      Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top (fun h => hne (hm.isUnit_iff.mp h)))
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

end Kummer

section LF

variable {A B : Type*} [CommRing A] [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra A B]
  [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B]

/-- **Local factorisation (LF)**: at a prime `w` of `B` over the principal prime `(π)` of `A`, every `a ≠ 0`
is a unit times a power of `π` near `w`: `s * a = v * π^n` with `s, v ∉ w`. -/
theorem exists_mul_eq_unit_mul_pow (π : A) (w : Ideal B) [w.IsPrime]
    (hw : w.comap (algebraMap A B) = Ideal.span {π}) (hπ : algebraMap A B π ≠ 0) {a : B} (ha : a ≠ 0) :
    ∃ (n : ℕ) (v s : B), v ∉ w ∧ s ∉ w ∧ s * a = v * algebraMap A B π ^ n := by
  have : (Ideal.span {π}).IsPrime := hw ▸ Ideal.comap_isPrime (algebraMap A B) w
  have : w.LiesOver (Ideal.span {π}) := ⟨hw.symm⟩
  let _ := Localization.AtPrime.algebraOfLiesOver (Ideal.span {π}) w
  have : Algebra.IsUnramifiedAt A w := Algebra.FormallyUnramified.comp A B (Localization.AtPrime w)
  have hm := ((Algebra.isUnramifiedAt_iff_map_eq A (Ideal.span {π}) w).mp inferInstance).2
  rw [Ideal.map_span, Set.image_singleton] at hm
  have hinj : Function.Injective (algebraMap B (Localization.AtPrime w)) :=
    IsLocalization.injective (Localization.AtPrime w) (Ideal.primeCompl_le_nonZeroDivisors w)
  have hπ' : algebraMap A (Localization.AtPrime w) π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime w)]
    exact fun h => hπ (hinj (h.trans (map_zero _).symm))
  have hprinc : (IsLocalRing.maximalIdeal (Localization.AtPrime w)).IsPrincipal := ⟨⟨_, hm.symm⟩⟩
  have ha' : algebraMap B (Localization.AtPrime w) a ≠ 0 := fun h => ha (hinj (h.trans (map_zero _).symm))
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal (R := Localization.AtPrime w) hprinc
    (Ideal.span {algebraMap B (Localization.AtPrime w) a}) (by simpa using ha')
  rw [← hm, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at hn
  obtain ⟨c, hc⟩ := hn
  obtain ⟨⟨v, s⟩, hvs⟩ := IsLocalization.surj w.primeCompl (↑c⁻¹ : Localization.AtPrime w)
  refine ⟨n, v, s, ?_, s.2, ?_⟩
  · intro hv
    have hu : IsUnit (algebraMap B (Localization.AtPrime w) v) := by
      rw [← hvs]; exact c⁻¹.isUnit.mul (IsLocalization.map_units (Localization.AtPrime w) s)
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime w) w v).mp hu hv
  · apply hinj
    have ha2 : algebraMap B (Localization.AtPrime w) a = algebraMap A (Localization.AtPrime w) π ^ n * ↑c⁻¹ := by
      rw [← hc, mul_assoc, Units.mul_inv, mul_one]
    rw [map_mul, map_mul, map_pow, ← IsScalarTower.algebraMap_apply, ha2, ← hvs]
    ring

end LF

end RamanujanPetersson.EtCompact.KumEt

end

end

-- ===== S4.Def_RP_EtCompact_LT =====
section

/-!
# S4-EtCompact, part 51: local triviality of Kummer-unit obstructions (F6 of plan v5)

`A` a domain, `g = gen A : Spec κ(η) ⟶ Spec A`, `x0` the point of `Spec κ(η)`, `Ω = κ(x0)^sep`.
`ι : Ns ⟶ I`, `p : I ⟶ Q` sheaves on `Spec κ(η)`, exact on stalks with `Gal` acting trivially on `ι(Ns)`.

* `specEt A B`: `Spec B` as an étale `Spec A`-scheme (`B` étale over `A`), `specEtMap h`, `Fib A B` (the fibre of the
  generic geometric point over `g^* Spec B`), `fmap`, `phiB A a : B →ₐ[A] Ω`, `phiB_map`;
* `KC hζ B q u e`: at every fibre point `a`, the germ of `q ∈ Q(g^* Spec B)` lifts to `m ∈ I_x̄` whose obstruction on
  `Stab(a)` is `∑ i, kchar(φ_a(u i)^{1/d}) • e i` (units `u i ∈ Bˣ`);
* **`exists_lift`**: then `q` lifts to `I` on an étale surjective `V' ⟶ Spec B` (Kummer covers adjoining the
  `d`-th roots of the `u i` one at a time; the empty case is `GalLift.exists_lift_of_fixed`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.LT

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.Kummer

variable (A : Type) [CommRing A] [IsDomain A]

/-- `Spec B` as an étale `Spec A`-scheme. -/
def specEt (B : Type) [CommRing B] [Algebra A B] [Algebra.Etale A B] : (Spec (CommRingCat.of A)).Etale :=
  MorphismProperty.Over.mk ⊤ (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    ((HasRingHomProperty.Spec_iff (P := @Etale)).2 (RingHom.etale_algebraMap.2 inferInstance))

variable {A}

/-- The map `Spec B' ⟶ Spec B` of an `A`-algebra map `B → B'`. -/
def specEtMap {B B' : Type} [CommRing B] [Algebra A B] [Algebra.Etale A B] [CommRing B'] [Algebra A B']
    [Algebra.Etale A B'] (h : B →ₐ[A] B') : specEt A B' ⟶ specEt A B :=
  MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom h.toRingHom))
    ((Spec.map_comp _ _).symm.trans (congrArg Spec.map (CommRingCat.hom_ext h.comp_algebraMap))) trivial

variable (A)

/-- The fibre of the generic geometric point over `g^* Spec B`. -/
abbrev Fib (B : Type) [CommRing B] [Algebra A B] [Algebra.Etale A B] : Type :=
  (geomPtAt (x0 A)).point.fiber.obj ((etPull (gen A)).obj (specEt A B))

/-- Transport of fibre points along `Spec B' ⟶ Spec B`. -/
def fmap {B B' : Type} [CommRing B] [Algebra A B] [Algebra.Etale A B] [CommRing B'] [Algebra A B']
    [Algebra.Etale A B'] (h : B →ₐ[A] B') (a : Fib A B') : Fib A B :=
  (geomPtAt (x0 A)).point.fiber.map ((etPull (gen A)).map (specEtMap h)) a

/-- `φ_a : B →ₐ[A] Ω` at a fibre point. -/
def phiB {B : Type} [CommRing B] [Algebra A B] [Algebra.Etale A B] (a : Fib A B) :
    B →ₐ[A] SeparableClosure (κ0 A) :=
  phiA A (specEt A B) (𝟙 _) (Category.id_comp _) a

theorem phiB_apply {B : Type} [CommRing B] [Algebra A B] [Algebra.Etale A B] (a : Fib A B) (c : B) :
    phiB A a c = (FibPt.phi (x0 A) (gen A) (specEt A B) (𝟙 _) a).hom c := rfl

theorem phiB_map {B B' : Type} [CommRing B] [Algebra A B] [Algebra.Etale A B] [CommRing B'] [Algebra A B']
    [Algebra.Etale A B'] (h : B →ₐ[A] B') (a : Fib A B') (c : B) :
    phiB A a (h c) = phiB A (fmap A h a) c := by
  have key : CommRingCat.ofHom h.toRingHom ≫ FibPt.phi (x0 A) (gen A) (specEt A B') (𝟙 _) a =
      FibPt.phi (x0 A) (gen A) (specEt A B) (𝟙 _) (fmap A h a) := by
    apply Spec.map_injective
    refine (Spec.map_comp _ _).trans ?_
    refine (congrArg (· ≫ Spec.map (CommRingCat.ofHom h.toRingHom))
      (FibPt.map_phi (x0 A) (gen A) (specEt A B') (𝟙 _) a)).trans ?_
    refine Eq.trans ?_ (FibPt.map_phi (x0 A) (gen A) (specEt A B) (𝟙 _) (fmap A h a)).symm
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (((geomPtAt (x0 A)).liftOf a).left ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (pullback.fst (specEt A B').hom (gen A) ≫ ·) (Category.id_comp _)))).trans ?_
    refine Eq.trans ?_ (congrArg (((geomPtAt (x0 A)).liftOf (fmap A h a)).left ≫ ·)
      (Category.comp_id (pullback.fst (specEt A B).hom (gen A)))).symm
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine congrArg (((geomPtAt (x0 A)).liftOf a).left ≫ ·) ?_
    exact (pullback.lift_fst _ _ _).symm
  exact congrArg (fun f => f.hom c) key

theorem galAct_fmap {B B' : Type} [CommRing B] [Algebra A B] [Algebra.Etale A B] [CommRing B'] [Algebra A B']
    [Algebra.Etale A B'] (h : B →ₐ[A] B') (σ : Gal (x0 A)) (a : Fib A B') :
    (galAct (x0 A) σ).app _ (fmap A h a) = fmap A h ((galAct (x0 A) σ).app _ a) :=
  fiber_ext _ ((galAct_left (x0 A) σ _ (fmap A h a)).trans (Category.assoc _ _ _).symm)

section Sheaves

variable {Λ : Type} [CommRing Λ]
  {Ns I Q : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))} (ι : Ns ⟶ I) (p : I ⟶ Q)

/-- **Kummer condition**: at every fibre point `a`, the germ of `q` lifts to `m ∈ I_x̄` with obstruction
`σ ↦ ∑ i, kchar(β i) σ • e i` on `Stab(a)`, where `β i ^ d = φ_a (u i)`. -/
def KC {d : ℕ} [NeZero d] {ζ : SeparableClosure (κ0 A)} (hζ : IsPrimitiveRoot ζ d)
    (B : Type) [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : Q.obj.obj (op ((etPull (gen A)).obj (specEt A B)))) {k : ℕ} (u : Fin k → Bˣ)
    (e : Fin k → stalk Λ Ns (x0 A)) : Prop :=
  ∀ a : Fib A B, ∃ m : stalk Λ I (x0 A),
    (((geomPtAt (x0 A)).stalkF Λ).map p).hom m =
      ((geomPtAt (x0 A)).point.toPresheafFiber _ a Q.obj).hom q ∧
    ∃ β : Fin k → SeparableClosure (κ0 A), (∀ i, β i ^ d = phiB A a (u i)) ∧
      ∀ σ : Gal (x0 A), (galAct (x0 A) σ).app _ a = a →
        Obs.obs (galRep Λ I (x0 A)) (((geomPtAt (x0 A)).stalkF Λ).map ι).hom m σ =
          ∑ i, (dlog hζ (σ (β i) / β i)).val • e i

variable {A ι p}

/-- Germs of `q` at points of a stabiliser are fixed: the obstruction is defined there. -/
theorem adm (hex : ∀ y, (((geomPtAt (x0 A)).stalkF Λ).map p).hom y = 0 →
      ∃ x, (((geomPtAt (x0 A)).stalkF Λ).map ι).hom x = y)
    {W : (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A))).Etale} (q : Q.obj.obj (op W))
    (a : (geomPtAt (x0 A)).point.fiber.obj W) (m : stalk Λ I (x0 A))
    (hm : (((geomPtAt (x0 A)).stalkF Λ).map p).hom m = ((geomPtAt (x0 A)).point.toPresheafFiber _ a Q.obj).hom q)
    (σ : Gal (x0 A)) (hσ : (galAct (x0 A) σ).app _ a = a) :
    ∃ n, (((geomPtAt (x0 A)).stalkF Λ).map ι).hom n = galRep Λ I (x0 A) σ m - m := by
  refine Obs.adm_of hex ?_
  have h1 := LinearMap.congr_fun (galRep_natural Λ p (x0 A) σ) m
  simp only [LinearMap.comp_apply] at h1
  rw [h1, hm, ← galRep_germ, hσ]

/-- **Local triviality (LT)**: a section of `Q` over `g^* Spec B` satisfying the Kummer condition for units of `B`
lifts to `I` on an étale surjective `V' ⟶ Spec B`. -/
theorem exists_lift (hex : ∀ y, (((geomPtAt (x0 A)).stalkF Λ).map p).hom y = 0 →
      ∃ x, (((geomPtAt (x0 A)).stalkF Λ).map ι).hom x = y)
    {d : ℕ} [NeZero d] (hdA : IsUnit (d : A)) {ζ : SeparableClosure (κ0 A)} (hζ : IsPrimitiveRoot ζ d)
    (hζG : ∀ σ : Gal (x0 A), σ ζ = ζ) (k : ℕ) :
    ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.Etale A B]
      (q : Q.obj.obj (op ((etPull (gen A)).obj (specEt A B)))) (u : Fin k → Bˣ) (e : Fin k → stalk Λ Ns (x0 A)),
      KC A ι p hζ B q u e →
      ∃ (V' : (Spec (CommRingCat.of A)).Etale) (F : V' ⟶ specEt A B), (∀ v : (specEt A B).left, ∃ v', F.left v' = v) ∧
        ∃ f : I.obj.obj (op ((etPull (gen A)).obj V')),
          (p.hom.app _).hom f = (Q.obj.map ((etPull (gen A)).map F).op).hom q := by
  induction k with
  | zero =>
    intro B _ _ _ q u e hkc
    obtain ⟨f, hf⟩ := GalLift.exists_lift_of_fixed (x0 A) p _ q (fun a => by
      obtain ⟨m, hm, β, -, hobs⟩ := hkc a
      refine ⟨m, fun σ hσ => Obs.fix_of_obs_eq_zero (adm hex q a m hm σ hσ) ?_, hm⟩
      rw [hobs σ hσ]
      exact Finset.sum_empty)
    refine ⟨specEt A B, 𝟙 _, fun v => ⟨v, rfl⟩, f, ?_⟩
    rw [hf, CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]
    rfl
  | succ k ih =>
    intro B _ _ _ q u e hkc
    have hdB : IsUnit (d : B) := by simpa using hdA.map (algebraMap A B)
    let B₁ := AdjoinRoot (KumEt.kumPoly d (u 0 : B))
    have : Algebra.Etale B B₁ := KumEt.etale_kum (NeZero.ne d) hdB (u 0).isUnit
    have : Algebra.Etale A B₁ := Algebra.Etale.comp A B B₁
    let h : B →ₐ[A] B₁ := IsScalarTower.toAlgHom A B B₁
    let q₁ := (Q.obj.map ((etPull (gen A)).map (specEtMap h)).op).hom q
    let u₁ : Fin k → B₁ˣ := fun i => Units.map (algebraMap B B₁ : B →* B₁) (u i.succ)
    have hkc₁ : KC A ι p hζ B₁ q₁ u₁ (fun i => e i.succ) := by
      intro a'
      obtain ⟨m, hm, β, hβ, hobs⟩ := hkc (fmap A h a')
      refine ⟨m, ?_, fun i => β i.succ, fun i => ?_, fun σ hσ => ?_⟩
      · have hw := congrArg (fun φ => φ.hom q) (GrothendieckTopology.Point.toPresheafFiber_w
          (Φ := (geomPtAt (x0 A)).point) ((etPull (gen A)).map (specEtMap h)) a' Q.obj)
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hw
        exact hm.trans hw.symm
      · rw [hβ i.succ]
        exact (phiB_map A h a' (u i.succ : B)).symm
      · have hσ' : (galAct (x0 A) σ).app _ (fmap A h a') = fmap A h a' := by
          rw [galAct_fmap, hσ]
        rw [hobs σ hσ', Fin.sum_univ_succ]
        have h0 : dlog hζ (σ (β 0) / β 0) = 0 := by
          let r := phiB A a' (AdjoinRoot.root (KumEt.kumPoly d (u 0 : B)))
          have hr : r ^ d = β 0 ^ d := by
            rw [hβ 0, ← map_pow, KumEt.root_pow_kum]
            exact phiB_map A h a' (u 0 : B)
          have hβ0 : β 0 ≠ 0 := by
            intro h0
            have := hβ 0
            rw [h0, zero_pow (NeZero.ne d)] at this
            exact ((u 0).isUnit.map (phiB A (fmap A h a'))).ne_zero this.symm
          have hr0 : r ≠ 0 := by
            intro h0
            rw [h0, zero_pow (NeZero.ne d)] at hr
            exact hβ0 (pow_eq_zero_iff (NeZero.ne d) |>.mp hr.symm)
          have hσr : σ r = r := by
            have := FibPt.phi_galAct_apply (x0 A) (gen A) (specEt A B₁) (𝟙 _) σ a'
              (AdjoinRoot.root (KumEt.kumPoly d (u 0 : B)))
            rw [hσ] at this
            exact this.symm
          have h1 : (β 0 / r) ^ d = 1 := by rw [div_pow, ← hr, div_self (pow_ne_zero _ hr0)]
          obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h1
          have hb : β 0 = ζ ^ i * r := by rw [hi, div_mul_cancel₀ _ hr0]
          have hσb : σ (β 0) = β 0 := by rw [hb, map_mul, map_pow, hζG, hσr]
          rw [hσb, div_self hβ0]
          have := dlog_epow hζ (0 : ZMod d)
          rwa [epow, ZMod.val_zero, pow_zero] at this
        rw [h0, ZMod.val_zero, zero_smul, zero_add]
    obtain ⟨V', F, hF, f, hf⟩ := ih B₁ q₁ u₁ (fun i => e i.succ) hkc₁
    refine ⟨V', F ≫ specEtMap h, fun v => ?_, f, ?_⟩
    · obtain ⟨v₁, hv₁⟩ := KumEt.comap_surjective_kum (NeZero.ne d) (u 0 : B) v
      obtain ⟨v', hv'⟩ := hF v₁
      refine ⟨v', ?_⟩
      show (specEtMap h).left (F.left v') = v
      rw [hv']
      exact hv₁
    · rw [hf]
      simp only [q₁, CategoryTheory.Functor.map_comp, op_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

end Sheaves

end RamanujanPetersson.EtCompact.LT

end

end

-- ===== S4.Def_RP_EtCompact_Supp =====
section

/-!
# S4-EtCompact, part 52: global sections of `Λ`-morphisms and where they vanish (F7a of plan v5)

For `c : Λ_X ⟶ F`:

* `sc c V := c(1) ∈ F(V)`; `sc_map` (restriction), `sc_comp`, `stalk_sc` (the stalk value at `1` is the germ of
  `sc c V`), **`stalk_eq_zero_of`** (`sc c V = 0` kills the stalk at every point of the image of `V`),
  **`eq_zero_of`** (`c = 0` when every point has such a `V`), **`exists_local_sc`** (local lifts of `sc c` along an
  epimorphism);
* on `X = Spec A`: **`exists_affine`** (every étale `V` is covered by `specEt A R` with `R` étale over `A`),
  `Good c` (points with a vanishing neighbourhood) and **`isOpen_good`** (Chevalley: `Spec R → Spec A` is open).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.Supp

open RamanujanPetersson.EtSheaves

section General

variable {X : Scheme.{u}} {Λ : Type u} [CommRing Λ]

/-- The section `c(1)` over `V`. -/
def sc {F : EtSh Λ X} (c : unitSh Λ X ⟶ F) (V : X.Etale) : F.obj.obj (op V) :=
  (c.hom.app (op V)).hom ((constUnit (ModuleCat.of Λ Λ) V).hom 1)

theorem sc_map {F : EtSh Λ X} (c : unitSh Λ X ⟶ F) {V W : X.Etale} (f : V ⟶ W) :
    (F.obj.map f.op).hom (sc c W) = sc c V := by
  have h1 := congrArg (fun φ => φ.hom ((constUnit (ModuleCat.of Λ Λ) W).hom 1)) (c.hom.naturality f.op)
  have h2 := (toSheafify X.smallEtaleTopology (constPre (X := X) (ModuleCat.of Λ Λ))).naturality f.op
  change 𝟙 _ ≫ constUnit (ModuleCat.of Λ Λ) V = constUnit (ModuleCat.of Λ Λ) W ≫ (unitSh Λ X).obj.map f.op at h2
  rw [Category.id_comp] at h2
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [sc, sc, ← h1, h2, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem sc_comp {F G : EtSh Λ X} (c : unitSh Λ X ⟶ F) (φ : F ⟶ G) (V : X.Etale) :
    sc (c ≫ φ) V = (φ.hom.app (op V)).hom (sc c V) := rfl

theorem sc_add {F : EtSh Λ X} (c c' : unitSh Λ X ⟶ F) (V : X.Etale) : sc (c + c') V = sc c V + sc c' V := by
  simp [sc]

theorem sc_sub {F : EtSh Λ X} (c c' : unitSh Λ X ⟶ F) (V : X.Etale) : sc (c - c') V = sc c V - sc c' V := by
  have h := sc_add (c - c') c' V
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

/-- The stalk value at `1` is the germ of `sc c V`. -/
theorem stalk_sc {F : EtSh Λ X} (c : unitSh Λ X ⟶ F) (y : X) (V : X.Etale)
    (b : (geomPtAt y).point.fiber.obj V) :
    (((geomPtAt y).stalkF Λ).map c).hom (oneStalk Λ y) =
      ((geomPtAt y).point.toPresheafFiber V b F.obj).hom (sc c V) := by
  have h2 := congrArg (fun φ => φ.hom (1 : Λ)) (constUnit_germ (geomPtAt y) (ModuleCat.of Λ Λ) V b)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  have h1 : (((geomPtAt y).stalkF Λ).map c).hom (((geomPtAt y).point.toPresheafFiber V b (unitSh Λ X).obj).hom
      ((constUnit (ModuleCat.of Λ Λ) V).hom 1)) = ((geomPtAt y).point.toPresheafFiber V b F.obj).hom (sc c V) :=
    congrArg (fun φ => φ.hom ((constUnit (ModuleCat.of Λ Λ) V).hom 1))
      (GrothendieckTopology.Point.toPresheafFiber_naturality (Φ := (geomPtAt y).point) c.hom V b)
  rw [← h1, h2]
  rfl

/-- **Vanishing spreads to stalks**: `sc c V = 0` kills the stalk of `c` at every point of the image of `V`. -/
theorem stalk_eq_zero_of {F : EtSh Λ X} (c : unitSh Λ X ⟶ F) {V : X.Etale} {w : V.left} {y : X}
    (hw : V.hom w = y) (h0 : sc c V = 0) : (((geomPtAt y).stalkF Λ).map c).hom (oneStalk Λ y) = 0 := by
  obtain ⟨b⟩ := GeomPt.exists_fiber (geomPtAt y) V w (hw.trans (center_geomPtAt y).symm)
  rw [stalk_sc c y V b, h0, map_zero]
  rfl

/-- `c = 0` as soon as every point has an étale neighbourhood on which `c(1)` vanishes. -/
theorem eq_zero_of {F : EtSh Λ X} (c : unitSh Λ X ⟶ F)
    (h : ∀ y : X, ∃ (V : X.Etale) (w : V.left), V.hom w = y ∧ sc c V = 0) : c = 0 := by
  refine hom_ext_stalk Λ fun y => ?_
  obtain ⟨V, w, hw, h0⟩ := h y
  refine stalk_unitSh_hom_ext Λ y ?_
  rw [stalk_eq_zero_of c hw h0, Functor.map_zero]
  rfl

/-- **Local lifts**: along an epimorphism `φ : F ⟶ G`, `sc c` lifts on an étale neighbourhood of every point. -/
theorem exists_local_sc {F G : EtSh Λ X} (φ : F ⟶ G) [Epi φ] (c : unitSh Λ X ⟶ G) (y : X) :
    ∃ (V : X.Etale) (w : V.left), V.hom w = y ∧ ∃ s : F.obj.obj (op V), (φ.hom.app (op V)).hom s = sc c V := by
  have hep : Epi (((geomPtAt y).stalkF Λ).map φ) := (epi_iff_stalk Λ φ).1 inferInstance y
  obtain ⟨p, hp⟩ := (ModuleCat.epi_iff_surjective _).1 hep ((((geomPtAt y).stalkF Λ).map c).hom (oneStalk Λ y))
  obtain ⟨W, b, z, rfl⟩ := (geomPtAt y).point.toPresheafFiber_jointly_surjective (P := F.obj) p
  have h1 : (((geomPtAt y).stalkF Λ).map φ).hom (((geomPtAt y).point.toPresheafFiber W b F.obj).hom z) =
      ((geomPtAt y).point.toPresheafFiber W b G.obj).hom ((φ.hom.app (op W)).hom z) :=
    congrArg (fun ψ => ψ.hom z) (GrothendieckTopology.Point.toPresheafFiber_naturality
      (Φ := (geomPtAt y).point) φ.hom W b)
  have h3 : (geomPtAt y).point.toPresheafFiber W b G.obj ((φ.hom.app (op W)).hom z) =
      (geomPtAt y).point.toPresheafFiber W b G.obj (sc c W) :=
    h1.symm.trans (hp.trans (stalk_sc c y W b))
  obtain ⟨W', f, b', hb', hfz⟩ := ((geomPtAt y).point.toPresheafFiber_eq_iff' W b _ _).1 h3
  obtain ⟨w, hw⟩ := (geomPtAt y).center_mem_range b'
  refine ⟨W', w, hw.trans (center_geomPtAt y), (F.obj.map f.op).hom z, ?_⟩
  have h4 := congrArg (fun ψ => ψ.hom z) (φ.hom.naturality f.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h4
  rw [h4]
  exact hfz.trans (sc_map c f)

end General

section Spec

variable (A : Type) [CommRing A] [IsDomain A] {Λ : Type} [CommRing Λ]

/-- **Affine refinement**: every point of an étale `V ⟶ Spec A` lies in the image of some `specEt A R`. -/
theorem exists_affine (V : (Spec (CommRingCat.of A)).Etale) (v : V.left) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra A R) (_ : Algebra.Etale A R) (F : LT.specEt A R ⟶ V)
      (r : (LT.specEt A R).left), F.left r = v := by
  obtain ⟨R, j, _, ⟨r, hr⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (x := v) (U := ⊤) (by simp)
  have : Etale V.hom := V.prop
  let ψ : Spec R ⟶ Spec (CommRingCat.of A) := j ≫ V.hom
  let φ : CommRingCat.of A ⟶ R := Spec.preimage ψ
  letI : Algebra A R := φ.hom.toAlgebra
  have hψ : Spec.map (CommRingCat.ofHom (algebraMap A R)) = ψ := Spec.map_preimage ψ
  have hEt : Etale (Spec.map (CommRingCat.ofHom (algebraMap A R))) := by
    rw [hψ]
    infer_instance
  have hAlg : Algebra.Etale A R :=
    RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 hEt)
  exact ⟨R, inferInstance, inferInstance, hAlg, MorphismProperty.Over.homMk j hψ.symm trivial, r, hr⟩

/-- Points of `Spec A` with an étale neighbourhood on which `c(1)` vanishes. -/
def Good {F : EtSh Λ (Spec (CommRingCat.of A))} (c : unitSh Λ (Spec (CommRingCat.of A)) ⟶ F) :
    Set (Spec (CommRingCat.of A)) :=
  {y | ∃ (V : (Spec (CommRingCat.of A)).Etale) (w : V.left), V.hom w = y ∧ sc c V = 0}

theorem isOpen_good {F : EtSh Λ (Spec (CommRingCat.of A))} (c : unitSh Λ (Spec (CommRingCat.of A)) ⟶ F) :
    IsOpen (Good A c) := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨V, w, hw, h0⟩
  obtain ⟨R, _, _, _, F, r, hr⟩ := exists_affine A V w
  have h0' : sc c (LT.specEt A R) = 0 := by rw [← sc_map c F, h0, map_zero]
  refine ⟨Set.range (PrimeSpectrum.comap (algebraMap A R)), ?_, ?_, ?_⟩
  · rintro _ ⟨r', rfl⟩
    exact ⟨LT.specEt A R, r', rfl, h0'⟩
  · exact (PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation (R := A) (S := R)).isOpen_range
  · refine ⟨r, ?_⟩
    rw [← hw, ← hr]
    exact congrArg (fun f => f r) (MorphismProperty.Over.w F).symm

end Spec

end RamanujanPetersson.EtCompact.Supp

end

end

-- ===== S4.Def_RP_EtCompact_KCe =====
section

/-!
# S4-EtCompact, part 53: the Kummer condition for elements (F7b of plan v5)

* `KCAt hζ q u e a` (one fibre point `a`, elements `u i ∈ B`), `KCe` (every fibre point); `kc_iff`: the condition
  `LT.KC` for units is `KCe` for their values;
* **`kc_of_one`**: over `g^* Spec B` with a single point, the condition at one fibre point gives it everywhere
  (Galois transitivity, conjugation of obstructions, `τ ζ = ζ`);
* `kcat_map`, `kce_map` (restriction along `B →ₐ[A] B'`), `obs_sub`;
* `good_iff` (`y ∈ Good c` iff the stalk of `c` at `1` vanishes), `good_sub`, `good_comp`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.dupNamespace false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.KCe

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.Kummer
  RamanujanPetersson.EtCompact.LT

section ObsSub

variable {Λ : Type*} [CommRing Λ] {G : Type*} [Group G] {MN MI : Type*} [AddCommGroup MN] [Module Λ MN]
  [AddCommGroup MI] [Module Λ MI] {ρ : Representation Λ G MI} {ι : MN →ₗ[Λ] MI}

theorem obs_sub (hι : Function.Injective ι) {m m' : MI} {σ : G} (h : ∃ n, ι n = ρ σ m - m)
    (h' : ∃ n, ι n = ρ σ m' - m') : Obs.obs ρ ι (m - m') σ = Obs.obs ρ ι m σ - Obs.obs ρ ι m' σ :=
  Obs.obs_eq_of hι (by rw [map_sub, Obs.obs_spec h, Obs.obs_spec h', map_sub]; abel)

end ObsSub

variable (A : Type) [CommRing A] [IsDomain A]

section Sheaves

variable {Λ : Type} [CommRing Λ]
  {Ns I Q : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))} (ι : Ns ⟶ I) (p : I ⟶ Q)

variable {A ι p}

end Sheaves

section Good

variable {A} {Λ : Type} [CommRing Λ] {F : EtSh Λ (Spec (CommRingCat.of A))}

end Good

end RamanujanPetersson.EtCompact.KCe

end

end

-- ===== S4.Def_RP_EtCompact_Twist =====
section

/-!
# S4-EtCompact, part 45: every Galois character is an obstruction (P2 of curve core v4)

`X` with `X.fromSpecResidueField x0` an isomorphism ("`X = Spec κ(x0)`"), `ι : N ⟶ I` a monomorphism into an
injective sheaf, `Gal(Ω/κ(x0))` acting trivially on `N_x̄`.

* `twAct x0 χ`: the twisted action `σ (n, c) = (n + c • χ σ, c)` on `N_x̄ × Λ`;
* **`exists_twist_lift`**: for every additive `χ : Gal x0 → N_x̄` vanishing on an open subgroup there is `m ∈ I_x̄`
  with `σ m - m = ι(χ σ)` for all `σ` (`H¹(G, I_x̄) = 0`): the twisted module is the stalk of a sheaf `E`
  (`specField_essSurj`), `N ⟶ E` is the equivariant inclusion (`specField_homEquiv`), extend `ι` along it
  (`I` injective) and take the image of `(0, 1)`.
-/

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.Twist

open RamanujanPetersson.EtSheaves

variable {X : Scheme.{u}} (x0 : X) {Λ : Type u} [CommRing Λ]

section Mod

variable {M : Type u} [AddCommGroup M] [Module Λ M]

/-- The twisted action on `M × Λ`: `σ (n, c) = (n + c • χ σ, c)`. -/
def twAct (χ : Gal x0 → M) (σ : Gal x0) : (M × Λ) →ₗ[Λ] (M × Λ) :=
  LinearMap.prod (LinearMap.fst Λ M Λ + (LinearMap.snd Λ M Λ).smulRight (χ σ)) (LinearMap.snd Λ M Λ)

theorem twAct_apply (χ : Gal x0 → M) (σ : Gal x0) (v : M × Λ) :
    twAct x0 χ σ v = (v.1 + v.2 • χ σ, v.2) := rfl

end Mod

variable [IsIso (X.fromSpecResidueField x0)]

end RamanujanPetersson.EtCompact.Twist

end

end

-- ===== S4.Def_RP_EtCompact_SgUnit =====
section

/-!
# S4-EtCompact, part 42: `Λ_U ≅ g_*Λ_η` at the generic point (K5)

For `g : Y ⟶ X` and a `Λ`-module `M`, `uC g M : M_X ⟶ g_* M_Y` is the sheafified map sending a constant section `m`
over `V` to the constant section `m` over `V ×_X Y` (`uC_constUnit`).
* `mono_uC`: it is a monomorphism when every nonempty etale `V` has nonempty `V ×_X Y` (constant sections over a
  nonempty object are injective, `constUnit_injective`, and every section is locally constant);
* `epi_uC`: it is an epimorphism when every point of every etale `V` has an etale neighbourhood `V'` with
  `V' ×_X Y` having at most one point (every section of `M_Y` over such an object is constant, `eq_constUnit`);
* **`isIso_uC_genPt`**, **`unitIsoPush`**: for `A` a noetherian integrally closed domain, `U = Spec A`, `η` its
  generic point and `g = Spec κ(η) ⟶ U`: `Λ_U ≅ g_* Λ_η` (charts with one generic point, `ChartSch.hChart`, and
  `g` a preimmersion, so `V ×_U Spec κ(η) ↪ V`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

namespace SgUnit

universe u

section General

variable {Λ : Type u} [CommRing Λ] {X Y : Scheme.{u}} (g : Y ⟶ X) (M : ModuleCat.{u} Λ)

/-- The presheaf map `M ⟶ (g_* M_Y)(V)` onto the constant sections. -/
def cPre : constPre (X := X) M ⟶ ((push g Λ).obj (constSh Λ Y M)).obj :=
  Functor.whiskerLeft (etPull g).op (toSheafify Y.smallEtaleTopology (constPre M))

end General

section Spec

variable (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]

variable {Λ : Type} [CommRing Λ]

end Spec

end SgUnit

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_GlobQ =====
section

/-!
# S4-EtCompact, part 54: the global Kummer section at a closed point (F7c of plan v5)

`A` a domain, `g = gen A`, `Ω = κ(η)^sep`, `ι : Ns ⟶ I`, `p : I ⟶ Q` on `Spec κ(η)` with `ι ≫ p = 0`, exact on
stalks, `I` injective, `Gal` trivial on `Ns_x̄`, `d • Ns_x̄ = 0`, `d` a unit of `A`, `ζ ∈ Ω` a primitive `d`-th root
fixed by `Gal`. For `π ≠ 0` in `A` and `r ∈ Ns_x̄`:

* `ϖ ^ d = π`, the character `σ ↦ (dlog(σϖ/ϖ)).val • r` (additive, open kernel), its twist lift `m ∈ I_x̄`;
* `alpha y₀ : Λ_Y ⟶ Q` (stalk `1 ↦ y₀` for a fixed `y₀`), `aMap y₀ := uC g ≫ g_* alpha : Λ_{Spec A} ⟶ g_* Q`;
* **`exists_globQ`**: a global `a : Λ ⟶ g_* Q` whose germs are all `p m`, and `a ≫ c` vanishes near every point of
  `D(π)` for every `c` killing `g_* p` (local triviality over `A[1/π]` with the unit `π`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.GlobQ

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.Kummer
  RamanujanPetersson.EtCompact.LT

section Char

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {d : ℕ} [NeZero d] {ζ : Ω} (hζ : IsPrimitiveRoot ζ d)
  (hζG : ∀ σ : Ω ≃ₐ[K] Ω, σ ζ = ζ) {ϖ : Ω} (hϖ0 : ϖ ≠ 0) (hϖ : ∀ σ : Ω ≃ₐ[K] Ω, σ (ϖ ^ d) = ϖ ^ d)
include hζG hϖ0 hϖ

theorem dlog_mul (σ τ : Ω ≃ₐ[K] Ω) :
    dlog hζ ((σ * τ) ϖ / ϖ) = dlog hζ (σ ϖ / ϖ) + dlog hζ (τ ϖ / ϖ) := by
  have hα : Units.mk0 ϖ hϖ0 ∈ rad (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) d := fun σ _ => hϖ σ
  exact kchar_mul hζ (fun σ _ => hζG σ) hα ⟨σ, Subgroup.mem_top σ⟩ ⟨τ, Subgroup.mem_top τ⟩

end Char

variable (A : Type) [CommRing A] [IsDomain A]

section Alpha

variable {Λ : Type} [CommRing Λ] {Q : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))}

end Alpha

section Main

variable {A} {Λ : Type} [CommRing Λ]
  {Ns I Q : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))} (ι : Ns ⟶ I) (p : I ⟶ Q)

end Main

end RamanujanPetersson.EtCompact.GlobQ

end

end

-- ===== S4.Def_RP_EtCompact_LerayG =====
section

/-!
# S4-EtCompact, part 40: a two-row Leray argument for `g_*` (CC4, formal part)

Generic part (`LerayG`): `adj : L ⊣ R` between abelian categories, `L` preserving monomorphisms, `eAB : L A ≅ B`.
For `N : D` with injective presentation `N ↪ I ↠ Qt N`:
* `R1 R N := coker(R I → R (Qt N))` (`= R¹R N`), short exact `presA : 0 → R N → R I → C → 0` and
  `presB : 0 → C → R (Qt N) → R1 → 0`;
* `lift_push`: lifting `A`-sections along `R φ` from lifting `B`-sections along `φ`.
Under `hη : Ext²(B, -) = 0` and `hR : R1 R (Qt M) = 0` for all `M` (`R²R = 0`):
* **`H_push_Qt_eq_zero`**: `Ext^(m+1)(A, R (Qt M)) = 0`;
* **`H_push_eq_zero_of_R1`**: `Ext^(n+3)(A, R N) = 0` if `Ext^(n+1)(A, R1 R N) = 0`;
* **`H_push_two_eq_zero`**: `Ext²(A, R N) = 0` if every `A`-section of `R1 R N` lifts to `R (Qt N)`.
Specialised to `pull g ⊣ push g`, `A = Λ_X`, `B = Λ_Y` (étale cohomology `H Λ`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

namespace LerayG

open Abelian

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [EnoughInjectives D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- `Qt N = I/N` for the chosen injective presentation. -/
abbrev Qt (N : D) : D := cokernel (Injective.ι N)

/-- `R` of the projection `I → I/N`. -/
abbrev pushπ (R : D ⥤ C) (N : D) : R.obj (Injective.under N) ⟶ R.obj (Qt N) :=
  R.map (cokernel.π (Injective.ι N))

/-- **`R¹R N`**: the cokernel of `R I → R (I/N)`. -/
abbrev R1 (R : D ⥤ C) (N : D) : C := cokernel (pushπ R N)

include adj in
theorem pzm : R.PreservesZeroMorphisms := by
  have := adj.isRightAdjoint
  infer_instance

include adj in
theorem plim : PreservesLimitsOfSize.{0, 0} R := adj.rightAdjoint_preservesLimits

/-- `R N → R I → R (I/N)`. -/
abbrev presI (R : D ⥤ C) [R.PreservesZeroMorphisms] (N : D) : ShortComplex C :=
  ShortComplex.mk (R.map (Injective.ι N)) (pushπ R N) (by
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero])

/-- `0 → R N → R I → C → 0`. -/
abbrev presA (R : D ⥤ C) [R.PreservesZeroMorphisms] (N : D) : ShortComplex C :=
  ShortComplex.mk (R.map (Injective.ι N)) (Abelian.factorThruImage (pushπ R N)) (by
    rw [← cancel_mono (Abelian.image.ι (pushπ R N)), Category.assoc, Abelian.image.fac, zero_comp,
      ← Functor.map_comp, cokernel.condition, Functor.map_zero])

/-- `0 → C → R (Qt N) → R1 → 0`. -/
abbrev presB (R : D ⥤ C) (N : D) : ShortComplex C :=
  ShortComplex.mk (Abelian.image.ι (pushπ R N)) (cokernel.π (pushπ R N)) (by
    rw [← cancel_epi (Abelian.factorThruImage (pushπ R N)), ← Category.assoc, Abelian.image.fac,
      cokernel.condition, comp_zero])

theorem presB_shortExact (R : D ⥤ C) (N : D) : (presB R N).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)

variable [R.PreservesZeroMorphisms]

include adj in
theorem presI_exact (N : D) : (presI R N).Exact := by
  have := plim adj
  exact (injPres_shortExact N).exact.map_of_mono_of_preservesKernel R inferInstance inferInstance

include adj in
theorem presA_shortExact (N : D) : (presA R N).ShortExact where
  exact := by
    let φ : presA R N ⟶ presI R N :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := Abelian.image.ι (pushπ R N)
        comm₁₂ := by simp
        comm₂₃ := by
          show 𝟙 _ ≫ pushπ R N = Abelian.factorThruImage (pushπ R N) ≫ Abelian.image.ι (pushπ R N)
          rw [Abelian.image.fac, Category.id_comp] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 (presI_exact adj N)
  mono_f := by
    have := plim adj
    exact R.map_mono _

variable [L.PreservesMonomorphisms]

include adj in
theorem injective_push (I : D) [Injective I] : Injective (R.obj I) := adj.map_injective I inferInstance

variable {A : C} {B : D} (eAB : L.obj A ≅ B)

include adj eAB in
/-- **Lifting `A`-sections along `R φ`** from lifting `B`-sections along `φ`. -/
theorem lift_push {F F' : D} (φ : F ⟶ F') (h : ∀ b : B ⟶ F', ∃ a : B ⟶ F, a ≫ φ = b)
    (b : A ⟶ R.obj F') : ∃ a : A ⟶ R.obj F, a ≫ R.map φ = b := by
  obtain ⟨a', ha'⟩ := h (eAB.inv ≫ (adj.homEquiv _ _).symm b)
  refine ⟨adj.homEquiv _ _ (eAB.hom ≫ a'), ?_⟩
  rw [← Adjunction.homEquiv_naturality_right, Category.assoc, ha', Iso.hom_inv_id_assoc,
    Equiv.apply_symm_apply]

variable [HasExt.{w} C] [HasExt.{w} D]

omit [EnoughInjectives D] in
/-- From `Ext¹`-vanishing to lifting of `Hom` classes through a short exact sequence. -/
theorem lift_of_ext_one (B : D) {S : ShortComplex D} (hS : S.ShortExact)
    (h : ∀ e : Ext.{w} B S.X₁ 1, e = 0) (b : B ⟶ S.X₃) : ∃ a : B ⟶ S.X₂, a ≫ S.g = b := by
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ _ hS (Ext.mk₀ b) (zero_add 1) (h _)
  refine ⟨Ext.homEquiv₀ x₂, mk₀_injective _ _ ?_⟩
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply, hx₂]

/-- `Ext¹(B, I/M) = 0` when `Ext²(B, -) = 0`. -/
theorem H_Qt_one_eq_zero (hη : ∀ (M : D) (e : Ext.{w} B M 2), e = 0) (M : D) (e : Ext.{w} B (Qt M) 1) :
    e = 0 := by
  obtain ⟨x₂, rfl⟩ := Ext.covariant_sequence_exact₃ _ (injPres_shortExact M) e (show 1 + 1 = 2 from rfl)
    (hη _ _)
  rw [Ext.eq_zero_of_injective x₂, Ext.zero_comp]

end LerayG

open RamanujanPetersson.EtSheaves

universe u

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (Λ : Type u) [CommRing Λ]

/-- `Qt N = I/N` (étale sheaves). -/
abbrev Qt (N : EtSh Λ Y) : EtSh Λ Y := LerayG.Qt N

/-- **`R¹g_* N`** := `coker(g_* I → g_* (I/N))`. -/
abbrev R1 (N : EtSh Λ Y) : EtSh Λ X := LerayG.R1 (push g Λ) N

variable {g Λ}

end RamanujanPetersson.EtCompact

end

end


