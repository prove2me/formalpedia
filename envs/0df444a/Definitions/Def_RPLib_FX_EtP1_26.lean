-- Prove2me | Definitions.Def_RPLib_FX_EtP1_26
-- name    : RPLib_FX_EtP1_26
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T10:26:55.863326+00:00
-- url     : https://prove2.me/theorems/c9b670d9-95ed-55d7-b4e2-cdb744a334f3
-- title:
--   Étale cohomology of the projective line, library file 26 of 34
-- statement:
--   File 26 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_CechSky`: S4-EtCompact: Cech complexes of skyscraper sheaves and of products of them (O8c (B), file C2a)
--   * `S4.Def_RP_EtCompact_God`: S4-EtCompact: the god sheaf of an etale sheaf (O8c (B), file C2b)
--   * `S4.Def_RP_EtCompact_CechAff`: S4-EtCompact: the Cech nerve of an arrow between affine etale objects is affine (O8c (B), file C3)
--   * `S4.Def_RP_EtCompact_Cop`: S4-EtCompact: finite coproducts of affine etale objects (O8c (B), file C4)
--   * `S4.Def_RP_EtCompact_CartanA`: S4-EtCompact: Cartan's lemma, sections part (O8c (B), file C5a)
--   * `S4.Def_RP_EtCompact_Cartan`: S4-EtCompact: Cartan's lemma (O8c (B), file C5b)
--   * `S4.Def_RP_EtCompact_Germ`: S4-EtCompact: germs at the points `geomPtAt x` (O8c (B), file C6a)
--   * `S4.Def_RP_EtCompact_SuppFin`: S4-EtCompact: supports of sections of sheaves supported on closed points (O8c (B), file C6b)
--   * `S4.Def_RP_EtCompact_CoInd`: S4-EtCompact, A1: co-induction from an open subgroup (group layer for `R²g_* = 0`)
--   * `S4.Def_RP_EtCompact_R1Gen`: S4-EtCompact, B1: `R¹g_* N` has vanishing generic stalk, hence no higher cohomology on a curve
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_41

/-!
# Étale cohomology of the projective line, library file 26 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_CechSky`: S4-EtCompact: Cech complexes of skyscraper sheaves and of products of them (O8c (B), file C2a)
* `S4.Def_RP_EtCompact_God`: S4-EtCompact: the god sheaf of an etale sheaf (O8c (B), file C2b)
* `S4.Def_RP_EtCompact_CechAff`: S4-EtCompact: the Cech nerve of an arrow between affine etale objects is affine (O8c (B), file C3)
* `S4.Def_RP_EtCompact_Cop`: S4-EtCompact: finite coproducts of affine etale objects (O8c (B), file C4)
* `S4.Def_RP_EtCompact_CartanA`: S4-EtCompact: Cartan's lemma, sections part (O8c (B), file C5a)
* `S4.Def_RP_EtCompact_Cartan`: S4-EtCompact: Cartan's lemma (O8c (B), file C5b)
* `S4.Def_RP_EtCompact_Germ`: S4-EtCompact: germs at the points `geomPtAt x` (O8c (B), file C6a)
* `S4.Def_RP_EtCompact_SuppFin`: S4-EtCompact: supports of sections of sheaves supported on closed points (O8c (B), file C6b)
* `S4.Def_RP_EtCompact_CoInd`: S4-EtCompact, A1: co-induction from an open subgroup (group layer for `R²g_* = 0`)
* `S4.Def_RP_EtCompact_R1Gen`: S4-EtCompact, B1: `R¹g_* N` has vanishing generic stalk, hence no higher cohomology on a curve
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_CechSky =====
section

/-!
# S4-EtCompact: Cech complexes of skyscraper sheaves and of products of them (O8c (B), file C2a)

* `Cech.ExtraCodeg.ofIso`, `Cech.ExtraCodeg.ofPi`: extra codegeneracies transport along isomorphisms of
  cosimplicial modules and pass to products.
* `Cech.fiber_map_surjective`: a point of a site is surjective on fibres along a covering arrow.
* `Cech.skyCodeg`: for a point `Φ` and an arrow `f` with a section of `Φ.fiber.map f`, the Cech cosimplicial module
  `n ↦ (Φ.skyscraperPresheaf M)(N_n)` of `f` has extra codegeneracies.
* **`Cech.godCodeg`, `Cech.god_cech_exactAt`**: for a covering arrow `f` and any family of points, the Cech complex
  of `f` with values in the product sheaf `∏ᵢ (Φ i).skyscraperSheaf (M i)` is exact in degrees `≥ 1`.
-/

set_option autoImplicit false

open CategoryTheory Limits AlgebraicTopology Opposite Simplicial

noncomputable section

namespace RamanujanPetersson.EtCompact.Cech

universe v u w w'

section Transfer

variable {Λ : Type w'} [CommRing Λ]

/-- Extra codegeneracies transport along an isomorphism of cosimplicial modules. -/
def ExtraCodeg.ofIso {X Y : SimplexCategory ⥤ ModuleCat.{w} Λ} (φ : X ≅ Y) (e : ExtraCodeg Y) :
    ExtraCodeg X where
  h n := φ.hom.app _ ≫ e.h n ≫ φ.inv.app _
  h_δ₀ n := by
    have h0 := e.h_δ₀ n
    dsimp only [CosimplicialObject.δ] at h0 ⊢
    rw [NatTrans.naturality_assoc, reassoc_of% h0, Iso.hom_inv_id_app]
  h_δ_succ n j := by
    have h1 := e.h_δ_succ n j
    dsimp only [CosimplicialObject.δ] at h1 ⊢
    rw [NatTrans.naturality_assoc, reassoc_of% h1, NatTrans.naturality]
    simp only [Category.assoc]

/-- Extra codegeneracies pass to products of cosimplicial modules. -/
def ExtraCodeg.ofPi {ι : Type w} (K : ι → SimplexCategory ⥤ ModuleCat.{w} Λ)
    (e : ∀ i, ExtraCodeg (K i)) : ExtraCodeg (∏ᶜ K : SimplexCategory ⥤ ModuleCat.{w} Λ) where
  h n := (piObjIso K ⦋n + 1⦌).hom ≫ Limits.Pi.map (fun i => (e i).h n) ≫ (piObjIso K ⦋n⦌).inv
  h_δ₀ n := by
    rw [← cancel_mono (piObjIso K ⦋n⦌).hom]
    refine Limits.Pi.hom_ext _ _ fun i => ?_
    have h0 := (e i).h_δ₀ n
    dsimp only [CosimplicialObject.δ] at h0 ⊢
    simp only [Category.assoc, piObjIso_inv_comp_π, Limits.Pi.map_π, piObjIso_hom_comp_π,
      piObjIso_hom_comp_π_assoc, Category.id_comp, NatTrans.naturality_assoc, h0, Category.comp_id]
  h_δ_succ n j := by
    rw [← cancel_mono (piObjIso K ⦋n + 1⦌).hom]
    refine Limits.Pi.hom_ext _ _ fun i => ?_
    have h1 := (e i).h_δ_succ n j
    dsimp only [CosimplicialObject.δ] at h1 ⊢
    simp only [Category.assoc, piObjIso_inv_comp_π, piObjIso_inv_comp_π_assoc, Limits.Pi.map_π,
      Limits.Pi.map_π_assoc, piObjIso_hom_comp_π, piObjIso_hom_comp_π_assoc,
      NatTrans.naturality, NatTrans.naturality_assoc, h1]

end Transfer

section Sky

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A point of a site is surjective on fibres along a covering arrow. -/
theorem fiber_map_surjective (Φ : J.Point) {V W : C} (f : V ⟶ W)
    (hf : Sieve.ofArrows _ (fun _ : Unit => f) ∈ J W) : Function.Surjective (Φ.fiber.map f) := by
  intro x
  obtain ⟨Z, g, hg, z, rfl⟩ := Φ.jointly_surjective _ hf x
  obtain ⟨Z', h, g', ⟨i⟩, rfl⟩ := hg
  exact ⟨Φ.fiber.map h z, by rw [← Functor.map_comp_apply]⟩

variable [HasFiniteWidePullbacks C] [LocallySmall.{w} C] (Φ : GrothendieckTopology.Point.{w} J) {Λ : Type w'} [CommRing Λ] (M : ModuleCat.{w} Λ)
  {V W : C} (f : V ⟶ W)

/-- The Cech cosimplicial module `n ↦ (Φ.skyscraperPresheaf M)(N_n)` of `f`. -/
def skyCech : CosimplicialObject (ModuleCat.{w} Λ) :=
  (Arrow.mk f).cechNerve.rightOp ⋙ Φ.skyscraperPresheaf M

omit [LocallySmall.{w} C] in
theorem sky_δ_π {n : ℕ} (i : Fin (n + 2))
    (b : Φ.fiber.obj (widePullback W (fun _ : Fin (n + 2) => V) (fun _ => f))) :
    CosimplicialObject.δ (skyCech Φ M f) i ≫ Limits.Pi.π (fun _ => M) b =
      Limits.Pi.π (fun _ => M) (Φ.fiber.map ((Arrow.mk f).cechNerve.δ i) b) :=
  (Limits.Pi.map'_comp_π _ _ b).trans (Category.comp_id _)

set_option backward.isDefEq.respectTransparency false in
/-- The extra codegeneracies of the Cech cosimplicial module of a skyscraper presheaf. -/
def skyCodeg (σ : Φ.fiber.obj W → Φ.fiber.obj V) (hσ : ∀ w, Φ.fiber.map f (σ w) = w) :
    ExtraCodeg (skyCech Φ M f) where
  h n := Limits.Pi.lift (fun a : Φ.fiber.obj (widePullback W (fun _ : Fin (n + 1) => V) (fun _ => f)) =>
    Limits.Pi.π (fun _ => M) (cons (P := Φ.fiber) (f := f) σ hσ a))
  h_δ₀ n := by
    refine Limits.Pi.hom_ext _ _ fun a => ?_
    rw [Category.assoc, Limits.Pi.lift_π, sky_δ_π, δ_zero_cons, Category.id_comp]
    rfl
  h_δ_succ n j := by
    refine Limits.Pi.hom_ext _ _ fun a => ?_
    rw [Category.assoc, Limits.Pi.lift_π, sky_δ_π, δ_succ_cons, Category.assoc, sky_δ_π]
    exact (Limits.Pi.lift_π
      (fun b : Φ.fiber.obj (widePullback W (fun _ : Fin (n + 1) => V) (fun _ => f)) =>
        Limits.Pi.π (fun _ => M) (cons (P := Φ.fiber) (f := f) σ hσ b))
      (Φ.fiber.map ((Arrow.mk f).cechNerve.δ j) a)).symm

variable {ι : Type w} (Φs : ι → GrothendieckTopology.Point.{w} J) (Ms : ι → ModuleCat.{w} Λ)

/-- The Cech cosimplicial module of the product sheaf `∏ᵢ (Φs i).skyscraperSheaf (Ms i)` is the product of the
Cech cosimplicial modules of the factors. -/
def godCechIso :
    (Arrow.mk f).cechNerve.rightOp ⋙ (∏ᶜ fun i => (Φs i).skyscraperSheaf (Ms i)).obj ≅
      ∏ᶜ fun i => (Arrow.mk f).cechNerve.rightOp ⋙ (Φs i).skyscraperPresheaf (Ms i) :=
  Functor.isoWhiskerLeft _
      (PreservesProduct.iso (sheafToPresheaf J (ModuleCat.{w} Λ))
        (fun i => (Φs i).skyscraperSheaf (Ms i))) ≪≫
    PreservesProduct.iso ((Functor.whiskeringLeft _ _ _).obj (Arrow.mk f).cechNerve.rightOp)
      (fun i => (Φs i).skyscraperPresheaf (Ms i))

/-- Extra codegeneracies of the Cech cosimplicial module of the product sheaf, along a covering arrow. -/
def godCodeg (hf : Sieve.ofArrows _ (fun _ : Unit => f) ∈ J W) :
    ExtraCodeg ((Arrow.mk f).cechNerve.rightOp ⋙ (∏ᶜ fun i => (Φs i).skyscraperSheaf (Ms i)).obj) :=
  ExtraCodeg.ofIso (godCechIso f Φs Ms) (ExtraCodeg.ofPi _ fun i =>
    skyCodeg (Φs i) (Ms i) f (fun w => (fiber_map_surjective (Φs i) f hf w).choose)
      (fun w => (fiber_map_surjective (Φs i) f hf w).choose_spec))

/-- **The Cech complex of a covering arrow with values in a product of skyscraper sheaves is exact in
degrees `≥ 1`.** -/
theorem god_cech_exactAt (hf : Sieve.ofArrows _ (fun _ : Unit => f) ∈ J W) (n : ℕ) :
    ((alternatingCofaceMapComplex (ModuleCat.{w} Λ)).obj
      ((Arrow.mk f).cechNerve.rightOp ⋙ (∏ᶜ fun i => (Φs i).skyscraperSheaf (Ms i)).obj)).ExactAt (n + 1) :=
  (godCodeg f Φs Ms hf).exactAt_succ n

end Sky

end RamanujanPetersson.EtCompact.Cech

end

end

-- ===== S4.Def_RP_EtCompact_God =====
section

/-!
# S4-EtCompact: the god sheaf of an etale sheaf (O8c (B), file C2b)

For `F : EtSh Λ Y`, `god Λ F := ∏ₓ (x_*) (J_x)` with `J_x` an injective module containing the stalk `F_x`
(`x : Y`, geometric points `geomPtAt x`).
* `god Λ F` is injective; `godι Λ F : F ⟶ god Λ F` is a monomorphism.
* `cover_of_surjective`: a surjective etale arrow is a covering of the small etale site.
* **`god_cech_exactAt'`**: the Cech complex of a surjective etale arrow with values in `god Λ F` is exact in degrees
  `≥ 1`.
-/

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry AlgebraicTopology Opposite Simplicial
open RamanujanPetersson.EtSheaves

noncomputable section

namespace RamanujanPetersson.EtCompact.Cech

universe u

/-- A surjective arrow of the small etale site is a covering. -/
theorem cover_of_surjective {Y : Scheme.{u}} {V W : Y.Etale} (f : V ⟶ W) (hf : Function.Surjective f.left) :
    Sieve.ofArrows _ (fun _ : Unit => f) ∈ Y.smallEtaleTopology W := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  exact Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 ⟨(), hf y⟩

variable (Λ : Type u) [CommRing Λ] {Y : Scheme.{u}} (F : EtSh Λ Y)

/-- An injective module containing the stalk of `F` at `x`. -/
def godJ (x : Y) : ModuleCat.{u} Λ := Injective.under ((geomPtAt x).point.sheafFiber.obj F)

instance (x : Y) : Injective (godJ Λ F x) := inferInstanceAs (Injective (Injective.under _))

/-- The embedding of the stalk `F_x` into `J_x`. -/
def godm (x : Y) : (geomPtAt x).point.sheafFiber.obj F ⟶ godJ Λ F x := Injective.ι _

instance (x : Y) : Mono (godm Λ F x) := inferInstanceAs (Mono (Injective.ι _))

/-- The god sheaf `∏ₓ (x_*) (J_x)`. -/
abbrev god : EtSh Λ Y := ∏ᶜ fun x : Y => (geomPtAt x).point.skyscraperSheaf (godJ Λ F x)

instance (x : Y) : Injective ((geomPtAt x).point.skyscraperSheaf (godJ Λ F x)) :=
  Injective.injective_of_adjoint (geomPtAt x).point.skyscraperSheafAdjunction _

instance : Injective (god Λ F) := by
  dsimp only [god]; infer_instance

/-- The component of `godι` at `x`. -/
def godιx (x : Y) : F ⟶ (geomPtAt x).point.skyscraperSheaf (godJ Λ F x) :=
  (geomPtAt x).point.skyscraperSheafAdjunction.homEquiv F (godJ Λ F x) (godm Λ F x)

/-- The embedding `F ⟶ god Λ F`. -/
def godι : F ⟶ god Λ F := Pi.lift fun x => godιx Λ F x

theorem godι_π (x : Y) :
    godι Λ F ≫ Pi.π (fun x : Y => (geomPtAt x).point.skyscraperSheaf (godJ Λ F x)) x = godιx Λ F x :=
  Pi.lift_π _ _

instance : Mono (godι Λ F) := by
  refine Preadditive.mono_of_cancel_zero _ fun {Z} g hg => ?_
  refine hom_ext_stalk Λ fun x => ?_
  rw [Functor.map_zero]
  change (geomPtAt x).point.sheafFiber.map g = 0
  have h1 : g ≫ godιx Λ F x = 0 := by
    have := congrArg (· ≫ Pi.π (fun x : Y => (geomPtAt x).point.skyscraperSheaf (godJ Λ F x)) x) hg
    simpa only [Category.assoc, godι_π, zero_comp] using this
  have h2 := congrArg ((geomPtAt x).point.skyscraperSheafAdjunction.homEquiv Z (godJ Λ F x)).symm h1
  rw [godιx, Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply, Adjunction.homEquiv_counit,
    Functor.map_zero, zero_comp] at h2
  exact (cancel_mono (godm Λ F x)).1 (h2.trans zero_comp.symm)

/-- **The Cech complex of a surjective etale arrow with values in the god sheaf is exact in degrees `≥ 1`.** -/
theorem god_cech_exactAt' {V W : Y.Etale} (f : V ⟶ W) (hf : Function.Surjective f.left) (n : ℕ) :
    ((alternatingCofaceMapComplex (ModuleCat.{u} Λ)).obj
      ((Arrow.mk f).cechNerve.rightOp ⋙ (god Λ F).obj)).ExactAt (n + 1) :=
  god_cech_exactAt f (fun x : Y => (geomPtAt x).point) (godJ Λ F) (cover_of_surjective f hf) n

end RamanujanPetersson.EtCompact.Cech

end

end

-- ===== S4.Def_RP_EtCompact_CechAff =====
section

/-!
# S4-EtCompact: the Cech nerve of an arrow between affine etale objects is affine (O8c (B), file C3)
* `nerve_isPullback`: the `(n+2)`-fold wide pullback is the pullback of the `(n+1)`-fold one along `f`.
* **`isAffine_cechNerve`**: for `f : V ⟶ W` in `Y.Etale` with `V.left`, `W.left` affine, every object of the
  Cech nerve of `f` has affine underlying scheme.
-/

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial

noncomputable section

namespace RamanujanPetersson.EtCompact.Cech

universe u

section Gen

variable {C : Type*} [Category C] [HasFiniteWidePullbacks C] {V W : C} (f : V ⟶ W)

/-- Dropping the last factor of a wide pullback. -/
abbrev dropLast (n : ℕ) :
    widePullback W (fun _ : Fin (n + 2) => V) (fun _ => f) ⟶
      widePullback W (fun _ : Fin (n + 1) => V) (fun _ => f) :=
  WidePullback.lift (WidePullback.base _) (fun j => WidePullback.π _ j.castSucc)
    (fun _ => WidePullback.π_arrow _ _)

theorem nerve_commSq (n : ℕ) :
    CommSq (dropLast f n) (WidePullback.π (fun _ : Fin (n + 2) => f) (Fin.last (n + 1)))
      (WidePullback.base (fun _ : Fin (n + 1) => f)) f :=
  ⟨by rw [WidePullback.lift_base, WidePullback.π_arrow]⟩

theorem nerve_isPullback (n : ℕ) :
    IsPullback (dropLast f n) (WidePullback.π (fun _ : Fin (n + 2) => f) (Fin.last (n + 1)))
      (WidePullback.base (fun _ : Fin (n + 1) => f)) f := by
  refine IsPullback.of_isLimit' (nerve_commSq f n) (PullbackCone.IsLimit.mk _
    (fun s => WidePullback.lift (s.fst ≫ WidePullback.base _)
      (Fin.lastCases s.snd fun j => s.fst ≫ WidePullback.π _ j) (fun j => by
        refine Fin.lastCases ?_ (fun j => ?_) j
        · rw [Fin.lastCases_last]; exact s.condition.symm
        · rw [Fin.lastCases_castSucc, Category.assoc, WidePullback.π_arrow]))
    (fun s => ?_) (fun s => ?_) (fun s m h1 h2 => ?_))
  · refine WidePullback.hom_ext _ _ _ (fun j => ?_) ?_
    · rw [Category.assoc, WidePullback.lift_π, WidePullback.lift_π, Fin.lastCases_castSucc]
    · rw [Category.assoc, WidePullback.lift_base, WidePullback.lift_base]
  · rw [WidePullback.lift_π, Fin.lastCases_last]
  · refine WidePullback.hom_ext _ _ _ (fun j => ?_) ?_
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [WidePullback.lift_π, Fin.lastCases_last]; exact h2
      · rw [WidePullback.lift_π, Fin.lastCases_castSucc, ← h1, Category.assoc, WidePullback.lift_π]
    · rw [WidePullback.lift_base, ← h1, Category.assoc, WidePullback.lift_base]

instance isIso_π_zero : IsIso (WidePullback.π (fun _ : Fin 1 => f) 0) :=
  ⟨⟨WidePullback.lift f (fun _ => 𝟙 V) (fun _ => Category.id_comp _), by
    refine WidePullback.hom_ext _ _ _ (fun j => ?_) ?_
    · rw [Subsingleton.elim j 0, Category.assoc, WidePullback.lift_π, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, WidePullback.lift_base, WidePullback.π_arrow, Category.id_comp], by
    rw [WidePullback.lift_π]⟩⟩

end Gen

variable {Y : Scheme.{u}} {V W : Y.Etale} (f : V ⟶ W)

/-- **The objects of the Cech nerve of an arrow between affine etale objects are affine.** -/
theorem isAffine_nerve [IsAffine V.left] [IsAffine W.left] (n : ℕ) :
    IsAffine (widePullback W (fun _ : Fin (n + 1) => V) (fun _ => f)).left := by
  induction n with
  | zero =>
    have : IsIso (WidePullback.π (fun _ : Fin 1 => f) 0).left :=
      Functor.map_isIso (Scheme.Etale.forget Y ⋙ CategoryTheory.Over.forget Y) _
    exact IsAffine.of_isIso (WidePullback.π (fun _ : Fin 1 => f) 0).left
  | succ n ih =>
    have hP := (nerve_isPullback f n).map (Scheme.Etale.forget Y ⋙ CategoryTheory.Over.forget Y)
    have : IsAffine (pullback (WidePullback.base (fun _ : Fin (n + 1) => f)).left f.left) := inferInstance
    let e := hP.isoPullback
    exact @IsAffine.of_isIso _ _ e.hom (Iso.isIso_hom e) this

theorem isAffine_cechNerve [IsAffine V.left] [IsAffine W.left] (n : ℕ) :
    IsAffine ((Arrow.mk f).cechNerve.obj (op ⦋n⦌)).left :=
  isAffine_nerve f n

end RamanujanPetersson.EtCompact.Cech

end

end

-- ===== S4.Def_RP_EtCompact_Cop =====
section

/-!
# S4-EtCompact: finite coproducts of affine etale objects (O8c (B), file C4)

* `exists_affine_refine`: a covering sieve of an affine etale object `T` contains a finite family of arrows from
  affine etale objects that is jointly surjective.
* `cop S`: the coproduct of a family of etale objects (`(cop S).left = ∐ (S k).left`), with `copι`, `copDesc`;
  `cop` of affine objects is affine; `copDesc` is surjective if the family is jointly surjective.
* `sep_of_cover`, **`cop_glue`**: every sheaf glues along the coproduct injections.
-/

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry Opposite
open RamanujanPetersson.EtSheaves

noncomputable section

namespace RamanujanPetersson.EtCompact.Cech

universe u

variable {Y : Scheme.{u}}

/-- **Finite affine refinement** of a covering sieve of an affine etale object. -/
theorem exists_affine_refine (T : Y.Etale) [IsAffine T.left] (R : Sieve T) (hR : R ∈ Y.smallEtaleTopology T) :
    ∃ (ι : Type u) (_ : Finite ι) (S : ι → Y.Etale) (g : ∀ k, S k ⟶ T),
      (∀ k, IsAffine (S k).left) ∧ (∀ k, R (g k)) ∧ ∀ x : T.left, ∃ k s, (g k).left s = x := by
  classical
  rw [mem_smallEtale_iff] at hR
  choose W g w hg hw using hR
  let a (x : T.left) : (W x).left.affineCover.X ((W x).left.affineCover.idx (w x)) ⟶ (W x).left :=
    (W x).left.affineCover.f _
  let S (x : T.left) : Y.Etale := Scheme.Etale.mk (a x ≫ (W x).hom)
  let h (x : T.left) : S x ⟶ W x := MorphismProperty.Over.homMk (a x) rfl
  have hO : ∀ x, IsOpen (Set.range ((h x ≫ g x).left)) := fun x =>
    ((h x ≫ g x).left).isOpenMap.isOpen_range
  have hcov : (Set.univ : Set T.left) ⊆ ⋃ x, Set.range ((h x ≫ g x).left) := by
    intro x _
    obtain ⟨y, hy⟩ := (W x).left.affineCover.covers (w x)
    refine Set.mem_iUnion.2 ⟨x, y, ?_⟩
    change (g x).left ((W x).left.affineCover.f _ y) = x
    rw [hy, hw]
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hO hcov
  refine ⟨t, inferInstance, fun k => S k.1, fun k => h k.1 ≫ g k.1, fun k => ?_,
    fun k => R.downward_closed (hg k.1) _, fun x => ?_⟩
  · change IsAffine ((W k.1).left.affineCover.X _)
    infer_instance
  · obtain ⟨k, hk, s, hs⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨⟨k, hk⟩, s, hs⟩

section Cop

variable {ι : Type u} (S : ι → Y.Etale)

instance etale_sigmaDesc : Etale (Sigma.desc fun k => (S k).hom) :=
  haveI : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance

/-- The coproduct of a finite family of etale objects. -/
def cop : Y.Etale := Scheme.Etale.mk (Sigma.desc fun k => (S k).hom)

/-- The coproduct injections. -/
def copι (k : ι) : S k ⟶ cop S :=
  MorphismProperty.Over.homMk (Sigma.ι (fun k => (S k).left) k) (Sigma.ι_desc _ _)

variable {S} {T : Y.Etale} (g : ∀ k, S k ⟶ T)

/-- The map from the coproduct. -/
def copDesc : cop S ⟶ T :=
  MorphismProperty.Over.homMk (Sigma.desc fun k => (g k).left) (Sigma.hom_ext _ _ fun k => by
    change Sigma.ι (fun k => (S k).left) k ≫ (Sigma.desc fun k => (g k).left) ≫ T.hom =
      Sigma.ι (fun k => (S k).left) k ≫ Sigma.desc fun k => (S k).hom
    rw [Sigma.ι_desc_assoc, Sigma.ι_desc]
    exact MorphismProperty.Over.w (g k))

theorem copι_desc (k : ι) : copι S k ≫ copDesc g = g k :=
  MorphismProperty.Over.Hom.ext (Sigma.ι_desc _ _)

theorem copι_left (k : ι) : (copι S k).left = Sigma.ι (fun k => (S k).left) k := rfl

variable (S) in
instance isAffine_cop [Finite ι] [∀ k, IsAffine (S k).left] : IsAffine (cop S).left :=
  inferInstanceAs (IsAffine (∐ fun k => (S k).left))

variable (S) in
theorem cop_jointly (z : (cop S).left) : ∃ k s, (copι S k).left s = z := by
  obtain ⟨⟨k, s⟩, rfl⟩ := (sigmaMk fun k => (S k).left).surjective z
  refine ⟨k, s, ?_⟩
  show Sigma.ι (fun k => (S k).left) k s = _
  exact (sigmaMk_mk (fun k => (S k).left) k s).symm

theorem copDesc_surjective (hg : ∀ x : T.left, ∃ k s, (g k).left s = x) :
    Function.Surjective (copDesc g).left := by
  intro x
  obtain ⟨k, s, rfl⟩ := hg x
  refine ⟨(copι S k).left s, ?_⟩
  rw [← Scheme.Hom.comp_apply]
  exact congrArg (fun φ : S k ⟶ T => φ.left s) (copι_desc g k)

variable (S) in
theorem cop_cover : Sieve.ofArrows S (copι S) ∈ Y.smallEtaleTopology (cop S) := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  exact Set.eq_univ_of_forall fun z => Set.mem_iUnion.2 (by
    obtain ⟨k, s, hs⟩ := cop_jointly S z
    exact ⟨k, s, hs⟩)

end Cop

variable {Λ : Type u} [CommRing Λ]

/-- Sections of a sheaf agreeing on a covering family agree. -/
theorem sep_of_cover (F : EtSh Λ Y) {U : Y.Etale} {I : Type*} {V : I → Y.Etale} (f : ∀ i, V i ⟶ U)
    (hR : Sieve.ofArrows V f ∈ Y.smallEtaleTopology U) (s s' : F.obj.obj (op U))
    (h : ∀ i, (F.obj.map (f i).op).hom s = (F.obj.map (f i).op).hom s') : s = s' := by
  obtain ⟨t, -, hu⟩ := existsUnique_glue F f hR (fun i => (F.obj.map (f i).op).hom s)
    (fun i j W gi gj e => by
      rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← F.obj.map_comp, ← F.obj.map_comp, ← op_comp,
        ← op_comp, e])
  exact (hu s fun i => rfl).trans (hu s' fun i => (h i).symm).symm

/-- **Gluing along the coproduct injections.** -/
theorem cop_glue {ι : Type u} (S : ι → Y.Etale) (F : EtSh Λ Y) (x : ∀ k, F.obj.obj (op (S k))) :
    ∃ s, ∀ k, (F.obj.map (copι S k).op).hom s = x k := by
  classical
  obtain ⟨s, hs, -⟩ := existsUnique_glue F (copι S) (cop_cover S) x fun i j W gi gj e => by
    have e' : gi.left ≫ Sigma.ι (fun k => (S k).left) i = gj.left ≫ Sigma.ι (fun k => (S k).left) j :=
      congrArg (fun φ : W ⟶ cop S => φ.left) e
    by_cases hij : i = j
    · subst hij
      have : gi = gj := MorphismProperty.Over.Hom.ext ((cancel_mono _).1 e')
      rw [this]
    · have hz := isZero_obj_of_isEmpty Λ F W (isEmpty_of_commSq_sigmaι_of_ne ⟨e'⟩ hij)
      exact (ModuleCat.subsingleton_of_isZero hz).elim _ _
  exact ⟨s, hs⟩

end RamanujanPetersson.EtCompact.Cech

end

end

-- ===== S4.Def_RP_EtCompact_CartanA =====
section

/-!
# S4-EtCompact: Cartan's lemma, sections part (O8c (B), file C5a)

`cechC Λ F f` is the Cech complex of the etale sheaf `F` along `f : V ⟶ W`; `CechExact Λ F` says it is exact in
degrees `≥ 1` for every surjective `f` between affine etale objects. For a short exact sequence
`0 → X₁ → X₂ → X₃ → 0` of etale sheaves:
* **`sections_surj`**: if `X₁` is Cech-exact, `X₂(T) → X₃(T)` is surjective for every affine `T`;
* **`cechExact_X₃`**: if `X₁` and `X₂` are Cech-exact, so is `X₃`.
-/

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry AlgebraicTopology Opposite Simplicial
open RamanujanPetersson.EtSheaves

noncomputable section

namespace RamanujanPetersson.EtCompact.Cech

universe u

theorem objD_zero {C : Type*} [Category C] [Preadditive C] (X : CosimplicialObject C) :
    AlternatingCofaceMapComplex.objD X 0 = X.δ 0 - X.δ 1 := by
  simp [AlternatingCofaceMapComplex.objD, Fin.sum_univ_two, sub_eq_add_neg]

theorem exactAt_iff_elt {Λ : Type u} [CommRing Λ] (K : CochainComplex (ModuleCat.{u} Λ) ℕ) (n : ℕ) :
    K.ExactAt (n + 1) ↔ ∀ x : K.X (n + 1), (K.d (n + 1) (n + 2)).hom x = 0 →
      ∃ y : K.X n, (K.d n (n + 1)).hom y = x := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp), ShortComplex.moduleCat_exact_iff]
  rfl

variable (Λ : Type u) [CommRing Λ] {Y : Scheme.{u}}

/-- The Cech complex of `F` along `f`. -/
abbrev cechC (F : EtSh Λ Y) {V W : Y.Etale} (f : V ⟶ W) : CochainComplex (ModuleCat.{u} Λ) ℕ :=
  (alternatingCofaceMapComplex (ModuleCat.{u} Λ)).obj ((Arrow.mk f).cechNerve.rightOp ⋙ F.obj)

/-- **Cech-exactness** on surjective arrows between affine etale objects. -/
def CechExact (F : EtSh Λ Y) : Prop :=
  ∀ ⦃V W : Y.Etale⦄ (f : V ⟶ W), IsAffine V.left → IsAffine W.left → Function.Surjective f.left →
    ∀ n : ℕ, (cechC Λ F f).ExactAt (n + 1)

variable {Λ}

/-- The `n`-th object of the Cech nerve. -/
abbrev nv {V W : Y.Etale} (f : V ⟶ W) (n : ℕ) : Y.Etale := (Arrow.mk f).cechNerve.obj (op ⦋n⦌)

/-- The Cech differential, typed on sections over the nerve. -/
abbrev cd (F : EtSh Λ Y) {V W : Y.Etale} (f : V ⟶ W) (i j : ℕ) :
    F.obj.obj (op (nv f i)) ⟶ F.obj.obj (op (nv f j)) :=
  (cechC Λ F f).d i j

/-- The face maps `N₁ ⟶ N₀`. -/
abbrev dl {V W : Y.Etale} (f : V ⟶ W) (i : Fin 2) : nv f 1 ⟶ nv f 0 := (Arrow.mk f).cechNerve.δ i

/-- The map of Cech complexes induced by a map of sheaves. -/
abbrev cechMap {F G : EtSh Λ Y} (φ : F ⟶ G) {V W : Y.Etale} (f : V ⟶ W) : cechC Λ F f ⟶ cechC Λ G f :=
  (alternatingCofaceMapComplex (ModuleCat.{u} Λ)).map
    (Functor.whiskerLeft (Arrow.mk f).cechNerve.rightOp φ.hom)

theorem cech_d_nat {F G : EtSh Λ Y} (φ : F ⟶ G) {V W : Y.Etale} (f : V ⟶ W) (i j : ℕ)
    (x : F.obj.obj (op (nv f i))) :
    (cd G f i j).hom ((φ.hom.app (op (nv f i))).hom x) = (φ.hom.app (op (nv f j))).hom ((cd F f i j).hom x) := by
  have h := congrArg (fun h => h.hom x) ((cechMap φ f).comm i j)
  exact h

theorem cd_cd (F : EtSh Λ Y) {V W : Y.Etale} (f : V ⟶ W) (i j k : ℕ) (x : F.obj.obj (op (nv f i))) :
    (cd F f j k).hom ((cd F f i j).hom x) = 0 := by
  have h := congrArg (fun h => h.hom x) ((cechC Λ F f).d_comp_d i j k)
  exact h

theorem cech_d0 (F : EtSh Λ Y) {V W : Y.Etale} (f : V ⟶ W) :
    cd F f 0 1 = F.obj.map (dl f 0).op - F.obj.map (dl f 1).op :=
  (d_eq (X := (Arrow.mk f).cechNerve.rightOp ⋙ F.obj) 0).trans
    (objD_zero ((Arrow.mk f).cechNerve.rightOp ⋙ F.obj))

theorem cech_d0_apply (F : EtSh Λ Y) {V W : Y.Etale} (f : V ⟶ W) (x : F.obj.obj (op (nv f 0))) :
    (cd F f 0 1).hom x = (F.obj.map (dl f 0).op).hom x - (F.obj.map (dl f 1).op).hom x := by
  rw [cech_d0]
  rfl

theorem cech_exact_elt (F : EtSh Λ Y) {V W : Y.Etale} (f : V ⟶ W) (i j k : ℕ) (hj : j = i + 1) (hk : k = i + 2)
    (h : (cechC Λ F f).ExactAt j) (x : F.obj.obj (op (nv f j))) (hx : (cd F f j k).hom x = 0) :
    ∃ y : F.obj.obj (op (nv f i)), (cd F f i j).hom y = x := by
  subst hj hk
  exact (exactAt_iff_elt _ i).1 h x hx

theorem cech_exactAt_of_elt (F : EtSh Λ Y) {V W : Y.Etale} (f : V ⟶ W) (n : ℕ)
    (h : ∀ x : F.obj.obj (op (nv f (n + 1))), (cd F f (n + 1) (n + 2)).hom x = 0 →
      ∃ y : F.obj.obj (op (nv f n)), (cd F f n (n + 1)).hom y = x) :
    (cechC Λ F f).ExactAt (n + 1) :=
  (exactAt_iff_elt _ n).2 h

section Nerve0

variable {V T : Y.Etale} (f : V ⟶ T)

/-- The structure map `N₀ ⟶ T`. -/
abbrev base0 : nv f 0 ⟶ T := WidePullback.base (fun _ : Fin 1 => f)

/-- The projection `N₀ ⟶ V` (an isomorphism). -/
abbrev pi0 : nv f 0 ⟶ V := WidePullback.π (fun _ : Fin 1 => f) 0

theorem pi0_arrow : pi0 f ≫ f = base0 f := WidePullback.π_arrow _ 0

theorem δ_π0 (i : Fin 2) :
    dl f i ≫ WidePullback.π (fun _ : Fin 1 => f) 0 =
      WidePullback.π (fun _ : Fin 2 => f) (i.succAbove 0) :=
  δ_π f i 0

theorem δ_base0 (i : Fin 2) :
    dl f i ≫ WidePullback.base (fun _ : Fin 1 => f) =
      WidePullback.base (fun _ : Fin 2 => f) :=
  δ_base f i

theorem base0_surj (hf : Function.Surjective f.left) : Function.Surjective (base0 f).left := by
  have : IsIso (pi0 f).left := Functor.map_isIso (Scheme.Etale.forget Y ⋙ CategoryTheory.Over.forget Y) (pi0 f)
  have e : (base0 f).left = (pi0 f).left ≫ f.left :=
    congrArg (fun φ : nv f 0 ⟶ T => φ.left) (pi0_arrow f).symm
  intro t
  obtain ⟨v, rfl⟩ := hf t
  refine ⟨(inv (pi0 f).left) v, ?_⟩
  rw [e, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (inv (pi0 f).left), IsIso.inv_hom_id]
  rfl

/-- **Descent** along a surjective arrow: a Cech `0`-cocycle comes from `T`. -/
theorem descend (F : EtSh Λ Y) (hf : Function.Surjective f.left) (x : F.obj.obj (op (nv f 0)))
    (hx : (cd F f 0 1).hom x = 0) :
    ∃ p : F.obj.obj (op T), (F.obj.map (base0 f).op).hom p = x := by
  rw [cech_d0_apply, sub_eq_zero] at hx
  obtain ⟨p, hp, -⟩ := existsUnique_glue F (fun _ : Unit => base0 f) (cover_of_surjective _ (base0_surj f hf))
    (fun _ => x) (fun _ _ Z gi gj e => by
      have w : ∀ j : Fin 2, (![gi ≫ pi0 f, gj ≫ pi0 f] : Fin 2 → (Z ⟶ V)) j ≫ f = gi ≫ base0 f := by
        refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
        · simp [Category.assoc]
        · simp [Category.assoc, e]
      obtain ⟨ℓ, hℓ0, hℓ1⟩ : ∃ ℓ : Z ⟶ nv f 1, ℓ ≫ dl f 0 = gj ∧ ℓ ≫ dl f 1 = gi := by
        refine ⟨WidePullback.lift (gi ≫ base0 f) _ w, ?_, ?_⟩
        · refine WidePullback.hom_ext (fun _ : Fin 1 => f) _ _ (fun j => ?_) ?_
          · rw [Subsingleton.elim j 0, Category.assoc, δ_π0, show (0 : Fin 2).succAbove 0 = 1 from rfl]
            exact WidePullback.lift_π ..
          · rw [Category.assoc, δ_base0]
            exact (WidePullback.lift_base ..).trans e
        · refine WidePullback.hom_ext (fun _ : Fin 1 => f) _ _ (fun j => ?_) ?_
          · rw [Subsingleton.elim j 0, Category.assoc, δ_π0, show (1 : Fin 2).succAbove 0 = 0 from rfl]
            exact WidePullback.lift_π ..
          · rw [Category.assoc, δ_base0]
            exact WidePullback.lift_base ..
      rw [← hℓ0, ← hℓ1, op_comp, op_comp, F.obj.map_comp, F.obj.map_comp, ModuleCat.comp_apply,
        ModuleCat.comp_apply, hx])
  exact ⟨p, hp ()⟩

end Nerve0

section Sec

variable {S : ShortComplex (EtSh Λ Y)} (hS : S.ShortExact)

/-- Sections over `U`. -/
abbrev secF (U : Y.Etale) : EtSh Λ Y ⥤ ModuleCat.{u} Λ :=
  sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u} Λ) ⋙ (evaluation _ _).obj (op U)

include hS in
theorem sec_exact (U : Y.Etale) (x : S.X₂.obj.obj (op U)) (hx : (S.g.hom.app (op U)).hom x = 0) :
    ∃ a, (S.f.hom.app (op U)).hom a = x :=
  (ShortComplex.moduleCat_exact_iff _).1
    (hS.exact.map_of_mono_of_preservesKernel (secF U) hS.mono_f inferInstance) x hx

include hS in
theorem sec_inj (U : Y.Etale) : Function.Injective (S.f.hom.app (op U)).hom := by
  have := hS.mono_f
  have : Mono ((secF U).map S.f) := Functor.map_mono _ _
  exact (ModuleCat.mono_iff_injective _).1 this

theorem sec_fg (U : Y.Etale) (b : S.X₁.obj.obj (op U)) :
    (S.g.hom.app (op U)).hom ((S.f.hom.app (op U)).hom b) = 0 := by
  have h0 : (secF U).map S.f ≫ (secF U).map S.g = 0 := by
    rw [← Functor.map_comp, S.zero, Functor.map_zero]
  exact congrArg (fun φ => φ.hom b) h0

include hS in
/-- **Step 1 of Cartan's lemma**: sections of `X₂ → X₃` are surjective over affine objects. -/
theorem sections_surj (h1 : CechExact Λ S.X₁) (T : Y.Etale) [IsAffine T.left] :
    Function.Surjective (S.g.hom.app (op T)).hom := by
  intro q
  have hls : Sheaf.IsLocallySurjective S.g := (Sheaf.isLocallySurjective_iff_epi' (φ := S.g)).2 hS.epi_g
  have hR := Presheaf.imageSieve_mem Y.smallEtaleTopology S.g.hom q
  obtain ⟨ι, _, Sk, g, haff, hg, hcov⟩ := exists_affine_refine T _ hR
  choose t ht using hg
  have ht' : ∀ k, (S.g.hom.app (op (Sk k))).hom (t k) = (S.X₃.obj.map (g k).op).hom q := ht
  obtain ⟨p', hp'⟩ := cop_glue Sk S.X₂ t
  have hVaff : IsAffine (cop Sk).left := isAffine_cop Sk
  have hfV : Function.Surjective (copDesc g).left := copDesc_surjective g hcov
  have hgp : (S.g.hom.app (op (cop Sk))).hom p' = (S.X₃.obj.map (copDesc g).op).hom q := by
    refine sep_of_cover S.X₃ (copι Sk) (cop_cover Sk) _ _ fun k => ?_
    calc _ = (S.g.hom.app (op (Sk k))).hom ((S.X₂.obj.map (copι Sk k).op).hom p') := by
          rw [← ModuleCat.comp_apply, ← NatTrans.naturality, ModuleCat.comp_apply]
      _ = _ := by
          rw [hp' k, ht' k, ← ModuleCat.comp_apply, ← Functor.map_comp, ← op_comp, copι_desc]
  let fV := copDesc g
  let p0 : S.X₂.obj.obj (op (nv fV 0)) := (S.X₂.obj.map (pi0 fV).op).hom p'
  have hgp0 : (S.g.hom.app (op (nv fV 0))).hom p0 = (S.X₃.obj.map (base0 fV).op).hom q := by
    calc _ = (S.X₃.obj.map (pi0 fV).op).hom ((S.g.hom.app (op (cop Sk))).hom p') := by
          rw [← ModuleCat.comp_apply, NatTrans.naturality, ModuleCat.comp_apply]
      _ = _ := by
          rw [hgp, ← ModuleCat.comp_apply, ← Functor.map_comp, ← op_comp, pi0_arrow]
  have hd3 : (cd S.X₃ fV 0 1).hom ((S.X₃.obj.map (base0 fV).op).hom q) = 0 := by
    rw [cech_d0_apply, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp,
      ← op_comp, ← op_comp, δ_base0, δ_base0, sub_self]
  have hc : (S.g.hom.app (op (nv fV 1))).hom ((cd S.X₂ fV 0 1).hom p0) = 0 := by
    rw [← cech_d_nat S.g fV 0 1 p0, hgp0, hd3]
  obtain ⟨a, ha⟩ := sec_exact hS (nv fV 1) _ hc
  have hda : (cd S.X₁ fV 1 2).hom a = 0 := by
    apply sec_inj hS (nv fV 2)
    rw [← cech_d_nat S.f fV 1 2 a, ha, map_zero, cd_cd]
  obtain ⟨b, hb⟩ := cech_exact_elt S.X₁ fV 0 1 2 rfl rfl (h1 fV hVaff inferInstance hfV 0) a hda
  have hx : (cd S.X₂ fV 0 1).hom (p0 - (S.f.hom.app (op (nv fV 0))).hom b) = 0 := by
    rw [map_sub, cech_d_nat S.f fV 0 1 b, hb, ha, sub_self]
  obtain ⟨p, hp⟩ := descend fV S.X₂ hfV _ hx
  refine ⟨p, sep_of_cover S.X₃ (fun _ : Unit => base0 fV) (cover_of_surjective _ (base0_surj fV hfV)) _ _
    fun _ => ?_⟩
  rw [← ModuleCat.comp_apply, ← NatTrans.naturality, ModuleCat.comp_apply, hp, map_sub, hgp0, sec_fg, sub_zero]

include hS in
/-- **Step 2 of Cartan's lemma**: the quotient of Cech-exact sheaves is Cech-exact. -/
theorem cechExact_X₃ (h1 : CechExact Λ S.X₁) (h2 : CechExact Λ S.X₂) : CechExact Λ S.X₃ := by
  intro V W f hV hW hf n
  refine cech_exactAt_of_elt S.X₃ f n fun q hq => ?_
  have := hV
  have := hW
  have : IsAffine (nv f (n + 1)).left := isAffine_cechNerve f (n + 1)
  obtain ⟨p, rfl⟩ := sections_surj hS h1 (nv f (n + 1)) q
  have hc : (S.g.hom.app (op (nv f (n + 2)))).hom ((cd S.X₂ f (n + 1) (n + 2)).hom p) = 0 := by
    rw [← cech_d_nat S.g f (n + 1) (n + 2) p]
    exact hq
  obtain ⟨a, ha⟩ := sec_exact hS (nv f (n + 2)) _ hc
  have hda : (cd S.X₁ f (n + 2) (n + 3)).hom a = 0 := by
    apply sec_inj hS (nv f (n + 3))
    rw [← cech_d_nat S.f f (n + 2) (n + 3) a, ha, map_zero, cd_cd]
  obtain ⟨b, hb⟩ := cech_exact_elt S.X₁ f (n + 1) (n + 2) (n + 3) rfl rfl (h1 f hV hW hf (n + 1)) a hda
  have hx : (cd S.X₂ f (n + 1) (n + 2)).hom (p - (S.f.hom.app (op (nv f (n + 1)))).hom b) = 0 := by
    rw [map_sub, cech_d_nat S.f f (n + 1) (n + 2) b, hb, ha, sub_self]
  obtain ⟨c, hc'⟩ := cech_exact_elt S.X₂ f n (n + 1) (n + 2) rfl rfl (h2 f hV hW hf n) _ hx
  refine ⟨(S.g.hom.app (op (nv f n))).hom c, ?_⟩
  rw [cech_d_nat S.g f n (n + 1) c, hc', map_sub, sec_fg, sub_zero]

end Sec

end RamanujanPetersson.EtCompact.Cech

end

end

-- ===== S4.Def_RP_EtCompact_Cartan =====
section

/-!
# S4-EtCompact: Cartan's lemma (O8c (B), file C5b)

**`H_eq_zero_of_cechExact`**: on an affine scheme `Y`, an etale sheaf `F` that is Cech-exact on surjective arrows
between affine etale objects (`CechExact Λ F`) has `H^(n+1)(Y, F) = 0` for all `n`.

Proof: embed `F` into the injective, Cech-exact sheaf `god Λ F`; the quotient `Q` is Cech-exact (`cechExact_X₃`), global
sections of `god Λ F → Q` are surjective (`sections_surj`), so `H¹(F) = 0`, and `H^(n+2)(F) ≅ H^(n+1)(Q)`.
-/

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry Opposite Abelian
open RamanujanPetersson.EtSheaves

noncomputable section

namespace RamanujanPetersson.EtCompact.Cech

universe u

variable {Λ : Type u} [CommRing Λ] {Y : Scheme.{u}}

/-- `0 → A → B → B / A → 0` for a monomorphism `A ⟶ B`. -/
abbrev cokSC {C : Type*} [Category C] [Abelian C] {A B : C} (f : A ⟶ B) : ShortComplex C :=
  ShortComplex.mk f (cokernel.π f) (cokernel.condition f)

end RamanujanPetersson.EtCompact.Cech

end

end

-- ===== S4.Def_RP_EtCompact_Germ =====
section

/-!
# S4-EtCompact: germs at the points `geomPtAt x` (O8c (B), file C6a)

* `etale_lqf`: etale morphisms are locally quasi-finite.
* `exists_fib_over`, `exists_lift_fib`: fibre points over a given point, lifts of fibre points along etale arrows.
* **`fiber_eq_of_pt`**: if `Gal x` is trivial, a fibre point of `geomPtAt x` is determined by its underlying point.
* `ux F x : F ⟶ x̄_* F_x̄` (the unit of the skyscraper adjunction), `ux_π_apply` (its components are the germs),
  `pi_ext`, `ux_eq_zero_iff`, `germ_map`.
* **`eq_zero_of_germs`**: a section all of whose germs vanish is zero.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry Opposite
open RamanujanPetersson.EtSheaves

noncomputable section

namespace RamanujanPetersson.EtCompact.Cech

universe u

/-- Etale morphisms are locally quasi-finite. -/
instance etale_lqf {X Z : Scheme.{u}} (f : X ⟶ Z) [Etale f] : LocallyQuasiFinite f where
  quasiFinite_appLE {U} hU {V} hV e := by
    have h := f.etale_appLE hU hV e
    algebraize [(f.appLE U V e).hom]
    exact (inferInstance : Algebra.QuasiFinite Γ(Z, U) Γ(X, V))

section Fib

variable {X : Scheme.{u}}

/-- The lift `Spec Ω ⟶ W` of a fibre point. -/
abbrev fl (x : X) {W : X.Etale} (a : (geomPtAt x).point.fiber.obj W) :
    Spec (CommRingCat.of (geomPtAt x).Ω) ⟶ W.left :=
  ((geomPtAt x).liftOf a).left

/-- The underlying point of a fibre point. -/
def fpt (x : X) {W : X.Etale} (a : (geomPtAt x).point.fiber.obj W) : W.left :=
  fl x a (default : Spec (CommRingCat.of (geomPtAt x).Ω))

/-- Every point of an etale object carries a fibre point of the geometric point at its image. -/
theorem exists_fib_over (W : X.Etale) (w : W.left) :
    ∃ a : (geomPtAt (W.hom w)).point.fiber.obj W, fpt (W.hom w) a = w := by
  obtain ⟨t, ht⟩ := Scheme.pointSmallEtaleFiberObjToPreimage_surjective (geomPtAt (W.hom w)).pt
    (center_geomPtAt (W.hom w)) W ⟨w, rfl⟩
  exact ⟨t, congrArg Subtype.val ht⟩

/-- Lifting a fibre point along an etale arrow through a given point. -/
theorem exists_lift_fib {V T : X.Etale} (g : V ⟶ T) (x : X) (a : (geomPtAt x).point.fiber.obj T) (v : V.left)
    (hv : g.left v = fpt x a) :
    ∃ b : (geomPtAt x).point.fiber.obj V, (geomPtAt x).point.fiber.map g b = a ∧ fpt x b = v := by
  obtain ⟨l, hl, hl'⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (Ω := (geomPtAt x).Ω) g.left (fl x a) v hv
  have hw : l ≫ V.hom = (geomPtAt x).pt := by
    rw [← MorphismProperty.Over.w g, ← Category.assoc, hl]
    exact Over.w ((geomPtAt x).liftOf a)
  let b : (geomPtAt x).point.fiber.obj V :=
    (Over.homMk l hw : CategoryTheory.Over.mk (geomPtAt x).pt ⟶ (Scheme.Etale.forget X).obj V)
  exact ⟨b, fiber_ext _ hl, hl'⟩

theorem fib_left_map {V T : X.Etale} (g : V ⟶ T) (x : X) (b : (geomPtAt x).point.fiber.obj V) :
    fpt x ((geomPtAt x).point.fiber.map g b) = g.left (fpt x b) := rfl

theorem fib_over (x : X) {T : X.Etale} (a : (geomPtAt x).point.fiber.obj T) : T.hom (fpt x a) = x := by
  rw [fpt, ← Scheme.Hom.comp_apply, show fl x a ≫ T.hom = (geomPtAt x).pt from Over.w ((geomPtAt x).liftOf a)]
  exact center_geomPtAt x

variable (x : X)

end Fib

section Germ

variable {Λ : Type u} [CommRing Λ] {Y : Scheme.{u}} (F : EtSh Λ Y)

/-- The germ module `F_x̄`. -/
abbrev Mx (x : Y) : ModuleCat.{u} Λ := (geomPtAt x).point.presheafFiber.obj F.obj

/-- The unit `F ⟶ x̄_* F_x̄` of the skyscraper adjunction. -/
def ux (x : Y) : F ⟶ (geomPtAt x).point.skyscraperSheaf (Mx F x) :=
  ⟨(geomPtAt x).point.skyscraperPresheafHomEquiv (𝟙 _)⟩

omit F in
theorem pi_ext {ι : Type u} {M : ModuleCat.{u} Λ} (z z' : (∏ᶜ fun _ : ι => M : ModuleCat.{u} Λ))
    (h : ∀ i, (Pi.π (fun _ : ι => M) i).hom z = (Pi.π (fun _ : ι => M) i).hom z') : z = z' :=
  Concrete.limit_ext (Discrete.functor fun _ : ι => M) z z' fun j => h j.as

/-- Germs of restrictions. -/
theorem germ_map {V T : Y.Etale} (g : V ⟶ T) (x : Y) (b : (geomPtAt x).point.fiber.obj V)
    (s : F.obj.obj (op T)) :
    ((geomPtAt x).point.toPresheafFiber V b F.obj).hom ((F.obj.map g.op).hom s) =
      ((geomPtAt x).point.toPresheafFiber T ((geomPtAt x).point.fiber.map g b) F.obj).hom s := by
  rw [← ModuleCat.comp_apply, (geomPtAt x).point.toPresheafFiber_w]

end Germ

end RamanujanPetersson.EtCompact.Cech

end

end

-- ===== S4.Def_RP_EtCompact_SuppFin =====
section

/-!
# S4-EtCompact: supports of sections of sheaves supported on closed points (O8c (B), file C6b)

* `isClosed_pt`: a point of an etale object over a closed point is closed; `finite_preimage_closed`: on a
  quasi-compact etale object only finitely many points lie over a closed point; `finite_fib` (trivial `Gal x`).
* `supp F s`: the points carrying a fibre point at which the germ of `s` is nonzero; `isClosed_supp`;
  `germ_eq_zero_of_not_mem_supp`.
* **`finite_supp`**: if the stalks of `F` vanish at non-closed points and `Y` is locally noetherian, every section
  over an affine etale object has finite support (`finite_of_isClosed_pts`: a closed set of closed points in a
  noetherian quasi-sober space is finite).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open RamanujanPetersson.EtSheaves

noncomputable section

namespace RamanujanPetersson.EtCompact.Cech

universe u

section Top

variable {X : Scheme.{u}}

/-- Finitely many points of a quasi-compact etale object lie over a closed point. -/
theorem finite_preimage_closed (T : X.Etale) [CompactSpace T.left] (x : X) (hx : IsClosed ({x} : Set X)) :
    (T.hom ⁻¹' {x}).Finite := by
  have hc : IsClosed (T.hom ⁻¹' {x} : Set T.left) := hx.preimage T.hom.continuous
  exact hc.isCompact.finite (T.hom.isDiscrete_preimage_singleton x)

end Top

section Supp

variable {Λ : Type u} [CommRing Λ] {Y : Scheme.{u}} (F : EtSh Λ Y)

/-- The support of a section. -/
def supp {T : Y.Etale} (s : F.obj.obj (op T)) : Set T.left :=
  {t | ∃ (y : Y) (a : (geomPtAt y).point.fiber.obj T), fpt y a = t ∧
    ((geomPtAt y).point.toPresheafFiber T a F.obj).hom s ≠ 0}

end Supp

end RamanujanPetersson.EtCompact.Cech

end

end

-- ===== S4.Def_RP_EtCompact_CoInd =====
section

/-!
# S4-EtCompact, A1: co-induction from an open subgroup (group layer for `R²g_* = 0`)

`H ≤ G` a subgroup, `σ` a representation of `H` on `X`.

* `CoInd.sub H σ = {f : G → X | f (h g) = σ h (f g)}` with `G` acting by right translation (`CoInd.rep`);
* `CoInd.unit : X → CoInd` (`H`-equivariant, `unit_equivariant`); `CoInd.map` (functorial, `map_injective`,
  `map_unit`);
* `CoInd.counit : CoInd(Res ρ) → M` for a `G`-representation `ρ` and finitely many cosets (`counit_rep`:
  `G`-equivariant; `counit_unit`: `counit ∘ unit = id`);
* `CoInd.rep_isDiscrete`: co-induction from an open subgroup of finite index preserves discreteness;
  `IsDiscreteRep.comp_subtype`: restriction to a subgroup preserves it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtCompact.CoInd

attribute [local instance] Classical.propDecidable

variable {Λ : Type*} [CommRing Λ] {G : Type*} [Group G] (H : Subgroup G)

section Def

variable {X : Type*} [AddCommGroup X] [Module Λ X] (σ : Representation Λ H X)

/-- `unitFun x g = σ g x` for `g ∈ H`, `0` otherwise. -/
def unitFun (x : X) (g : G) : X := if hg : g ∈ H then σ ⟨g, hg⟩ x else 0

variable {Y : Type*} [AddCommGroup Y] [Module Λ Y] {σ} {σY : Representation Λ H Y}

variable (φ : X →ₗ[Λ] Y) (hφ : ∀ h : H, φ ∘ₗ σ h = σY h ∘ₗ φ)

end Def

section Counit

variable {M : Type*} [AddCommGroup M] [Module Λ M] (ρ : Representation Λ G M)

/-- Right cosets `H\G`. -/
abbrev RC := Quotient (QuotientGroup.rightRel H)

theorem exists_out_eq (g : G) :
    ∃ h : H, ((Quotient.mk (QuotientGroup.rightRel H) g).out : G) = h * g := by
  have h1 : g * ((Quotient.mk (QuotientGroup.rightRel H) g).out)⁻¹ ∈ H :=
    QuotientGroup.rightRel_apply.1 (Quotient.mk_out (s := QuotientGroup.rightRel H) g)
  refine ⟨⟨(g * ((Quotient.mk (QuotientGroup.rightRel H) g).out)⁻¹)⁻¹, H.inv_mem h1⟩, ?_⟩
  show _ = (g * ((Quotient.mk (QuotientGroup.rightRel H) g).out)⁻¹)⁻¹ * g
  group

variable [Fintype (RC H)]

end Counit

section Disc

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable {X : Type*} [AddCommGroup X] [Module Λ X]

/-- Restriction to a subgroup preserves discreteness. -/
theorem _root_.RamanujanPetersson.EtCompact.IsDiscreteRep.comp_subtype {ρ : Representation Λ G X}
    (hρ : IsDiscreteRep ρ) : IsDiscreteRep (ρ.comp H.subtype) := fun m => by
  obtain ⟨K, hKo, hK⟩ := hρ m
  exact ⟨K.comap H.subtype, hKo.preimage continuous_subtype_val, fun s hs => hK s hs⟩

end Disc

end RamanujanPetersson.EtCompact.CoInd

end

end

-- ===== S4.Def_RP_EtCompact_R1Gen =====
section

/-!
# S4-EtCompact, B1: `R¹g_* N` has vanishing generic stalk, hence no higher cohomology on a curve

`A` a noetherian integrally closed domain of dimension `≤ 1`, `g = gen A : Spec κ(η) ⟶ Spec A`.

* **`isZero_R1_gen`**: the stalk of `R¹g_* N` at `η` vanishes (`GenStalk.epi_push` + `GPtIso.isZero_stalk_cokernel`);
* `eq_genPt`: the only non-closed point of `Spec A` is `η`; `hF_R1`;
* **`H_R1_eq_zero`**: `H^(n+1)(Spec A, R¹g_* N) = 0` when the closed points have trivial Galois groups
  (`Cech.H_eq_zero_of_closed`);
* **`H_push_gen_eq_zero`**: `H^(n+3)(Spec A, g_* N) = 0` given `H²(η, -) = 0` and `R²g_* = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.R1Gen

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact.GenFrac

variable {A : Type} [CommRing A] [IsDomain A] {Λ : Type} [CommRing Λ]

/-- On a domain of dimension `≤ 1`, the only non-closed point is the generic point. -/
theorem eq_genPt [Ring.KrullDimLE 1 A] (y : Spec (CommRingCat.of A))
    (hy : ¬ IsClosed ({y} : Set (Spec (CommRingCat.of A)))) : y = GenBr.genPt A := by
  by_contra hne
  apply hy
  refine (PrimeSpectrum.isClosed_singleton_iff_isMaximal (R := A) y).2 ?_
  exact Ideal.IsPrime.isMaximal_of_ne_bot y.isPrime fun h => hne (PrimeSpectrum.ext h)

end RamanujanPetersson.EtCompact.R1Gen

end

end


