-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesWedge
-- name    : AlgebraicGeometry_ModulesWedge
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/92339ad2-d51f-5f43-be07-5cd5442d8b8e
-- title:
--   Wedge multiplication by a vector on exterior powers of sheaves
-- statement:
--   Three levels of the same construction are set up. At the module level, for a commutative ring $R$, an $R$-module $M$ and $a,b\in\mathbb N$, [`exteriorPower.mulₗ R M a b`](../def/AlgebraicGeometry_ModulesWedge.html#L17) is the $R$-bilinear map $\bigwedge^a M \times \bigwedge^b M \to \bigwedge^{a+b} M$ given on representatives by multiplication in the exterior algebra $\Lambda_R M$, using that the exterior powers form a graded family of submodules; it sends a pair of pure wedges $\iota v$, $\iota w$ to $\iota(\mathrm{Fin.append}\,v\,w)$, and it commutes with the functorial maps $\bigwedge^\bullet f$ of a linear map $f\colon M \to N$. Specialising $b=1$ and precomposing in the second variable with the inverse of the canonical isomorphism $M \cong \bigwedge^1 M$ gives [`exteriorPower.mulVec R M n`](../def/AlgebraicGeometry_ModulesWedge.html#L66), the bilinear wedge $\bigwedge^n M \times M \to \bigwedge^{n+1} M$, again computed on pure wedges and shown to commute with $\bigwedge^\bullet f$ and $f$.
--
--   At the presheaf level, for a presheaf of commutative rings $R$ on a category $C$ and a presheaf of $R$-modules $P$, the pairing above is compatible with the (semilinear) restriction maps on exterior powers, and [`PresheafOfModules.wedgeVec n P`](../def/AlgebraicGeometry_ModulesWedge.html#L129) is the resulting morphism $\bigwedge^n P \otimes P \to \bigwedge^{n+1} P$, whose component at $X$ is induced on the tensor product over $R(X)$ by $x \otimes m \mapsto x \wedge m$; it is natural in $P$, i.e. $(\bigwedge^n\varphi \otimes \varphi)$ followed by $\mathrm{wedgeVec}_Q$ equals $\mathrm{wedgeVec}_P$ followed by $\bigwedge^{n+1}\varphi$.
--
--   At the scheme level, for a scheme $X$ and $M$ a sheaf of modules, `sheafifyValIso M` is the counit isomorphism identifying the sheafification of the underlying presheaf of $M$ with $M$, with its naturality in both directions, and `Scheme.Modules.wedgeVec n M` $\colon \det^n M \otimes M \to \det^{n+1} M$ is the composite of this isomorphism (whiskered on the right), the lax monoidal structure map of sheafification, and the sheafification of the presheaf-level `wedgeVec`. Two further lemmas record the identification of $\det^n$ and of $\bigwedge^n$ on morphisms with sheafified presheaf exterior powers, a rewriting of $(\bigwedge^n\varphi \triangleright N)$ followed by $\mathrm{wedgeVec}$, and naturality of $\mathrm{wedgeVec}$ in $M$.
--
--   **Relation to Mathlib.** Mathlib supplies exterior powers $\bigwedge^n M$ of a module as graded submodules of the exterior algebra, together with `ιMulti`, the functorial `map` and the isomorphism $M \cong \bigwedge^1 M$; the bilinear multiplication $\bigwedge^a \times \bigwedge^b \to \bigwedge^{a+b}$, exterior powers of presheaves and sheaves of modules, and the wedge-with-a-vector morphism are the project's own.
--
--   **Where it is used.** These maps belong to the project's theory of exterior powers and determinants of sheaves of modules on a scheme; the morphism $\det^n \mathcal M \otimes \mathcal M \to \det^{n+1}\mathcal M$ is what is needed to compare determinant sheaves along a short exact sequence with invertible quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesWedge.lean

import Mathlib
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory

namespace exteriorPower

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (a b : ℕ)

noncomputable def mulₗ : ⋀[R]^a M →ₗ[R] ⋀[R]^b M →ₗ[R] ⋀[R]^(a + b) M :=
  LinearMap.mk₂ R (fun x y => ⟨x.1 * y.1, SetLike.mul_mem_graded x.2 y.2⟩)
    (fun x x' y => Subtype.ext (add_mul x.1 x'.1 y.1))
    (fun r x y => Subtype.ext (smul_mul_assoc r x.1 y.1))
    (fun x y y' => Subtype.ext (mul_add x.1 y.1 y'.1))
    (fun r x y => Subtype.ext (mul_smul_comm r x.1 y.1))

@[simp] lemma mulₗ_apply_coe (x : ⋀[R]^a M) (y : ⋀[R]^b M) :
    ((mulₗ R M a b x y : ⋀[R]^(a + b) M) : ExteriorAlgebra R M) = x.1 * y.1 := rfl

lemma mulₗ_ιMulti_ιMulti (v : Fin a → M) (w : Fin b → M) :
    mulₗ R M a b (ιMulti R a v) (ιMulti R b w) = ιMulti R (a + b) (Fin.append v w) :=
  Subtype.ext (ExteriorAlgebra.ιMulti_mul_ιMulti v w)

variable {R M} in
omit [AddCommGroup M] [Module R M] in
lemma comp_append {N : Type*} (f : M → N) (v : Fin a → M) (w : Fin b → M) :
    f ∘ Fin.append v w = Fin.append (f ∘ v) (f ∘ w) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Fin.append_left]
  · simp [Fin.append_right]

variable {R M} in

lemma map_mulₗ {N : Type u} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (x : ⋀[R]^a M) (y : ⋀[R]^b M) :
    map (a + b) f (mulₗ R M a b x y) = mulₗ R N a b (map a f x) (map b f y) := by
  have hx : x ∈ Submodule.span R (Set.range (ιMulti R a (M := M))) := by
    rw [ιMulti_span]; trivial
  have hy : y ∈ Submodule.span R (Set.range (ιMulti R b (M := M))) := by
    rw [ιMulti_span]; trivial
  induction hx using Submodule.span_induction generalizing y with
  | mem x hx' =>
    obtain ⟨v, rfl⟩ := hx'
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨w, rfl⟩ := hy'
      rw [mulₗ_ιMulti_ιMulti, map_apply_ιMulti, map_apply_ιMulti, map_apply_ιMulti, mulₗ_ιMulti_ιMulti,
        comp_append]
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, map_add, map_add, map_add, hy, hz]
    | smul r y _ hy => rw [map_smul, map_smul, map_smul, map_smul, hy]
  | zero => simp
  | add x x' _ _ hx hx' =>
    simp only [map_add, LinearMap.add_apply, hx y hy, hx' y hy]
  | smul r x _ hx =>
    simp only [map_smul, LinearMap.smul_apply, hx y hy]

noncomputable def mulVec (n : ℕ) : ⋀[R]^n M →ₗ[R] M →ₗ[R] ⋀[R]^(n + 1) M :=
  (mulₗ R M n 1).compl₂ (oneEquiv R M).symm.toLinearMap

lemma mulVec_apply (n : ℕ) (x : ⋀[R]^n M) (m : M) :
    mulVec R M n x m = mulₗ R M n 1 x ((oneEquiv R M).symm m) := rfl

lemma mulVec_ιMulti (n : ℕ) (v : Fin n → M) (m : M) :
    mulVec R M n (ιMulti R n v) m = ιMulti R (n + 1) (Fin.append v (fun _ : Fin 1 => m)) := by
  rw [mulVec_apply, oneEquiv_symm_apply, mulₗ_ιMulti_ιMulti]

variable {R M} in

lemma map_mulVec {N : Type u} [AddCommGroup N] [Module R N] (n : ℕ) (f : M →ₗ[R] N)
    (x : ⋀[R]^n M) (m : M) :
    map (n + 1) f (mulVec R M n x m) = mulVec R N n (map n f x) (f m) := by
  rw [mulVec_apply, mulVec_apply, map_mulₗ, oneEquiv_symm_apply, oneEquiv_symm_apply, map_apply_ιMulti]
  rfl

end exteriorPower

namespace PresheafOfModules

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}} (n : ℕ)

namespace ExteriorPower

variable (P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

set_option maxHeartbeats 1600000 in

lemma mapₗ_mulVec {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : ⋀[R.obj X]^n (P.obj X)) (m : P.obj X) :
    mapₗ (n + 1) P f (exteriorPower.mulVec (R.obj X) (P.obj X) n x m) =
      exteriorPower.mulVec (R.obj Y) (P.obj Y) n (mapₗ n P f x) (P.map f m) := by
  letI := moduleAlong R f (⋀[R.obj Y]^(n + 1) (P.obj Y))
  letI := moduleAlong R f (⋀[R.obj Y]^n (P.obj Y))
  have hx : x ∈ Submodule.span (R.obj X) (Set.range (exteriorPower.ιMulti (R.obj X) n (M := P.obj X))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨v, rfl⟩ := hx'
    have h1 := mapₗ_ιMulti n P f v
    have h2 := mapₗ_ιMulti (n + 1) P f (Fin.append v (fun _ : Fin 1 => m))
    rw [exteriorPower.mulVec_ιMulti, h2, h1, exteriorPower.mulVec_ιMulti]
    congr 1
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [Fin.append_left]
    · simp [Fin.append_right]
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x y _ _ hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | smul r x _ hx => rw [LinearMap.map_smul₂, mapₗ_smul, mapₗ_smul, LinearMap.map_smul₂, hx]

end ExteriorPower

variable (P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

noncomputable abbrev ExteriorPower.mulVecObj (X : Cᵒᵖ) :
    (exteriorPower n P).obj X →ₗ[(R ⋙ forget₂ CommRingCat RingCat).obj X]
      (P.obj X →ₗ[(R ⋙ forget₂ CommRingCat RingCat).obj X] (exteriorPower (n + 1) P).obj X) :=
  exteriorPower.mulVec (R.obj X) (P.obj X) n

set_option maxHeartbeats 1600000 in

noncomputable def wedgeVec : exteriorPower n P ⊗ P ⟶ exteriorPower (n + 1) P where
  app X := ModuleCat.ofHom (TensorProduct.lift (ExteriorPower.mulVecObj n P X))
  naturality {X Y} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x m
    change exteriorPower.mulVec (R.obj Y) (P.obj Y) n
        (ExteriorPower.mapₗ n P f (show ⋀[R.obj X]^n (P.obj X) from x)) (P.map f m) =
      ExteriorPower.mapₗ (n + 1) P f
        (exteriorPower.mulVec (R.obj X) (P.obj X) n (show ⋀[R.obj X]^n (P.obj X) from x) m)
    exact (ExteriorPower.mapₗ_mulVec n P f _ m).symm

lemma wedgeVec_app_tmul (X : Cᵒᵖ) (x : ⋀[R.obj X]^n (P.obj X)) (m : P.obj X) :
    ((wedgeVec n P).app X ((show (exteriorPower n P).obj X from x) ⊗ₜ[R.obj X] m) :
      ⋀[R.obj X]^(n + 1) (P.obj X)) = exteriorPower.mulVec (R.obj X) (P.obj X) n x m := rfl

variable {P} in

lemma wedgeVec_naturality {Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (φ : P ⟶ Q) :
    (exteriorPowerMap n φ ⊗ₘ φ) ≫ wedgeVec n Q = wedgeVec n P ≫ exteriorPowerMap (n + 1) φ := by
  ext X : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x m
  change exteriorPower.mulVec (R.obj X) (Q.obj X) n
      (exteriorPower.map n (ExteriorPower.appₗ φ X) (show ⋀[R.obj X]^n (P.obj X) from x)) (φ.app X m) =
    exteriorPower.map (n + 1) (ExteriorPower.appₗ φ X)
      (exteriorPower.mulVec (R.obj X) (P.obj X) n (show ⋀[R.obj X]^n (P.obj X) from x) m)
  rw [exteriorPower.map_mulVec]
  rfl

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (n : ℕ)

noncomputable def sheafifyValIso (M : X.Modules) : (Scheme.Modules.sheafify X).obj M.val ≅ M :=
  SheafOfModules.sheafifyCounitIso X.sheaf.obj X.ringCatSheaf.property M

@[reassoc]
lemma sheafifyValIso_hom_naturality {M N : X.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.sheafify X).map φ.val ≫ (sheafifyValIso N).hom = (sheafifyValIso M).hom ≫ φ := by
  have h := (SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).counit.naturality φ
  exact h

@[reassoc]
lemma sheafifyValIso_inv_naturality {M N : X.Modules} (φ : M ⟶ N) :
    φ ≫ (sheafifyValIso N).inv = (sheafifyValIso M).inv ≫ (Scheme.Modules.sheafify X).map φ.val := by
  rw [Iso.comp_inv_eq, Category.assoc, sheafifyValIso_hom_naturality, Iso.inv_hom_id_assoc]

lemma det_eq (M : X.Modules) :
    Scheme.Modules.det n M = (Scheme.Modules.sheafify X).obj ((presheafExteriorPower X n).obj M.val) := rfl

lemma exteriorPower_map_eq {M N : X.Modules} (φ : M ⟶ N) :
    (exteriorPower X n).map φ = (Scheme.Modules.sheafify X).map ((presheafExteriorPower X n).map φ.val) := rfl

noncomputable def wedgeVec (M : X.Modules) : Scheme.Modules.det n M ⊗ M ⟶ Scheme.Modules.det (n + 1) M :=
  (Scheme.Modules.det n M ◁ (sheafifyValIso M).inv) ≫
    Functor.LaxMonoidal.μ (Scheme.Modules.sheafify X) ((presheafExteriorPower X n).obj M.val) M.val ≫
      (Scheme.Modules.sheafify X).map (PresheafOfModules.wedgeVec n M.val)

lemma whiskerRight_exteriorPower_map_comp_wedgeVec {M N : X.Modules} (φ : M ⟶ N) :
    ((exteriorPower X n).map φ ▷ N) ≫ wedgeVec n N =
      (Scheme.Modules.det n M ◁ (sheafifyValIso N).inv) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.sheafify X) ((presheafExteriorPower X n).obj M.val) N.val ≫
          (Scheme.Modules.sheafify X).map
            (((presheafExteriorPower X n).map φ.val ▷ N.val) ≫ PresheafOfModules.wedgeVec n N.val) := by
  rw [wedgeVec, ← whisker_exchange_assoc, exteriorPower_map_eq, Functor.LaxMonoidal.μ_natural_left_assoc,
    ← Functor.map_comp]

lemma wedgeVec_naturality {M N : X.Modules} (φ : M ⟶ N) :
    ((exteriorPower X n).map φ ⊗ₘ φ) ≫ wedgeVec n N = wedgeVec n M ≫ (exteriorPower X (n + 1)).map φ := by
  have h1 : ((exteriorPower X n).map φ ⊗ₘ φ) ≫ (Scheme.Modules.det n N ◁ (sheafifyValIso N).inv) =
      (Scheme.Modules.det n M ◁ (sheafifyValIso M).inv) ≫
        ((Scheme.Modules.sheafify X).map ((presheafExteriorPower X n).map φ.val) ⊗ₘ
          (Scheme.Modules.sheafify X).map φ.val) := by
    rw [exteriorPower_map_eq, MonoidalCategory.tensorHom_def, Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, sheafifyValIso_inv_naturality, MonoidalCategory.whiskerLeft_comp,
      ← whisker_exchange_assoc, ← MonoidalCategory.tensorHom_def]
  have h2 : ((presheafExteriorPower X n).map φ.val ⊗ₘ φ.val) ≫ PresheafOfModules.wedgeVec n N.val =
      PresheafOfModules.wedgeVec n M.val ≫ (presheafExteriorPower X (n + 1)).map φ.val :=
    PresheafOfModules.wedgeVec_naturality n φ.val
  simp only [wedgeVec, Category.assoc]
  rw [reassoc_of% h1, Functor.LaxMonoidal.μ_natural_assoc, ← Functor.map_comp, h2, Functor.map_comp,
    exteriorPower_map_eq]
  rfl

end AlgebraicGeometry.Scheme.Modules


