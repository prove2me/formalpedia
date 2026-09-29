-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
-- name    : AlgebraicGeometry_ModulesGlueOfCocycle
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/9fd76563-b5a5-54ec-827f-6bc9f4332cb5
-- title:
--   Gluing a module from a unit cocycle on opens
-- statement:
--   Fix a scheme $X$ and a family of opens $U : \iota \to X.\mathrm{Opens}$. A `UnitCocycle U` is a structure carrying functions $u_{ij} \in \Gamma(X, U_i \cap U_j)$ for all $i,j$ together with two equations as fields: $u_{ii} = 1$, and, after restriction to $(U_i \cap U_j) \cap U_k$, the relation $u_{ij}\,u_{jk} = u_{ik}$. The abbreviation `rO` names the restriction ring homomorphism $\Gamma(X,A) \to \Gamma(X,B)$ attached to $B \le A$, with the expected functoriality, proof-irrelevance, identity and (when $A \le B$ as well) bijectivity lemmas. From the cocycle relation it follows that $u_{ij}$ times the restriction of $u_{ji}$ equals $1$, so each $u_{ij}$ is a unit, and a version `cocycle_le` of the cocycle identity over any open $W$ contained in the three pairwise intersections. Further constructions on cocycles: the trivial cocycle $u_{ij} = 1$; the pointwise product of two cocycles; the twist $u_{ij} \mapsto h_i\,u_{ij}\,h_j^{-1}$ by a family of units $h_i \in \Gamma(X, U_i)^\times$; and the pull-back along $g : X' \to X$, a cocycle on the opens $g^{-1}U_i$ with entries $g^\sharp u_{ij}$.
--
--   For an open $T$, `families c T` is the additive subgroup of $\prod_i \Gamma(X, T \cap U_i)$ consisting of the families $(x_i)$ satisfying $x_i = u_{ij}\,x_j$ after restriction to $T \cap (U_i \cap U_j)$; it is a $\Gamma(X,T)$-module by $g \cdot (x_i) = (g\,x_i)$, and componentwise restriction makes $T \mapsto \mathtt{families}\ c\ T$ a presheaf `preGlue` of abelian groups, compatible with the module structures, hence a presheaf of modules `preGlueMod` over the structure sheaf. The theorem `preGlue_isSheaf` verifies the unique-gluing condition, componentwise, from the sheaf axioms for $\mathcal O_X$; `glueOfCocycle c` is the resulting object of `X.Modules`. Accessors give the components $(\mathtt{glueComponent})$, extensionality, the transition identity for components, their behaviour under restriction and scalar multiplication, and the constructor `glueMk` from a compatible family. Finally, `glueFrame c i` $\in \Gamma(\mathtt{glueOfCocycle}\ c, U_i)$ is the section with $k$-th component the restriction of $u_{ki}$; `isFrameOn_glueFrame` states that for every open $W \le U_i$ the map $g \mapsto g \cdot (\mathtt{glueFrame}\ c\ i)|_W$ is a bijection $\Gamma(X,W) \to \Gamma(\mathtt{glueOfCocycle}\ c, W)$, and `map_glueFrame_eq_smul` states that on $U_i \cap U_j$ the restriction of `glueFrame c j` equals $u_{ij}$ times that of `glueFrame c i`.
--
--   **Relation to Mathlib.** Mathlib supplies the ingredients used here — presheaves of modules and `PresheafOfModules.ofPresheaf`, the characterisation of sheaves by unique gluing, and the unique-gluing statements for the structure sheaf — but has no construction of a sheaf of modules from a unit $1$-cocycle on a family of opens; `UnitCocycle` and `glueOfCocycle` are the project's own.
--
--   **Where it is used.** The construction provides invertible modules from explicit trivialisation data on an arbitrary family of opens, generalising the two-open gluing used elsewhere in the project; the notion `IsFrameOn` of the imported module records that `glueFrame c i` trivialises the glued module on $U_i$. It is used, in particular, in the construction of the norm of a line bundle along a finite morphism, which is obtained as the glue of a cocycle of field norms of a trivialisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesGlueOfCocycle.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {ι : Type u}

namespace GlueOfCocycle

noncomputable abbrev rO {A B : X.Opens} (h : B ≤ A) : Γ(X, A) →+* Γ(X, B) :=
  (X.presheaf.map (homOfLE h).op).hom

theorem rO_rO {A B C : X.Opens} (hBA : B ≤ A) (hCB : C ≤ B) (g : Γ(X, A)) :
    rO hCB (rO hBA g) = rO (hCB.trans hBA) g := by
  change (X.presheaf.map (homOfLE hBA).op ≫ X.presheaf.map (homOfLE hCB).op).hom g = _
  rw [← Functor.map_comp]; rfl

theorem rO_irrel {A B : X.Opens} (h h' : B ≤ A) (g : Γ(X, A)) : rO h g = rO h' g := rfl

theorem rO_refl {A : X.Opens} (g : Γ(X, A)) : rO (le_refl A) g = g := by
  change (X.presheaf.map (homOfLE (le_refl A)).op).hom g = g
  rw [Subsingleton.elim (homOfLE (le_refl A)) (𝟙 A), op_id, X.presheaf.map_id]; rfl

theorem rO_rO_self {A B : X.Opens} (h : B ≤ A) (h' : A ≤ B) (g : Γ(X, B)) : rO h (rO h' g) = g := by
  rw [rO_rO]; exact rO_refl g

theorem rO_bijective_of_le_le {A B : X.Opens} (h : B ≤ A) (h' : A ≤ B) : Function.Bijective (rO h) :=
  Function.bijective_iff_has_inverse.2 ⟨rO h', fun g => rO_rO_self h' h g, fun g => rO_rO_self h h' g⟩

end GlueOfCocycle

open GlueOfCocycle

structure UnitCocycle (U : ι → X.Opens) where

  u : ∀ i j, Γ(X, U i ⊓ U j)

  refl : ∀ i, u i i = 1

  cocycle : ∀ i j k,
    rO (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j) (u i j) *
      rO (le_inf (inf_le_left.trans inf_le_right) inf_le_right : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k) (u j k) =
    rO (le_inf (inf_le_left.trans inf_le_left) inf_le_right : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k) (u i k)

namespace UnitCocycle

variable {U : ι → X.Opens} (c : UnitCocycle U)

theorem cocycle_le (i j k : ι) {W : X.Opens} (hij : W ≤ U i ⊓ U j) (hjk : W ≤ U j ⊓ U k) (hik : W ≤ U i ⊓ U k) :
    rO hij (c.u i j) * rO hjk (c.u j k) = rO hik (c.u i k) := by
  have hW : W ≤ U i ⊓ U j ⊓ U k := le_inf hij (hjk.trans inf_le_right)
  have := congrArg (rO hW) (c.cocycle i j k)
  rw [map_mul, rO_rO, rO_rO, rO_rO] at this
  exact this

theorem mul_symm (i j : ι) :
    c.u i j * rO (le_of_eq (inf_comm (U i) (U j)) : U i ⊓ U j ≤ U j ⊓ U i) (c.u j i) = 1 := by
  have h := c.cocycle_le i j i (W := U i ⊓ U j) le_rfl (le_of_eq (inf_comm _ _)) (le_inf inf_le_left inf_le_left)
  rw [rO_refl, c.refl, map_one] at h
  exact h

theorem isUnit (i j : ι) : IsUnit (c.u i j) :=
  isUnit_iff_exists_inv.mpr ⟨_, c.mul_symm i j⟩

variable (U) in

def trivial : UnitCocycle U where
  u _ _ := 1
  refl _ := rfl
  cocycle _ _ _ := by simp only [map_one, mul_one]

def mul (c' : UnitCocycle U) : UnitCocycle U where
  u i j := c.u i j * c'.u i j
  refl i := by rw [c.refl, c'.refl, mul_one]
  cocycle i j k := by
    simp only [map_mul]
    rw [mul_mul_mul_comm, c.cocycle, c'.cocycle]

noncomputable def twist (h : ∀ i, Γ(X, U i)ˣ) : UnitCocycle U where
  u i j := rO inf_le_left (h i : Γ(X, U i)) * c.u i j * rO inf_le_right (↑(h j)⁻¹ : Γ(X, U j))
  refl i := by
    rw [c.refl, mul_one, rO_irrel inf_le_left inf_le_right, ← map_mul, Units.mul_inv, map_one]
  cocycle i j k := by
    simp only [map_mul, rO_rO]
    have hc := c.cocycle i j k

    have hj : rO ((le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j).trans
          inf_le_right) (↑(h j)⁻¹ : Γ(X, U j)) *
        rO ((le_inf (inf_le_left.trans inf_le_right) inf_le_right : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k).trans inf_le_left)
          (h j : Γ(X, U j)) = 1 := by
      rw [rO_irrel _ ((le_inf (inf_le_left.trans inf_le_right) inf_le_right : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k).trans inf_le_left),
        ← map_mul, Units.inv_mul, map_one]
    calc _ = rO _ (h i : Γ(X, U i)) * (rO _ (c.u i j) * rO _ (c.u j k)) *
          (rO _ (↑(h j)⁻¹ : Γ(X, U j)) * rO _ (h j : Γ(X, U j))) * rO _ (↑(h k)⁻¹ : Γ(X, U k)) := by ring
      _ = _ := by rw [hj, mul_one, hc]

noncomputable def comap {X' : Scheme.{u}} (g : X' ⟶ X) : UnitCocycle (fun i => g ⁻¹ᵁ U i) where
  u i j := (g.app (U i ⊓ U j)).hom (c.u i j)
  refl i := by rw [c.refl, map_one]; rfl
  cocycle i j k := by
    have nat : ∀ {A B : X.Opens} (hBA : B ≤ A) (s : Γ(X, A)),
        GlueOfCocycle.rO (X := X') (show g ⁻¹ᵁ B ≤ g ⁻¹ᵁ A from fun _ hx => hBA hx) ((g.app A).hom s) =
          (g.app B).hom (rO hBA s) := by
      intro A B hBA s
      have h := CategoryTheory.ConcreteCategory.congr_hom (g.naturality (homOfLE hBA).op) s
      rw [CategoryTheory.ConcreteCategory.comp_apply, CategoryTheory.ConcreteCategory.comp_apply] at h
      exact h.symm
    have := congrArg (g.app (U i ⊓ U j ⊓ U k)).hom (c.cocycle i j k)
    rw [map_mul, ← nat, ← nat, ← nat] at this
    exact this

end UnitCocycle

namespace GlueOfCocycle

variable {U : ι → X.Opens} (c : UnitCocycle U) (T : X.Opens)

theorem leTi (i j : ι) : T ⊓ (U i ⊓ U j) ≤ T ⊓ U i := inf_le_inf_left T inf_le_left
theorem leTj (i j : ι) : T ⊓ (U i ⊓ U j) ≤ T ⊓ U j := inf_le_inf_left T inf_le_right
theorem leij (i j : ι) : T ⊓ (U i ⊓ U j) ≤ U i ⊓ U j := inf_le_right

def families : AddSubgroup (∀ i, Γ(X, T ⊓ U i)) where
  carrier := {x | ∀ i j, rO (leTi T i j) (x i) = rO (leij T i j) (c.u i j) * rO (leTj T i j) (x j)}
  zero_mem' := by intro i j; simp
  add_mem' := by
    intro x y hx hy i j
    simp only [Pi.add_apply, map_add]
    rw [hx, hy, mul_add]
  neg_mem' := by
    intro x hx i j
    simp only [Pi.neg_apply, map_neg]
    rw [hx, mul_neg]

variable {c T}

theorem mem_families {x : ∀ i, Γ(X, T ⊓ U i)} :
    x ∈ families c T ↔ ∀ i j, rO (leTi T i j) (x i) = rO (leij T i j) (c.u i j) * rO (leTj T i j) (x j) := Iff.rfl

variable (c T)

noncomputable instance : SMul Γ(X, T) (families c T) where
  smul g x := ⟨fun i => rO inf_le_left g * x.1 i, by
    have hx := x.2
    rw [mem_families] at hx ⊢
    intro i j
    simp only [map_mul, rO_rO]
    rw [hx i j, rO_irrel ((leTi T i j).trans inf_le_left) ((leTj T i j).trans inf_le_left)]
    ring⟩

theorem smul_val (g : Γ(X, T)) (x : families c T) (i : ι) : (g • x).1 i = rO inf_le_left g * x.1 i := rfl

noncomputable instance : Module Γ(X, T) (families c T) where
  one_smul x := by apply Subtype.ext; funext i; rw [smul_val]; simp
  mul_smul a b x := by apply Subtype.ext; funext i; simp only [smul_val, map_mul, mul_assoc]
  smul_zero a := by apply Subtype.ext; funext i; rw [smul_val]; simp
  smul_add a x y := by apply Subtype.ext; funext i; simp only [smul_val, AddSubgroup.coe_add, Pi.add_apply, mul_add]
  add_smul a b x := by apply Subtype.ext; funext i; simp only [smul_val, map_add, add_mul, AddSubgroup.coe_add, Pi.add_apply]
  zero_smul x := by apply Subtype.ext; funext i; rw [smul_val]; simp

variable {T}

noncomputable def resFam {T T' : X.Opens} (h : T' ≤ T) : families c T →+ families c T' where
  toFun x := ⟨fun i => rO (inf_le_inf_right (U i) h) (x.1 i), by
    have hx := x.2
    rw [mem_families] at hx ⊢
    intro i j
    rw [rO_rO, rO_rO]
    have e1 : rO ((leTi T' i j).trans (inf_le_inf_right (U i) h)) (x.1 i) =
        rO (inf_le_inf_right (U i ⊓ U j) h) (rO (leTi T i j) (x.1 i)) := by rw [rO_rO]
    have e2 : rO ((leTj T' i j).trans (inf_le_inf_right (U j) h)) (x.1 j) =
        rO (inf_le_inf_right (U i ⊓ U j) h) (rO (leTj T i j) (x.1 j)) := by rw [rO_rO]
    rw [e1, e2, hx i j, map_mul, rO_rO]⟩
  map_zero' := by apply Subtype.ext; funext i; simp
  map_add' x y := by apply Subtype.ext; funext i; simp

theorem resFam_val {T T' : X.Opens} (h : T' ≤ T) (x : families c T) (i : ι) :
    (resFam c h x).1 i = rO (inf_le_inf_right (U i) h) (x.1 i) := rfl

noncomputable def preGlue : (Opens X)ᵒᵖ ⥤ Ab where
  obj T := AddCommGrpCat.of (families c T.unop)
  map {T T'} f := AddCommGrpCat.ofHom (resFam c f.unop.le)
  map_id T := by
    ext
    exact rO_refl _
  map_comp {T₁ T₂ T₃} f g := by
    ext
    exact (rO_rO _ _ _).symm

noncomputable instance instModulePreGlue (T : (Opens X)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj T) ((preGlue c).obj T) :=
  inferInstanceAs (Module Γ(X, T.unop) (families c T.unop))

theorem preGlue_map_smul ⦃T T' : (Opens X)ᵒᵖ⦄ (f : T ⟶ T') (r : X.ringCatSheaf.obj.obj T) (m : (preGlue c).obj T) :
    (preGlue c).map f (r • m) = X.ringCatSheaf.obj.map f r • (preGlue c).map f m := by
  apply Subtype.ext; funext i
  change rO _ (rO _ r * m.1 i) = rO _ (rO _ r) * rO _ (m.1 i)
  simp only [map_mul, rO_rO]

noncomputable def preGlueMod : _root_.PresheafOfModules X.ringCatSheaf.obj :=
  _root_.PresheafOfModules.ofPresheaf (preGlue c) (preGlue_map_smul c)

set_option maxHeartbeats 400000 in
theorem preGlue_isSheaf : TopCat.Presheaf.IsSheaf (preGlue c) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ W sf hsf
  let T : X.Opens := iSup W
  have hWT : ∀ a, W a ≤ T := fun a => le_iSup W a

  let xs : ∀ (i : ι) (a : κ), Γ(X, W a ⊓ U i) := fun i a => (sf a).1 i
  have hx : ∀ i, TopCat.Presheaf.IsCompatible X.sheaf.obj (fun a => W a ⊓ U i) (xs i) := by
    intro i a b
    have h := congrArg (fun p : families c (W a ⊓ W b) => p.1 i) (hsf a b)
    change rO (inf_le_left : (W a ⊓ U i) ⊓ (W b ⊓ U i) ≤ W a ⊓ U i) (xs i a) =
      rO (inf_le_right : (W a ⊓ U i) ⊓ (W b ⊓ U i) ≤ W b ⊓ U i) (xs i b)
    have hle : (W a ⊓ U i) ⊓ (W b ⊓ U i) ≤ (W a ⊓ W b) ⊓ U i :=
      le_inf (inf_le_inf inf_le_left inf_le_left) (inf_le_left.trans inf_le_right)
    have e1 : rO (inf_le_left : (W a ⊓ U i) ⊓ (W b ⊓ U i) ≤ W a ⊓ U i) (xs i a) =
        rO hle (rO (inf_le_inf_right (U i) inf_le_left) (xs i a)) := by rw [rO_rO]
    have e2 : rO (inf_le_right : (W a ⊓ U i) ⊓ (W b ⊓ U i) ≤ W b ⊓ U i) (xs i b) =
        rO hle (rO (inf_le_inf_right (U i) inf_le_right) (xs i b)) := by rw [rO_rO]
    rw [e1, e2]
    exact congrArg _ h
  have hcov : ∀ i, T ⊓ U i ≤ ⨆ a, W a ⊓ U i := fun i => by rw [← iSup_inf_eq]
  have hcov2 : ∀ i j, T ⊓ (U i ⊓ U j) ≤ ⨆ a, W a ⊓ (U i ⊓ U j) := fun i j => by rw [← iSup_inf_eq]

  choose x hxg hxu using fun i => X.sheaf.existsUnique_gluing' (fun a => W a ⊓ U i) (T ⊓ U i)
    (fun a => homOfLE (inf_le_inf_right (U i) (hWT a))) (hcov i) (xs i) (hx i)

  have hxmem : ∀ i j, rO (leTi T i j) (x i) = rO (leij T i j) (c.u i j) * rO (leTj T i j) (x j) := by
    intro i j
    apply X.sheaf.eq_of_locally_eq' (fun a => W a ⊓ (U i ⊓ U j)) (T ⊓ (U i ⊓ U j))
      (fun a => homOfLE (inf_le_inf_right (U i ⊓ U j) (hWT a))) (hcov2 i j)
    intro a
    change rO (inf_le_inf_right (U i ⊓ U j) (hWT a)) (rO (leTi T i j) (x i)) =
      rO (inf_le_inf_right (U i ⊓ U j) (hWT a)) (rO (leij T i j) (c.u i j) * rO (leTj T i j) (x j))
    rw [map_mul, rO_rO, rO_rO, rO_rO]
    have ei : rO ((inf_le_inf_right (U i ⊓ U j) (hWT a)).trans (leTi T i j)) (x i : Γ(X, T ⊓ U i)) =
        rO (leTi (W a) i j) (xs i a) := by
      rw [← hxg i a]; exact (rO_rO _ _ _).symm
    have ej : rO ((inf_le_inf_right (U i ⊓ U j) (hWT a)).trans (leTj T i j)) (x j : Γ(X, T ⊓ U j)) =
        rO (leTj (W a) i j) (xs j a) := by
      rw [← hxg j a]; exact (rO_rO _ _ _).symm
    rw [ei, ej]
    exact (sf a).2 i j
  refine ⟨⟨fun i => x i, hxmem⟩, fun a => ?_, fun s hs => ?_⟩
  · apply Subtype.ext; funext i
    exact hxg i a
  · apply Subtype.ext; funext i
    exact hxu i (s.1 i) fun a => congrArg (fun p : families c (W a) => p.1 i) (hs a)

end GlueOfCocycle

variable {U : ι → X.Opens}

noncomputable def glueOfCocycle (c : UnitCocycle U) : X.Modules :=
  ⟨GlueOfCocycle.preGlueMod c, GlueOfCocycle.preGlue_isSheaf c⟩

theorem glueOfCocycle_sections_eq (c : UnitCocycle U) (T : X.Opens) :
    (Γ(glueOfCocycle c, T) : Type u) = GlueOfCocycle.families c T := rfl

theorem glue_map_val (c : UnitCocycle U) {T T' : X.Opens} (h : T' ≤ T) (p : Γ(glueOfCocycle c, T)) (i : ι) :
    (((glueOfCocycle c).presheaf.map (homOfLE h).op p : Γ(glueOfCocycle c, T')) : GlueOfCocycle.families c T').1 i =
      rO (inf_le_inf_right (U i) h) ((p : GlueOfCocycle.families c T).1 i) := rfl

theorem glue_smul_val (c : UnitCocycle U) {T : X.Opens} (g : Γ(X, T)) (p : Γ(glueOfCocycle c, T)) (i : ι) :
    ((g • p : Γ(glueOfCocycle c, T)) : GlueOfCocycle.families c T).1 i =
      rO inf_le_left g * (p : GlueOfCocycle.families c T).1 i := rfl

noncomputable def glueComponent (c : UnitCocycle U) (T : X.Opens) (i : ι) : Γ(glueOfCocycle c, T) →+ Γ(X, T ⊓ U i) where
  toFun p := (p : GlueOfCocycle.families c T).1 i
  map_zero' := rfl
  map_add' _ _ := rfl

theorem glueComponent_apply (c : UnitCocycle U) (T : X.Opens) (i : ι) (p : Γ(glueOfCocycle c, T)) :
    glueComponent c T i p = (p : GlueOfCocycle.families c T).1 i := rfl

theorem glue_ext (c : UnitCocycle U) {T : X.Opens} {p q : Γ(glueOfCocycle c, T)}
    (h : ∀ i, glueComponent c T i p = glueComponent c T i q) : p = q :=
  Subtype.ext (funext h)

theorem glueComponent_transition (c : UnitCocycle U) (T : X.Opens) (i j : ι) (p : Γ(glueOfCocycle c, T)) :
    rO (GlueOfCocycle.leTi T i j) (glueComponent c T i p) =
      rO (GlueOfCocycle.leij T i j) (c.u i j) * rO (GlueOfCocycle.leTj T i j) (glueComponent c T j p) :=
  (p : GlueOfCocycle.families c T).2 i j

theorem glueComponent_map (c : UnitCocycle U) {T T' : X.Opens} (h : T' ≤ T) (i : ι) (p : Γ(glueOfCocycle c, T)) :
    glueComponent c T' i ((glueOfCocycle c).presheaf.map (homOfLE h).op p) =
      rO (inf_le_inf_right (U i) h) (glueComponent c T i p) := rfl

theorem glueComponent_smul (c : UnitCocycle U) {T : X.Opens} (g : Γ(X, T)) (i : ι) (p : Γ(glueOfCocycle c, T)) :
    glueComponent c T i (g • p) = rO inf_le_left g * glueComponent c T i p := rfl

noncomputable def glueMk (c : UnitCocycle U) (T : X.Opens) (x : ∀ i, Γ(X, T ⊓ U i))
    (hx : ∀ i j, rO (GlueOfCocycle.leTi T i j) (x i) =
      rO (GlueOfCocycle.leij T i j) (c.u i j) * rO (GlueOfCocycle.leTj T i j) (x j)) : Γ(glueOfCocycle c, T) :=
  (⟨x, hx⟩ : GlueOfCocycle.families c T)

@[simp] theorem glueComponent_glueMk (c : UnitCocycle U) (T : X.Opens) (x : ∀ i, Γ(X, T ⊓ U i))
    (hx : ∀ i j, rO (GlueOfCocycle.leTi T i j) (x i) =
      rO (GlueOfCocycle.leij T i j) (c.u i j) * rO (GlueOfCocycle.leTj T i j) (x j)) (i : ι) :
    glueComponent c T i (glueMk c T x hx) = x i := rfl

noncomputable def glueFrame (c : UnitCocycle U) (i : ι) : Γ(glueOfCocycle c, U i) :=
  glueMk c (U i) (fun k => rO (le_of_eq (inf_comm (U i) (U k))) (c.u k i)) fun k l => by
    rw [rO_rO, rO_rO]
    exact (c.cocycle_le k l i (GlueOfCocycle.leij (U i) k l) _ _).symm

theorem glueComponent_glueFrame (c : UnitCocycle U) (i k : ι) :
    glueComponent c (U i) k (glueFrame c i) = rO (le_of_eq (inf_comm (U i) (U k))) (c.u k i) := rfl

theorem glueComponent_glueFrame_self (c : UnitCocycle U) (i : ι) :
    glueComponent c (U i) i (glueFrame c i) = 1 := by
  rw [glueComponent_glueFrame, c.refl, map_one]

theorem isFrameOn_glueFrame (c : UnitCocycle U) (i : ι) : IsFrameOn (glueFrame c i) (U i) := by
  intro W hWU _

  have key : ∀ (g : Γ(X, W)) (k : ι),
      glueComponent c W k (g • (glueOfCocycle c).presheaf.map (homOfLE hWU).op (glueFrame c i)) =
        rO (inf_le_left : W ⊓ U k ≤ W) g * rO (inf_le_inf_right (U k) hWU) (rO (le_of_eq (inf_comm (U i) (U k))) (c.u k i)) :=
    fun g k => rfl
  constructor
  · intro g g' hgg'
    have h := congrArg (glueComponent c W i) hgg'
    simp only [key, rO_rO] at h
    rw [show rO ((inf_le_inf_right (U i) hWU).trans (le_of_eq (inf_comm (U i) (U i)))) (c.u i i) = 1 by
      rw [c.refl, map_one], mul_one, mul_one] at h
    exact (rO_bijective_of_le_le (inf_le_left : W ⊓ U i ≤ W) (le_inf le_rfl hWU)).1 h
  · intro p
    refine ⟨rO (le_inf le_rfl hWU : W ≤ W ⊓ U i) (glueComponent c W i p), ?_⟩
    apply glue_ext
    intro k
    rw [key, rO_rO, rO_rO]

    have hp := glueComponent_transition c W k i p

    apply (rO_bijective_of_le_le (GlueOfCocycle.leTi W k i)
      (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hWU)))).1
    rw [map_mul, rO_rO, rO_rO, hp, mul_comm]

theorem map_glueFrame_eq_smul (c : UnitCocycle U) (i j : ι) :
    (glueOfCocycle c).presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (glueFrame c j) =
      c.u i j • (glueOfCocycle c).presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (glueFrame c i) := by
  apply glue_ext
  intro k
  rw [glueComponent_map, glueComponent_smul, glueComponent_map, glueComponent_glueFrame, glueComponent_glueFrame,
    rO_rO, rO_rO]

  have h := c.cocycle_le k i j (W := U i ⊓ U j ⊓ U k) (le_inf inf_le_right (inf_le_left.trans inf_le_left))
    inf_le_left (le_inf inf_le_right (inf_le_left.trans inf_le_right))
  rw [← h, mul_comm]

end AlgebraicGeometry.Scheme.Modules


