-- Prove2me | Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward
-- name    : AlgebraicGeometry_OModulePresheafCechPushforward
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/ff2e5e6d-85c0-51c6-b3e3-2b6811fa1a6d
-- title:
--   Čech pushforward of a presheaf-of-modules datum
-- statement:
--   Fix a commutative ring $R$, schemes $V', Z$, morphisms $p : V' \to Z$ and $\pi_Z : Z \to \operatorname{Spec} R$, and a finite linearly ordered affine open cover $K'$ of $V'$. For an open $U \subseteq Z$ and an index $i$, `chart` is the open $K'_i \cap p^{-1}U$ of $V'$; it is contained in $p^{-1}U$ and is monotone in $U$. Given a datum $G$ of type `OModulePresheaf (p ≫ πZ)` — an assignment of an $R$-module and $\Gamma(V',O)$-module $G(O)$ to each open $O \subseteq V'$, with the two actions compatible over the $R$-algebra structure on $\Gamma(V',O)$ coming from $p \circ \pi_Z$, together with $R$-linear restrictions satisfying semilinearity, reflexivity and transitivity — `cocycles` is the $R$-submodule of $\prod_i G(K'_i \cap p^{-1}U)$ cut out by the equalities $x_i|_{W_{ij}} = x_j|_{W_{ij}}$ on $W_{ij} = (K'_i \cap p^{-1}U) \cap (K'_j \cap p^{-1}U)$, for all ordered pairs $(i,j)$ (`mem_cocycles_iff` records this description). The maps `toChart` are the components $\Gamma(Z,U) \to \Gamma(V', K'_i \cap p^{-1}U)$ of $p$; through them $\Gamma(Z,U)$ acts componentwise on the cocycles (`sectionsSMul`, `sectionsModule`), compatibly with the $R$-action since `toChart` is an $R$-algebra map. Componentwise restriction preserves cocycles (`res_mem`, `resL`), and `cechPushforward` packages all this as a datum of type `OModulePresheaf πZ` with $U \mapsto$ these cocycles: the sections $p_*G$ computed by degree-zero Čech sections over the fixed cover, rather than by $U \mapsto G(p^{-1}U)$.
--
--   Helper lemmas describe the values, scalar multiplications, addition and extensionality componentwise. `Hom.cechPushforward` pushes a morphism of data defined on all opens to the Čech pushforwards, componentwise. For morphisms given on affine opens only, `AffHom.affineChart` exhibits $K'_i \cap p^{-1}U$ as an affine open for $U$ affine when $\pi_Z$ is separated, and `AffHom.cechPushforward`, assuming in addition that $p$ is separated (so that the pairwise intersections are affine too), produces the corresponding `AffHom` between the pushforwards.
--
--   **Relation to Mathlib.** The `OModulePresheaf` structure over a morphism to $\operatorname{Spec} R$ and the Čech pushforward constructed from it are the project's own; they are not Mathlib's presheaf-of-modules or pushforward-of-sheaves machinery, and no sheaf condition is imposed.
--
--   **Where it is used.** These data form part of the project's Čech-theoretic treatment of coherent and quasi-coherent modules on schemes over an affine base, where direct images along a morphism must be available with sections that are computed by an explicit cover rather than taken on possibly non-affine preimages.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OModulePresheafCechPushforward.lean

import Mathlib

import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R)) (K' : V'.OrderedAffineCover)

namespace cechPushforward

abbrev chart (U : Z.Opens) (i : K'.ι) : V'.Opens := K'.U i ⊓ p ⁻¹ᵁ U

theorem chart_le_preimage (U : Z.Opens) (i : K'.ι) : chart p K' U i ≤ p ⁻¹ᵁ U := inf_le_right

theorem chart_mono {U U' : Z.Opens} (h : U ≤ U') (i : K'.ι) : chart p K' U i ≤ chart p K' U' i :=
  inf_le_inf_left _ ((Opens.map p.base).monotone h)

variable (G : OModulePresheaf (p ≫ πZ))

def cocycles (U : Z.Opens) : Submodule R (∀ i : K'.ι, G.obj (chart p K' U i)) :=
  ⨅ i : K'.ι, ⨅ j : K'.ι, LinearMap.ker
    ((G.res (U := chart p K' U i ⊓ chart p K' U j) inf_le_left).comp (LinearMap.proj i)
      - (G.res (U := chart p K' U i ⊓ chart p K' U j) inf_le_right).comp (LinearMap.proj j))

theorem mem_cocycles_iff (U : Z.Opens) (x : ∀ i : K'.ι, G.obj (chart p K' U i)) :
    x ∈ cocycles p πZ K' G U ↔ ∀ i j : K'.ι,
      G.res (U := chart p K' U i ⊓ chart p K' U j) inf_le_left (x i)
        = G.res (U := chart p K' U i ⊓ chart p K' U j) inf_le_right (x j) := by
  simp only [cocycles, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, sub_eq_zero]

abbrev toChart (U : Z.Opens) (i : K'.ι) : Γ(Z, U) ⟶ Γ(V', chart p K' U i) :=
  p.appLE U (chart p K' U i) (chart_le_preimage p K' U i)

theorem toChart_algebraMap (U : Z.Opens) (i : K'.ι) (r : R) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom πZ U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (p ≫ πZ) (chart p K' U i)
    (toChart p K' U i).hom (algebraMap R Γ(Z, U) r) = algebraMap R Γ(V', chart p K' U i) r := by
  show (p.appLE U _ _).hom ((πZ.appLE ⊤ U le_top).hom _) = ((p ≫ πZ).appLE ⊤ _ le_top).hom _
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem map_toChart_left (U : Z.Opens) (i j : K'.ι) (a : Γ(Z, U)) :
    (V'.presheaf.map (homOfLE (inf_le_left : chart p K' U i ⊓ chart p K' U j ≤ chart p K' U i)).op).hom
        ((toChart p K' U i).hom a)
      = (p.appLE U (chart p K' U i ⊓ chart p K' U j) (inf_le_left.trans (chart_le_preimage p K' U i))).hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem map_toChart_right (U : Z.Opens) (i j : K'.ι) (a : Γ(Z, U)) :
    (V'.presheaf.map (homOfLE (inf_le_right : chart p K' U i ⊓ chart p K' U j ≤ chart p K' U j)).op).hom
        ((toChart p K' U j).hom a)
      = (p.appLE U (chart p K' U i ⊓ chart p K' U j) (inf_le_left.trans (chart_le_preimage p K' U i))).hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

@[reducible] def sectionsSMul (U : Z.Opens) : SMul Γ(Z, U) (cocycles p πZ K' G U) where
  smul a x := ⟨fun i => (toChart p K' U i).hom a • x.1 i, by
    rw [mem_cocycles_iff]
    intro i j
    rw [G.res_smul, G.res_smul, map_toChart_left, map_toChart_right,
      (mem_cocycles_iff p πZ K' G U x.1).mp x.2 i j]⟩

@[reducible] def sectionsModule (U : Z.Opens) : Module Γ(Z, U) (cocycles p πZ K' G U) :=
  letI := sectionsSMul p πZ K' G U
  { one_smul := fun x => Subtype.ext (funext fun i => by
      show (toChart p K' U i).hom 1 • x.1 i = x.1 i
      rw [map_one, one_smul])
    mul_smul := fun a b x => Subtype.ext (funext fun i => by
      show (toChart p K' U i).hom (a * b) • x.1 i = (toChart p K' U i).hom a • ((toChart p K' U i).hom b • x.1 i)
      rw [map_mul, mul_smul])
    smul_zero := fun a => Subtype.ext (funext fun i => smul_zero _)
    smul_add := fun a x y => Subtype.ext (funext fun i => smul_add _ _ _)
    add_smul := fun a b x => Subtype.ext (funext fun i => by
      show (toChart p K' U i).hom (a + b) • x.1 i = (toChart p K' U i).hom a • x.1 i + (toChart p K' U i).hom b • x.1 i
      rw [map_add, add_smul])
    zero_smul := fun x => Subtype.ext (funext fun i => by
      show (toChart p K' U i).hom 0 • x.1 i = 0
      rw [map_zero, zero_smul]) }

theorem res_mem {U U' : Z.Opens} (h : U ≤ U') (x : cocycles p πZ K' G U') :
    (fun i => G.res (chart_mono p K' h i) (x.1 i)) ∈ cocycles p πZ K' G U := by
  rw [mem_cocycles_iff]
  intro i j
  rw [G.res_res, G.res_res,
    ← G.res_res (inf_le_inf (chart_mono p K' h i) (chart_mono p K' h j))
      (inf_le_left : chart p K' U' i ⊓ chart p K' U' j ≤ _),
    ← G.res_res (inf_le_inf (chart_mono p K' h i) (chart_mono p K' h j))
      (inf_le_right : chart p K' U' i ⊓ chart p K' U' j ≤ _),
    (mem_cocycles_iff p πZ K' G U' x.1).mp x.2 i j]

def resL {U U' : Z.Opens} (h : U ≤ U') : cocycles p πZ K' G U' →ₗ[R] cocycles p πZ K' G U where
  toFun x := ⟨fun i => G.res (chart_mono p K' h i) (x.1 i), res_mem p πZ K' G h x⟩
  map_add' x y := Subtype.ext (funext fun i => (G.res (chart_mono p K' h i)).map_add (x.1 i) (y.1 i))
  map_smul' r x := Subtype.ext (funext fun i => (G.res (chart_mono p K' h i)).map_smul r (x.1 i))

end cechPushforward

open cechPushforward in

def cechPushforward (G : OModulePresheaf (p ≫ πZ)) : OModulePresheaf πZ where
  obj U := cocycles p πZ K' G U
  module U := inferInstance
  moduleSections U := sectionsModule p πZ K' G U
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom πZ U
    letI := sectionsModule p πZ K' G U
    refine ⟨fun r a x => Subtype.ext (funext fun i => ?_)⟩
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (p ≫ πZ) (chart p K' U i)
    show (toChart p K' U i).hom (r • a) • x.1 i = r • ((toChart p K' U i).hom a • x.1 i)
    rw [Algebra.smul_def, map_mul, mul_smul, toChart_algebraMap, algebraMap_smul]
  res h := resL p πZ K' G h
  res_smul {U U'} h a x := Subtype.ext (funext fun i => by
    show G.res _ ((toChart p K' U' i).hom a • x.1 i)
      = (toChart p K' U i).hom ((Z.presheaf.map (homOfLE h).op).hom a) • G.res (chart_mono p K' h i) (x.1 i)
    rw [G.res_smul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply (f := Z.presheaf.map _),
      Scheme.Hom.appLE_map, Scheme.Hom.map_appLE])
  res_refl U := LinearMap.ext fun x => Subtype.ext (funext fun i => G.res_refl_apply _ _)
  res_comp h h' := LinearMap.ext fun x => Subtype.ext (funext fun i => (G.res_res _ _ _).symm)

section Lemmas

variable (G : OModulePresheaf (p ≫ πZ))

@[simp] theorem cechPushforward_obj (U : Z.Opens) :
    (cechPushforward p πZ K' G).obj U = ↥(cechPushforward.cocycles p πZ K' G U) := rfl

namespace cechPushforward

theorem coe_res {U U' : Z.Opens} (h : U ≤ U') (x : (cechPushforward p πZ K' G).obj U') (i : K'.ι) :
    ((cechPushforward p πZ K' G).res h x).1 i = G.res (cechPushforward.chart_mono p K' h i) (x.1 i) := rfl

theorem coe_smul (U : Z.Opens) (r : R) (x : (cechPushforward p πZ K' G).obj U) (i : K'.ι) :
    (r • x).1 i = r • x.1 i := rfl

theorem coe_sectionsSMul (U : Z.Opens) (a : Γ(Z, U)) (x : (cechPushforward p πZ K' G).obj U) (i : K'.ι) :
    (a • x).1 i = (cechPushforward.toChart p K' U i).hom a • x.1 i := rfl

theorem coe_add (U : Z.Opens) (x y : (cechPushforward p πZ K' G).obj U) (i : K'.ι) :
    (x + y).1 i = x.1 i + y.1 i := rfl

theorem ext {U : Z.Opens} {x y : (cechPushforward p πZ K' G).obj U} (h : ∀ i, x.1 i = y.1 i) : x = y :=
  Subtype.ext (funext h)

end cechPushforward

end Lemmas

namespace Hom

variable {G G' : OModulePresheaf (p ≫ πZ)}

def cechPushforward (φ : Hom G G') :
    Hom (OModulePresheaf.cechPushforward p πZ K' G) (OModulePresheaf.cechPushforward p πZ K' G') where
  app U :=
    { toFun := fun x => ⟨fun i => φ.app _ (x.1 i), by
        rw [cechPushforward.mem_cocycles_iff]
        intro i j
        rw [← φ.naturality_apply, ← φ.naturality_apply,
          (cechPushforward.mem_cocycles_iff p πZ K' G U x.1).mp x.2 i j]⟩
      map_add' := fun x y => Subtype.ext (funext fun i => map_add _ _ _)
      map_smul' := fun r x => Subtype.ext (funext fun i => LinearMap.map_smul _ _ _) }
  app_smul U a x := Subtype.ext (funext fun i => φ.app_smul _ _ _)
  naturality h := LinearMap.ext fun x => Subtype.ext (funext fun i => φ.naturality_apply _ _)

@[simp] theorem coe_cechPushforward_app (φ : Hom G G') (U : Z.Opens)
    (x : (OModulePresheaf.cechPushforward p πZ K' G).obj U) (i : K'.ι) :
    ((φ.cechPushforward p πZ K').app U x).1 i = φ.app _ (x.1 i) := rfl

end Hom

namespace AffHom

variable {G G' : OModulePresheaf (p ≫ πZ)}

abbrev affineChart [IsSeparated πZ] (U : Z.affineOpens) (i : K'.ι) : V'.affineOpens :=
  ⟨OModulePresheaf.cechPushforward.chart p K' U.1 i,
    Scheme.OrderedAffineCover.fiberAffineOpen p πZ (K'.isAffineOpen i) U.2⟩

def cechPushforward [IsSeparated πZ] [IsSeparated p] (φ : AffHom G G') :
    AffHom (OModulePresheaf.cechPushforward p πZ K' G) (OModulePresheaf.cechPushforward p πZ K' G') where
  app U :=
    { toFun := fun x => ⟨fun i => φ.app (affineChart p πZ K' U i) (x.1 i), by
        rw [OModulePresheaf.cechPushforward.mem_cocycles_iff]
        intro i j
        have hij : IsAffineOpen (OModulePresheaf.cechPushforward.chart p K' U.1 i
            ⊓ OModulePresheaf.cechPushforward.chart p K' U.1 j) :=
          haveI : IsSeparated (p ≫ πZ) := inferInstance
          Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated (p ≫ πZ)
            (affineChart p πZ K' U i).2 (affineChart p πZ K' U j).2
        rw [← φ.naturality_apply (U := ⟨_, hij⟩) (U' := affineChart p πZ K' U i),
          ← φ.naturality_apply (U := ⟨_, hij⟩) (U' := affineChart p πZ K' U j),
          (OModulePresheaf.cechPushforward.mem_cocycles_iff p πZ K' G U.1 x.1).mp x.2 i j]⟩
      map_add' := fun x y => Subtype.ext (funext fun i => map_add _ _ _)
      map_smul' := fun r x => Subtype.ext (funext fun i => LinearMap.map_smul _ _ _) }
  app_smul U a x := Subtype.ext (funext fun i => φ.app_smul _ _ _)
  naturality {U U'} h := LinearMap.ext fun x => Subtype.ext (funext fun i =>
    φ.naturality_apply (U := affineChart p πZ K' U i) (U' := affineChart p πZ K' U' i) _ _)

@[simp] theorem coe_cechPushforward_app [IsSeparated πZ] [IsSeparated p] (φ : AffHom G G') (U : Z.affineOpens)
    (x : (OModulePresheaf.cechPushforward p πZ K' G).obj U.1) (i : K'.ι) :
    ((φ.cechPushforward p πZ K').app U x).1 i = φ.app (affineChart p πZ K' U i) (x.1 i) := rfl

end AffHom

end OModulePresheaf

end AlgebraicGeometry

end


