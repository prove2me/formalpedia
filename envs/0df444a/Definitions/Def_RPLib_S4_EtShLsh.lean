-- Prove2me | Definitions.Def_RPLib_S4_EtShLsh
-- name    : RPLib_S4_EtShLsh
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:27:05.041474+00:00
-- url     : https://prove2.me/theorems/20d1b171-16b8-466a-b6d4-1c17993dd801
-- title:
--   Extension by zero $j_!$ for etale sheaves
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. For an etale $j : U \to X$, extension by zero $j_!$ is the left adjoint of restriction $j^*$. Its stalks are $(j_! G)_{j \circ \bar t} \cong G_{\bar t}$ when $j$ is a monomorphism (an open immersion), and $(j_! G)_{\bar s} = 0$ when the centre of $\bar s$ is not in the image of $j$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose IV, Section 11; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter II

import Mathlib
import Definitions.Def_RPLib_S4_EtShRes

/-!
# S4-EtSheaves, part 12: extension by zero `j_!`

For an etale `j : U ⟶ X`, `lsh j Λ = j_!` is the left adjoint of restriction `res j ≅ j^*`
(`Functor.sheafPullback` along `etComp j`, with the universe trick used for `push`).
Stalks: `(j_! G)_(t ≫ j) ≅ G_t` when `j` is a monomorphism (an open immersion), and
`(j_! G)_s = 0` when the centre of `s` is not in the image of `j`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

section Lsh

variable (Λ : Type u) [CommRing Λ]

/-- `etComp j` restricted to affine etale `U`-schemes. -/
def affComp : U.AffineEtale ⥤ X.Etale := Scheme.AffineEtale.Spec U ⋙ etComp j

instance : (affComp j).IsContinuous (Scheme.AffineEtale.topology U) X.smallEtaleTopology :=
  Functor.isContinuous_comp _ _ _ U.smallEtaleTopology _

instance (V : (X.Etale)ᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow (affComp j).op V) (ModuleCat.{u} Λ) :=
  hasColimitsOfShape_of_essentiallySmall.{u} _ _

instance (F : (U.AffineEtale)ᵒᵖ ⥤ ModuleCat.{u} Λ) : (affComp j).op.HasLeftKanExtension F := by
  have : (affComp j).op.HasPointwiseLeftKanExtension F := fun _ => inferInstance
  infer_instance

instance : (res j Λ).IsRightAdjoint := by
  have h1 : ((affComp j).sheafPushforwardContinuous (ModuleCat.{u} Λ)
      (Scheme.AffineEtale.topology U) X.smallEtaleTopology).IsRightAdjoint := inferInstance
  have h2 : (res j Λ ⋙ (Scheme.AffineEtale.Spec U).sheafPushforwardContinuous (ModuleCat.{u} Λ)
      (Scheme.AffineEtale.topology U) U.smallEtaleTopology).IsRightAdjoint := h1
  exact (Functor.isRightAdjoint_comp_iff_left _ _).1 h2

/-- **Extension by zero** `j_!`: the left adjoint of restriction along the etale `j`. -/
abbrev lsh : EtSh Λ U ⥤ EtSh Λ X :=
  (etComp j).sheafPullback (ModuleCat.{u} Λ) U.smallEtaleTopology X.smallEtaleTopology

/-- `j_! ⊣ res j`. -/
def lshAdj : lsh j Λ ⊣ res j Λ := Functor.sheafAdjunctionContinuous _ _ _ _

/-- `j_! ⊣ j^*`. -/
def lshPullAdj : lsh j Λ ⊣ pull j Λ := (lshAdj j Λ).ofNatIsoRight (pullIsoRes j Λ).symm

end Lsh

section Stalks

/-- For a monomorphism `j`, `X`-maps `Spec Ω ⟶ W` (with `W` over `U`) are the `U`-maps. -/
def lshFiberIso [Mono j] (t : GeomPt U) :
    t.point.fiber ≅ etComp j ⋙ (t.map j).point.fiber :=
  NatIso.ofComponents (fun W => Equiv.toIso
    { toFun := fun (a : Over.mk t.pt ⟶ (Scheme.Etale.forget U).obj W) =>
        (Over.homMk a.left ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ j) (Over.w a))) :
          Over.mk (t.pt ≫ j) ⟶ (Scheme.Etale.forget X).obj ((etComp j).obj W))
      invFun := fun (b : Over.mk (t.pt ≫ j) ⟶ (Scheme.Etale.forget X).obj ((etComp j).obj W)) =>
        (Over.homMk b.left ((cancel_mono j).1 ((Category.assoc _ _ _).trans (Over.w b))) :
          Over.mk t.pt ⟶ (Scheme.Etale.forget U).obj W)
      left_inv := fun _ => Over.OverMorphism.ext rfl
      right_inv := fun _ => Over.OverMorphism.ext rfl })
    (fun _ => ConcreteCategory.hom_ext _ _ fun _ => Over.OverMorphism.ext rfl)

/-- The categories of elements of the two fibre functors agree. -/
def lshElemEquiv [Mono j] (t : GeomPt U) :
    t.point.fiber.Elements ≌ (etComp j ⋙ (t.map j).point.fiber).Elements :=
  (CategoryOfElements.structuredArrowEquivalence _).trans
    ((StructuredArrow.mapNatIso (lshFiberIso j t)).trans
      (CategoryOfElements.structuredArrowEquivalence _).symm)

/-- The point of `U`'s site with fibre `etComp j ⋙ (t ≫ j).fiber`, for `j` mono. -/
def lshPt [Mono j] (t : GeomPt U) : (U.smallEtaleTopology).Point where
  fiber := etComp j ⋙ (t.map j).point.fiber
  isCofiltered := IsCofiltered.of_equivalence (lshElemEquiv j t)
  initiallySmall := by
    have : InitiallySmall.{u} t.point.fiber.Elements := t.point.initiallySmall
    exact initiallySmall_of_initial_of_initiallySmall (lshElemEquiv j t).functor
  jointly_surjective {W} R hR x := by
    obtain ⟨Y, f, hf, y, hy⟩ := t.point.jointly_surjective R hR ((lshFiberIso j t).inv.app W x)
    refine ⟨Y, f, hf, (lshFiberIso j t).hom.app Y y, ?_⟩
    calc (etComp j ⋙ (t.map j).point.fiber).map f ((lshFiberIso j t).hom.app Y y)
        = (lshFiberIso j t).hom.app W (t.point.fiber.map f y) :=
          (types_congr_hom ((lshFiberIso j t).hom.naturality f) y).symm
      _ = (lshFiberIso j t).hom.app W ((lshFiberIso j t).inv.app W x) := by rw [hy]
      _ = x := types_congr_hom ((lshFiberIso j t).inv_hom_id_app W) x

/-- `t` and `lshPt j t` are isomorphic points. -/
def lshPtIso [Mono j] (t : GeomPt U) : t.point ≅ lshPt j t where
  hom := ⟨(lshFiberIso j t).inv⟩
  inv := ⟨(lshFiberIso j t).hom⟩
  hom_inv_id := by ext : 1; exact (lshFiberIso j t).hom_inv_id
  inv_hom_id := by ext : 1; exact (lshFiberIso j t).inv_hom_id

variable (Λ : Type u) [CommRing Λ]

/-- **Stalks of `j_!` on `U`** (`j` mono, e.g. an open immersion): `(j_! G)_(t ≫ j) ≅ G_t`. -/
def lshStalkIso [Mono j] (t : GeomPt U) :
    lsh j Λ ⋙ (t.map j).stalkF Λ ≅ t.stalkF Λ :=
  ((conjugateIsoEquiv
      ((lshAdj j Λ).comp ((t.map j).point.skyscraperSheafAdjunction (A := ModuleCat.{u} Λ)))
      ((lshPt j t).skyscraperSheafAdjunction (A := ModuleCat.{u} Λ))).symm (Iso.refl _)).symm ≪≫
    ptIsoSheafFiber Λ (lshPtIso j t)

/-- **Stalks of `j_!` off the image of `j`** vanish. -/
theorem lsh_stalk_isZero (s : GeomPt X) (hs : s.center ∉ Set.range j) (G : EtSh Λ U) :
    IsZero ((s.stalkF Λ).obj ((lsh j Λ).obj G)) := by
  let adj := (lshAdj j Λ).comp (s.point.skyscraperSheafAdjunction (A := ModuleCat.{u} Λ))
  have hE : ∀ W : U.Etale, IsEmpty (s.point.fiber.obj ((etComp j).obj W)) := fun W =>
    ⟨fun (b : Over.mk s.pt ⟶ (Scheme.Etale.forget X).obj ((etComp j).obj W)) => hs
      ⟨(b.left ≫ W.hom : Spec (CommRingCat.of s.Ω) ⟶ U) default, by
        have hw : (b.left ≫ W.hom) ≫ j = s.pt := (Category.assoc _ _ _).trans (Over.w b)
        rw [← Scheme.Hom.comp_apply, hw]; rfl⟩⟩
  have hsub : ∀ f g : G ⟶ (s.point.skyscraperSheafFunctor ⋙ res j Λ).obj
      ((s.stalkF Λ).obj ((lsh j Λ).obj G)), f = g := by
    intro f g
    refine Sheaf.hom_ext (NatTrans.ext (funext fun W => ?_))
    exact Pi.hom_ext _ _ (fun i => (hE W.unop).elim i)
  rw [IsZero.iff_id_eq_zero]
  exact (adj.homEquiv G _).injective (hsub _ _)

end Stalks

end RamanujanPetersson.EtSheaves


