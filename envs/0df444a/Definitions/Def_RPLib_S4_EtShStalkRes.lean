-- Prove2me | Definitions.Def_RPLib_S4_EtShStalkRes
-- name    : RPLib_S4_EtShStalkRes
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:26:56.838191+00:00
-- url     : https://prove2.me/theorems/5522a1f8-a140-44e1-bf05-64336cdc46cc
-- title:
--   Stalks of a restriction along an etale morphism
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. For an etale $g : U \to X$, a geometric point $\bar t$ of $U$ and $F \in \mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$, the map $(F|_U)_{\bar t} \to F_{g \circ \bar t}$ sending the germ of $z \in F(W \to U \to X)$ at a lift $b$ (over $U$) to the germ of $z$ at $b$ viewed as a lift over $X$ is bijective: every etale neighbourhood of $g \circ \bar t$ is refined by one of the form $W \times_X U$, and a neighbourhood over $X$ of a lift over $U$ is again etale over $U$. So it is an isomorphism with an explicit formula on germs.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose VIII; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter II

import Mathlib
import Definitions.Def_RPLib_S4_EtShRes

/-!
# S4-EtSheaves, part 38: stalks of a restriction, on germs

For an etale `g : U ⟶ X` and a geometric point `t` of `U`, `resFib g t Λ F : (res g F)_t ⟶ F_(t ≫ g)` sends the germ of
`z ∈ F(W → U → X)` at a lift `b : Spec Ω ⟶ W` (over `U`) to the germ of `z` at `b` viewed as a lift over `X`
(`liftX`). It is bijective (`resFib_surjective`: every neighbourhood of `t ≫ g` is refined by one of the form
`W ×_X U`; `resFib_injective`: a neighbourhood over `X` of a lift over `U` is again etale over `U`, `etLift`), so it is
an isomorphism `resFibIso` with an explicit germ formula (`resFib_germ`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] (t : GeomPt U)

/-- A lift of `t` into `W` over `U` is a lift of `t ≫ g` into `W` over `X`. -/
def liftX {W : U.Etale} (b : t.point.fiber.obj W) : (t.map g).point.fiber.obj ((etComp g).obj W) :=
  let b' : CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget U).obj W := b
  (Over.homMk b'.left ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ g) (Over.w b'))) :
    CategoryTheory.Over.mk (t.pt ≫ g) ⟶ (Scheme.Etale.forget X).obj ((etComp g).obj W))

theorem liftX_left {W : U.Etale} (b : t.point.fiber.obj W) :
    (show CategoryTheory.Over.mk (t.pt ≫ g) ⟶ (Scheme.Etale.forget X).obj ((etComp g).obj W) from
      liftX g t b).left = (show CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget U).obj W from b).left := rfl

theorem liftX_map {W W' : U.Etale} (f : W ⟶ W') (b : t.point.fiber.obj W) :
    liftX g t (t.point.fiber.map f b) = (t.map g).point.fiber.map ((etComp g).map f) (liftX g t b) :=
  Over.OverMorphism.ext rfl

variable (Λ : Type u) [CommRing Λ]

/-- **The germ map** `(res g F)_t ⟶ F_(t ≫ g)`. -/
def resFib (F : EtSh Λ X) : (t.stalkF Λ).obj ((res g Λ).obj F) ⟶ ((t.map g).stalkF Λ).obj F :=
  t.point.presheafFiberDesc (P := ((res g Λ).obj F).obj)
    (fun W b => (t.map g).point.toPresheafFiber ((etComp g).obj W) (liftX g t b) F.obj)
    (fun _ W' f b => ((t.map g).point.toPresheafFiber_w ((etComp g).map f) (liftX g t b) F.obj).trans
      (congrArg (fun a => (t.map g).point.toPresheafFiber ((etComp g).obj W') a F.obj)
        (liftX_map g t f b).symm))

@[reassoc]
theorem germ_resFib (F : EtSh Λ X) (W : U.Etale) (b : t.point.fiber.obj W) :
    t.point.toPresheafFiber W b ((res g Λ).obj F).obj ≫ resFib g t Λ F =
      (t.map g).point.toPresheafFiber ((etComp g).obj W) (liftX g t b) F.obj :=
  GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc _ _ _ _ _

theorem resFib_germ (F : EtSh Λ X) (W : U.Etale) (b : t.point.fiber.obj W)
    (z : F.obj.obj (op ((etComp g).obj W))) :
    (resFib g t Λ F).hom (t.point.toPresheafFiber W b ((res g Λ).obj F).obj z) =
      (t.map g).point.toPresheafFiber ((etComp g).obj W) (liftX g t b) F.obj z :=
  congrArg (fun φ => φ.hom z) (germ_resFib g t Λ F W b)

theorem resFib_surjective (F : EtSh Λ X) : Function.Surjective (resFib g t Λ F).hom := by
  intro p
  obtain ⟨W, a, z, rfl⟩ := GrothendieckTopology.Point.toPresheafFiber_jointly_surjective
    (A := ModuleCat.{u} Λ) (t.map g).point (P := F.obj) p
  let a' : CategoryTheory.Over.mk (t.pt ≫ g) ⟶ (Scheme.Etale.forget X).obj W := a
  let T : U.Etale := (etPull g).obj W
  let bl : Spec (CommRingCat.of t.Ω) ⟶ pullback W.hom g := pullback.lift a'.left t.pt (Over.w a')
  let b : t.point.fiber.obj T :=
    (Over.homMk bl (pullback.lift_snd _ _ _) :
      CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget U).obj T)
  let fX : (etComp g).obj T ⟶ W := MorphismProperty.Over.homMk (pullback.fst W.hom g) pullback.condition trivial
  have hb : (t.map g).point.fiber.map fX (liftX g t b) = a := by
    change (_ : CategoryTheory.Over.mk (t.pt ≫ g) ⟶ (Scheme.Etale.forget X).obj W) = a'
    exact Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  refine ⟨t.point.toPresheafFiber T b ((res g Λ).obj F).obj ((F.obj.map fX.op).hom z), ?_⟩
  rw [resFib_germ]
  exact (congrArg (fun φ => φ.hom z) ((t.map g).point.toPresheafFiber_w fX (liftX g t b) F.obj)).trans
    (congrArg (fun a => (t.map g).point.toPresheafFiber W a F.obj z) hb)

theorem resFib_injective (F : EtSh Λ X) : Function.Injective (resFib g t Λ F).hom := by
  refine (injective_iff_map_eq_zero _).2 fun q hq => ?_
  obtain ⟨T, b, z, rfl⟩ := GrothendieckTopology.Point.toPresheafFiber_jointly_surjective
    (A := ModuleCat.{u} Λ) t.point (P := ((res g Λ).obj F).obj) q
  rw [resFib_germ] at hq
  have h0 : (t.map g).point.toPresheafFiber ((etComp g).obj T) (liftX g t b) F.obj z =
      (t.map g).point.toPresheafFiber ((etComp g).obj T) (liftX g t b) F.obj 0 := by
    rw [hq]; exact (map_zero _).symm
  obtain ⟨W, f, y, hy, hz⟩ :=
    ((t.map g).point.toPresheafFiber_eq_iff' ((etComp g).obj T) (liftX g t b) z 0).1 h0
  let b' : CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget U).obj T := b
  let y' : CategoryTheory.Over.mk (t.pt ≫ g) ⟶ (Scheme.Etale.forget X).obj W := y
  have hyl : y'.left ≫ f.left = b'.left := congrArg (fun φ : CategoryTheory.Over.mk (t.pt ≫ g) ⟶
    (Scheme.Etale.forget X).obj ((etComp g).obj T) => φ.left) hy
  let W' : U.Etale := etLift g (W := T) W f.left (MorphismProperty.Over.w f)
  let f' : W' ⟶ T := MorphismProperty.Over.homMk f.left rfl trivial
  let yU : t.point.fiber.obj W' :=
    (Over.homMk y'.left (by
        change y'.left ≫ f.left ≫ T.hom = t.pt
        rw [← Category.assoc, hyl]
        exact Over.w b') :
      CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget U).obj W')
  have hyU : t.point.fiber.map f' yU = b := by
    change (_ : CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget U).obj T) = b'
    exact Over.OverMorphism.ext hyl
  let e : (etComp g).obj W' ≅ W := MorphismProperty.Over.isoMk (Iso.refl _)
    (by
    change 𝟙 _ ≫ W.hom = (f.left ≫ T.hom) ≫ g
    rw [Category.id_comp, Category.assoc]
    exact (MorphismProperty.Over.w f).symm)
  have hf : f = e.inv ≫ (etComp g).map f' :=
    MorphismProperty.Over.Hom.ext (Category.id_comp f.left).symm
  have hz0 : (F.obj.map ((etComp g).map f').op).hom z = 0 := by
    have h1 : (F.obj.map e.inv.op).hom ((F.obj.map ((etComp g).map f').op).hom z) = 0 := by
      have h2 : (F.obj.map f.op).hom z = 0 := hz.trans (map_zero _)
      rw [hf, op_comp, CategoryTheory.Functor.map_comp] at h2
      exact h2
    have h3 := congrArg (F.obj.map e.hom.op).hom h1
    rw [map_zero] at h3
    refine Eq.trans ?_ h3
    change _ = (F.obj.map e.inv.op ≫ F.obj.map e.hom.op).hom _
    rw [← CategoryTheory.Functor.map_comp, ← op_comp, e.hom_inv_id, op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [← hyU]
  have hw := congrArg (fun φ => φ.hom z) (t.point.toPresheafFiber_w f' yU ((res g Λ).obj F).obj)
  refine hw.symm.trans ?_
  change (t.point.toPresheafFiber W' yU ((res g Λ).obj F).obj).hom
    ((F.obj.map ((etComp g).map f').op).hom z) = 0
  exact (congrArg (t.point.toPresheafFiber W' yU ((res g Λ).obj F).obj).hom hz0).trans (map_zero _)

/-- **Stalks of a restriction along an etale map**, with the germ formula `resFib_germ`. -/
def resFibIso (F : EtSh Λ X) : (t.stalkF Λ).obj ((res g Λ).obj F) ≅ ((t.map g).stalkF Λ).obj F :=
  (LinearEquiv.ofBijective (resFib g t Λ F).hom
    ⟨resFib_injective g t Λ F, resFib_surjective g t Λ F⟩).toModuleIso

theorem resFibIso_hom (F : EtSh Λ X) : (resFibIso g t Λ F).hom = resFib g t Λ F := rfl

theorem resFibIso_inv_germ (F : EtSh Λ X) (W : U.Etale) (b : t.point.fiber.obj W)
    (z : F.obj.obj (op ((etComp g).obj W))) :
    (resFibIso g t Λ F).inv.hom ((t.map g).point.toPresheafFiber ((etComp g).obj W) (liftX g t b) F.obj z) =
      t.point.toPresheafFiber W b ((res g Λ).obj F).obj z := by
  rw [← resFib_germ]
  exact congrArg (fun φ => φ.hom (t.point.toPresheafFiber W b ((res g Λ).obj F).obj z))
    (resFibIso g t Λ F).hom_inv_id

/-- `resFib` is natural in the sheaf. -/
@[reassoc]
theorem resFib_natural {F G : EtSh Λ X} (φ : F ⟶ G) :
    (t.stalkF Λ).map ((res g Λ).map φ) ≫ resFib g t Λ G = resFib g t Λ F ≫ ((t.map g).stalkF Λ).map φ := by
  refine GrothendieckTopology.Point.presheafFiber_hom_ext _ (fun W b => ?_)
  change t.point.toPresheafFiber W b _ ≫ t.point.presheafFiber.map ((res g Λ).map φ).hom ≫ resFib g t Λ G =
    t.point.toPresheafFiber W b _ ≫ resFib g t Λ F ≫ (t.map g).point.presheafFiber.map φ.hom
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality_assoc, germ_resFib, germ_resFib_assoc,
    GrothendieckTopology.Point.toPresheafFiber_naturality]
  rfl

end RamanujanPetersson.EtSheaves


