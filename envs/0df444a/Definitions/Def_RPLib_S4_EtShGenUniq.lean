-- Prove2me | Definitions.Def_RPLib_S4_EtShGenUniq
-- name    : RPLib_S4_EtShGenUniq
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:38:35.898094+00:00
-- url     : https://prove2.me/theorems/3696e0b0-4258-4093-ae48-f4dbe1dec9f7
-- title:
--   Sections of a locally constant sheaf are determined by their generic germs
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. Let $x_0 \in X$ lie in every nonempty open subset of $X$ (a generic point) and $G$ a locally constant etale sheaf on $X$. A section $d \in G(W)$ over an etale $W \to X$ whose germs at all lifts of the geometric point $\bar x_0$ vanish is zero; hence two sections with the same generic germs are equal. Near any point of $W$, on a trivialising chart, $d$ is locally a constant $n \in M$; the image of that neighbourhood in $X$ is a nonempty open, so it contains $x_0$, and the germ of $d$ at a lift of $\bar x_0$ through it is $n$, so $n = 0$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose IX, Section 2; J. S. Milne, Etale Cohomology, Princeton University Press (1980)

import Mathlib
import Definitions.Def_RPLib_S4_EtShConstFix
import Definitions.Def_RPLib_S4_EtShFV

/-!
# S4-EtSheaves, O10f part b: sections of a locally constant sheaf are determined by their generic germs

Let `x0 : X` lie in every nonempty open subset of `X` (a generic point) and `G` be a locally constant etale sheaf on
`X`. A section `d ∈ G(W)` over an etale `W → X` whose germs at all lifts of the geometric point `geomPtAt x0` vanish is
zero (`eq_zero_of_germ`); hence two sections with the same generic germs are equal (`eq_of_germ`).

Proof: near any `w ∈ W` take a chart `U → X` trivialising `G`, `G|_U ≅ M_U`; on `W ×_X U` the section `d` becomes a
section of the constant sheaf `M`, which is locally (on some `V1 ∋` a point over `w`) a constant `n ∈ M`. The image of
`V1` in `X` is a nonempty open, so it meets `x0`; the germ of `d` at a lift of `geomPtAt x0` through `V1` is `n`, so
`n = 0`. Thus `d` vanishes on a covering of `W`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

namespace GenUniq

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} (x0 : X)

/-- **Local vanishing**: a section of a locally constant sheaf with zero germs at all lifts of the generic geometric
point vanishes on an etale neighbourhood of every point. -/
theorem exists_zero_nbhd (hgen : ∀ O : Set X, IsOpen O → O.Nonempty → x0 ∈ O) {G : EtSh Λ X}
    (hG : IsLocConst Λ G) (W : X.Etale) (d : G.obj.obj (op W))
    (h : ∀ a : (geomPtAt x0).point.fiber.obj W, ((geomPtAt x0).point.toPresheafFiber W a G.obj).hom d = 0)
    (w : W.left) :
    ∃ (V : X.Etale) (g : V ⟶ W) (v : V.left), (G.obj.map g.op).hom d = 0 ∧ g.left v = w := by
  obtain ⟨U, v, hv, M, ⟨e⟩⟩ := hG (W.hom w)
  obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback w v hv.symm
  let V0 : U.left.Etale := (etPull U.hom).obj W
  let g0 : (etComp U.hom).obj V0 ⟶ W :=
    MorphismProperty.Over.homMk (pullback.fst W.hom U.hom) pullback.condition trivial
  let E : (res U.hom Λ).obj G ≅ constSh Λ U.left M := ((pullIsoRes U.hom Λ).app G).symm ≪≫ e
  let d0 : ((res U.hom Λ).obj G).obj.obj (op V0) := (G.obj.map g0.op).hom d
  obtain ⟨V1, g1, v1, ⟨n, hn⟩, hv1⟩ := (mem_smallEtale_iff V0 _).1
    (Presheaf.imageSieve_mem U.left.smallEtaleTopology (toSheafify U.left.smallEtaleTopology (constPre M))
      ((E.hom.hom.app (op V0)).hom d0)) p
  let d1 : ((res U.hom Λ).obj G).obj.obj (op V1) := (((res U.hom Λ).obj G).obj.map g1.op).hom d0
  have hn' : (E.hom.hom.app (op V1)).hom d1 = (constUnit M V1).hom n := by
    rw [app_map]
    exact hn.symm
  -- a lift of the generic geometric point through `V1`
  have hne : (Set.range ((etComp U.hom).obj V1).hom).Nonempty := ⟨_, v1, rfl⟩
  obtain ⟨v', hv'⟩ := hgen _ ((etComp U.hom).obj V1).hom.isOpenMap.isOpen_range hne
  have hu' : U.hom (V1.hom v') = (geomPtAt x0).center := by
    rw [center_geomPtAt, ← hv']
    rfl
  obtain ⟨t, ht, htx⟩ := exists_geomPt_lift (Y := U.left) (X := X) U.hom (geomPtAt x0) (V1.hom v') hu'
  obtain ⟨b1⟩ := t.exists_fiber V1 v' ht.symm
  rw [← htx] at h
  -- the germ of `d1` at `b1` vanishes
  have h1 : (t.point.toPresheafFiber V1 b1 ((res U.hom Λ).obj G).obj).hom d1 = 0 := by
    apply resFib_injective U.hom t Λ G
    refine (resFib_germ U.hom t Λ G V1 b1 d1).trans (Eq.trans ?_ (map_zero _).symm)
    have h3 : ((t.map U.hom).point.toPresheafFiber ((etComp U.hom).obj V1) (liftX U.hom t b1) G.obj).hom
        ((G.obj.map ((etComp U.hom).map g1 ≫ g0).op).hom d) =
        ((t.map U.hom).point.toPresheafFiber W
          ((t.map U.hom).point.fiber.map ((etComp U.hom).map g1 ≫ g0) (liftX U.hom t b1)) G.obj).hom d :=
      congrArg (fun φ => φ.hom d) (GrothendieckTopology.Point.toPresheafFiber_w
        (Φ := (t.map U.hom).point) ((etComp U.hom).map g1 ≫ g0) (liftX U.hom t b1) G.obj)
    exact (congrArg ((t.map U.hom).point.toPresheafFiber ((etComp U.hom).obj V1) (liftX U.hom t b1) G.obj).hom
      (map_map_apply G g0 ((etComp U.hom).map g1) d)).trans (h3.trans (h _))
  -- hence the constant `n` is zero
  have h4 : (constStalkIso Λ t M).inv.hom n = 0 := by
    have h7 : (constStalkIso Λ t M).inv.hom n =
        (t.point.toPresheafFiber V1 b1 (constSh Λ U.left M).obj).hom ((constUnit M V1).hom n) :=
      (congrArg (fun φ => φ.hom n) (constUnit_germ t M V1 b1)).symm
    have h5 : (t.point.toPresheafFiber V1 b1 (constSh Λ U.left M).obj).hom ((E.hom.hom.app (op V1)).hom d1) =
        (t.point.presheafFiber.map E.hom.hom).hom
          ((t.point.toPresheafFiber V1 b1 ((res U.hom Λ).obj G).obj).hom d1) :=
      (congrArg (fun φ => φ.hom d1) (GrothendieckTopology.Point.toPresheafFiber_naturality
        (Φ := t.point) E.hom.hom V1 b1)).symm
    exact h7.trans ((congrArg (t.point.toPresheafFiber V1 b1 (constSh Λ U.left M).obj).hom hn'.symm).trans
      (h5.trans ((congrArg (t.point.presheafFiber.map E.hom.hom).hom h1).trans (map_zero _))))
  have hn0 : n = 0 := (iso_inv_eq_zero (constStalkIso Λ t M) n).1 h4
  have hd1 : d1 = 0 := by
    have h6 : (E.hom.hom.app (op V1)).hom d1 = 0 :=
      hn'.trans ((congrArg (constUnit M V1).hom hn0).trans (map_zero _))
    have key : (E.inv.hom.app (op V1)).hom ((E.hom.hom.app (op V1)).hom d1) = d1 :=
      congrArg (fun φ => (φ.hom.app (op V1)).hom d1) E.hom_inv_id
    exact key.symm.trans ((congrArg (E.inv.hom.app (op V1)).hom h6).trans (map_zero _))
  refine ⟨(etComp U.hom).obj V1, (etComp U.hom).map g1 ≫ g0, v1, ?_, ?_⟩
  · exact (map_map_apply G g0 ((etComp U.hom).map g1) d).symm.trans hd1
  · change pullback.fst W.hom U.hom (g1.left v1) = w
    exact (congrArg (fun z => pullback.fst W.hom U.hom z) hv1).trans hp1

/-- **Generic germs detect zero**: a section of a locally constant sheaf whose germs at all lifts of the generic
geometric point vanish is zero. -/
theorem eq_zero_of_germ (hgen : ∀ O : Set X, IsOpen O → O.Nonempty → x0 ∈ O) {G : EtSh Λ X}
    (hG : IsLocConst Λ G) (W : X.Etale) (d : G.obj.obj (op W))
    (h : ∀ a : (geomPtAt x0).point.fiber.obj W, ((geomPtAt x0).point.toPresheafFiber W a G.obj).hom d = 0) :
    d = 0 := by
  let R : Sieve W :=
    { arrows := fun _ f => (G.obj.map f.op).hom d = 0
      downward_closed := fun {_ _} {f} (hf : (G.obj.map f.op).hom d = 0) g => by
        show (G.obj.map (g ≫ f).op).hom d = 0
        exact (map_map_apply G f g d).symm.trans ((congrArg (G.obj.map g.op).hom hf).trans (map_zero _)) }
  have hR : R ∈ X.smallEtaleTopology W :=
    (mem_smallEtale_iff W R).2 fun w => exists_zero_nbhd x0 hgen hG W d h w
  exact sep_eq G R hR d 0 fun _ f (hf : (G.obj.map f.op).hom d = 0) => hf.trans (map_zero _).symm

/-- **Generic germs determine sections** of a locally constant sheaf. -/
theorem eq_of_germ (hgen : ∀ O : Set X, IsOpen O → O.Nonempty → x0 ∈ O) {G : EtSh Λ X}
    (hG : IsLocConst Λ G) (W : X.Etale) (y₁ y₂ : G.obj.obj (op W))
    (h : ∀ a : (geomPtAt x0).point.fiber.obj W, ((geomPtAt x0).point.toPresheafFiber W a G.obj).hom y₁ =
      ((geomPtAt x0).point.toPresheafFiber W a G.obj).hom y₂) :
    y₁ = y₂ :=
  sub_eq_zero.1 (eq_zero_of_germ x0 hgen hG W (y₁ - y₂) fun a => by rw [map_sub, h a, sub_self])

end GenUniq

end RamanujanPetersson.EtSheaves


