-- Prove2me | Definitions.Def_RPLib_S4_EtShFaith
-- name    : RPLib_S4_EtShFaith
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:32:01.666271+00:00
-- url     : https://prove2.me/theorems/80a58271-d7c7-4ba1-b13e-37b0e958e3ab
-- title:
--   The stalk functor is faithful on lisse sheaves over a connected base
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. Germs of constant sections span the stalks of a constant sheaf, and a section of a constant sheaf has locally constant germs, so for maps $\varphi, \psi$ between constant sheaves with finite source the set of geometric points where their stalks agree is open and closed. Transporting along a common etale trivialisation gives the same for $\varphi, \psi : F \to G$ with $F$ lisse and $G$ locally constant. Main result: if $X$ is connected, then for ANY geometric point $\bar s$ of $X$, $\varphi_{\bar s} = \psi_{\bar s}$ implies $\varphi = \psi$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose IX, Section 2; J. S. Milne, Etale Cohomology, Princeton University Press (1980)

import Mathlib
import Definitions.Def_RPLib_S4_EtShHomConst
import Definitions.Def_RPLib_S4_EtShPullComp

/-!
# S4-EtSheaves, part 33 (O10a): the stalk functor is faithful on lisse sheaves over a connected base

Germs of constant sections span the stalks of a constant sheaf (`constUnit_germ`); a section of a constant sheaf
has locally constant germs (`germ_constSh`, from local surjectivity of sheafification), so for maps `φ ψ` of constant
sheaves with finite source the locus of geometric points where their stalks agree is locally constant
(`constMap_stalk_locConst`). Transporting along a common etale trivialisation (`exists_common_triv`) gives the same
for `φ ψ : F ⟶ G` with `F` lisse and `G` locally constant (`stalkEq_locConst`). Headline: on a connected `X`, the stalk
functor at ANY geometric point is faithful on such maps (`stalk_faithful`, `stalkF_map_injective`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ]

attribute [local instance] IsFiltered.isConnected in
/-- `M → M_X(V) → (M_X)_s` (germ at any fibre element) is `constStalkIso⁻¹`. -/
theorem constUnit_germ {X : Scheme.{u}} (s : GeomPt X) (M : ModuleCat.{u} Λ) (V : X.Etale)
    (a : s.point.fiber.obj V) :
    constUnit M V ≫ s.point.toPresheafFiber V a (constSh Λ X M).obj = (constStalkIso Λ s M).inv := by
  have h1 := IsColimit.comp_coconePointUniqueUpToIso_inv
    (s.point.isColimitPresheafFiberCocone ((Functor.const X.Etaleᵒᵖ).obj M))
    (isColimitConstCocone _ M) (op (Functor.elementsMk s.point.fiber V a))
  have h2 : (IsColimit.coconePointUniqueUpToIso
      (s.point.isColimitPresheafFiberCocone ((Functor.const X.Etaleᵒᵖ).obj M))
      (isColimitConstCocone _ M)).inv = s.point.toPresheafFiber V a (constPre M) :=
    (Category.id_comp _).symm.trans h1
  rw [constStalkIso, Iso.trans_inv, h2]
  change _ = s.point.toPresheafFiber V a (constPre M) ≫
    s.point.presheafFiber.map (toSheafify X.smallEtaleTopology (constPre M))
  rw [GrothendieckTopology.Point.toPresheafFiber_naturality]
  rfl

namespace GeomPt

variable {Y : Scheme.{u}} (t : GeomPt Y)

/-- The fibre element of `t` over the identity `Y → Y`. -/
def top : t.point.fiber.obj (etId Y) :=
  (Over.homMk t.pt (Category.comp_id t.pt) :
    CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget Y).obj (etId Y))

/-- The fibre over the identity is a singleton. -/
theorem eq_top (b : t.point.fiber.obj (etId Y)) : b = t.top := by
  let b' : CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget Y).obj (etId Y) := b
  have hw : b'.left ≫ 𝟙 Y = t.pt := Over.w b'
  show b' = _
  exact Over.OverMorphism.ext ((Category.comp_id _).symm.trans hw)

/-- A geometric point lifts through an etale `W` at any point over its centre. -/
theorem exists_fiber (W : Y.Etale) (w : W.left) (hw : W.hom w = t.center) :
    Nonempty (t.point.fiber.obj W) := by
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed W.hom t.pt w hw
  exact ⟨(Over.homMk l hl : CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget Y).obj W)⟩

/-- The centre of `t` is in the image of any `W` with a fibre element. -/
theorem center_mem_range {W : Y.Etale} (b : t.point.fiber.obj W) : t.center ∈ Set.range W.hom := by
  let b' : CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget Y).obj W := b
  let l : Spec (CommRingCat.of t.Ω) ⟶ W.left := b'.left
  have hw : l ≫ W.hom = t.pt := Over.w b'
  exact ⟨l default, by rw [← Scheme.Hom.comp_apply, hw]; rfl⟩

end GeomPt

theorem iso_inv_eq_zero {A B : ModuleCat.{u} Λ} (e : A ≅ B) (n : B) : e.inv.hom n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have := congrArg e.hom.hom h
    rwa [← LinearMap.comp_apply, ← ModuleCat.hom_comp, e.inv_hom_id, ModuleCat.hom_id, LinearMap.id_apply,
      map_zero] at this
  · rintro rfl
    exact map_zero _

/-- **Germs of a section of a constant sheaf are locally constant**: near the centre of `t`, the germ of `c` at every
geometric point is the constant germ of one `n ∈ N`. -/
theorem germ_constSh {Y : Scheme.{u}} (N : ModuleCat.{u} Λ) (c : (constSh Λ Y N).obj.obj (op (etId Y)))
    (t : GeomPt Y) :
    ∃ O : Set Y, IsOpen O ∧ t.center ∈ O ∧ ∃ n : N, ∀ t' : GeomPt Y, t'.center ∈ O →
      (t'.point.toPresheafFiber (etId Y) t'.top (constSh Λ Y N).obj).hom c =
        (constStalkIso Λ t' N).inv.hom n := by
  obtain ⟨W, g, ⟨n, hn⟩, b, -⟩ := t.point.jointly_surjective _
    (Presheaf.imageSieve_mem Y.smallEtaleTopology (toSheafify Y.smallEtaleTopology (constPre N)) c) t.top
  have hn' : ((constSh Λ Y N).obj.map g.op).hom c = (constUnit N W).hom n := hn.symm
  refine ⟨Set.range W.hom, W.hom.isOpenMap.isOpen_range, t.center_mem_range b, n, ?_⟩
  rintro t' ⟨w, hw⟩
  obtain ⟨b'⟩ := t'.exists_fiber W w hw
  rw [← t'.eq_top (t'.point.fiber.map g b'), ← GrothendieckTopology.Point.toPresheafFiber_w,
    ModuleCat.hom_comp, LinearMap.comp_apply, hn', ← constUnit_germ t' N W b']
  rfl

/-- The stalk at `t` of `φ : M_Y ⟶ N_Y` on the constant germ of `m` is the germ of `φ(m)`. -/
theorem constMap_germ {Y : Scheme.{u}} {M N : ModuleCat.{u} Λ} (φ : constSh Λ Y M ⟶ constSh Λ Y N)
    (t : GeomPt Y) (m : M) :
    ((t.stalkF Λ).map φ).hom ((constStalkIso Λ t M).inv.hom m) =
      (t.point.toPresheafFiber (etId Y) t.top (constSh Λ Y N).obj).hom
        ((φ.hom.app (op (etId Y))).hom ((constUnit M (etId Y)).hom m)) := by
  rw [← constUnit_germ t M (etId Y) t.top]
  change (constUnit M (etId Y) ≫ t.point.toPresheafFiber (etId Y) t.top (constSh Λ Y M).obj ≫
    t.point.presheafFiber.map φ.hom).hom m = _
  rw [GrothendieckTopology.Point.toPresheafFiber_naturality]
  rfl

/-- **Maps of constant sheaves with finite source have locally constant stalks**: the predicate "the stalks of `φ`
and `ψ` agree at `t'`" is constant for `t'` centred near the centre of `t`. -/
theorem constMap_stalk_locConst {Y : Scheme.{u}} {M N : ModuleCat.{u} Λ} [Module.Finite Λ M]
    (φ ψ : constSh Λ Y M ⟶ constSh Λ Y N) (t : GeomPt Y) :
    ∃ O : Set Y, IsOpen O ∧ t.center ∈ O ∧ ∀ t' : GeomPt Y, t'.center ∈ O →
      ((t'.stalkF Λ).map φ = (t'.stalkF Λ).map ψ ↔ (t.stalkF Λ).map φ = (t.stalkF Λ).map ψ) := by
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := Λ) (M := M)
  obtain ⟨c, hc⟩ : ∃ c : M → (constSh Λ Y N).obj.obj (op (etId Y)), ∀ m, c m =
      (φ.hom.app (op (etId Y))).hom ((constUnit M (etId Y)).hom m) -
        (ψ.hom.app (op (etId Y))).hom ((constUnit M (etId Y)).hom m) := ⟨_, fun _ => rfl⟩
  choose O hO hcO n hn using fun m => germ_constSh N (c m) t
  have char : ∀ t' : GeomPt Y, (t'.stalkF Λ).map φ = (t'.stalkF Λ).map ψ ↔
      ∀ m ∈ S, (t'.point.toPresheafFiber (etId Y) t'.top (constSh Λ Y N).obj).hom (c m) = 0 := by
    intro t'
    constructor
    · intro e m _
      have h1 := constMap_germ φ t' m
      have h2 := constMap_germ ψ t' m
      rw [e] at h1
      rw [hc, map_sub, ← h1, ← h2, sub_self]
    · intro h
      rw [← cancel_epi (constStalkIso Λ t' M).inv]
      apply ModuleCat.hom_ext
      refine LinearMap.ext_on hS ?_
      intro m hm
      have := h m (Finset.mem_coe.1 hm)
      rw [hc, map_sub, sub_eq_zero] at this
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
        constMap_germ, constMap_germ, this]
  refine ⟨⋂ m ∈ S, O m, isOpen_biInter_finset fun m _ => hO m, Set.mem_iInter₂.2 fun m _ => hcO m,
    fun t' ht' => ?_⟩
  rw [char t', char t]
  refine forall₂_congr fun m hm => ?_
  rw [hn m t' (Set.mem_iInter₂.1 ht' m hm), hn m t (hcO m)]
  exact (iso_inv_eq_zero (constStalkIso Λ t' N) (n m)).trans (iso_inv_eq_zero (constStalkIso Λ t N) (n m)).symm

variable {X : Scheme.{u}}

/-- Lift a geometric point through an etale map at a chosen point over its centre. -/
theorem exists_geomPt_lift {Y : Scheme.{u}} (h : Y ⟶ X) [Etale h] (s : GeomPt X) (y : Y)
    (hy : h y = s.center) : ∃ t : GeomPt Y, t.center = y ∧ t.map h = s := by
  obtain ⟨Ω, pt⟩ := s
  obtain ⟨l, hl, hl2⟩ := Scheme.exists_fac_of_etale_of_isSepClosed h pt y hy
  exact ⟨⟨Ω, l⟩, hl2, by rw [← hl]; rfl⟩

/-- Stalks of `φ, ψ` at `t ≫ h` agree iff the stalks of `h^*φ, h^*ψ` at `t` agree. -/
theorem stalk_eq_iff_pull {Y : Scheme.{u}} (h : Y ⟶ X) (t : GeomPt Y) {F G : EtSh Λ X} (φ ψ : F ⟶ G) :
    ((t.map h).stalkF Λ).map φ = ((t.map h).stalkF Λ).map ψ ↔
      (t.stalkF Λ).map ((pull h Λ).map φ) = (t.stalkF Λ).map ((pull h Λ).map ψ) := by
  rw [← NatIso.naturality_1 (pullStalkIso h Λ t) φ, ← NatIso.naturality_1 (pullStalkIso h Λ t) ψ,
    Functor.comp_map, Functor.comp_map]
  refine ⟨fun e => (Iso.cancel_iso_hom_right _ _ ((pullStalkIso h Λ t).app G)).1 ?_, fun e => by rw [e]⟩
  simpa using e

/-- A lisse `F` and a locally constant `G` are constant on one etale neighbourhood of any point. -/
theorem exists_common_triv {F G : EtSh Λ X} (hF : IsLisse Λ F) (hG : IsLocConst Λ G) (x : X) :
    ∃ (Y : Scheme.{u}) (h : Y ⟶ X) (_ : Etale h) (y : Y), h y = x ∧
      ∃ (M N : ModuleCat.{u} Λ), Module.Finite Λ M ∧
        Nonempty ((pull h Λ).obj F ≅ constSh Λ Y M) ∧ Nonempty ((pull h Λ).obj G ≅ constSh Λ Y N) := by
  obtain ⟨U, v, hv, M, hM, ⟨eF⟩⟩ := hF x
  obtain ⟨W, w, hw, N, ⟨eG⟩⟩ := hG.pull U.hom v
  refine ⟨W.left, W.hom ≫ U.hom, inferInstance, w, by rw [Scheme.Hom.comp_apply, hw, hv], M, N, hM,
    ⟨(pullCompIso Λ W.hom U.hom).app F ≪≫ (pull W.hom Λ).mapIso eF ≪≫ pullConst Λ W.hom M⟩,
    ⟨(pullCompIso Λ W.hom U.hom).app G ≪≫ eG⟩⟩

/-- **Agreement of stalk maps is locally constant** for `φ ψ : F ⟶ G`, `F` lisse, `G` locally constant. -/
theorem stalkEq_locConst {F G : EtSh Λ X} (hF : IsLisse Λ F) (hG : IsLocConst Λ G) (φ ψ : F ⟶ G)
    (s : GeomPt X) :
    ∃ O : Set X, IsOpen O ∧ s.center ∈ O ∧ ∀ s' : GeomPt X, s'.center ∈ O →
      ((s'.stalkF Λ).map φ = (s'.stalkF Λ).map ψ ↔ (s.stalkF Λ).map φ = (s.stalkF Λ).map ψ) := by
  obtain ⟨Y, h, hh, y, hy, M, N, hM, ⟨eF⟩, ⟨eG⟩⟩ := exists_common_triv hF hG s.center
  obtain ⟨t, ht, rfl⟩ := exists_geomPt_lift h s y hy
  have key : ∀ t' : GeomPt Y, ((t'.map h).stalkF Λ).map φ = ((t'.map h).stalkF Λ).map ψ ↔
      (t'.stalkF Λ).map (eF.inv ≫ (pull h Λ).map φ ≫ eG.hom) =
        (t'.stalkF Λ).map (eF.inv ≫ (pull h Λ).map ψ ≫ eG.hom) := fun t' => by
    rw [stalk_eq_iff_pull]
    simp only [Functor.map_comp, cancel_epi]
    exact (Iso.cancel_iso_hom_right _ _ ((t'.stalkF Λ).mapIso eG)).symm
  obtain ⟨O, hO, hyO, hc⟩ := constMap_stalk_locConst (eF.inv ≫ (pull h Λ).map φ ≫ eG.hom)
    (eF.inv ≫ (pull h Λ).map ψ ≫ eG.hom) t
  have hcen : ∀ t' : GeomPt Y, (t'.map h).center = h t'.center := fun t' =>
    Scheme.Hom.comp_apply t'.pt h default
  refine ⟨h '' O, h.isOpenMap O hO, ⟨t.center, hyO, (hcen t).symm⟩, ?_⟩
  rintro s' ⟨y', hy'O, hy'⟩
  obtain ⟨t', ht', rfl⟩ := exists_geomPt_lift h s' y' hy'
  rw [key, key]
  exact hc t' (ht' ▸ hy'O)

/-- **Faithfulness of the fibre functor on lisse sheaves (O10a)**: on a connected `X`, maps `φ ψ : F ⟶ G` (`F` lisse,
`G` locally constant) with the same stalk map at one geometric point `s` are equal. -/
theorem stalk_faithful [PreconnectedSpace X] {F G : EtSh Λ X} (hF : IsLisse Λ F) (hG : IsLocConst Λ G)
    {φ ψ : F ⟶ G} (s : GeomPt X) (h : (s.stalkF Λ).map φ = (s.stalkF Λ).map ψ) : φ = ψ := by
  have hf : IsLocallyConstant
      (fun x : X => ((geomPtAt x).stalkF Λ).map φ = ((geomPtAt x).stalkF Λ).map ψ) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    obtain ⟨O, hO, hxO, hc⟩ := stalkEq_locConst hF hG φ ψ (geomPtAt x)
    refine ⟨O, hO, (center_geomPtAt x) ▸ hxO, fun x' hx' => propext (hc (geomPtAt x') ?_)⟩
    rw [center_geomPtAt]
    exact hx'
  have h0 : ((geomPtAt s.center).stalkF Λ).map φ = ((geomPtAt s.center).stalkF Λ).map ψ := by
    obtain ⟨O, -, hsO, hc⟩ := stalkEq_locConst hF hG φ ψ s
    exact (hc (geomPtAt s.center) (by rw [center_geomPtAt]; exact hsO)).2 h
  exact hom_ext_stalk Λ fun x => (hf.apply_eq_of_preconnectedSpace x s.center).mpr h0

/-- The stalk functor at any geometric point is injective on maps from a lisse to a locally constant sheaf over a
connected scheme. -/
theorem stalkF_map_injective [PreconnectedSpace X] {F G : EtSh Λ X} (hF : IsLisse Λ F) (hG : IsLocConst Λ G)
    (s : GeomPt X) : Function.Injective (fun φ : F ⟶ G => (s.stalkF Λ).map φ) :=
  fun _ _ h => stalk_faithful hF hG s h

end RamanujanPetersson.EtSheaves


