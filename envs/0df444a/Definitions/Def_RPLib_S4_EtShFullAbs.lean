-- Prove2me | Definitions.Def_RPLib_S4_EtShFullAbs
-- name    : RPLib_S4_EtShFullAbs
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:43:25.381895+00:00
-- url     : https://prove2.me/theorems/d3963e30-68b4-45e7-89e7-7ce4e75fa1fc
-- title:
--   Fullness of the generic fibre functor (abstract form)
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. Let $x_0 \in X$ lie in every nonempty open subset of $X$, and $F, G$ etale sheaves with $G$ locally constant such that every point of every etale $U \to X$ has an etale neighbourhood $T \to X$ mapping to $U$ on which $G$ is constant and which has at most one point over $x_0$. Then every Galois-equivariant linear map $f : F_{\bar x_0} \to G_{\bar x_0}$ is the stalk of a morphism of sheaves $\varphi : F \to G$. (Sections of $G$ with prescribed generic germs are unique, exist on charts, and hence glue.)
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose IX; J. S. Milne, Etale Cohomology, Princeton University Press (1980)

import Mathlib
import Definitions.Def_RPLib_S4_EtShLocalEx

/-!
# S4-EtSheaves, O10f part c2: fullness of the generic fibre functor (abstract form)

Let `x0 : X` lie in every nonempty open subset of `X`, `F, G` etale sheaves on `X` with `G` locally constant, and
suppose `G` has *charts*: every point of every etale `U → X` has an etale neighbourhood `T → X` mapping to `U` on which
`G` is constant and which has at most one point over `x0` (`HChart`). Then every Galois-equivariant linear map
`f : F_x̄₀ → G_x̄₀` of stalks at `x̄₀ = geomPtAt x0` is the stalk of a sheaf map `φ : F ⟶ G` (`full`).

Proof: a section `y ∈ G(U)` is *good* for `z ∈ F(U)` when its germ at every lift of `x̄₀` is `f` of the germ of `z`.
Good sections are unique (generic germs determine sections, `GenUniq.eq_of_germ`), exist on charts
(`LocalEx.exists_good`), hence glue to a good section on every `U`; `φ_U z` is that section.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

namespace FullAbs

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} (x0 : X)

/-- **Charts** for `G` at `x0`: every point of every etale `U → X` has an etale neighbourhood `T → X` over `U` on
which `G` is constant and which has at most one point over `x0`. -/
def HChart (G : EtSh Λ X) : Prop :=
  ∀ (U : X.Etale) (u : U.left), ∃ (T : Scheme.{u}) (h : T ⟶ X) (_ : Etale h)
    (g : (etComp h).obj (etId T) ⟶ U) (w : ((etComp h).obj (etId T)).left), g.left w = u ∧
    (∃ M : ModuleCat.{u} Λ, Nonempty ((pull h Λ).obj G ≅ constSh Λ T M)) ∧
    ∀ w₁ w₂ : T, h w₁ = x0 → h w₂ = x0 → w₁ = w₂

variable {F G : EtSh Λ X} (f : stalk Λ F x0 →ₗ[Λ] stalk Λ G x0)

/-- The hypotheses of the fullness theorem. -/
structure Hyp : Prop where
  gen : ∀ O : Set X, IsOpen O → O.Nonempty → x0 ∈ O
  locConst : IsLocConst Λ G
  chart : HChart x0 G
  equiv : ∀ (σ : Gal x0) (v : stalk Λ F x0), f (galRep Λ F x0 σ v) = galRep Λ G x0 σ (f v)

/-- `y ∈ G(U)` is good for `z ∈ F(U)`: its generic germs are the images under `f` of those of `z`. -/
def Good (U : X.Etale) (z : F.obj.obj (op U)) (y : G.obj.obj (op U)) : Prop :=
  ∀ a : (geomPtAt x0).point.fiber.obj U,
    ((geomPtAt x0).point.toPresheafFiber U a G.obj).hom y = f (((geomPtAt x0).point.toPresheafFiber U a F.obj).hom z)

/-- Germs of restrictions. -/
theorem germ_map (P : EtSh Λ X) {U V : X.Etale} (g : V ⟶ U) (a : (geomPtAt x0).point.fiber.obj V)
    (s : P.obj.obj (op U)) :
    ((geomPtAt x0).point.toPresheafFiber V a P.obj).hom ((P.obj.map g.op).hom s) =
      ((geomPtAt x0).point.toPresheafFiber U ((geomPtAt x0).point.fiber.map g a) P.obj).hom s :=
  congrArg (fun φ => φ.hom s) (GrothendieckTopology.Point.toPresheafFiber_w (Φ := (geomPtAt x0).point) g a P.obj)

theorem good_map {U V : X.Etale} (g : V ⟶ U) {z : F.obj.obj (op U)} {y : G.obj.obj (op U)}
    (hy : Good x0 f U z y) : Good x0 f V ((F.obj.map g.op).hom z) ((G.obj.map g.op).hom y) := fun a =>
  (germ_map x0 G g a y).trans ((hy _).trans (congrArg f (germ_map x0 F g a z).symm))

theorem good_unique (H : Hyp x0 f) (U : X.Etale) {z : F.obj.obj (op U)} {y₁ y₂ : G.obj.obj (op U)}
    (h₁ : Good x0 f U z y₁) (h₂ : Good x0 f U z y₂) : y₁ = y₂ :=
  GenUniq.eq_of_germ x0 H.gen H.locConst U y₁ y₂ fun a => (h₁ a).trans (h₂ a).symm

/-- **Good sections exist** on every etale `U`: glue the local ones from the charts. -/
theorem exists_good (H : Hyp x0 f) (U : X.Etale) (z : F.obj.obj (op U)) : ∃ y, Good x0 f U z y := by
  let R : Sieve U :=
    { arrows := fun _ g => ∃ y, Good x0 f _ ((F.obj.map g.op).hom z) y
      downward_closed := fun {V W} {g} (hg : ∃ y, Good x0 f V ((F.obj.map g.op).hom z) y) k => by
        obtain ⟨y, hy⟩ := hg
        refine ⟨(G.obj.map k.op).hom y, fun a => ((good_map x0 f k hy) a).trans ?_⟩
        exact congrArg (fun s => f (((geomPtAt x0).point.toPresheafFiber W a F.obj).hom s))
          (map_map_apply F g k z) }
  have hR : R ∈ X.smallEtaleTopology U := by
    refine (mem_smallEtale_iff U R).2 fun u => ?_
    obtain ⟨T, h, _, g, w, hw, ⟨M, ⟨e⟩⟩, huniq⟩ := H.chart U u
    exact ⟨_, g, w, LocalEx.exists_good x0 f H.equiv h M e huniq _, hw⟩
  obtain ⟨s, hs, -⟩ := existsUnique_glueS G R hR (fun _ _ hg => Classical.choose hg) (by
    intro V₁ V₂ W g₁ g₂ h₁ h₂ k₁ k₂ hk
    refine GenUniq.eq_of_germ x0 H.gen H.locConst W _ _ fun a => ?_
    refine ((germ_map x0 G k₁ a _).trans (Classical.choose_spec h₁ _)).trans
      (Eq.trans ?_ ((germ_map x0 G k₂ a _).trans (Classical.choose_spec h₂ _)).symm)
    refine congrArg f ((germ_map x0 F g₁ _ z).trans (Eq.trans ?_ (germ_map x0 F g₂ _ z).symm))
    have e : (geomPtAt x0).point.fiber.map g₁ ((geomPtAt x0).point.fiber.map k₁ a) =
        (geomPtAt x0).point.fiber.map g₂ ((geomPtAt x0).point.fiber.map k₂ a) :=
      (Functor.map_comp_apply (geomPtAt x0).point.fiber k₁ g₁ a).symm.trans
        ((congrArg (fun m => (geomPtAt x0).point.fiber.map m a) hk).trans (Functor.map_comp_apply (geomPtAt x0).point.fiber k₂ g₂ a))
    exact congrArg (fun b => ((geomPtAt x0).point.toPresheafFiber U b F.obj).hom z) e)
  refine ⟨s, fun a => ?_⟩
  obtain ⟨V, g, hg, b, rfl⟩ := (geomPtAt x0).point.jointly_surjective R hR a
  exact (germ_map x0 G g b s).symm.trans
    ((congrArg ((geomPtAt x0).point.toPresheafFiber V b G.obj).hom (hs g hg)).trans
      ((Classical.choose_spec hg b).trans (congrArg f (germ_map x0 F g b z))))

/-- The glued map on sections over `U`. -/
def phiFun (H : Hyp x0 f) (U : X.Etale) (z : F.obj.obj (op U)) : G.obj.obj (op U) :=
  Classical.choose (exists_good x0 f H U z)

theorem phiFun_good (H : Hyp x0 f) (U : X.Etale) (z : F.obj.obj (op U)) : Good x0 f U z (phiFun x0 f H U z) :=
  Classical.choose_spec (exists_good x0 f H U z)

theorem phiFun_map (H : Hyp x0 f) {U V : X.Etale} (g : V ⟶ U) (z : F.obj.obj (op U)) :
    phiFun x0 f H V ((F.obj.map g.op).hom z) = (G.obj.map g.op).hom (phiFun x0 f H U z) :=
  good_unique x0 f H V (phiFun_good x0 f H V _) (good_map x0 f g (phiFun_good x0 f H U z))

/-- `phiFun` is linear. -/
def phiLin (H : Hyp x0 f) (U : X.Etale) : F.obj.obj (op U) →ₗ[Λ] G.obj.obj (op U) where
  toFun := phiFun x0 f H U
  map_add' z₁ z₂ := good_unique x0 f H U (phiFun_good x0 f H U (z₁ + z₂)) fun a =>
    (map_add _ _ _).trans ((congrArg₂ (· + ·) (phiFun_good x0 f H U z₁ a) (phiFun_good x0 f H U z₂ a)).trans
      ((map_add f _ _).symm.trans (congrArg f (map_add _ _ _).symm)))
  map_smul' c z := good_unique x0 f H U (phiFun_good x0 f H U (c • z)) fun a =>
    (map_smul _ c _).trans ((congrArg (c • ·) (phiFun_good x0 f H U z a)).trans
      ((map_smul f c _).symm.trans (congrArg f (map_smul _ c z).symm)))

/-- The sheaf map glued from good sections. -/
def phi (H : Hyp x0 f) : F ⟶ G :=
  ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom (phiLin x0 f H U.unop)
      naturality := fun _ _ g => ModuleCat.hom_ext (LinearMap.ext fun z => phiFun_map x0 f H g.unop z) }

/-- **The stalk of `φ` at the generic geometric point is `f`.** -/
theorem stalk_phi (H : Hyp x0 f) : (((geomPtAt x0).stalkF Λ).map (phi x0 f H)).hom = f := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨U, a, z, rfl⟩ := (geomPtAt x0).point.toPresheafFiber_jointly_surjective (P := F.obj) v
  have h1 : (((geomPtAt x0).stalkF Λ).map (phi x0 f H)).hom
      (((geomPtAt x0).point.toPresheafFiber U a F.obj).hom z) =
      ((geomPtAt x0).point.toPresheafFiber U a G.obj).hom (phiFun x0 f H U z) :=
    congrArg (fun φ => φ.hom z) (GrothendieckTopology.Point.toPresheafFiber_naturality
      (Φ := (geomPtAt x0).point) (phi x0 f H).hom U a)
  exact h1.trans (phiFun_good x0 f H U z a)

/-- **Fullness of the generic fibre functor** (abstract form): under `Hyp`, every Galois-equivariant map of generic
stalks `F_x̄₀ → G_x̄₀` is the stalk of a sheaf map `F ⟶ G`. -/
theorem full (H : Hyp x0 f) : ∃ φ : F ⟶ G, (((geomPtAt x0).stalkF Λ).map φ).hom = f :=
  ⟨phi x0 f H, stalk_phi x0 f H⟩

end FullAbs

end RamanujanPetersson.EtSheaves


