-- Prove2me | Definitions.Def_RPLib_S4_EtShConst
-- name    : RPLib_S4_EtShConst
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:16:57.116596+00:00
-- url     : https://prove2.me/theorems/c3271726-b97d-4ae4-9914-d6e401c85e72
-- title:
--   Constant, locally constant and lisse etale sheaves
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. For a $\Lambda$-module $M$, the constant sheaf $M_X$ is the sheafification of the constant presheaf; its stalk at every geometric point is $M$, and $f^* M_Y \cong M_X$ for every $f : X \to Y$ (both are left adjoint to global sections). A sheaf $F$ is locally constant if every point of $X$ is in the image of an etale $U \to X$ with $F|_U$ constant, and lisse (locally constant constructible) if moreover the values are finite $\Lambda$-modules. A lisse sheaf has finite stalks, and conversely a locally constant sheaf with finite stalks is lisse.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose IX, Section 2; J. S. Milne, Etale Cohomology, Princeton University Press (1980)

import Mathlib
import Definitions.Def_RPLib_S4_EtShPull

/-!
# S4-EtSheaves, part 3: constant, locally constant and lisse etale sheaves

`constSh Λ X M` is the constant sheaf with value `M` (Mathlib's `constantSheaf`: sheafification of the
constant presheaf), `unitSh Λ X = Λ_X`. Its stalk at every geometric point is `M` (`constStalkIso`), and
`f^*` of a constant sheaf is constant (`pullConstIso`: both are left adjoint to global sections).
`F` is locally constant (`IsLocConst`) if every point of `X` is in the image of an etale `U → X` with
`F|_U` constant; lisse (`IsLisse`, = locally constant constructible) if moreover the values are finite
`Λ`-modules. A lisse sheaf has finite stalks, and conversely a locally constant sheaf with finite stalks
is lisse (`isLisse_iff`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ]

/-- The constant etale sheaf with value `M`. -/
abbrev constSh (X : Scheme.{u}) (M : ModuleCat.{u} Λ) : EtSh Λ X :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).obj M

/-- The unit sheaf `Λ_X`. -/
abbrev unitSh (X : Scheme.{u}) : EtSh Λ X := constSh Λ X (ModuleCat.of Λ Λ)

attribute [local instance] IsFiltered.isConnected in
/-- **Stalks of a constant sheaf**: `(M_X)_s ≅ M` at every geometric point `s`. -/
def constStalkIso {X : Scheme.{u}} (s : GeomPt X) (M : ModuleCat.{u} Λ) :
    (s.stalkF Λ).obj (constSh Λ X M) ≅ M :=
  (s.point.presheafToSheafCompSheafFiberIso (ModuleCat.{u} Λ)).app ((Functor.const _).obj M) ≪≫
    IsColimit.coconePointUniqueUpToIso
      (s.point.isColimitPresheafFiberCocone ((Functor.const X.Etaleᵒᵖ).obj M))
      (isColimitConstCocone _ M)

section PullConst

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **`f^*` of a constant sheaf is constant**, naturally in the value: both `constantSheaf ⋙ f^*`
and `constantSheaf` are left adjoint to global sections over `X = X ×_Y Y`. -/
def pullConstIso :
    constantSheaf Y.smallEtaleTopology (ModuleCat.{u} Λ) ⋙ pull f Λ ≅
      constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ) :=
  ((constantSheafAdj _ _ (terminalIsTerminal (C := Y.Etale))).comp (pullAdj f Λ)).leftAdjointUniq
    ((constantSheafAdj _ _ ((terminalIsTerminal (C := Y.Etale)).isTerminalObj (etPull f))).ofNatIsoRight
      (Iso.refl _))

/-- `f^* M_Y ≅ M_X`. -/
def pullConst (M : ModuleCat.{u} Λ) : (pull f Λ).obj (constSh Λ Y M) ≅ constSh Λ X M :=
  (pullConstIso Λ f).app M

end PullConst

variable {X : Scheme.{u}}

/-- `F` is locally constant: every point lies in the image of an etale `U → X` with `F|_U` constant. -/
def IsLocConst (F : EtSh Λ X) : Prop :=
  ∀ x : X, ∃ (U : X.Etale) (v : U.left), U.hom v = x ∧
    ∃ M : ModuleCat.{u} Λ, Nonempty ((pull U.hom Λ).obj F ≅ constSh Λ U.left M)

/-- `F` is lisse (locally constant constructible): locally constant with finite values. -/
def IsLisse (F : EtSh Λ X) : Prop :=
  ∀ x : X, ∃ (U : X.Etale) (v : U.left), U.hom v = x ∧
    ∃ M : ModuleCat.{u} Λ, Module.Finite Λ M ∧ Nonempty ((pull U.hom Λ).obj F ≅ constSh Λ U.left M)

variable {Λ}

theorem IsLisse.isLocConst {F : EtSh Λ X} (hF : IsLisse Λ F) : IsLocConst Λ F := fun x => by
  obtain ⟨U, v, hv, M, -, e⟩ := hF x
  exact ⟨U, v, hv, M, e⟩

theorem IsLocConst.of_iso {F G : EtSh Λ X} (e : F ≅ G) (hF : IsLocConst Λ F) : IsLocConst Λ G :=
  fun x => by
    obtain ⟨U, v, hv, M, ⟨e'⟩⟩ := hF x
    exact ⟨U, v, hv, M, ⟨(pull U.hom Λ).mapIso e.symm ≪≫ e'⟩⟩

theorem IsLisse.of_iso {F G : EtSh Λ X} (e : F ≅ G) (hF : IsLisse Λ F) : IsLisse Λ G :=
  fun x => by
    obtain ⟨U, v, hv, M, hM, ⟨e'⟩⟩ := hF x
    exact ⟨U, v, hv, M, hM, ⟨(pull U.hom Λ).mapIso e.symm ≪≫ e'⟩⟩

/-- The identity of `X` as an etale `X`-scheme. -/
def etId (X : Scheme.{u}) : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance)

/-- A constant sheaf with finite value is lisse. -/
theorem isLisse_constSh (M : ModuleCat.{u} Λ) [Module.Finite Λ M] : IsLisse Λ (constSh Λ X M) :=
  fun x => ⟨etId X, x, rfl, M, inferInstance, ⟨pullConst Λ (𝟙 X) M⟩⟩

theorem isLisse_unitSh : IsLisse Λ (unitSh Λ X) := isLisse_constSh _

/-- If `F|_U ≅ M_U` and `U → X` hits the centre of `s`, then `F_s ≅ M`. -/
theorem nonempty_stalk_iso {F : EtSh Λ X} (U : X.Etale) (v : U.left) (M : ModuleCat.{u} Λ)
    (e : (pull U.hom Λ).obj F ≅ constSh Λ U.left M) (s : GeomPt X) (hv : U.hom v = s.center) :
    Nonempty ((s.stalkF Λ).obj F ≅ M) := by
  have : Etale U.hom := U.prop
  obtain ⟨Ω, pt⟩ := s
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed U.hom pt v hv
  let t : GeomPt U.left := ⟨Ω, l⟩
  have ht : t.map U.hom = ⟨Ω, pt⟩ := by rw [← hl]; rfl
  rw [← ht]
  exact ⟨((pullStalkIso U.hom Λ t).app F).symm ≪≫ (t.stalkF Λ).mapIso e ≪≫ constStalkIso Λ t M⟩

/-- **Stalks of a lisse sheaf are finite**, at every geometric point. -/
theorem IsLisse.finite_stalkF {F : EtSh Λ X} (hF : IsLisse Λ F) (s : GeomPt X) :
    Module.Finite Λ ((s.stalkF Λ).obj F) := by
  obtain ⟨U, v, hv, M, hM, ⟨e⟩⟩ := hF s.center
  obtain ⟨e'⟩ := nonempty_stalk_iso U v M e s hv
  exact Module.Finite.equiv e'.toLinearEquiv.symm

/-- **Lisse = locally constant with finite stalks.** -/
theorem isLisse_iff (F : EtSh Λ X) :
    IsLisse Λ F ↔ IsLocConst Λ F ∧ ∀ x : X, Module.Finite Λ (stalk Λ F x) := by
  refine ⟨fun h => ⟨h.isLocConst, fun x => h.finite_stalkF _⟩, fun ⟨h, hfin⟩ x => ?_⟩
  obtain ⟨U, v, hv, M, ⟨e⟩⟩ := h x
  obtain ⟨e'⟩ := nonempty_stalk_iso U v M e (geomPtAt x) (hv.trans (center_geomPtAt x).symm)
  have := hfin x
  exact ⟨U, v, hv, M, Module.Finite.equiv e'.toLinearEquiv, ⟨e⟩⟩

end RamanujanPetersson.EtSheaves


