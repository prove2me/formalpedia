-- Prove2me | Definitions.Def_RPLib_S4_EtShPullComp
-- name    : RPLib_S4_EtShPullComp
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:18:18.270934+00:00
-- url     : https://prove2.me/theorems/4eb783b5-249a-446c-9ff3-34ad2e84362b
-- title:
--   Pullback of etale sheaves along a composite; pullback preserves lisse sheaves
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. For $g : Z \to X$ and $f : X \to Y$ there is a natural isomorphism $(f \circ g)^* \cong g^* \circ f^*$ (from base change along a composite and uniqueness of left adjoints), and equal morphisms give isomorphic pullbacks. Consequently $f^*$ preserves locally constant and lisse sheaves: if $F|_U$ is constant then $(f^*F)|_{U \times_Y X}$ is constant.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose IX, Section 2; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter II

import Mathlib
import Definitions.Def_RPLib_S4_EtShConst

/-!
# S4-EtSheaves, part 4: pullback along a composite; pullback preserves (locally) constant sheaves

`pullCompIso g f : (g ≫ f)^* ≅ f^* ⋙ g^*` (from base change along a composite and uniqueness of left
adjoints), `pullCongr` (equal maps give isomorphic pullbacks). Consequently `f^*` preserves locally
constant and lisse sheaves (`IsLocConst.pull`, `IsLisse.pull`): if `F|_U` is constant then
`(f^*F)|_(U ×_Y X)` is constant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ]

section Comp

variable {W X Y : Scheme.{u}} (g : W ⟶ X) (f : X ⟶ Y)

/-- Base change along a composite: `etPull (g ≫ f) ≅ etPull f ⋙ etPull g`. -/
def etPullCompIso : etPull (g ≫ f) ≅ etPull f ⋙ etPull g :=
  MorphismProperty.Over.pullbackComp g f

/-- `f_*` along a composite: `g_* ⋙ f_* ≅ (g ≫ f)_*`. -/
def pushCompIso : push g Λ ⋙ push f Λ ≅ push (g ≫ f) Λ :=
  Functor.sheafPushforwardContinuousComp' (etPullCompIso g f).symm (ModuleCat.{u} Λ)
    Y.smallEtaleTopology X.smallEtaleTopology W.smallEtaleTopology

/-- **Pullback along a composite**: `(g ≫ f)^* ≅ f^* ⋙ g^*`. -/
def pullCompIso : pull (g ≫ f) Λ ≅ pull f Λ ⋙ pull g Λ :=
  (pullAdj (g ≫ f) Λ).leftAdjointUniq
    (((pullAdj f Λ).comp (pullAdj g Λ)).ofNatIsoRight (pushCompIso Λ g f))

end Comp

/-- Equal morphisms have isomorphic pullback functors. -/
def pullCongr {X Y : Scheme.{u}} {f f' : X ⟶ Y} (h : f = f') : pull f Λ ≅ pull f' Λ :=
  eqToIso (by rw [h])

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Λ}

/-- If `F|_U ≅ M_U` for `U` etale over `Y`, then `(f^*F)|_(U ×_Y X) ≅ M`. -/
def pullLocalIso {F : EtSh Λ Y} (U : Y.Etale) (M : ModuleCat.{u} Λ)
    (e : (pull U.hom Λ).obj F ≅ constSh Λ U.left M) :
    (pull ((etPull f).obj U).hom Λ).obj ((pull f Λ).obj F) ≅ constSh Λ ((etPull f).obj U).left M :=
  ((pullCompIso Λ (pullback.snd U.hom f) f).app F).symm ≪≫
    (pullCongr Λ (pullback.condition (f := U.hom) (g := f)).symm).app F ≪≫
    (pullCompIso Λ (pullback.fst U.hom f) U.hom).app F ≪≫
    (pull (pullback.fst U.hom f) Λ).mapIso e ≪≫ pullConst Λ (pullback.fst U.hom f) M

/-- **`f^*` preserves locally constant sheaves.** -/
theorem IsLocConst.pull {F : EtSh Λ Y} (hF : IsLocConst Λ F) :
    IsLocConst Λ ((EtSheaves.pull f Λ).obj F) := by
  intro x
  obtain ⟨U, v, hv, M, ⟨e⟩⟩ := hF (f x)
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback v x hv
  exact ⟨(etPull f).obj U, z, hz, M, ⟨pullLocalIso f U M e⟩⟩

/-- **`f^*` preserves lisse sheaves.** -/
theorem IsLisse.pull {F : EtSh Λ Y} (hF : IsLisse Λ F) :
    IsLisse Λ ((EtSheaves.pull f Λ).obj F) := by
  intro x
  obtain ⟨U, v, hv, M, hM, ⟨e⟩⟩ := hF (f x)
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback v x hv
  exact ⟨(etPull f).obj U, z, hz, M, hM, ⟨pullLocalIso f U M e⟩⟩

end RamanujanPetersson.EtSheaves


