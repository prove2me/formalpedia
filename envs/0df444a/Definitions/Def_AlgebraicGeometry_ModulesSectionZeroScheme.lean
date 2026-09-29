-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
-- name    : AlgebraicGeometry_ModulesSectionZeroScheme
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/a63b352f-3dbf-5897-8191-6cf0020ea26b
-- title:
--   Zero scheme of a section of a module on a scheme
-- statement:
--   Throughout, $X$ is a scheme and $M$ an object of $X.Modules$ (a sheaf of modules over the sheaf of rings of $X$), with the symmetric closed monoidal structure on $X.Modules$ whose unit is the structure sheaf. A first group of declarations records the identification of sections of the monoidal unit with sections of $\mathcal O_X$: `toUnitSection` and `ofUnitSection` are mutually inverse bijections $\Gamma(X,U)\leftrightarrow\Gamma(\mathbf 1_{X.Modules},U)$ for an open $U$, and the accompanying lemmas state that `ofUnitSection` is injective, commutes with restriction along $V\le U$, and carries the module action $r\cdot m$ to the product $r\cdot\mathrm{ofUnitSection}\,m$.
--
--   Given a section $s\colon \mathbf 1_{X.Modules}\to M$, `restrictSection s U` is the image of $1$ under $s$ over the open image of $U$, viewed as a global section of the restriction $M|_U$. For a homomorphism $\varphi\colon M|_U\to\mathbf 1_{U.Modules}$, the coefficient `coeff s U φ` is the element of $\Gamma(X,U)$ obtained by evaluating $\varphi$ on this section over $\top$ and transporting along the canonical isomorphism $\Gamma(U,\top)\cong\Gamma(X,U)$; `coeffIdeal s U` is the ideal of $\Gamma(X,U)$ spanned by the range of `coeff s U`, and `coeff_mem_coeffIdeal` records membership. The ideal sheaf of the zero scheme, `zeroSchemeIdeal s`, is defined as the infimum in the complete lattice `X.IdealSheafData` of all $J$ with $\mathrm{coeffIdeal}(s,U)\le J(U)$ for every affine open $U$; `zeroScheme s` is the associated closed subscheme. The three lattice lemmas express the defining infimum property, and `zeroSchemeIdeal_eq_of_isLeast` identifies it with any least element of that set.
--
--   The remaining items are vocabulary: `pullbackSection` transports $s$ along $F\colon X'\to X$ using the isomorphism $F^{*}\mathbf 1\cong\mathbf 1$; `restrictIsoOfLE` converts a trivialisation of $F^{*}M$ along $U\hookrightarrow X$ into a trivialisation of the restriction $M|_W$ for $W\le U$, whence `IsInvertible.exists_restrict_iso`: if $M$ satisfies the predicate `IsInvertible` (every point has a neighbourhood on which the pullback is isomorphic to the unit) and $x\in V$, there is an affine open $U$ with $x\in U\subseteq V$ and $M|_U\cong\mathbf 1_{U.Modules}$. Finally `sectionDual` is the transpose $M^{\vee}\to\mathbf 1$ of $s$, and `Scheme.IdealSheafData.invModuleSection` is the section $\mathbf 1\to I^{\vee}$ obtained by currying the inclusion $I.module\to\mathbf 1$, where $I.module$ is the kernel of the map from the unit to the pushforward of the unit along the closed immersion of the subscheme cut out by $I$.
--
--   **Relation to Mathlib.** Mathlib supplies `Scheme.IdealSheafData` with its complete lattice structure and the category `Scheme.Modules`; the monoidal and monoidal-closed structure used here, the predicate `Scheme.Modules.IsInvertible`, and the coefficient ideal and zero scheme of a section are the project's own.
--
--   **Where it is used.** These notions provide the local vocabulary for divisors attached to sections of invertible modules, feeding the project's treatment of relative effective Cartier divisors and of the rigidified relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesSectionZeroScheme.lean

import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules}

def toUnitSection (U : X.Opens) (r : Γ(X, U)) : Γ(𝟙_ X.Modules, U) := r

def ofUnitSection (U : X.Opens) (m : Γ(𝟙_ X.Modules, U)) : Γ(X, U) := m

@[simp] lemma ofUnitSection_toUnitSection (U : X.Opens) (r : Γ(X, U)) :
    ofUnitSection U (toUnitSection U r) = r := rfl

@[simp] lemma toUnitSection_ofUnitSection (U : X.Opens) (m : Γ(𝟙_ X.Modules, U)) :
    toUnitSection U (ofUnitSection U m) = m := rfl

lemma ofUnitSection_injective (U : X.Opens) : Function.Injective (ofUnitSection (X := X) U) :=
  fun _ _ h => h

lemma ofUnitSection_map {U V : X.Opens} (i : V ⟶ U) (m : Γ(𝟙_ X.Modules, U)) :
    ofUnitSection V ((𝟙_ X.Modules).presheaf.map i.op m) =
      X.presheaf.map i.op (ofUnitSection U m) := rfl

lemma ofUnitSection_smul (U : X.Opens) (r : Γ(X, U)) (m : Γ(𝟙_ X.Modules, U)) :
    ofUnitSection U (r • m) = r * ofUnitSection U m := rfl

def restrictSection (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) : Γ(M.restrict U.ι, ⊤) :=
  s.app (U.ι ''ᵁ ⊤) (toUnitSection (U.ι ''ᵁ ⊤) 1)

def coeff (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)
    (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) : Γ(X, U) :=
  U.topIso.hom (ofUnitSection ⊤ (φ.app ⊤ (restrictSection s U)))

def coeffIdeal (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) : Ideal Γ(X, U) :=
  Ideal.span (Set.range (coeff s U))

lemma coeff_mem_coeffIdeal (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)
    (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) : coeff s U φ ∈ coeffIdeal s U :=
  Ideal.subset_span ⟨φ, rfl⟩

def zeroSchemeIdeal (s : 𝟙_ X.Modules ⟶ M) : X.IdealSheafData :=
  sInf {J : X.IdealSheafData | ∀ U : X.affineOpens, coeffIdeal s U.1 ≤ J.ideal U}

abbrev zeroScheme (s : 𝟙_ X.Modules ⟶ M) : Scheme.{u} :=
  (zeroSchemeIdeal s).subscheme

lemma zeroSchemeIdeal_le {s : 𝟙_ X.Modules ⟶ M} {J : X.IdealSheafData}
    (h : ∀ U : X.affineOpens, coeffIdeal s U.1 ≤ J.ideal U) : zeroSchemeIdeal s ≤ J :=
  sInf_le h

lemma le_zeroSchemeIdeal {s : 𝟙_ X.Modules ⟶ M} {K : X.IdealSheafData}
    (h : ∀ J : X.IdealSheafData, (∀ U : X.affineOpens, coeffIdeal s U.1 ≤ J.ideal U) → K ≤ J) :
    K ≤ zeroSchemeIdeal s :=
  le_sInf fun _ hJ => h _ hJ

lemma zeroSchemeIdeal_eq_of_isLeast {s : 𝟙_ X.Modules ⟶ M} {P : X.IdealSheafData}
    (hP : IsLeast {J : X.IdealSheafData | ∀ U : X.affineOpens, coeffIdeal s U.1 ≤ J.ideal U} P) :
    zeroSchemeIdeal s = P :=
  hP.isGLB.sInf_eq

def pullbackSection {X' : Scheme.{u}} (F : X' ⟶ X) (s : 𝟙_ X.Modules ⟶ M) :
    𝟙_ X'.Modules ⟶ (Scheme.Modules.pullback F).obj M :=
  (Scheme.Modules.pullbackUnitIso F).inv ≫ (Scheme.Modules.pullback F).map s

@[simp] lemma pullbackSection_def {X' : Scheme.{u}} (F : X' ⟶ X) (s : 𝟙_ X.Modules ⟶ M) :
    pullbackSection F s =
      (Scheme.Modules.pullbackUnitIso F).inv ≫ (Scheme.Modules.pullback F).map s :=
  rfl

def restrictIsoOfLE {U W : X.Opens} (h : W ≤ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    M.restrict W.ι ≅ 𝟙_ (W : Scheme.{u}).Modules :=
  (restrictFunctorCongr (X.homOfLE_ι h).symm).app M ≪≫
    (restrictFunctorComp (X.homOfLE h) U.ι).app M ≪≫
    (restrictFunctor (X.homOfLE h)).mapIso ((restrictFunctorIsoPullback U.ι).app M ≪≫ e) ≪≫
    (restrictFunctorIsoPullback (X.homOfLE h)).app _ ≪≫
    Scheme.Modules.pullbackUnitIso (X.homOfLE h)

theorem IsInvertible.exists_restrict_iso (hM : Scheme.Modules.IsInvertible M) {V : X.Opens} {x : X}
    (hx : x ∈ V) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ V ∧
      Nonempty (M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules) := by
  obtain ⟨U₀, hxU₀, ⟨e⟩⟩ := hM.exists_trivialization x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ V ⊓ U₀ from ⟨hx, hxU₀⟩)
      (V ⊓ U₀).isOpen
  exact ⟨⟨U, hU⟩, hxU, fun y hy => (hUle hy).1, ⟨restrictIsoOfLE (fun y hy => (hUle hy).2) e⟩⟩

def sectionDual (s : 𝟙_ X.Modules ⟶ M) : Scheme.Modules.dual M ⟶ 𝟙_ X.Modules :=
  (MonoidalClosed.pre s).app (𝟙_ X.Modules) ≫
    (MonoidalClosed.unitIsoSelf (𝟙_ X.Modules)).hom

end Scheme.Modules

def Scheme.IdealSheafData.invModuleSection {X : Scheme.{u}} (I : X.IdealSheafData) :
    𝟙_ X.Modules ⟶ I.invModule :=
  MonoidalClosed.curry' I.moduleι

end AlgebraicGeometry

end


