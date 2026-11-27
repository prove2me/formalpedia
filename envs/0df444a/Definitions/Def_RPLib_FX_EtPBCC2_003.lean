-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC2_003
-- name    : RPLib_FX_EtPBCC2_003
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-27T01:41:28.579435+00:00
-- url     : https://prove2.me/theorems/c76da38a-597e-5824-81ed-6e1bbe8874fa
-- title:
--   Sheaf-level proper base change with compact supports, library file 003
-- statement:
--   File 003 of the library for sheaf-level proper base change with compact supports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_C2_BcIso`: S4-EtPBC-C2, part 3: the base change morphism is an isomorphism (generic, closed-point form)
--   * `S4.Def_RP_EtPBC_C2_GoodIso`: S4-EtPBC-C2, part 1: `PBCGood` is invariant under isomorphisms of the source
--
--   **Formalization note.** One file of a library formalizing sheaf-level proper base change for étale cohomology with compact supports: for $f : X \to S$ with a compactification $X \xrightarrow{j} Z \xrightarrow{i} P \xrightarrow{\bar f} S$ ($j$ an open immersion, $i$ a closed immersion, $\bar f$ a tower of projective-line bundles over a noetherian $S$ of finite type over an algebraically closed field), $R^q f_! = R^q \bar f_* \circ i_* j_!$, and any $g : S' \to S$ of finite type, the base change morphism $g^* R^q f_! F \to R^q f'_! (g_X^* F)$ is an isomorphism for every sheaf $F$ of $\Lambda$-modules ($\Lambda$ finite, $\ell$-power torsion). It builds on the proper base change libraries for the projective line (`RPLib_FX_EtPBC_*`), for iterated projective-line bundles (`RPLib_FX_EtPBCB_*`) and for the stalks of $R^q f_!$ (`RPLib_FX_EtPBCC1_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre) and Exposé XVII, 5.2.8 (P. Deligne, changement de base pour R f_!), Lecture Notes in Math. 269, 270, 305, Springer (1972-73); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2-§3

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCC2_006

/-!
# Sheaf-level proper base change with compact supports, library file 003

Declarations of the formalization of sheaf-level proper base change for compactly supported étale
cohomology: for a compactified X ⟶ S whose proper part is an iterated projective-line bundle (a tower)
and any g : S' ⟶ S of finite type, the base change morphism g^* R^q f_! F ⟶ R^q f'_! (g_X^* F) is an
isomorphism, re-hosted declaration by declaration from the library modules below, on top of the proper
base change libraries RPLib_FX_EtPBC, RPLib_FX_EtPBCB and RPLib_FX_EtPBCC1. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_C2_BcIso`: S4-EtPBC-C2, part 3: the base change morphism is an isomorphism (generic, closed-point form)
* `S4.Def_RP_EtPBC_C2_GoodIso`: S4-EtPBC-C2, part 1: `PBCGood` is invariant under isomorphisms of the source
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_C2_BcIso =====
section

/-! # S4-EtPBC-C2, part 3: the base change morphism is an isomorphism (generic, closed-point form)

For `g₁ : P ⟶ S` universally closed and `g : S' ⟶ S` with `S'` of finite type over a field, `bcMorSq` of the
base-change square `P ×_S S'` is an isomorphism as soon as `g₁` and `pullback.snd g₁ g` are `PBCGood` at the closed
points (`isIso_bcMorSq_bc`); proof: closed-point test, `SqMor.pbcEquiv_sqTr` for the square of `(g, s)`-squares with
`σ = 𝟙`, bijectivity of the stalk transport and of the fibre pull-back.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.C2

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.C1

universe u

section PtId

end PtId

section Gen

end Gen

section Sq
variable {Λ : Type u} [CommRing Λ] {P S S' : Scheme.{u}} (g₁ : P ⟶ S) (g : S' ⟶ S) (s₂ : GeomPt S')

theorem bcSq_fibH_bijective (F : EtSh Λ P) (q : ℕ) : Function.Bijective ((bcSq g₁ g s₂).fibH F q) := by
  have : IsIso ((bcSq g₁ g s₂).κApp F) := by unfold SqMor.κApp nestComp; infer_instance
  exact fibHGen_bijective (pull (bcSq g₁ g s₂).fibMap Λ) _ _ q
    (pull_ext_bijective (Λ := Λ) (bcSq g₁ g s₂).fibMap _ _ q)

end Sq

section Main
variable {Λ : Type u} [CommRing Λ] {K : Type u} [Field K] {P S S' : Scheme.{u}} (g₁ : P ⟶ S)
  [UniversallyClosed g₁] (g : S' ⟶ S) (gX : S' ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType gX]

include gX in
/-- **Base change along `g` is an isomorphism** on `R^q g₁_*` once `g₁` and its base change are `PBCGood` at the
closed points of `S'`. -/
theorem isIso_bcMorSq_bc (hg₁ : ∀ x : S', IsClosed ({x} : Set S') → PBCGood Λ g₁ ((geomPtAt x).map g))
    (hg₂ : ∀ x : S', IsClosed ({x} : Set S') → PBCGood Λ (pullback.snd g₁ g) (geomPtAt x)) (q : ℕ)
    (F : EtSh Λ P) :
    IsIso (bcMorSq Λ (pullback.fst g₁ g) g g₁ (pullback.snd g₁ g) pullback.condition.symm q F) := by
  apply isIso_of_closed gX
  intro x hx
  have key := (bcSq g₁ g (geomPtAt x)).pbcEquiv_sqTr (hg₁ x hx) (hg₂ x hx) F q
  have hcomp : (fun y => (((geomPtAt x).stalkF Λ).map (bcMorSq Λ (pullback.fst g₁ g) g g₁ (pullback.snd g₁ g)
      pullback.condition.symm q F)).hom y) ∘ (fun y₁ => ((bcSq g₁ g (geomPtAt x)).stalkTr
        (((push g₁ Λ).rightDerived q).obj F)).hom y₁) =
      (pbcEquiv (pullback.snd g₁ g) (geomPtAt x) (hg₂ x hx) ((pull (pullback.fst g₁ g) Λ).obj F) q).symm ∘
        ((bcSq g₁ g (geomPtAt x)).fibH F q) ∘ (pbcEquiv g₁ ((geomPtAt x).map g) (hg₁ x hx) F q) := by
    funext y₁
    simp only [Function.comp_apply]
    rw [← key, AddEquiv.symm_apply_apply]
  have hb : Function.Bijective ((pbcEquiv (pullback.snd g₁ g) (geomPtAt x) (hg₂ x hx)
      ((pull (pullback.fst g₁ g) Λ).obj F) q).symm ∘ ((bcSq g₁ g (geomPtAt x)).fibH F q) ∘
        (pbcEquiv g₁ ((geomPtAt x).map g) (hg₁ x hx) F q)) :=
    (AddEquiv.bijective _).comp ((bcSq_fibH_bijective g₁ g _ F q).comp (AddEquiv.bijective _))
  rw [← hcomp] at hb
  exact (Function.Bijective.of_comp_iff _ (bcSq_stalkTr_bijective g₁ g _ _)).1 hb

end Main

end RamanujanPetersson.EtPBC.C2

end

end

-- ===== S4.Def_RP_EtPBC_C2_GoodIso =====
section

/-! # S4-EtPBC-C2, part 1: `PBCGood` is invariant under isomorphisms of the source -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.C2

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.Mate

universe u

variable {Λ : Type u} [CommRing Λ]

section Sq

end Sq

section Fib

end Fib

section HZero

end HZero

section Good
variable (Λ) {Y' Y S : Scheme.{u}} (e : Y' ⟶ Y) [IsIso e] (g : Y ⟶ S) (s : GeomPt S)

theorem fibVan_iso (hv : FibVan Λ g s) : FibVan Λ (e ≫ g) s := by
  intro I _ q β
  have : Injective ((push e Λ).obj I) := (pullAdj e Λ).map_injective I inferInstance
  refine H_zero_of_iso (fibPullIso Λ e g s I).symm (fun x => ?_) β
  exact H_zero_pull (fibCompH e g s) _ (fun z => hv _ q z) x

/-- **`PBCGood` along an isomorphism of the source.** -/
theorem pbcGood_iso (hg : PBCGood Λ g s) : PBCGood Λ (e ≫ g) s :=
  ⟨bcSurj_iso Λ e g s hg.1, fibVan_iso Λ e g s hg.2⟩

end Good

end RamanujanPetersson.EtPBC.C2

end

end


