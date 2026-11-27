-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC2_006
-- name    : RPLib_FX_EtPBCC2_006
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-27T01:21:05.244723+00:00
-- url     : https://prove2.me/theorems/42bcafd2-9e27-51a0-b1f3-684040a7d506
-- title:
--   Sheaf-level proper base change with compact supports, library file 006
-- statement:
--   File 006 of the library for sheaf-level proper base change with compact supports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_C1_PbcSqC`: S4-EtPBC-C1, part 29c: naturality of the named `pbcEquiv` under morphisms of `(g, s)`-squares
--
--   **Formalization note.** One file of a library formalizing sheaf-level proper base change for étale cohomology with compact supports: for $f : X \to S$ with a compactification $X \xrightarrow{j} Z \xrightarrow{i} P \xrightarrow{\bar f} S$ ($j$ an open immersion, $i$ a closed immersion, $\bar f$ a tower of projective-line bundles over a noetherian $S$ of finite type over an algebraically closed field), $R^q f_! = R^q \bar f_* \circ i_* j_!$, and any $g : S' \to S$ of finite type, the base change morphism $g^* R^q f_! F \to R^q f'_! (g_X^* F)$ is an isomorphism for every sheaf $F$ of $\Lambda$-modules ($\Lambda$ finite, $\ell$-power torsion). It builds on the proper base change libraries for the projective line (`RPLib_FX_EtPBC_*`), for iterated projective-line bundles (`RPLib_FX_EtPBCB_*`) and for the stalks of $R^q f_!$ (`RPLib_FX_EtPBCC1_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre) and Exposé XVII, 5.2.8 (P. Deligne, changement de base pour R f_!), Lecture Notes in Math. 269, 270, 305, Springer (1972-73); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2-§3

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCC2_005

/-!
# Sheaf-level proper base change with compact supports, library file 006

Declarations of the formalization of sheaf-level proper base change for compactly supported étale
cohomology: for a compactified X ⟶ S whose proper part is an iterated projective-line bundle (a tower)
and any g : S' ⟶ S of finite type, the base change morphism g^* R^q f_! F ⟶ R^q f'_! (g_X^* F) is an
isomorphism, re-hosted declaration by declaration from the library modules below, on top of the proper
base change libraries RPLib_FX_EtPBC, RPLib_FX_EtPBCB and RPLib_FX_EtPBCC1. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_C1_PbcSqC`: S4-EtPBC-C1, part 29c: naturality of the named `pbcEquiv` under morphisms of `(g, s)`-squares
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_C1_PbcSqC =====
section

/-!
# S4-EtPBC-C1, part 29c: naturality of the named `pbcEquiv` under morphisms of `(g, s)`-squares

**`pbcEquiv_sq`** [P4-CANON] (every degree, `PBCGood` at both points): for `z` in the stalk at `s₂` of
`eS^* R^q g₁_* F` whose section over `Spec Ω₂` is the `σ`-pull-back of that of `y₁` (hypothesis `hz`),
`pbcEquiv (stalk of bcMorSq(m) z) = m.fibH (pbcEquiv y₁)`. Degree `0` by `nat0_gen` with `psi0_all` and `keyMor`,
degrees `p + 1` by `pbcEquivS_sq`.

**`pbcEquiv_sqTr`** [P4-CANON]: the hypothesis-free form, with `z` the stalk transport `m.stalkTr _ y₁`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtCompact.PtSec

universe u

variable {Λ : Type u} [CommRing Λ]

namespace SqMor

variable {P₁ S₁ P₂ S₂ : Scheme.{u}} {g₁ : P₁ ⟶ S₁} {g₂ : P₂ ⟶ S₂} {s₁ : GeomPt S₁} {s₂ : GeomPt S₂}
  (m : SqMor g₁ g₂ s₁ s₂)

/-- **Naturality of the named `pbcEquiv` under a morphism of `(g, s)`-squares** (every degree; `PBCGood` at both
points). [P4-CANON] -/
theorem pbcEquiv_sq [UniversallyClosed g₁] [UniversallyClosed g₂] (hg₁ : PBCGood Λ g₁ s₁)
    (hg₂ : PBCGood Λ g₂ s₂) (F : EtSh Λ P₁) (q : ℕ)
    (y₁ : (s₁.stalkF Λ).obj (((push g₁ Λ).rightDerived q).obj F))
    (z : (s₂.stalkF Λ).obj ((pull m.eS Λ).obj (((push g₁ Λ).rightDerived q).obj F)))
    (hz : stalkSec s₂ _ z = (pullUnit Λ m.σ).hom ≫ (pull m.σ Λ).map (stalkSec s₁ _ y₁) ≫
      m.θApp (((push g₁ Λ).rightDerived q).obj F)) :
    pbcEquiv g₂ s₂ hg₂ ((pull m.eP Λ).obj F) q
        (((s₂.stalkF Λ).map (bcMorSq Λ m.eP m.eS g₁ g₂ m.wE q F)).hom z) =
      m.fibH F q (pbcEquiv g₁ s₁ hg₁ F q y₁) := by
  cases q with
  | zero =>
    exact nat0_gen _ _ _ _ _ _ _ _ _ _ _
      (unitCell_sq Λ m.fibMap m.σ (pullback.snd g₁ s₁.pt) (pullback.snd g₂ s₂.pt) m.fibMap_π.symm) (m.κApp F)
      (psi0_all g₂ s₂ _ _ _ _).symm (psi0_all g₁ s₁ F _ _ y₁).symm
      (by rw [stalkSec_natural]; exact m.keyMor F 0 y₁ z hz)
  | succ p => exact m.pbcEquivS_sq F p _ _ _ _ y₁ z hz

/-- **Naturality of the named `pbcEquiv` under a morphism of `(g, s)`-squares**, hypothesis-free form: the stalk
element at `s₂` is the stalk transport of `y₁` along `m`. [P4-CANON] -/
theorem pbcEquiv_sqTr [UniversallyClosed g₁] [UniversallyClosed g₂] (hg₁ : PBCGood Λ g₁ s₁)
    (hg₂ : PBCGood Λ g₂ s₂) (F : EtSh Λ P₁) (q : ℕ)
    (y₁ : (s₁.stalkF Λ).obj (((push g₁ Λ).rightDerived q).obj F)) :
    pbcEquiv g₂ s₂ hg₂ ((pull m.eP Λ).obj F) q
        (((s₂.stalkF Λ).map (bcMorSq Λ m.eP m.eS g₁ g₂ m.wE q F)).hom
          ((m.stalkTr (((push g₁ Λ).rightDerived q).obj F)).hom y₁)) =
      m.fibH F q (pbcEquiv g₁ s₁ hg₁ F q y₁) :=
  m.pbcEquiv_sq hg₁ hg₂ F q y₁ _ (m.stalkSec_stalkTr _ y₁)

end SqMor

end RamanujanPetersson.EtPBC.C1

end

end


