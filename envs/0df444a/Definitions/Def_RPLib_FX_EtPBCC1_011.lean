-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC1_011
-- name    : RPLib_FX_EtPBCC1_011
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T19:17:48.159013+00:00
-- url     : https://prove2.me/theorems/a715e6cf-cbb1-5a78-8e25-1e0268d0fdc5
-- title:
--   Proper base change with compact supports, library file 011
-- statement:
--   File 011 of the library for proper base change with compact supports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_C1_NatF`: S4-EtPBC-C1, part 19: naturality in `F` of the named proper-base-change equivalences
--   * `S4.Def_RP_EtPBC_C1_PbcG`: S4-EtPBC-C1, part 20a: the named equivalence `pbcEquiv` in every degree
--   * `S4.Def_RP_EtPBC_C1_PbcC`: S4-EtPBC-C1, part 20b: the named equivalence `pbcEquivC` for `R^q f_!`
--
--   **Formalization note.** One file of a library formalizing the canonical proper base change isomorphism for étale cohomology with compact supports: for $f : X \to S$ with a compactification $X \xrightarrow{j} Z \xrightarrow{i} P \xrightarrow{\bar f} S$ ($j$ an open immersion, $i$ a closed immersion, $\bar f$ proper), $R^q f_! = R^q \bar f_* \circ i_* j_!$, and a geometric point $s$ of $S$ at which $\bar f$ satisfies proper base change, the stalk $(R^q f_! F)_s$ is identified with $H^q_c(X_s, F|_{X_s})$ by a named isomorphism that is natural in the sheaf $F$ of $\Lambda$-modules (built from the base change morphism of the fibre square). It builds on the proper base change libraries for the projective line (`RPLib_FX_EtPBC_*`) and for iterated projective-line bundles (`RPLib_FX_EtPBCB_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre) and Exposé XVII, 5.2.8 (P. Deligne, changement de base pour R f_!), Lecture Notes in Math. 269, 270, 305, Springer (1972-73); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2-§3

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCC1_009
import Definitions.Def_RPLib_FX_EtPBCC1_010

/-!
# Proper base change with compact supports, library file 011

Declarations of the formalization of the canonical proper base change isomorphism for compactly
supported étale cohomology (R^q f_! F)_s ≃ H^q_c(X_s, F|X_s), natural in F, for compactified X ⟶ S
(the base change morphism, its stalk form and its naturality), re-hosted declaration by declaration
from the library modules below, on top of the proper base change libraries RPLib_FX_EtPBC and
RPLib_FX_EtPBCB (projective line and iterated projective-line bundles). Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_C1_NatF`: S4-EtPBC-C1, part 19: naturality in `F` of the named proper-base-change equivalences
* `S4.Def_RP_EtPBC_C1_PbcG`: S4-EtPBC-C1, part 20a: the named equivalence `pbcEquiv` in every degree
* `S4.Def_RP_EtPBC_C1_PbcC`: S4-EtPBC-C1, part 20b: the named equivalence `pbcEquivC` for `R^q f_!`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_C1_NatF =====
section

/-!
# S4-EtPBC-C1, part 19: naturality in `F` of the named proper-base-change equivalences

* (generic) **`absRelR_natural`**: `absRelR I' (x ∘ ψ) = absRelR I x ≫ R^(p+1)(ψ)`; **`abs0_natural`** and
  **`abs0_injective`**: the same for the degree-`0` description `x ↦ adj.homEquiv (u ≫ x) ≫ R.toRD₀`;
* **`pbcEquivS_natural`**, **`pbcEquivZero_natural`**: `pbcEquiv (stalk of R^q g_*(φ) y) = H^q(ι^* φ) (pbcEquiv y)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtCompact.PtSec

set_option backward.isDefEq.respectTransparency false

section GenN

universe w v₁ v₂ u₁ u₂

end GenN

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S) {F F' : EtSh Λ P} (φ : F ⟶ F')

/-- **Naturality in `F` of `pbcEquivS`** (degrees `p + 1`). -/
theorem pbcEquivS_natural (p : ℕ) (hI : BCInj Λ g s (p + 1) F) (hS : BCSurj Λ g s (p + 1) F)
    (hI' : BCInj Λ g s (p + 1) F') (hS' : BCSurj Λ g s (p + 1) F')
    (y : (s.stalkF Λ).obj (((push g Λ).rightDerived (p + 1)).obj F)) :
    pbcEquivS g s F' p hI' hS' (((s.stalkF Λ).map (((push g Λ).rightDerived (p + 1)).map φ)).hom y) =
      Hmap Λ ((pull (fibι g s) Λ).map φ) (p + 1) (pbcEquivS g s F p hI hS y) := by
  have := unitSh_projective_spec s.Ω Λ
  apply (absRelR (pullAdj (X := fib g s) (pullback.snd g s.pt) Λ) (pullUnit (X := fib g s) Λ (pullback.snd g s.pt)).symm
    (injectiveResolution ((pull (fibι g s) Λ).obj F')) p).injective
  rw [pbcEquivS_spec g s F' p _ hI' hS', stalkSec_natural, Hmap_apply,
    absRelR_natural _ _ (injectiveResolution ((pull (fibι g s) Λ).obj F)), pbcEquivS_spec g s F p _ hI hS,
    Category.assoc, Category.assoc, bcMorSq_natural]

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_PbcG =====
section

/-!
# S4-EtPBC-C1, part 20a: the named equivalence `pbcEquiv` in every degree

* `bcSurj_of_good`, `bcInj_of_good`: `PBCGood` gives the hypotheses of `pbcEquivZero` / `pbcEquivS` in every degree;
* **`pbcEquiv g s hg F q : (R^q g_* F)_s ≃+ H^q(P_s, ι^* F)`** (named; `pbcEquivZero` in degree `0`, `pbcEquivS` in
  degrees `p + 1`, by the equation lemmas of `pbcEquiv`) and **`pbcEquiv_natural`** (naturality in `F`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact

universe u

set_option backward.isDefEq.respectTransparency false

section Good

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S) [UniversallyClosed g]

/-- **Naturality in `F` of `pbcEquiv`** (every degree). -/
theorem pbcEquiv_natural (hg : PBCGood Λ g s) {F F' : EtSh Λ P} (φ : F ⟶ F') (q : ℕ)
    (y : (s.stalkF Λ).obj (((push g Λ).rightDerived q).obj F)) :
    pbcEquiv g s hg F' q (((s.stalkF Λ).map (((push g Λ).rightDerived q).map φ)).hom y) =
      Hmap Λ ((pull (fibι g s) Λ).map φ) q (pbcEquiv g s hg F q y) := by
  cases q with
  | zero => exact pbcEquivZero_natural g s φ _ _ _ _ y
  | succ p => exact pbcEquivS_natural g s φ p _ _ _ _ y

end Good

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_PbcC =====
section

/-!
# S4-EtPBC-C1, part 20b: the named equivalence `pbcEquivC` for `R^q f_!`

* `hiso_hmap`: `H^n(Z, -)` on a commutative square whose sides are isomorphisms;
* `extFib c s F : ι^* (ext F) ≅ ext_s (F|X_s)` (`itExtNat` at `g = s.pt`) and `extFib_natural`;
* **`pbcEquivC c s hg F q : (R^q f_! F)_s ≃+ H^q(P_s, ext_s (F|X_s))`** (`pbcEquiv` for `c.fbar` on `c.ext F`, then
  `extFib`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact

universe u

set_option backward.isDefEq.respectTransparency false

section Shriek

variable {Λ : Type u} [CommRing Λ] {X B : Scheme.{u}} {f : X ⟶ B} (c : Cpt f) (s : GeomPt B)

/-- **`pbcEquivC : (R^q f_! F)_s ≃+ H^q(P_s, ext_s (F|X_s))`**. -/
def pbcEquivC (hg : PBCGood Λ c.fbar s) (F : EtSh Λ X) (q : ℕ) :
    ToType ((s.stalkF Λ).obj ((c.Rshriek Λ q).obj F)) ≃+
      H Λ (((fibCpt c s).ext Λ).obj ((pull (cptιX c s) Λ).obj F)) q :=
  (pbcEquiv c.fbar s hg ((c.ext Λ).obj F) q).trans (Hiso Λ (extFib c s F) q)

end Shriek

end RamanujanPetersson.EtPBC.C1

end

end


