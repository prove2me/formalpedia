-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC1_012
-- name    : RPLib_FX_EtPBCC1_012
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T19:29:34.00031+00:00
-- url     : https://prove2.me/theorems/24b4aced-4ec7-5653-9ed0-7796b3e1aa27
-- title:
--   Proper base change with compact supports, library file 012
-- statement:
--   File 012 of the library for proper base change with compact supports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_C1_PbcCN`: S4-EtPBC-C1, part 20c: naturality of `pbcEquivC` and the `H_c` form `pbcEquivHc`
--
--   **Formalization note.** One file of a library formalizing the canonical proper base change isomorphism for étale cohomology with compact supports: for $f : X \to S$ with a compactification $X \xrightarrow{j} Z \xrightarrow{i} P \xrightarrow{\bar f} S$ ($j$ an open immersion, $i$ a closed immersion, $\bar f$ proper), $R^q f_! = R^q \bar f_* \circ i_* j_!$, and a geometric point $s$ of $S$ at which $\bar f$ satisfies proper base change, the stalk $(R^q f_! F)_s$ is identified with $H^q_c(X_s, F|_{X_s})$ by a named isomorphism that is natural in the sheaf $F$ of $\Lambda$-modules (built from the base change morphism of the fibre square). It builds on the proper base change libraries for the projective line (`RPLib_FX_EtPBC_*`) and for iterated projective-line bundles (`RPLib_FX_EtPBCB_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre) and Exposé XVII, 5.2.8 (P. Deligne, changement de base pour R f_!), Lecture Notes in Math. 269, 270, 305, Springer (1972-73); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2-§3

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCC1_011

/-!
# Proper base change with compact supports, library file 012

Declarations of the formalization of the canonical proper base change isomorphism for compactly
supported étale cohomology (R^q f_! F)_s ≃ H^q_c(X_s, F|X_s), natural in F, for compactified X ⟶ S
(the base change morphism, its stalk form and its naturality), re-hosted declaration by declaration
from the library modules below, on top of the proper base change libraries RPLib_FX_EtPBC and
RPLib_FX_EtPBCB (projective line and iterated projective-line bundles). Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_C1_PbcCN`: S4-EtPBC-C1, part 20c: naturality of `pbcEquivC` and the `H_c` form `pbcEquivHc`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_C1_PbcCN =====
section

/-!
# S4-EtPBC-C1, part 20c: naturality of `pbcEquivC` and the `H_c` form `pbcEquivHc`

* **`pbcEquivC_natural`**: `pbcEquivC (stalk of R^q f_!(φ) y) = H^q(ext_s (φ|X_s)) (pbcEquivC y)`;
* **`pbcEquivHc c s hg F q : (R^q f_! F)_s ≃+ H^q_c(X_s, F|X_s)`**, the named form of `rshriek_stalk`.
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

/-- **Naturality in `F` of `pbcEquivC`** (every degree). -/
theorem pbcEquivC_natural (hg : PBCGood Λ c.fbar s) {F F' : EtSh Λ X} (φ : F ⟶ F') (q : ℕ)
    (y : (s.stalkF Λ).obj ((c.Rshriek Λ q).obj F)) :
    pbcEquivC c s hg F' q (((s.stalkF Λ).map ((c.Rshriek Λ q).map φ)).hom y) =
      Hmap Λ (((fibCpt c s).ext Λ).map ((pull (cptιX c s) Λ).map φ)) q (pbcEquivC c s hg F q y) := by
  show Hiso Λ (extFib c s F') q (pbcEquiv c.fbar s hg ((c.ext Λ).obj F') q
    (((s.stalkF Λ).map (((push c.fbar Λ).rightDerived q).map ((c.ext Λ).map φ))).hom y)) = _
  rw [pbcEquiv_natural]
  exact hiso_hmap _ _ _ _ (extFib_natural c s φ) q _

end Shriek

end RamanujanPetersson.EtPBC.C1

end

end


