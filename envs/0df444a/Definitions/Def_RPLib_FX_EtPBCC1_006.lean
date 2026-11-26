-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC1_006
-- name    : RPLib_FX_EtPBCC1_006
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T18:51:50.147361+00:00
-- url     : https://prove2.me/theorems/e03ae22d-a22e-46c3-84d3-26dbfd6c34e3
-- title:
--   Proper base change with compact supports, library file 006
-- statement:
--   File 006 of the library for proper base change with compact supports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
--
--   **Formalization note.** One file of a library formalizing the canonical proper base change isomorphism for étale cohomology with compact supports: for $f : X \to S$ with a compactification $X \xrightarrow{j} Z \xrightarrow{i} P \xrightarrow{\bar f} S$ ($j$ an open immersion, $i$ a closed immersion, $\bar f$ proper), $R^q f_! = R^q \bar f_* \circ i_* j_!$, and a geometric point $s$ of $S$ at which $\bar f$ satisfies proper base change, the stalk $(R^q f_! F)_s$ is identified with $H^q_c(X_s, F|_{X_s})$ by a named isomorphism that is natural in the sheaf $F$ of $\Lambda$-modules (built from the base change morphism of the fibre square). It builds on the proper base change libraries for the projective line (`RPLib_FX_EtPBC_*`) and for iterated projective-line bundles (`RPLib_FX_EtPBCB_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre) and Exposé XVII, 5.2.8 (P. Deligne, changement de base pour R f_!), Lecture Notes in Math. 269, 270, 305, Springer (1972-73); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2-§3

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCC1_003

/-!
# Proper base change with compact supports, library file 006

Declarations of the formalization of the canonical proper base change isomorphism for compactly
supported étale cohomology (R^q f_! F)_s ≃ H^q_c(X_s, F|X_s), natural in F, for compactified X ⟶ S
(the base change morphism, its stalk form and its naturality), re-hosted declaration by declaration
from the library modules below, on top of the proper base change libraries RPLib_FX_EtPBC and
RPLib_FX_EtPBCB (projective line and iterated projective-line bundles). Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_Exc =====
section

/-!
# S4-EtCompact, part 5: the excision sequence (compact supports, subset model)

On an ambient scheme `P` (the compactification), cohomology with compact supports of the
locally closed set `W ∩ Vᶜ` (`W, V` open) is `HcWV W V F n := H^n(P, cutWV W V F)`.
For opens `V ≤ V'` the set `S = W ∩ Vᶜ` splits into the relatively open `U = (W ⊓ V') ∩ Vᶜ`
and the relatively closed `Z = W ∩ V'ᶜ`, and
`0 ⟶ cutWV (W ⊓ V') V F ⟶ cutWV W V F ⟶ cutWV W V' F ⟶ 0`
is short exact (checked on stalks). Hence the **excision long exact sequence**
`… ⟶ H^n_c(U) ⟶ H^n_c(S) ⟶ H^n_c(Z) ⟶ H^(n+1)_c(U) ⟶ …` (E0Probe P2a).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}}

variable {Λ} (W : X.Opens) {V V' : X.Opens} (h : V ≤ V') (F : EtSh Λ X)

theorem epi_excComplex_g : Epi (excComplex W h F).g := by
  rw [epi_iff_stalk]
  intro x
  by_cases hW : x ∈ W
  · by_cases hV' : x ∈ V'
    · exact (isZero_stalk_cutWV_of_mem F _ (mem_center_geomPtAt hW)
        (mem_center_geomPtAt hV')).epi _
    · have : IsIso (((geomPtAt x).stalkF Λ).map (excComplex W h F).g) :=
        isIso_stalk_openCutMap W (quotCutLe h F) _ (mem_center_geomPtAt hW)
          (isIso_stalk_quotCutLe h F _ (not_mem_center_geomPtAt hV'))
      exact IsIso.epi_of_iso _
  · exact (isZero_stalk_cutWV_of_not_mem F _ (not_mem_center_geomPtAt hW)).epi _

end RamanujanPetersson.EtCompact

end

end


