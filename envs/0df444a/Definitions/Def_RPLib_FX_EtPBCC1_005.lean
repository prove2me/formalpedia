-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC1_005
-- name    : RPLib_FX_EtPBCC1_005
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T18:46:14.662403+00:00
-- url     : https://prove2.me/theorems/226effec-e4df-5029-b571-c18c5b106484
-- title:
--   Proper base change with compact supports, library file 005
-- statement:
--   File 005 of the library for proper base change with compact supports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
--   * `S4.Def_RP_EtPBC_C1_PsiB`: S4-EtPBC-C1, part 14b: `pbcEquivSucc` on the germ of a cocycle class
--
--   **Formalization note.** One file of a library formalizing the canonical proper base change isomorphism for étale cohomology with compact supports: for $f : X \to S$ with a compactification $X \xrightarrow{j} Z \xrightarrow{i} P \xrightarrow{\bar f} S$ ($j$ an open immersion, $i$ a closed immersion, $\bar f$ proper), $R^q f_! = R^q \bar f_* \circ i_* j_!$, and a geometric point $s$ of $S$ at which $\bar f$ satisfies proper base change, the stalk $(R^q f_! F)_s$ is identified with $H^q_c(X_s, F|_{X_s})$ by a named isomorphism that is natural in the sheaf $F$ of $\Lambda$-modules (built from the base change morphism of the fibre square). It builds on the proper base change libraries for the projective line (`RPLib_FX_EtPBC_*`) and for iterated projective-line bundles (`RPLib_FX_EtPBCB_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre) and Exposé XVII, 5.2.8 (P. Deligne, changement de base pour R f_!), Lecture Notes in Math. 269, 270, 305, Springer (1972-73); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2-§3

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCC1_003

/-!
# Proper base change with compact supports, library file 005

Declarations of the formalization of the canonical proper base change isomorphism for compactly
supported étale cohomology (R^q f_! F)_s ≃ H^q_c(X_s, F|X_s), natural in F, for compactified X ⟶ S
(the base change morphism, its stalk form and its naturality), re-hosted declaration by declaration
from the library modules below, on top of the proper base change libraries RPLib_FX_EtPBC and
RPLib_FX_EtPBCB (projective line and iterated projective-line bundles). Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
* `S4.Def_RP_EtPBC_C1_PsiB`: S4-EtPBC-C1, part 14b: `pbcEquivSucc` on the germ of a cocycle class
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

theorem mono_excComplex_f : Mono (excComplex W h F).f := by
  rw [mono_iff_stalk]
  intro x
  by_cases hx : x ∈ W ⊓ V'
  · have : IsIso (((geomPtAt x).stalkF Λ).map (excComplex W h F).f) :=
      isIso_stalk_openCutLe (inf_le_left : W ⊓ V' ≤ W) (quotCut Λ V F) _ (mem_center_geomPtAt hx)
    exact IsIso.mono_of_iso _
  · exact (isZero_stalk_cutWV_of_not_mem F _ (not_mem_center_geomPtAt hx)).mono _

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtPBC_C1_PsiB =====
section

/-!
# S4-EtPBC-C1, part 14b: `pbcEquivSucc` on the germ of a cocycle class

* **`pbcSucc_germ`**: `pbcEquivSucc` of the germ of `[cyc]` is `J.extMk (u_v ≫ ι^* ĉ ≫ lift)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtCompact.PtSec

universe u

set_option backward.isDefEq.respectTransparency false

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S) {F : EtSh Λ P}
  (I : InjectiveResolution F) (J : InjectiveResolution ((pull (fibι g s) Λ).obj F)) (p : ℕ)

/-- **`pbcEquivSucc` on the germ of a cocycle class.** -/
theorem pbcSucc_germ (hI : BCInj Λ g s (p + 1) F) (hS : BCSurj Λ g s (p + 1) F) (j : Nbhd s)
    (cyc : ((secCx Λ I.cocomplex ((etPull g).obj j.1)).sc (p + 1)).cycles) :
    pbcEquivSucc Λ g s I p hI hS ((stalkRDIso Λ g s I (p + 1)).inv.hom
        ((s.point.toPresheafFiber j.1 j.2 ((preCx Λ g I.cocomplex).homology (p + 1))).hom
          ((preHomologyObjIso Λ g I.cocomplex (p + 1) j.1).inv.hom
            (((secCx Λ I.cocomplex ((etPull g).obj j.1)).sc (p + 1)).homologyπ.hom cyc)))) =
      J.extMk (bcUnit Λ g s j ≫ (pull (fibι g s) Λ).map (freeCocP g I p cyc) ≫
        (liftLc (pull (fibι g s) Λ) I J).f (p + 1)) (p + 1 + 1) rfl (freeCocP_cond g s I J p j cyc) := by
  have e1 : ∀ x, (stalkRDIso Λ g s I (p + 1)).hom.hom ((stalkRDIso Λ g s I (p + 1)).inv.hom x) = x := fun x => by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.inv_hom_id, ModuleCat.hom_id, LinearMap.id_apply]
  refine (congrArg (stalkEquiv s (Q := (preCx Λ g I.cocomplex).homology (p + 1)) (germExt_map Λ g I p) hI hS)
    (e1 _)).trans ?_
  refine (stalkEquivE_apply s (germExt_map Λ g I p) hI hS _).trans ?_
  refine (stalkBC_germ s (germExt_map Λ g I p) j.1 j.2 _).trans ?_
  change (Abelian.Ext.mk₀ (bcUnit Λ g s j)).comp ((germExt Λ g I p j.1 _).mapExactFunctor (pull (fibι g s) Λ))
    (zero_add _) = _
  rw [germExt_cyc g I p j.1 cyc, mapExactFunctor_extMk (pull (fibι g s) Λ) I J (liftLc (pull (fibι g s) Λ) I J)
    (liftLc_f_zero (pull (fibι g s) Λ) I J), InjectiveResolution.mk₀_comp_extMk]

end RamanujanPetersson.EtPBC.C1

end

end


