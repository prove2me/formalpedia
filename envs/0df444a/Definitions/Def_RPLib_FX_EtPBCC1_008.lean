-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC1_008
-- name    : RPLib_FX_EtPBCC1_008
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T18:55:03.294236+00:00
-- url     : https://prove2.me/theorems/e94c5d05-1e94-50f8-a05b-966fb545cd7b
-- title:
--   Proper base change with compact supports, library file 008
-- statement:
--   File 008 of the library for proper base change with compact supports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
--   * `S4.Def_RP_EtCompact_Cpt`: S4-EtCompact, part 9: compactifications, `R^n f_!` and `H^n_c` (O6, first part)
--   * `S4.Def_RP_EtPBC_C1_PsiEq`: S4-EtPBC-C1, part 14d: `absRelR` and the comparison `psi_germ` on germs
--   * `S4.Def_RP_EtPBC_C1_PbcC`: S4-EtPBC-C1, part 20b: the named equivalence `pbcEquivC` for `R^q f_!`
--
--   **Formalization note.** One file of a library formalizing the canonical proper base change isomorphism for étale cohomology with compact supports: for $f : X \to S$ with a compactification $X \xrightarrow{j} Z \xrightarrow{i} P \xrightarrow{\bar f} S$ ($j$ an open immersion, $i$ a closed immersion, $\bar f$ proper), $R^q f_! = R^q \bar f_* \circ i_* j_!$, and a geometric point $s$ of $S$ at which $\bar f$ satisfies proper base change, the stalk $(R^q f_! F)_s$ is identified with $H^q_c(X_s, F|_{X_s})$ by a named isomorphism that is natural in the sheaf $F$ of $\Lambda$-modules (built from the base change morphism of the fibre square). It builds on the proper base change libraries for the projective line (`RPLib_FX_EtPBC_*`) and for iterated projective-line bundles (`RPLib_FX_EtPBCB_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre) and Exposé XVII, 5.2.8 (P. Deligne, changement de base pour R f_!), Lecture Notes in Math. 269, 270, 305, Springer (1972-73); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2-§3

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCC1_004
import Definitions.Def_RPLib_FX_EtPBCC1_005
import Definitions.Def_RPLib_FX_EtPBCC1_006
import Definitions.Def_RPLib_FX_EtPBCC1_007

/-!
# Proper base change with compact supports, library file 008

Declarations of the formalization of the canonical proper base change isomorphism for compactly
supported étale cohomology (R^q f_! F)_s ≃ H^q_c(X_s, F|X_s), natural in F, for compactified X ⟶ S
(the base change morphism, its stalk form and its naturality), re-hosted declaration by declaration
from the library modules below, on top of the proper base change libraries RPLib_FX_EtPBC and
RPLib_FX_EtPBCB (projective line and iterated projective-line bundles). Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
* `S4.Def_RP_EtCompact_Cpt`: S4-EtCompact, part 9: compactifications, `R^n f_!` and `H^n_c` (O6, first part)
* `S4.Def_RP_EtPBC_C1_PsiEq`: S4-EtPBC-C1, part 14d: `absRelR` and the comparison `psi_germ` on germs
* `S4.Def_RP_EtPBC_C1_PbcC`: S4-EtPBC-C1, part 20b: the named equivalence `pbcEquivC` for `R^q f_!`
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

/-- **The excision short exact sequence** `0 → F_U → F_S → F_Z → 0`. -/
theorem excComplex_shortExact : (excComplex W h F).ShortExact :=
  ShortComplex.ShortExact.mk' (exact_excComplex W h F) (mono_excComplex_f W h F)
    (epi_excComplex_g W h F)

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_Cpt =====
section

/-!
# S4-EtCompact, part 9: compactifications, `R^n f_!` and `H^n_c` (O6, first part)

A compactification `c : Cpt f` of `f : X ⟶ B` is an open immersion `j : X ⟶ Z`, a closed immersion
`i : Z ⟶ P` and a proper `fbar : P ⟶ B` with `j ≫ i ≫ fbar = f`. Then
* `c.ext = j_! ⋙ i_*` (exact), `R^n f_! := R^n fbar_* ∘ c.ext` (`Functor.rightDerived`);
* `H^n_c(S, F) := H^n(P, c.ext (cut S F))` for `S ⊆ X` locally closed (`c.Hc`), with the excision
  long exact sequence (`excE_exact₁/₂/₃` for any exact `E`, here `E = c.ext`);
* independence of the compactification along a closed change of ambient `ι : P ⟶ P'`
  (`Cpt.pushAlong`, `Cpt.hcPushAlong`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ]

section ExcE

variable {X Y : Scheme.{u}} (E : EtSh Λ X ⥤ EtSh Λ Y) [E.Additive] [PreservesFiniteLimits E]
  [PreservesFiniteColimits E] (F : EtSh Λ X)

theorem excE_shortExact (S : Set X) (O : X.Opens) : (excE E F S O).ShortExact :=
  (excComplex_shortExact (cutOpen S) (le_sup_left : cutCompl S ≤ cutCompl S ⊔ O) F).map_of_exact E

end ExcE

namespace Cpt

end Cpt

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtPBC_C1_PsiEq =====
section

/-!
# S4-EtPBC-C1, part 14d: `absRelR` and the comparison `psi_germ` on germs

* **`absRelR adj e I p : Ext^(p+1)(X, Y) ≃+ Hom(A, R^(p+1) R Y)`** (`A` projective): `absRelGen` followed by
  `H^(p+1)(R I) ≅ R^(p+1) R Y`, stated generically (one form for every instance; `absRelR_apply`);
* **`psi_germ`**: `absRelR (pbcEquivSucc y) = stalkSec y ≫ bcMorSq` for every germ `y` of a cocycle class
  (`absRelR` for `π^* ⊣ π_*`, `π : P_s ⟶ Spec Ω`).

Kernel note: `absRelR` is used directly (no sheaf-level wrapper): a wrapper `absRelU := absRelR ..` with
`homIsoRight` at the sheaf level, or an `absRelU_apply` lemma, cost 8-13 s of kernel time each.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtCompact.PtSec

section GenR

universe w v₁ v₂ u₁ u₂

end GenR

universe u

set_option backward.isDefEq.respectTransparency false

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S) {F : EtSh Λ P}
  (I : InjectiveResolution F) (J : InjectiveResolution ((pull (fibι g s) Λ).obj F)) (p : ℕ)

/-- **The comparison on germs**: `absRelR (pbcEquivSucc y) = stalkSec y ≫ bcMorSq` (for `π^* ⊣ π_*`). -/
theorem psi_germ (hI : BCInj Λ g s (p + 1) F) (hS : BCSurj Λ g s (p + 1) F) (j : Nbhd s)
    (cyc : ((secCx Λ I.cocomplex ((etPull g).obj j.1)).sc (p + 1)).cycles) :
    haveI := unitSh_projective_spec s.Ω Λ
    absRelR (pullAdj (X := fib g s) (pullback.snd g s.pt) Λ) (pullUnit (X := fib g s) Λ (pullback.snd g s.pt)).symm J p
      (pbcEquivSucc Λ g s I p hI hS ((stalkRDIso Λ g s I (p + 1)).inv.hom
        ((s.point.toPresheafFiber j.1 j.2 ((preCx Λ g I.cocomplex).homology (p + 1))).hom
          ((preHomologyObjIso Λ g I.cocomplex (p + 1) j.1).inv.hom
            (((secCx Λ I.cocomplex ((etPull g).obj j.1)).sc (p + 1)).homologyπ.hom cyc))))) =
      stalkSec s (((push g Λ).rightDerived (p + 1)).obj F) ((stalkRDIso Λ g s I (p + 1)).inv.hom
        ((s.point.toPresheafFiber j.1 j.2 ((preCx Λ g I.cocomplex).homology (p + 1))).hom
          ((preHomologyObjIso Λ g I.cocomplex (p + 1) j.1).inv.hom
            (((secCx Λ I.cocomplex ((etPull g).obj j.1)).sc (p + 1)).homologyπ.hom cyc)))) ≫
        bcMorSq Λ (fibι g s) s.pt g (pullback.snd g s.pt) (pullback.condition (f := g) (g := s.pt)).symm (p + 1) F := by
  have := unitSh_projective_spec s.Ω Λ
  have hb : bcMorSq Λ (fibι g s) s.pt g (pullback.snd g s.pt) (pullback.condition (f := g) (g := s.pt)).symm
      (p + 1) F = bcMorRes (push g Λ) (push (X := fib g s) (pullback.snd g s.pt) Λ) (pull (fibι g s) Λ)
        (pull s.pt Λ) (bcCell Λ (fibι g s) s.pt g (pullback.snd g s.pt) (pullback.condition (f := g) (g := s.pt)).symm)
        (p + 1) I J :=
    bcMorGen_eq _ _ _ _ _ (p + 1) I J
  rw [absRelR_apply, pbcSucc_germ g s I J p hI hS j cyc, stalkSec_rd g s p I j.2 cyc, hb]
  exact psi_core g s I J p j cyc

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

/-- `H^n(Z, -)` on a commutative square of sheaves whose sides are isomorphisms. -/
theorem hiso_hmap {Λ : Type u} [CommRing Λ] {Z : Scheme.{u}} {G G' K K' : EtSh Λ Z} (a : G ⟶ K) (b : G' ⟶ K')
    (e : G ≅ G') (e' : K ≅ K') (w : a ≫ e'.hom = e.hom ≫ b) (n : ℕ) (x : H Λ G n) :
    Hiso Λ e' n (Hmap Λ a n x) = Hmap Λ b n (Hiso Λ e n x) := by
  simp only [Hiso, extIsoRight_apply, Hmap_apply, Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀, w]

section Shriek

end Shriek

end RamanujanPetersson.EtPBC.C1

end

end


