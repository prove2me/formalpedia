-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC1_010
-- name    : RPLib_FX_EtPBCC1_010
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T18:59:20.639727+00:00
-- url     : https://prove2.me/theorems/8a424935-db3b-55ca-b2d5-a438af3aa181
-- title:
--   Proper base change with compact supports, library file 010
-- statement:
--   File 010 of the library for proper base change with compact supports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_Cpt`: S4-EtCompact, part 9: compactifications, `R^n f_!` and `H^n_c` (O6, first part)
--   * `S4.Def_RP_EtPBC_C1_Psi`: S4-EtPBC-C1, part 15: the comparison `psi_all` for every stalk element
--   * `S4.Def_RP_EtPBC_C1_PbcS`: S4-EtPBC-C1, part 16: the named equivalence `pbcEquivS` (degrees `p + 1`)
--
--   **Formalization note.** One file of a library formalizing the canonical proper base change isomorphism for étale cohomology with compact supports: for $f : X \to S$ with a compactification $X \xrightarrow{j} Z \xrightarrow{i} P \xrightarrow{\bar f} S$ ($j$ an open immersion, $i$ a closed immersion, $\bar f$ proper), $R^q f_! = R^q \bar f_* \circ i_* j_!$, and a geometric point $s$ of $S$ at which $\bar f$ satisfies proper base change, the stalk $(R^q f_! F)_s$ is identified with $H^q_c(X_s, F|_{X_s})$ by a named isomorphism that is natural in the sheaf $F$ of $\Lambda$-modules (built from the base change morphism of the fibre square). It builds on the proper base change libraries for the projective line (`RPLib_FX_EtPBC_*`) and for iterated projective-line bundles (`RPLib_FX_EtPBCB_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre) and Exposé XVII, 5.2.8 (P. Deligne, changement de base pour R f_!), Lecture Notes in Math. 269, 270, 305, Springer (1972-73); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2-§3

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCC1_008

/-!
# Proper base change with compact supports, library file 010

Declarations of the formalization of the canonical proper base change isomorphism for compactly
supported étale cohomology (R^q f_! F)_s ≃ H^q_c(X_s, F|X_s), natural in F, for compactified X ⟶ S
(the base change morphism, its stalk form and its naturality), re-hosted declaration by declaration
from the library modules below, on top of the proper base change libraries RPLib_FX_EtPBC and
RPLib_FX_EtPBCB (projective line and iterated projective-line bundles). Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_Cpt`: S4-EtCompact, part 9: compactifications, `R^n f_!` and `H^n_c` (O6, first part)
* `S4.Def_RP_EtPBC_C1_Psi`: S4-EtPBC-C1, part 15: the comparison `psi_all` for every stalk element
* `S4.Def_RP_EtPBC_C1_PbcS`: S4-EtPBC-C1, part 16: the named equivalence `pbcEquivS` (degrees `p + 1`)
-/

set_option autoImplicit false

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

/-- The boundary map of the `E`-pushed excision sequence. -/
def excEδ (S : Set X) (O : X.Opens) (n : ℕ) :
    H Λ (excE E F S O).X₃ n →+ H Λ (excE E F S O).X₁ (n + 1) :=
  (excE_shortExact E F S O).extClass.postcomp _ rfl

end ExcE

namespace Cpt

variable {X B : Scheme.{u}} {f : X ⟶ B} (c : Cpt f)

variable (Λ) in
/-- **`R^n f_! := R^n fbar_* ∘ i_* j_!`.** -/
def Rshriek (n : ℕ) : EtSh Λ X ⥤ EtSh Λ B :=
  c.ext Λ ⋙ (push c.fbar Λ).rightDerived n

end Cpt

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtPBC_C1_Psi =====
section

/-!
# S4-EtPBC-C1, part 15: the comparison `psi_all` for every stalk element

For `g : P ⟶ S`, a geometric point `s` and `F` on `P`, with `ι : P_s ⟶ P`, `π : P_s ⟶ Spec Ω`:
* `exists_germ`: every element of a stalk is a germ;
* **`psi_all`**: `absRelR J (pbcEquivSucc I y) = stalkSec y ≫ bcMorSq` for every `y` and all injective resolutions
  `I` of `F` and `J` of `ι^* F` (`absRelR` for `π^* ⊣ π_*`): `pbcEquivSucc` is "the base-change morphism of the fibre
  square followed by sections over `Spec Ω`".
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtCompact.PtSec

universe u

set_option backward.isDefEq.respectTransparency false

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S) (F : EtSh Λ P) (p : ℕ)

/-- **The comparison for every element**: `absRelR J (pbcEquivSucc I y) = stalkSec y ≫ bcMorSq`. -/
theorem psi_all (I : InjectiveResolution F) (J : InjectiveResolution ((pull (fibι g s) Λ).obj F))
    (hI : BCInj Λ g s (p + 1) F) (hS : BCSurj Λ g s (p + 1) F)
    (y : (s.stalkF Λ).obj (((push g Λ).rightDerived (p + 1)).obj F)) :
    haveI := unitSh_projective_spec s.Ω Λ
    absRelR (pullAdj (X := fib g s) (pullback.snd g s.pt) Λ) (pullUnit (X := fib g s) Λ (pullback.snd g s.pt)).symm J p
      (pbcEquivSucc Λ g s I p hI hS y) =
      stalkSec s (((push g Λ).rightDerived (p + 1)).obj F) y ≫ bcMorSq Λ (fibι g s) s.pt g (pullback.snd g s.pt)
        (pullback.condition (f := g) (g := s.pt)).symm (p + 1) F := by
  obtain ⟨x, rfl⟩ : ∃ x, (stalkRDIso Λ g s I (p + 1)).inv.hom x = y :=
    ⟨(stalkRDIso Λ g s I (p + 1)).hom.hom y, by
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.hom_inv_id, ModuleCat.hom_id, LinearMap.id_apply]⟩
  obtain ⟨j, z, rfl⟩ := exists_germ s ((preCx Λ g I.cocomplex).homology (p + 1)) x
  obtain ⟨cyc, hc⟩ := (ModuleCat.epi_iff_surjective
    ((secCx Λ I.cocomplex ((etPull g).obj j.1)).sc (p + 1)).homologyπ).1 inferInstance
      ((preHomologyObjIso Λ g I.cocomplex (p + 1) j.1).hom.hom z)
  have hz : z = (preHomologyObjIso Λ g I.cocomplex (p + 1) j.1).inv.hom
      (((secCx Λ I.cocomplex ((etPull g).obj j.1)).sc (p + 1)).homologyπ.hom cyc) := by
    have hc' : ((secCx Λ I.cocomplex ((etPull g).obj j.1)).sc (p + 1)).homologyπ.hom cyc =
        (preHomologyObjIso Λ g I.cocomplex (p + 1) j.1).hom.hom z := hc
    rw [hc', ← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.hom_inv_id, ModuleCat.hom_id, LinearMap.id_apply]
  subst hz
  exact psi_germ g s I J p hI hS j cyc

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_PbcS =====
section

/-!
# S4-EtPBC-C1, part 16: the named equivalence `pbcEquivS` (degrees `p + 1`)

* **`pbcEquivS hI hS : (R^(p+1) g_* F)_s ≃+ H^(p+1)(P_s, ι^* F)`**, the named proper-base-change equivalence
  (`pbcEquivSucc` on the chosen injective resolution);
* **`pbcEquivS_spec`**: its canonical description, `absRelR J (pbcEquivS y) = stalkSec y ≫ bcMorSq` (the base-change
  morphism of the fibre square followed by sections over `Spec Ω`), for every injective resolution `J` of `ι^* F`;
* **`pbcEquivS_eq`**: `pbcEquivS = pbcEquivSucc I` for every injective resolution `I` of `F`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtCompact.PtSec

universe u

set_option backward.isDefEq.respectTransparency false

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S) (F : EtSh Λ P) (p : ℕ)

/-- **Canonical description of `pbcEquivS`**: the base-change morphism of the fibre square followed by sections
over `Spec Ω`, read through `absRelR` (any injective resolution `J` of `ι^* F`). -/
theorem pbcEquivS_spec (J : InjectiveResolution ((pull (fibι g s) Λ).obj F))
    (hI : BCInj Λ g s (p + 1) F) (hS : BCSurj Λ g s (p + 1) F)
    (y : (s.stalkF Λ).obj (((push g Λ).rightDerived (p + 1)).obj F)) :
    haveI := unitSh_projective_spec s.Ω Λ
    absRelR (pullAdj (X := fib g s) (pullback.snd g s.pt) Λ) (pullUnit (X := fib g s) Λ (pullback.snd g s.pt)).symm J p
      (pbcEquivS g s F p hI hS y) =
      stalkSec s (((push g Λ).rightDerived (p + 1)).obj F) y ≫ bcMorSq Λ (fibι g s) s.pt g (pullback.snd g s.pt)
        (pullback.condition (f := g) (g := s.pt)).symm (p + 1) F :=
  psi_all g s F p (injectiveResolution F) J hI hS y

end RamanujanPetersson.EtPBC.C1

end

end


