-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC1_001
-- name    : RPLib_FX_EtPBCC1_001
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T18:40:19.405625+00:00
-- url     : https://prove2.me/theorems/bd1162a5-c74e-5ef3-801f-b7f60bb0c50d
-- title:
--   Proper base change with compact supports, library file 001
-- statement:
--   File 001 of the library for proper base change with compact supports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtSheaves_CutSet`: S4-EtSheaves, part 21: `F_S` for a subset `S`
--   * `S4.Def_RP_EtCompact_CutMap`: S4-EtCompact, part 4: maps between cut sheaves
--   * `S4.Def_RP_EtSheaves_ClosedFF`: S4-EtSheaves, part 15: the cut sequence `0 → j_! j^* F → F → i_* i^* F → 0`
--   * `S4.Def_RP_EtCompact_Coh`: S4-EtCompact, part 3: etale cohomology as `Ext` from the constant sheaf
--   * `S4.Def_RP_EtCompact_Cpt`: S4-EtCompact, part 9: compactifications, `R^n f_!` and `H^n_c` (O6, first part)
--   * `S4.Def_RP_EtCompact_Pt`: S4-EtCompact, part 14: cohomology of a separably closed point (O6d / O7 in dimension 0)
--   * `S4.Def_RP_EtCompact_PushBC`: S4-EtCompact (b2'): pushforward commutes with restriction to an etale chart
--   * `S4.Def_RP_EtCompact_AbsRel`: S4-EtCompact, part 15: absolute = relative cohomology over a base with projective unit (O6d)
--   * `S4.Def_RP_EtCompact_ChAmb`: S4-EtCompact, part 7: closed change of ambient (E0Probe P2d)
--   * `S4.Def_RP_EtLeray_ResDer`: S4-EtLeray, part 8: étale restriction commutes with `R^q h_*`
--   * `S4.Def_RP_EtPBC_B_BCc`: S4-EtPBC-B, D1a: base change for extension by zero and for closed push-forward
--   * `S4.Def_RP_EtPBC_B_Rsh`: S4-EtPBC-B, D1: stalks of `R^q f_!` are the compactly supported cohomology of the geometric fibre
--   * `S4.Def_RP_EtPBC_C1_Desc`: S4-EtPBC-C1, part 1: lifting a resolution into an injective resolution
--   * `S4.Def_RP_EtPBC_C1_Gen`: S4-EtPBC-C1, part 2: the generic degree-`q` base change morphism
--   * `S4.Def_RP_EtPBC_C1_HomBk`: S4-EtPBC-C1, part 10: homology bookkeeping for exact functors
--   * `S4.Def_RP_EtPBC_C1_ClsGen`: S4-EtPBC-C1, part 13: classes of cocycles under the base change morphism and `absRelGen` (generic)
--   * `S4.Def_RP_EtPBC_C1_Mor`: S4-EtPBC-C1, part 3: the base change morphism `g^* R^q f_! F ⟶ R^q f'_! g'^* F`
--   * `S4.Def_RP_EtPBC_C1_SecA`: S4-EtPBC-C1, part 7: `bcCell` on pulled-back sections
--   * `S4.Def_RP_EtPBC_C1_StalkSec`: S4-EtPBC-C1, part 9: stalks as global sections of the pullback to the geometric point
--   * `S4.Def_RP_EtPBC_C1_Coc`: S4-EtPBC-C1, part 11: the cochain identity behind `pbcEquiv`
--   * `S4.Def_RP_EtPBC_C1_ExtMap`: S4-EtPBC-C1, part 6: `Ext.mapExactFunctor` of an `extMk` class
--   * `S4.Def_RP_EtPBC_C1_StkHom`: S4-EtPBC-C1, part 12: a cocycle class in the stalk of `R^(p+1) g_* F`
--   * `S4.Def_RP_EtPBC_C1_PtProj`: S4-EtPBC-C1, part 8: `Λ` is projective on `Spec Ω`, `Ω` separably closed
--   * `S4.Def_RP_EtPBC_C1_PsiA`: S4-EtPBC-C1, part 14a: generic glue in `coc_gen` shape; the section cocycle on `P`
--
--   **Formalization note.** One file of a library formalizing the canonical proper base change isomorphism for étale cohomology with compact supports: for $f : X \to S$ with a compactification $X \xrightarrow{j} Z \xrightarrow{i} P \xrightarrow{\bar f} S$ ($j$ an open immersion, $i$ a closed immersion, $\bar f$ proper), $R^q f_! = R^q \bar f_* \circ i_* j_!$, and a geometric point $s$ of $S$ at which $\bar f$ satisfies proper base change, the stalk $(R^q f_! F)_s$ is identified with $H^q_c(X_s, F|_{X_s})$ by a named isomorphism that is natural in the sheaf $F$ of $\Lambda$-modules (built from the base change morphism of the fibre square). It builds on the proper base change libraries for the projective line (`RPLib_FX_EtPBC_*`) and for iterated projective-line bundles (`RPLib_FX_EtPBCB_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre) and Exposé XVII, 5.2.8 (P. Deligne, changement de base pour R f_!), Lecture Notes in Math. 269, 270, 305, Springer (1972-73); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2-§3

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_20
import Definitions.Def_RPLib_FX_EtPBCB_003

/-!
# Proper base change with compact supports, library file 001

Declarations of the formalization of the canonical proper base change isomorphism for compactly
supported étale cohomology (R^q f_! F)_s ≃ H^q_c(X_s, F|X_s), natural in F, for compactified X ⟶ S
(the base change morphism, its stalk form and its naturality), re-hosted declaration by declaration
from the library modules below, on top of the proper base change libraries RPLib_FX_EtPBC and
RPLib_FX_EtPBCB (projective line and iterated projective-line bundles). Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtSheaves_CutSet`: S4-EtSheaves, part 21: `F_S` for a subset `S`
* `S4.Def_RP_EtCompact_CutMap`: S4-EtCompact, part 4: maps between cut sheaves
* `S4.Def_RP_EtSheaves_ClosedFF`: S4-EtSheaves, part 15: the cut sequence `0 → j_! j^* F → F → i_* i^* F → 0`
* `S4.Def_RP_EtCompact_Coh`: S4-EtCompact, part 3: etale cohomology as `Ext` from the constant sheaf
* `S4.Def_RP_EtCompact_Cpt`: S4-EtCompact, part 9: compactifications, `R^n f_!` and `H^n_c` (O6, first part)
* `S4.Def_RP_EtCompact_Pt`: S4-EtCompact, part 14: cohomology of a separably closed point (O6d / O7 in dimension 0)
* `S4.Def_RP_EtCompact_PushBC`: S4-EtCompact (b2'): pushforward commutes with restriction to an etale chart
* `S4.Def_RP_EtCompact_AbsRel`: S4-EtCompact, part 15: absolute = relative cohomology over a base with projective unit (O6d)
* `S4.Def_RP_EtCompact_ChAmb`: S4-EtCompact, part 7: closed change of ambient (E0Probe P2d)
* `S4.Def_RP_EtLeray_ResDer`: S4-EtLeray, part 8: étale restriction commutes with `R^q h_*`
* `S4.Def_RP_EtPBC_B_BCc`: S4-EtPBC-B, D1a: base change for extension by zero and for closed push-forward
* `S4.Def_RP_EtPBC_B_Rsh`: S4-EtPBC-B, D1: stalks of `R^q f_!` are the compactly supported cohomology of the geometric fibre
* `S4.Def_RP_EtPBC_C1_Desc`: S4-EtPBC-C1, part 1: lifting a resolution into an injective resolution
* `S4.Def_RP_EtPBC_C1_Gen`: S4-EtPBC-C1, part 2: the generic degree-`q` base change morphism
* `S4.Def_RP_EtPBC_C1_HomBk`: S4-EtPBC-C1, part 10: homology bookkeeping for exact functors
* `S4.Def_RP_EtPBC_C1_ClsGen`: S4-EtPBC-C1, part 13: classes of cocycles under the base change morphism and `absRelGen` (generic)
* `S4.Def_RP_EtPBC_C1_Mor`: S4-EtPBC-C1, part 3: the base change morphism `g^* R^q f_! F ⟶ R^q f'_! g'^* F`
* `S4.Def_RP_EtPBC_C1_SecA`: S4-EtPBC-C1, part 7: `bcCell` on pulled-back sections
* `S4.Def_RP_EtPBC_C1_StalkSec`: S4-EtPBC-C1, part 9: stalks as global sections of the pullback to the geometric point
* `S4.Def_RP_EtPBC_C1_Coc`: S4-EtPBC-C1, part 11: the cochain identity behind `pbcEquiv`
* `S4.Def_RP_EtPBC_C1_ExtMap`: S4-EtPBC-C1, part 6: `Ext.mapExactFunctor` of an `extMk` class
* `S4.Def_RP_EtPBC_C1_StkHom`: S4-EtPBC-C1, part 12: a cocycle class in the stalk of `R^(p+1) g_* F`
* `S4.Def_RP_EtPBC_C1_PtProj`: S4-EtPBC-C1, part 8: `Λ` is projective on `Spec Ω`, `Ω` separably closed
* `S4.Def_RP_EtPBC_C1_PsiA`: S4-EtPBC-C1, part 14a: generic glue in `coc_gen` shape; the section cocycle on `P`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtSheaves_CutSet =====
section

/-!
# S4-EtSheaves, part 21: `F_S` for a subset `S`

For an open `W`: `openCut W F = j_! j^* F` with `openCutι : F_W ⟶ F`. For the closed complement of an open `V`:
`quotCut V F = coker (F_V ⟶ F)` (`= i_* i^* F`, part 19). For any `S`: `cut S F = (F_{closure S})_O` with
`O = interior (coborder S)` (`= coborder S`, open, when `S` is locally closed). For `S` locally closed the stalk of
`cut S F` is `F_s` over `S` (`cutStalkIso`) and zero elsewhere (`isZero_stalk_cut`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Topology

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}}

/-- The open `interior (coborder S)` (`= coborder S` for locally closed `S`). -/
def cutOpen (S : Set X) : X.Opens := ⟨interior (coborder S), isOpen_interior⟩

/-- The open `(closure S)ᶜ`. -/
def cutCompl (S : Set X) : X.Opens := ⟨(closure S)ᶜ, isClosed_closure.isOpen_compl⟩

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtCompact_CutMap =====
section

/-!
# S4-EtCompact, part 4: maps between cut sheaves

For opens `W' ≤ W` the inclusion `j_{W'!} G|_{W'} ⟶ j_{W!} G|_W` (`openCutLe`, the lift of
`openCutι W'` through the monomorphism `openCutι W`), for opens `V ≤ V'` the quotient map
`G / j_{V!} ⟶ G / j_{V'!}` (`quotCutLe`), functoriality `openCutMap`, and their stalks.
`cutWV W V F := j_{W!}(F / j_{V!} F|_V)|_W` is `F` cut to `W ∩ Vᶜ`; its stalks are
`F_x` for `x ∈ W \ V` and `0` otherwise.
All identities are checked on stalks at the points `geomPtAt x`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

/-- The stalk of `openCut W G` at a point of `W` where `G` has zero stalk vanishes. -/
theorem isZero_stalk_openCut_of (W : X.Opens) (G : EtSh Λ X) (s : GeomPt X) (hs : s.center ∈ W)
    (hG : IsZero ((s.stalkF Λ).obj G)) : IsZero ((s.stalkF Λ).obj (openCut Λ W G)) :=
  have := isIso_stalk_openCutι W G s hs
  hG.of_iso (asIso ((s.stalkF Λ).map (openCutι Λ W G)))

section OpenLe

variable {W W' : X.Opens} (h : W' ≤ W)

theorem isIso_stalk_openCutLe (G : EtSh Λ X) (s : GeomPt X) (hs : s.center ∈ W') :
    IsIso ((s.stalkF Λ).map (openCutLe h G)) := by
  have := isIso_stalk_openCutι W G s (h hs)
  have h2 := isIso_stalk_openCutι W' G s hs
  have : IsIso ((s.stalkF Λ).map (openCutLe h G) ≫ (s.stalkF Λ).map (openCutι Λ W G)) := by
    rw [← Functor.map_comp, openCutLe_comp]; exact h2
  exact IsIso.of_isIso_comp_right _ ((s.stalkF Λ).map (openCutι Λ W G))

end OpenLe

section QuotLe

variable {V V' : X.Opens} (h : V ≤ V')

/-- The quotient map `G / j_{V!} ⟶ G / j_{V'!}` for opens `V ≤ V'`. -/
def quotCutLe (G : EtSh Λ X) : quotCut Λ V G ⟶ quotCut Λ V' G :=
  cokernel.desc (openCutι Λ V G) (quotCutπ Λ V' G) (openCutι_comp_quotCutπ h G)

end QuotLe

section OpenMap

variable (W : X.Opens)

theorem isIso_stalk_openCutMap {G G' : EtSh Λ X} (φ : G ⟶ G') (s : GeomPt X) (hs : s.center ∈ W)
    (hφ : IsIso ((s.stalkF Λ).map φ)) : IsIso ((s.stalkF Λ).map (openCutMap W φ)) := by
  have := isIso_stalk_openCutι W G s hs
  have h2 := isIso_stalk_openCutι W G' s hs
  have : IsIso ((s.stalkF Λ).map (openCutMap W φ) ≫ (s.stalkF Λ).map (openCutι Λ W G')) := by
    rw [← Functor.map_comp, openCutMap_comp, Functor.map_comp]; infer_instance
  exact IsIso.of_isIso_comp_right _ ((s.stalkF Λ).map (openCutι Λ W G'))

end OpenMap

variable (Λ) in
/-- `F` cut to `W ∩ Vᶜ`: `j_{W!}(F / j_{V!} F|_V)|_W`. -/
abbrev cutWV (W V : X.Opens) (F : EtSh Λ X) : EtSh Λ X := openCut Λ W (quotCut Λ V F)

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtSheaves_ClosedFF =====
section

/-!
# S4-EtSheaves, part 15: the cut sequence `0 → j_! j^* F → F → i_* i^* F → 0`

Any family of geometric points whose images cover `X` detects zero objects, exactness and
epimorphisms. If base change along `i : Z ⟶ X` is cover-dense and locally full on the small etale
site of `Z` (true for closed immersions, proved separately), then `i_*` is fully faithful, so the
counit `i^* i_* ⟶ 𝟭` is an isomorphism and the stalks of the unit `F ⟶ i_* i^* F` at points of `Z`
are isomorphisms. Checking on the points of `Z` and of the open complement `U` gives the short
exact sequence `0 → j_! j^* F → F → i_* i^* F → 0`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

section Family

end Family

section Pts

end Pts

section CoverDense

variable (Λ : Type u) [CommRing Λ] {Z X : Scheme.{u}} (i : Z ⟶ X)
  [(etPull i).IsCoverDense Z.smallEtaleTopology] [(etPull i).IsLocallyFull Z.smallEtaleTopology]

/-- `i^*` of the unit `F ⟶ i_* i^* F` is an isomorphism. -/
theorem isIso_pull_unit (F : EtSh Λ X) : IsIso ((pull i Λ).map ((pullAdj i Λ).unit.app F)) := by
  have h : IsIso ((pull i Λ).map ((pullAdj i Λ).unit.app F) ≫
      (pullAdj i Λ).counit.app ((pull i Λ).obj F)) := by
    rw [(pullAdj i Λ).left_triangle_components F]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_right _ ((pullAdj i Λ).counit.app ((pull i Λ).obj F))

/-- **Stalks of `F ⟶ i_* i^* F` at points of `Z` are isomorphisms.** -/
theorem isIso_stalk_unit (t : GeomPt Z) (F : EtSh Λ X) :
    IsIso (((t.map i).stalkF Λ).map ((pullAdj i Λ).unit.app F)) := by
  have := isIso_pull_unit Λ i F
  have : IsIso ((pull i Λ ⋙ t.stalkF Λ).map ((pullAdj i Λ).unit.app F)) :=
    Functor.map_isIso (t.stalkF Λ) ((pull i Λ).map ((pullAdj i Λ).unit.app F))
  exact (NatIso.isIso_map_iff (pullStalkIso i Λ t) _).1 this

end CoverDense

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtCompact_Coh =====
section

/-!
# S4-EtCompact, part 3: etale cohomology as `Ext` from the constant sheaf

`H Λ F n := Ext^n(Λ_X, F)` in `EtSh Λ X` (a Grothendieck abelian category, so `Ext` exists and
there are enough injectives). Long exact sequences in `F` are Mathlib's
`Ext.covariant_sequence_exact₁/₂/₃` (E0Probe amendment A7).

Comparisons (via `extAdjEquiv`):
* `closedH`: for a closed immersion `i : Z ⟶ X`, `H^n(X, i_* G) ≃ H^n(Z, G)`;
* `openH`: for an open immersion `j : U ⟶ X`, `Ext^n_X(j_! Λ_U, F) ≃ H^n(U, F|_U)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe w v u

section ExtIso

end ExtIso

variable (Λ : Type u) [CommRing Λ]

/-- Functoriality of `H^n(X, -)`. -/
def Hmap {X : Scheme.{u}} {F G : EtSh Λ X} (φ : F ⟶ G) (n : ℕ) : H Λ F n →+ H Λ G n where
  toFun x := x.comp (Ext.mk₀ φ) (add_zero n)
  map_zero' := by simp
  map_add' x y := by simp [Ext.add_comp]

section Closed

end Closed

section Open

end Open

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

end ExcE

/-- A **compactification** of `f : X ⟶ B`: `X` open in `Z` (via `j`), `Z` closed in `P` (via `i`),
`P` proper over `B`, compatibly with `f`. -/
structure Cpt {X B : Scheme.{u}} (f : X ⟶ B) where
  /-- the ambient proper `B`-scheme -/
  P : Scheme.{u}
  /-- the closure of `X` (any closed subscheme of `P` containing `X` as an open) -/
  Z : Scheme.{u}
  /-- the open immersion `X ⟶ Z` -/
  j : X ⟶ Z
  /-- the closed immersion `Z ⟶ P` -/
  i : Z ⟶ P
  /-- the proper structure map -/
  fbar : P ⟶ B
  isOpenImmersion_j : IsOpenImmersion j
  isClosedImmersion_i : IsClosedImmersion i
  isProper_fbar : IsProper fbar
  comm : j ≫ i ≫ fbar = f

attribute [instance] Cpt.isOpenImmersion_j Cpt.isClosedImmersion_i Cpt.isProper_fbar

namespace Cpt

variable {X B : Scheme.{u}} {f : X ⟶ B} (c : Cpt f)

variable (Λ) in
/-- The extension `i_* j_! : EtSh Λ X ⥤ EtSh Λ P`. -/
abbrev ext : EtSh Λ X ⥤ EtSh Λ c.P := lsh c.j Λ ⋙ push c.i Λ

instance ext_additive : (c.ext Λ).Additive := inferInstance

instance ext_preservesFiniteLimits : PreservesFiniteLimits (c.ext Λ) := inferInstance

instance ext_preservesFiniteColimits : PreservesFiniteColimits (c.ext Λ) := inferInstance

end Cpt

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_Pt =====
section

/-!
# S4-EtCompact, part 14: cohomology of a separably closed point (O6d / O7 in dimension 0)

For a scheme `X` with a point `x0` such that `Spec κ(x0) ⟶ X` is an isomorphism (`X` "is" `Spec κ(x0)`) and
`Gal(κ(x0)^sep/κ(x0))` trivial (e.g. `κ(x0)` separably closed: `gal_subsingleton`), the unit sheaf `Λ_X` is
projective (`unitSh_projective`, via the S4-EtSheaves Galois description `specField_homEquiv`), hence
**`H^n(X, F) = 0` for `n ≥ 1`** (`H_eq_zero_of_point`, `H_subsingleton_of_point`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] (Λ : Type u) [CommRing Λ]

/-- **`Λ_X` is projective** on a point with trivial Galois group. -/
theorem unitSh_projective [Subsingleton (Gal x0)] : Projective (unitSh Λ X) := by
  refine ⟨fun {F G} f e _ => ?_⟩
  let s := (geomPtAt x0).stalkF Λ
  let c := constStalkIso Λ (geomPtAt x0) (ModuleCat.of Λ Λ)
  let g0 : stalk Λ (unitSh Λ X) x0 := c.inv.hom (1 : Λ)
  have hepi : Epi (s.map e) := inferInstance
  obtain ⟨m', hm'⟩ := (ModuleCat.epi_iff_surjective (s.map e)).1 hepi ((s.map f).hom g0)
  let ℓ : stalk Λ (unitSh Λ X) x0 →ₗ[Λ] stalk Λ F x0 :=
    (LinearMap.toSpanSingleton Λ _ m').comp c.hom.hom
  have hℓ : ∀ σ : Gal x0, ℓ ∘ₗ galRep Λ (unitSh Λ X) x0 σ = galRep Λ F x0 σ ∘ₗ ℓ := by
    intro σ
    rw [Subsingleton.elim σ 1, map_one, map_one]
    exact LinearMap.ext fun v => by simp
  have key : ∀ r : Λ, c.hom.hom (c.inv.hom r) = r := fun r => by
    change (c.inv ≫ c.hom).hom r = r
    rw [Iso.inv_hom_id]
    rfl
  have key2 : ∀ v, c.inv.hom (c.hom.hom v) = v := fun v => by
    change (c.hom ≫ c.inv).hom v = v
    rw [Iso.hom_inv_id]
    rfl
  refine ⟨(specField_homEquiv x0 Λ (unitSh Λ X) F).symm ⟨ℓ, hℓ⟩, ?_⟩
  apply (specField_homEquiv x0 Λ (unitSh Λ X) G).injective
  apply Subtype.ext
  rw [specField_homEquiv_apply, specField_homEquiv_apply, Functor.map_comp, ModuleCat.hom_comp]
  have h1 : (s.map ((specField_homEquiv x0 Λ (unitSh Λ X) F).symm ⟨ℓ, hℓ⟩)).hom = ℓ := by
    rw [← specField_homEquiv_apply, Equiv.apply_symm_apply]
  rw [h1]
  apply LinearMap.ext
  intro v
  rw [← key2 v]
  have hv : c.inv.hom (c.hom.hom v) = c.hom.hom v • g0 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  have hg0 : ℓ g0 = m' := by
    change LinearMap.toSpanSingleton Λ _ m' (c.hom.hom (c.inv.hom 1)) = m'
    rw [key, LinearMap.toSpanSingleton_apply, one_smul]
  rw [LinearMap.comp_apply, hv, map_smul, map_smul, map_smul, hg0]
  exact congrArg _ hm'

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_PushBC =====
section

/-!
# S4-EtCompact (b2'): pushforward commutes with restriction to an etale chart

For an etale `c : V ⟶ X` and any `j : U ⟶ X`, put `U' = V ×_X U` with `j' = fst : U' ⟶ V`, `i = snd : U' ⟶ U`.
* `etBC`: `etComp c ⋙ etPull j ≅ etPull j' ⋙ etComp i` (`(W → V → X) ×_X U ≅ W ×_V U'` over `U`);
* **`pushResBC`**: `j_* ⋙ c^* ≅ i^* ⋙ j'_*` on etale sheaves (base change for an etale map);
* `stkBC` (`c` an open immersion): `(j_* G)_(c t) ≅ (j'_* (i^* G))_t`;
* **`stalkEquivBC`** (b2 on a chart): for `c : Spec A ⟶ X`, `j` open, `G` lisse, `t` closed,
  `(j_* G)_(c t) ≃ (j'_* (i^* G))_η̄^{II}`;
* on `P¹`: `p1Chart k s` (`chartA1` or `chartA1'`) and `p1Pt k s` with `p1Chart k s (p1Pt k s) = s` (closed if `s` is),
  `nonempty_pb` (`U ×_{P¹} A¹ ≠ ∅` for `U` nonempty), **`stalkEquivP1`**: `(j_* G)_s̄ ≃ (j'_* (i^* G))_η̄^{II}`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.PushBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

section Gen

variable {V X U : Scheme.{u}} (c : V ⟶ X) [Etale c] (j : U ⟶ X)

omit [Etale c] in
theorem bc_nat {W W' : V.Etale} (φ : W ⟶ W')
    (h1 : (pullback.fst (W.hom ≫ c) j ≫ φ.left) ≫ W'.hom ≫ c = pullback.snd (W.hom ≫ c) j ≫ j)
    (h2 : (pullback.fst W.hom (pullback.fst c j) ≫ φ.left) ≫ W'.hom =
      pullback.snd W.hom (pullback.fst c j) ≫ pullback.fst c j) :
    pullback.lift (pullback.fst (W.hom ≫ c) j ≫ φ.left) (pullback.snd (W.hom ≫ c) j) h1 ≫
        (pullbackRightPullbackFstIso c j W'.hom).inv =
      (pullbackRightPullbackFstIso c j W.hom).inv ≫
        pullback.lift (pullback.fst W.hom (pullback.fst c j) ≫ φ.left)
          (pullback.snd W.hom (pullback.fst c j)) h2 := by
  have hw : φ.left ≫ W'.hom = W.hom := MorphismProperty.Over.w φ
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [pullbackRightPullbackFstIso_inv_fst, pullback.lift_fst, pullback.lift_fst,
      pullbackRightPullbackFstIso_inv_fst_assoc]
  · apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [pullbackRightPullbackFstIso_inv_snd_fst, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
        pullbackRightPullbackFstIso_inv_snd_fst, Category.assoc, hw]
    · simp only [Category.assoc]
      rw [pullbackRightPullbackFstIso_inv_snd_snd, pullback.lift_snd, pullback.lift_snd_assoc,
        pullbackRightPullbackFstIso_inv_snd_snd]

/-- **Base change of etale `V`-schemes**: `(W → V → X) ×_X U ≅ W ×_V (V ×_X U)` over `U`. -/
def etBC : etComp c ⋙ etPull j ≅ etPull (pullback.fst c j) ⋙ etComp (pullback.snd c j) :=
  NatIso.ofComponents (fun W => MorphismProperty.Over.isoMk (pullbackRightPullbackFstIso c j W.hom).symm
      (pullbackRightPullbackFstIso_inv_snd_snd c j W.hom)) (by
    intro W W' φ
    refine MorphismProperty.Over.Hom.ext ?_
    exact bc_nat c j φ _ _)

variable (Λ : Type u) [CommRing Λ]

/-- **`j_* ⋙ c^* ≅ i^* ⋙ j'_*`** for an etale `c` (with `i = snd`, `j' = fst`). -/
def pushResBC : push j Λ ⋙ res c Λ ≅ res (pullback.snd c j) Λ ⋙ push (pullback.fst c j) Λ :=
  have : (etPull (pullback.fst c j) ⋙ etComp (pullback.snd c j)).IsContinuous V.smallEtaleTopology
      U.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ (pullback c j).smallEtaleTopology _
  Functor.sheafPushforwardContinuousComp' (etBC c j) (A := ModuleCat.{u} Λ) (J := V.smallEtaleTopology)
      (K := X.smallEtaleTopology) (L := U.smallEtaleTopology) ≪≫
    (Functor.sheafPushforwardContinuousComp' (F := etPull (pullback.fst c j)) (G := etComp (pullback.snd c j))
      (Iso.refl _) (A := ModuleCat.{u} Λ) (J := V.smallEtaleTopology) (K := (pullback c j).smallEtaleTopology)
      (L := U.smallEtaleTopology)).symm

end Gen

section Chart

end Chart

section P1

end P1

end RamanujanPetersson.EtCompact.PushBC

end

end

-- ===== S4.Def_RP_EtCompact_AbsRel =====
section

/-!
# S4-EtCompact, part 15: absolute = relative cohomology over a base with projective unit (O6d)

Generic part: for an adjunction `L ⊣ R` of abelian categories, `R` additive, a projective `A` with
`L A ≅ X`, and an injective resolution `I` of `Y`, the cocycle description of `Ext` (Mathlib's
`InjectiveResolution.extMk`) and the adjunction give
`absRelGen : Ext X Y (p + 1) ≃+ (A ⟶ H^(p+1)(R I))` (`exists_boundary_of_projective`: projective objects see
coboundaries).

Sheaves: for `g : P ⟶ B` with `Λ_B` projective (e.g. `B` a separably closed point, `Def_RP_EtCompact_Pt`),
**`absRelEquiv : H^(p+1)(P, G) ≃+ Hom(Λ_B, R^(p+1) g_* G)`** and `absRelEquiv₀ : H^0(P, G) ≃+ Hom(Λ_B, R^0 g_* G)`:
absolute cohomology of `P` is the global sections of the relative cohomology over `B`.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact

section Generic

universe w v₁ u₁ v₂ u₂

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- **Projective objects see coboundaries**: a cocycle `A ⟶ K^(p+1)` that vanishes in homology is a
coboundary. -/
theorem exists_boundary_of_projective (K : CochainComplex D ℕ) {A : D} [Projective A] (p : ℕ)
    (f : A ⟶ K.X (p + 1)) (hf : f ≫ K.d (p + 1) (p + 1 + 1) = 0)
    (h : K.liftCycles f (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) hf ≫ K.homologyπ (p + 1) = 0) :
    ∃ g : A ⟶ K.X p, g ≫ K.d p (p + 1) = f := by
  let S : ShortComplex D := ShortComplex.mk (K.toCycles p (p + 1)) (K.homologyπ (p + 1))
    (K.toCycles_comp_homologyπ p (p + 1))
  have hS : S.Exact := S.exact_of_g_is_cokernel (K.homologyIsCokernel p (p + 1) (CochainComplex.prev_nat_succ p))
  refine ⟨hS.liftFromProjective (K.liftCycles f (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) hf) h, ?_⟩
  have h2 := hS.liftFromProjective_comp (K.liftCycles f (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) hf) h
  rw [← K.toCycles_i p (p + 1), ← Category.assoc]
  change (hS.liftFromProjective _ h ≫ S.f) ≫ K.iCycles (p + 1) = f
  rw [h2, K.liftCycles_i]

/-- Two cocycles differing by a coboundary have the same class. -/
theorem liftCycles_homologyπ_congr (K : CochainComplex D ℕ) {A : D} (p : ℕ) {a b : A ⟶ K.X (p + 1)}
    (ha : a ≫ K.d (p + 1) (p + 1 + 1) = 0) (hb : b ≫ K.d (p + 1) (p + 1 + 1) = 0) (g : A ⟶ K.X p)
    (hab : a = b + g ≫ K.d p (p + 1)) :
    K.liftCycles a (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) ha ≫ K.homologyπ (p + 1) =
      K.liftCycles b (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) hb ≫ K.homologyπ (p + 1) := by
  have hgd : (g ≫ K.d p (p + 1)) ≫ K.d (p + 1) (p + 1 + 1) = 0 := by simp
  have e : K.liftCycles a (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) ha =
      K.liftCycles b (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) hb +
        K.liftCycles (g ≫ K.d p (p + 1)) (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) hgd := by
    rw [← cancel_mono (K.iCycles (p + 1)), Preadditive.add_comp, K.liftCycles_i, K.liftCycles_i,
      K.liftCycles_i, hab]
  rw [e, Preadditive.add_comp, K.liftCycles_homologyπ_eq_zero_of_boundary _ _ _ g rfl, add_zero]

theorem liftCycles_eq_of_eq (K : CochainComplex D ℕ) {A : D} (i j : ℕ) (hj : (ComplexShape.up ℕ).next i = j)
    {a b : A ⟶ K.X i} (h : a = b) (ha : a ≫ K.d i j = 0) (hb : b ≫ K.d i j = 0) :
    K.liftCycles a j hj ha = K.liftCycles b j hj hb := by
  subst h
  rfl

theorem liftCycles_add (K : CochainComplex D ℕ) {A : D} (p : ℕ) {a b : A ⟶ K.X (p + 1)}
    (ha : a ≫ K.d (p + 1) (p + 1 + 1) = 0) (hb : b ≫ K.d (p + 1) (p + 1 + 1) = 0)
    (hab : (a + b) ≫ K.d (p + 1) (p + 1 + 1) = 0) :
    K.liftCycles (a + b) (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) hab =
      K.liftCycles a (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) ha +
        K.liftCycles b (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) hb := by
  rw [← cancel_mono (K.iCycles (p + 1)), Preadditive.add_comp, K.liftCycles_i, K.liftCycles_i,
    K.liftCycles_i]

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
  {L : D ⥤ C} {R : C ⥤ D} [R.Additive] (adj : L ⊣ R)
  {A : D} {X : C} (e : L.obj A ≅ X) {Y : C} (I : InjectiveResolution Y)

/-- The complex `R I^•`. -/
abbrev RI : CochainComplex D ℕ := (R.mapHomologicalComplex _).obj I.cocomplex

/-- `X ⟶ I^n` as `A ⟶ R I^n`. -/
def flat {n : ℕ} (f : X ⟶ I.cocomplex.X n) : A ⟶ (RI I (R := R)).X n :=
  adj.homEquiv _ _ (e.hom ≫ f)

/-- `A ⟶ R I^n` as `X ⟶ I^n`. -/
def unflat {n : ℕ} (h : A ⟶ (RI I (R := R)).X n) : X ⟶ I.cocomplex.X n :=
  e.inv ≫ (adj.homEquiv _ _).symm h

theorem flat_unflat {n : ℕ} (h : A ⟶ (RI I (R := R)).X n) : flat adj e I (unflat adj e I h) = h := by
  unfold flat unflat
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact (adj.homEquiv _ _).apply_symm_apply h

theorem flat_injective {n : ℕ} : Function.Injective (flat adj e I (n := n)) := by
  intro f f' hff
  have := (adj.homEquiv _ _).injective hff
  simpa using this

theorem flat_comp {n m : ℕ} (f : X ⟶ I.cocomplex.X n) :
    flat adj e I (f ≫ I.cocomplex.d n m) = flat adj e I f ≫ (RI I (R := R)).d n m := by
  unfold flat
  rw [← Category.assoc, adj.homEquiv_naturality_right]
  rfl

theorem flat_add {n : ℕ} (f f' : X ⟶ I.cocomplex.X n) :
    flat adj e I (f + f') = flat adj e I f + flat adj e I f' := by
  simp only [flat, Adjunction.homEquiv_unit, Preadditive.comp_add, Functor.map_add]
  rfl

theorem flat_zero {n : ℕ} : flat adj e I (0 : X ⟶ I.cocomplex.X n) = 0 := by
  simp only [flat, Adjunction.homEquiv_unit, comp_zero, Functor.map_zero]
  rfl

theorem flat_cocycle {p : ℕ} {f : X ⟶ I.cocomplex.X (p + 1)} (hf : f ≫ I.cocomplex.d (p + 1) (p + 1 + 1) = 0) :
    flat adj e I f ≫ (RI I (R := R)).d (p + 1) (p + 1 + 1) = 0 := by
  rw [← flat_comp, hf, flat_zero]

/-- The class of a cocycle in `H^(p+1)(R I)`, seen from `A`. -/
def clsOf (p : ℕ) (f : X ⟶ I.cocomplex.X (p + 1)) (hf : f ≫ I.cocomplex.d (p + 1) (p + 1 + 1) = 0) :
    A ⟶ (RI I (R := R)).homology (p + 1) :=
  (RI I (R := R)).liftCycles (flat adj e I f) (p + 1 + 1) (CochainComplex.next ℕ (p + 1))
    (flat_cocycle adj e I hf) ≫ (RI I (R := R)).homologyπ (p + 1)

/-- `Ext^(p+1)(X, Y) → Hom(A, H^(p+1)(R I))`. -/
def toHomFun (p : ℕ) (α : Ext X Y (p + 1)) : A ⟶ (RI I (R := R)).homology (p + 1) :=
  clsOf adj e I p (I.extMk_surjective α (p + 1 + 1) rfl).choose
    (I.extMk_surjective α (p + 1 + 1) rfl).choose_spec.choose

end Generic

section Sheaves

open AlgebraicGeometry RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ] {P B : Scheme.{u}} (g : P ⟶ B)

/-- Post-composition with an isomorphism, as an additive equivalence of Hom groups. -/
def homIsoRight {C : Type*} [Category C] [Preadditive C] (A : C) {Z Z' : C} (i : Z ≅ Z') :
    (A ⟶ Z) ≃+ (A ⟶ Z') where
  toFun φ := φ ≫ i.hom
  invFun φ := φ ≫ i.inv
  left_inv φ := by simp
  right_inv φ := by simp
  map_add' a b := Preadditive.add_comp _ _ _ _ _ _

end Sheaves

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_ChAmb =====
section

/-!
# S4-EtCompact, part 7: closed change of ambient (E0Probe P2d)

For a closed immersion `i : Z ⟶ X` and opens `W, V` of `X`, cutting commutes with `i_*`:
`cutWV W V (i_* G) ≅ i_* (cutWV (i⁻¹W) (i⁻¹V) G)` (checked on the covering family of geometric
points `cutPts i`). Hence compactly supported cohomology of `i⁻¹(W ∩ Vᶜ)` may be computed in the
ambient `X`: `H^n_c(X; W, V; i_* G) ≃ H^n_c(Z; i⁻¹W, i⁻¹V; G)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section Family

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} {κ : Type u} (s : κ → GeomPt X)
  (hs : ⋃ k, Set.range (s k).pt = Set.univ)

include hs

/-- Isomorphisms are detected on a covering family of geometric points. -/
theorem isIso_of_family {F G : EtSh Λ X} (φ : F ⟶ G) (h : ∀ k, IsIso (((s k).stalkF Λ).map φ)) :
    IsIso φ := by
  have : ∀ i : (ObjectProperty.ofObj (fun k => (s k).point)).FullSubcategory,
      IsIso ((i.obj.sheafFiber (A := ModuleCat.{u} Λ)).map φ) := by
    rintro ⟨Φ, hΦ⟩
    cases hΦ with
    | mk k => exact h k
  exact ((conservative_family s hs).jointlyReflectIsomorphisms (ModuleCat.{u} Λ)).isIso φ

end Family

theorem center_map' {A B : Scheme.{u}} (f : A ⟶ B) (t : GeomPt A) : (t.map f).center = f t.center :=
  rfl

section ChAmb

end ChAmb

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtLeray_ResDer =====
section

/-!
# S4-EtLeray, part 8: étale restriction commutes with `R^q h_*`

* `homologyMapIso` (generic): an exact functor commutes with the homology of a cochain complex;
* `rderCompExactIso` (generic): `R^q(F ⋙ G) ≅ G ∘ R^q F` for `G` exact;
* **`resRDerIso`**: for `c : V ⟶ X` étale and `h : P ⟶ X`,
  `c^* (R^q h_* Y) ≅ R^q (pullback.fst c h)_* ((pullback.snd c h)^* Y)`.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian AlgebraicGeometry

noncomputable section

namespace RamanujanPetersson.EtLeray

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

section Gen

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] (G : C ⥤ D) [G.Additive]
  [G.PreservesHomology]

/-- An exact functor commutes with the homology of a cochain complex. -/
def homologyMapIso (K : CochainComplex C ℕ) (q : ℕ) :
    ((G.mapHomologicalComplex _).obj K).homology q ≅ G.obj (K.homology q) :=
  (Iso.refl _ : _ ≅ ((K.sc q).map G).homology) ≪≫ (K.sc q).mapHomologyIso G

end Gen

end RamanujanPetersson.EtLeray

end

end

-- ===== S4.Def_RP_EtPBC_B_BCc =====
section

/-!
# S4-EtPBC-B, D1a: base change for extension by zero and for closed push-forward

* **`lshPullBC`**: for `c : V ⟶ X` étale and any `j : U ⟶ X`,
  `j^* ∘ c_! ≅ c'_! ∘ j'^*` (`c' = pullback.snd c j`, `j' = pullback.fst c j`), by uniqueness of left
  adjoints from the base change `pushResBC : c^* ∘ j_* ≅ j'_* ∘ c'^*`;
* **`closedBC`**: for `i : Z ⟶ P` a closed immersion and any `ιP : P' ⟶ P`,
  `ιP^* i_* M ≅ i'_* ιZ^* M` (`i' = pullback.snd i ιP`, `ιZ = pullback.fst i ιP`): the unit of `i'` is an
  isomorphism on `ιP^* i_* M` (stalks at `cutPts i'`), then `i^* i_* ≅ id`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Mate

universe u

section Lsh

variable (Λ : Type u) [CommRing Λ] {V X U : Scheme.{u}} (c : V ⟶ X) [Etale c] (j : U ⟶ X)

/-- **Base change for extension by zero along an étale map.** -/
def lshPullBC : lsh c Λ ⋙ pull j Λ ≅ pull (pullback.fst c j) Λ ⋙ lsh (pullback.snd c j) Λ :=
  Adjunction.leftAdjointUniq ((lshAdj c Λ).comp (pullAdj j Λ))
    (((pullAdj (pullback.fst c j) Λ).comp (lshAdj (pullback.snd c j) Λ)).ofNatIsoRight
      (PushBC.pushResBC c j Λ).symm)

end Lsh

section Closed

variable {Λ : Type u} [CommRing Λ] {Z P P' : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i] (ιP : P' ⟶ P)

omit [IsClosedImmersion i] in
theorem not_mem_range_comp {x : P'} (hx : x ∉ Set.range (pullback.snd i ιP)) : ιP x ∉ Set.range i := by
  rw [Scheme.Pullback.range_snd] at hx
  exact hx

end Closed

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_B_Rsh =====
section

/-!
# S4-EtPBC-B, D1: stalks of `R^q f_!` are the compactly supported cohomology of the geometric fibre

For a compactification `c : Cpt f` (`X ⊆ Z ⊆ P`, `P` proper over `B`) and a geometric point `s` of `B`:
* `fibCpt c s`: the base change of `c` to `s`, a compactification of `X_s ⟶ Spec Ω`
  (`P_s = fib c.fbar s`, `Z_s = Z ×_P P_s`, `X_s = X ×_Z Z_s`);
* `extBC`: `ι_P^* (i_* j_! F) ≅ i_{s*} j_{s!} (ι_X^* F)` (`closedBC` + `lshPullBC`);
* **`rshriek_stalk`**: if `c.fbar` satisfies `PBCGood` at `s` (e.g. `(P^1)^{n+1}_S ⟶ S`, `good_towerP`), then
  `(R^q f_! F)_s ≃+ H^q_c(X_s, F|X_s)` (computed with `fibCpt c s`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

section Fib

variable {X B : Scheme.{u}} {f : X ⟶ B} (c : Cpt f) (s : GeomPt B)

/-- `Z_s = Z ×_P P_s`. -/
abbrev cptZs : Scheme.{u} := pullback c.i (fibι c.fbar s)

/-- `Z_s ⟶ Z`. -/
abbrev cptιZ : cptZs c s ⟶ c.Z := pullback.fst c.i (fibι c.fbar s)

/-- `X_s = X ×_Z Z_s`. -/
abbrev cptXs : Scheme.{u} := pullback c.j (cptιZ c s)

/-- `X_s ⟶ X`. -/
abbrev cptιX : cptXs c s ⟶ X := pullback.fst c.j (cptιZ c s)

/-- `X_s ⟶ Spec Ω`. -/
abbrev cptfs : cptXs c s ⟶ Spec (CommRingCat.of s.Ω) :=
  pullback.snd c.j (cptιZ c s) ≫ pullback.snd c.i (fibι c.fbar s) ≫ pullback.snd c.fbar s.pt

/-- **The base change of `c` to the geometric point `s`.** -/
abbrev fibCpt : Cpt (cptfs c s) where
  P := fib c.fbar s
  Z := cptZs c s
  j := pullback.snd c.j (cptιZ c s)
  i := pullback.snd c.i (fibι c.fbar s)
  fbar := pullback.snd c.fbar s.pt
  isOpenImmersion_j := inferInstance
  isClosedImmersion_i := inferInstance
  isProper_fbar := inferInstance
  comm := rfl

end Fib

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_C1_Desc =====
section

/-!
# S4-EtPBC-C1, part 1: lifting a resolution into an injective resolution

An `ExRes Z` is an exact augmented complex `Z ⟶ K⁰ ⟶ K¹ ⟶ ⋯` (`a` mono, exact everywhere) with no injectivity
condition (e.g. `L I` for an exact functor `L` and an injective resolution `I`). `descR f E I : E.K ⟶ I` lifts
`f : Z ⟶ Y` into an injective resolution `I` of `Y` (Mathlib's `InjectiveResolution.desc` uses only the exactness
of the source and the injectivity of the target); `descRHomotopy`: two such lifts that agree on `a` are homotopic.
-/

set_option autoImplicit false

open CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An exact augmented complex (a resolution, not necessarily injective). -/
structure ExRes (Z : C) where
  /-- the complex -/
  K : CochainComplex C ℕ
  /-- the augmentation -/
  a : Z ⟶ K.X 0
  mono_a : Mono a
  w : a ≫ K.d 0 1 = 0
  exact₀ : (ShortComplex.mk a (K.d 0 1) w).Exact
  exact_succ : ∀ n : ℕ, (ShortComplex.mk _ _ (K.d_comp_d n (n + 1) (n + 2))).Exact

namespace ExRes

set_option backward.isDefEq.respectTransparency false in
/-- An injective resolution is an exact resolution. -/
def ofInj {Z : C} (I : InjectiveResolution Z) : ExRes Z where
  K := I.cocomplex
  a := I.ι.f 0
  mono_a := inferInstance
  w := I.ι_f_zero_comp_complex_d
  exact₀ := I.exact₀
  exact_succ := I.exact_succ

variable {D : Type u'} [Category.{v'} D] [Abelian D] (L : C ⥤ D) [L.Additive] [L.PreservesHomology]
  [L.PreservesMonomorphisms]

/-- The image of an exact resolution under an exact functor. -/
def map {Z : C} (E : ExRes Z) : ExRes (L.obj Z) where
  K := (L.mapHomologicalComplex _).obj E.K
  a := L.map E.a
  mono_a := by have := E.mono_a; exact L.map_mono E.a
  w := by
    change L.map E.a ≫ L.map (E.K.d 0 1) = 0
    rw [← L.map_comp, E.w, L.map_zero]
  exact₀ := E.exact₀.map L
  exact_succ n := (E.exact_succ n).map L

@[simp] theorem map_K {Z : C} (E : ExRes Z) : (E.map L).K = (L.mapHomologicalComplex _).obj E.K := rfl

@[simp] theorem map_a {Z : C} (E : ExRes Z) : (E.map L).a = L.map E.a := rfl

end ExRes

variable {Y Z : C}

set_option backward.isDefEq.respectTransparency false in
/-- Degree `0` of `descR`. -/
def descR0 (f : Z ⟶ Y) (E : ExRes Z) (I : InjectiveResolution Y) : E.K.X 0 ⟶ I.cocomplex.X 0 :=
  haveI := E.mono_a
  Injective.factorThru (f ≫ I.ι.f 0) E.a

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem a_descR0 (f : Z ⟶ Y) (E : ExRes Z) (I : InjectiveResolution Y) :
    E.a ≫ descR0 f E I = f ≫ I.ι.f 0 := by
  have := E.mono_a
  exact Injective.comp_factorThru _ _

set_option backward.isDefEq.respectTransparency false in
/-- Degree `1` of `descR`. -/
def descR1 (f : Z ⟶ Y) (E : ExRes Z) (I : InjectiveResolution Y) : E.K.X 1 ⟶ I.cocomplex.X 1 :=
  E.exact₀.descToInjective (descR0 f E I ≫ I.cocomplex.d 0 1)
    (by
      change E.a ≫ descR0 f E I ≫ I.cocomplex.d 0 1 = 0
      rw [a_descR0_assoc, I.ι_f_zero_comp_complex_d, Limits.comp_zero])

theorem descR1_comm (f : Z ⟶ Y) (E : ExRes Z) (I : InjectiveResolution Y) :
    E.K.d 0 1 ≫ descR1 f E I = descR0 f E I ≫ I.cocomplex.d 0 1 :=
  E.exact₀.comp_descToInjective _ _

/-- The inductive step of `descR`. -/
def descRSucc (E : ExRes Z) (I : InjectiveResolution Y) (n : ℕ)
    (g : E.K.X n ⟶ I.cocomplex.X n) (g' : E.K.X (n + 1) ⟶ I.cocomplex.X (n + 1))
    (w : E.K.d n (n + 1) ≫ g' = g ≫ I.cocomplex.d n (n + 1)) :
    Σ' g'' : E.K.X (n + 2) ⟶ I.cocomplex.X (n + 2),
      E.K.d (n + 1) (n + 2) ≫ g'' = g' ≫ I.cocomplex.d (n + 1) (n + 2) :=
  ⟨(E.exact_succ n).descToInjective (g' ≫ I.cocomplex.d (n + 1) (n + 2))
      (by
        change E.K.d n (n + 1) ≫ g' ≫ I.cocomplex.d (n + 1) (n + 2) = 0
        rw [reassoc_of% w, HomologicalComplex.d_comp_d, Limits.comp_zero]),
    (E.exact_succ n).comp_descToInjective _ _⟩

/-- **The lift of `f : Z ⟶ Y` from an exact resolution of `Z` into an injective resolution of `Y`.** -/
def descR (f : Z ⟶ Y) (E : ExRes Z) (I : InjectiveResolution Y) : E.K ⟶ I.cocomplex :=
  CochainComplex.mkHom _ _ (descR0 f E I) (descR1 f E I) (descR1_comm f E I).symm
    fun n ⟨g, g', w⟩ => ⟨(descRSucc E I n g g' w.symm).1, (descRSucc E I n g g' w.symm).2.symm⟩

@[reassoc]
theorem descR_f_zero (f : Z ⟶ Y) (E : ExRes Z) (I : InjectiveResolution Y) :
    E.a ≫ (descR f E I).f 0 = f ≫ I.ι.f 0 :=
  a_descR0 f E I

/-- Degree `0` of the null-homotopy. -/
def hzZero {E : ExRes Z} {I : InjectiveResolution Y} (φ : E.K ⟶ I.cocomplex) (h : E.a ≫ φ.f 0 = 0) :
    E.K.X 1 ⟶ I.cocomplex.X 0 :=
  E.exact₀.descToInjective (φ.f 0) h

theorem comp_hzZero {E : ExRes Z} {I : InjectiveResolution Y} (φ : E.K ⟶ I.cocomplex)
    (h : E.a ≫ φ.f 0 = 0) : E.K.d 0 1 ≫ hzZero φ h = φ.f 0 :=
  E.exact₀.comp_descToInjective _ _

/-- Degree `1` of the null-homotopy. -/
def hzOne {E : ExRes Z} {I : InjectiveResolution Y} (φ : E.K ⟶ I.cocomplex) (h : E.a ≫ φ.f 0 = 0) :
    E.K.X 2 ⟶ I.cocomplex.X 1 :=
  (E.exact_succ 0).descToInjective (φ.f 1 - hzZero φ h ≫ I.cocomplex.d 0 1)
    (by
      change E.K.d 0 1 ≫ (φ.f 1 - hzZero φ h ≫ I.cocomplex.d 0 1) = 0
      rw [Preadditive.comp_sub, ← Category.assoc, comp_hzZero, HomologicalComplex.Hom.comm, sub_self])

theorem comp_hzOne {E : ExRes Z} {I : InjectiveResolution Y} (φ : E.K ⟶ I.cocomplex)
    (h : E.a ≫ φ.f 0 = 0) : E.K.d 1 2 ≫ hzOne φ h = φ.f 1 - hzZero φ h ≫ I.cocomplex.d 0 1 :=
  (E.exact_succ 0).comp_descToInjective _ _

/-- The inductive step of the null-homotopy. -/
def hzSucc {E : ExRes Z} {I : InjectiveResolution Y} (φ : E.K ⟶ I.cocomplex) (n : ℕ)
    (g : E.K.X (n + 1) ⟶ I.cocomplex.X n) (g' : E.K.X (n + 2) ⟶ I.cocomplex.X (n + 1))
    (w : φ.f (n + 1) = g ≫ I.cocomplex.d n (n + 1) + E.K.d (n + 1) (n + 2) ≫ g') :
    E.K.X (n + 3) ⟶ I.cocomplex.X (n + 2) :=
  (E.exact_succ (n + 1)).descToInjective (φ.f (n + 2) - g' ≫ I.cocomplex.d _ _)
    (by
      change E.K.d (n + 1) (n + 2) ≫ (φ.f (n + 2) - g' ≫ I.cocomplex.d (n + 1) (n + 2)) = 0
      rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, w, Preadditive.add_comp,
        Category.assoc, Category.assoc, HomologicalComplex.d_comp_d, Limits.comp_zero,
        zero_add, sub_self])

theorem comp_hzSucc {E : ExRes Z} {I : InjectiveResolution Y} (φ : E.K ⟶ I.cocomplex) (n : ℕ)
    (g : E.K.X (n + 1) ⟶ I.cocomplex.X n) (g' : E.K.X (n + 2) ⟶ I.cocomplex.X (n + 1))
    (w : φ.f (n + 1) = g ≫ I.cocomplex.d n (n + 1) + E.K.d (n + 1) (n + 2) ≫ g') :
    E.K.d (n + 2) (n + 3) ≫ hzSucc φ n g g' w = φ.f (n + 2) - g' ≫ I.cocomplex.d _ _ :=
  (E.exact_succ (n + 1)).comp_descToInjective _ _

/-- A lift of `0` is null-homotopic. -/
def hzHomotopy {E : ExRes Z} {I : InjectiveResolution Y} (φ : E.K ⟶ I.cocomplex) (h : E.a ≫ φ.f 0 = 0) :
    Homotopy φ 0 :=
  Homotopy.mkCoinductive _ (hzZero φ h) (comp_hzZero φ h).symm (hzOne φ h)
    (by rw [comp_hzOne]; abel)
    (fun n ⟨g, g', w⟩ => ⟨hzSucc φ n g g' w, by rw [comp_hzSucc]; dsimp only; abel⟩)

/-- **Two lifts that agree on the augmentation are homotopic.** -/
def descRHomotopy {E : ExRes Z} {I : InjectiveResolution Y} (φ ψ : E.K ⟶ I.cocomplex)
    (h : E.a ≫ φ.f 0 = E.a ≫ ψ.f 0) : Homotopy φ ψ :=
  Homotopy.equivSubZero.invFun (hzHomotopy (φ - ψ) (by
    rw [HomologicalComplex.sub_f_apply, Preadditive.comp_sub, h, sub_self]))

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_Gen =====
section

/-!
# S4-EtPBC-C1, part 2: the generic degree-`q` base change morphism

`R : C ⥤ D`, `R' : C' ⥤ D'` additive, `Lc : C ⥤ C'`, `Ld : D ⥤ D'` exact, `β : R ⋙ Ld ⟶ Lc ⋙ R'`.
`bcMorRes q I J : Ld (R^q X) ⟶ R'^q (Lc X)` for injective resolutions `I` of `X` and `J` of `Lc X`:
`Ld H^q(R I) ≅ H^q(Ld R I) ⟶ H^q(R' Lc I) ⟶ H^q(R' J)` (`β` degreewise, then `R'` of the lift `descR` of
`Lc I` into `J`). **`bcMorRes_natural`** (naturality in `X`, any resolutions), `bcMorRes_indep`, `bcMorGen`.
-/

set_option autoImplicit false

open CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {C' : Type u₃} [Category.{v₃} C'] [Abelian C'] {D' : Type u₄} [Category.{v₄} D'] [Abelian D']

section HMI

variable (Ld : D ⥤ D') [Ld.Additive] [Ld.PreservesHomology]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of `homologyMapIso` (inverse form). -/
theorem homologyMapIso_inv_nat {K K' : CochainComplex D ℕ} (ψ : K ⟶ K') (q : ℕ) :
    Ld.map (HomologicalComplex.homologyMap ψ q) ≫ (EtLeray.homologyMapIso Ld K' q).inv =
      (EtLeray.homologyMapIso Ld K q).inv ≫
        HomologicalComplex.homologyMap ((Ld.mapHomologicalComplex _).map ψ) q := by
  have h := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor D (ComplexShape.up ℕ) q).map ψ) Ld
  simp only [EtLeray.homologyMapIso, Iso.trans_inv, Iso.refl_inv, Category.comp_id]
  exact h

end HMI

variable (R : C ⥤ D) [R.Additive] (R' : C' ⥤ D') [R'.Additive]
  (Lc : C ⥤ C') [Lc.Additive] [Lc.PreservesHomology] [Lc.PreservesMonomorphisms]
  (Ld : D ⥤ D') [Ld.Additive] [Ld.PreservesHomology]
  (β : R ⋙ Ld ⟶ Lc ⋙ R')

/-- `β` on complexes: `Ld (R K) ⟶ R' (Lc K)`. -/
def betaCx (K : CochainComplex C ℕ) :
    (Ld.mapHomologicalComplex _).obj ((R.mapHomologicalComplex _).obj K) ⟶
      (R'.mapHomologicalComplex _).obj ((Lc.mapHomologicalComplex _).obj K) where
  f n := β.app (K.X n)
  comm' i j _ := (β.naturality (K.d i j)).symm

@[simp] theorem betaCx_f (K : CochainComplex C ℕ) (n : ℕ) : (betaCx R R' Lc Ld β K).f n = β.app (K.X n) := rfl

theorem betaCx_natural {K K' : CochainComplex C ℕ} (g : K ⟶ K') :
    (Ld.mapHomologicalComplex _).map ((R.mapHomologicalComplex _).map g) ≫ betaCx R R' Lc Ld β K' =
      betaCx R R' Lc Ld β K ≫ (R'.mapHomologicalComplex _).map ((Lc.mapHomologicalComplex _).map g) := by
  ext n
  exact β.naturality (g.f n)

/-- The lift `Lc I ⟶ J` of the identity. -/
abbrev liftLc {X : C} (I : InjectiveResolution X) (J : InjectiveResolution (Lc.obj X)) :
    (Lc.mapHomologicalComplex _).obj I.cocomplex ⟶ J.cocomplex :=
  descR (𝟙 _) ((ExRes.ofInj I).map Lc) J

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem liftLc_f_zero {X : C} (I : InjectiveResolution X) (J : InjectiveResolution (Lc.obj X)) :
    Lc.map (I.ι.f 0) ≫ (liftLc Lc I J).f 0 = J.ι.f 0 :=
  (descR_f_zero (𝟙 _) ((ExRes.ofInj I).map Lc) J).trans (Category.id_comp _)

variable [HasInjectiveResolutions C] [HasInjectiveResolutions C']

/-- **The base change morphism computed with resolutions `I`, `J`.** -/
def bcMorRes (q : ℕ) {X : C} (I : InjectiveResolution X) (J : InjectiveResolution (Lc.obj X)) :
    Ld.obj ((R.rightDerived q).obj X) ⟶ (R'.rightDerived q).obj (Lc.obj X) :=
  Ld.map (I.isoRightDerivedObj R q).hom ≫
    (EtLeray.homologyMapIso Ld ((R.mapHomologicalComplex _).obj I.cocomplex) q).inv ≫
    HomologicalComplex.homologyMap
      (betaCx R R' Lc Ld β I.cocomplex ≫ (R'.mapHomologicalComplex _).map (liftLc Lc I J)) q ≫
    (J.isoRightDerivedObj R' q).inv

set_option backward.isDefEq.respectTransparency false in
/-- The two lifts `Lc I_X ⟶ J_Y` of `Lc f` are homotopic. -/
def liftHomotopy {X Y : C} (f : X ⟶ Y) (IX : InjectiveResolution X) (JX : InjectiveResolution (Lc.obj X))
    (IY : InjectiveResolution Y) (JY : InjectiveResolution (Lc.obj Y)) :
    Homotopy ((Lc.mapHomologicalComplex _).map (InjectiveResolution.desc f IY IX) ≫ liftLc Lc IY JY)
      (liftLc Lc IX JX ≫ InjectiveResolution.desc (Lc.map f) JY JX) :=
  descRHomotopy (E := (ExRes.ofInj IX).map Lc) _ _ (by
    change Lc.map (IX.ι.f 0) ≫ (Lc.map ((InjectiveResolution.desc f IY IX).f 0) ≫ (liftLc Lc IY JY).f 0) =
      Lc.map (IX.ι.f 0) ≫ ((liftLc Lc IX JX).f 0 ≫ (InjectiveResolution.desc (Lc.map f) JY JX).f 0)
    rw [← Category.assoc, ← Lc.map_comp, InjectiveResolution.desc_commutes_zero, Lc.map_comp,
      Category.assoc, liftLc_f_zero, liftLc_f_zero_assoc, InjectiveResolution.desc_commutes_zero])

set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of the base change morphism** (any resolutions). -/
theorem bcMorRes_natural (q : ℕ) {X Y : C} (f : X ⟶ Y) (IX : InjectiveResolution X)
    (JX : InjectiveResolution (Lc.obj X)) (IY : InjectiveResolution Y) (JY : InjectiveResolution (Lc.obj Y)) :
    Ld.map ((R.rightDerived q).map f) ≫ bcMorRes R R' Lc Ld β q IY JY =
      bcMorRes R R' Lc Ld β q IX JX ≫ (R'.rightDerived q).map (Lc.map f) := by
  have key : HomologicalComplex.homologyMap
      ((Ld.mapHomologicalComplex _).map ((R.mapHomologicalComplex _).map (InjectiveResolution.desc f IY IX)) ≫
        betaCx R R' Lc Ld β IY.cocomplex ≫ (R'.mapHomologicalComplex _).map (liftLc Lc IY JY)) q =
      HomologicalComplex.homologyMap ((betaCx R R' Lc Ld β IX.cocomplex ≫
        (R'.mapHomologicalComplex _).map (liftLc Lc IX JX)) ≫
          (R'.mapHomologicalComplex _).map (InjectiveResolution.desc (Lc.map f) JY JX)) q := by
    rw [← Category.assoc, betaCx_natural, Category.assoc, ← Functor.map_comp, Category.assoc,
      ← Functor.map_comp]
    exact ((R'.mapHomotopy (liftHomotopy Lc f IX JX IY JY)).compLeft _).homologyMap_eq q
  rw [R.rightDerived_map_eq q f (InjectiveResolution.desc f IY IX) (InjectiveResolution.desc_commutes f IY IX),
    R'.rightDerived_map_eq q (Lc.map f) (InjectiveResolution.desc (Lc.map f) JY JX)
      (InjectiveResolution.desc_commutes (Lc.map f) JY JX)]
  simp only [bcMorRes, Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc, Iso.inv_hom_id_assoc,
    Functor.comp_map, HomologicalComplex.homologyFunctor_map]
  rw [← Category.assoc (Ld.map (HomologicalComplex.homologyMap _ q)), homologyMapIso_inv_nat, Category.assoc,
    ← HomologicalComplex.homologyMap_comp_assoc, ← HomologicalComplex.homologyMap_comp_assoc, key]

/-- **Independence of the resolutions.** -/
theorem bcMorRes_indep (q : ℕ) {X : C} (I I' : InjectiveResolution X) (J J' : InjectiveResolution (Lc.obj X)) :
    bcMorRes R R' Lc Ld β q I J = bcMorRes R R' Lc Ld β q I' J' := by
  have h := bcMorRes_natural R R' Lc Ld β q (𝟙 X) I J I' J'
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at h
  exact h.symm

/-- **The degree-`q` base change morphism** `Ld (R^q X) ⟶ R'^q (Lc X)`. -/
def bcMorGen (q : ℕ) (X : C) : Ld.obj ((R.rightDerived q).obj X) ⟶ (R'.rightDerived q).obj (Lc.obj X) :=
  bcMorRes R R' Lc Ld β q (injectiveResolution X) (injectiveResolution (Lc.obj X))

theorem bcMorGen_eq (q : ℕ) {X : C} (I : InjectiveResolution X) (J : InjectiveResolution (Lc.obj X)) :
    bcMorGen R R' Lc Ld β q X = bcMorRes R R' Lc Ld β q I J :=
  bcMorRes_indep R R' Lc Ld β q _ _ _ _

theorem bcMorGen_natural (q : ℕ) {X Y : C} (f : X ⟶ Y) :
    Ld.map ((R.rightDerived q).map f) ≫ bcMorGen R R' Lc Ld β q Y =
      bcMorGen R R' Lc Ld β q X ≫ (R'.rightDerived q).map (Lc.map f) :=
  bcMorRes_natural R R' Lc Ld β q f _ _ _ _

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_HomBk =====
section

/-!
# S4-EtPBC-C1, part 10: homology bookkeeping for exact functors

Generic lemmas: an exact functor `F` sends the class `[k]` of a cocycle `k : A ⟶ K^(p+1)` to the class of `F k`
under `EtLeray.homologyMapIso` (**`map_liftCycles_homologyπ_cx`**), and `[k]` composed with a homology map is the
class of `k ≫ ψ` (**`liftCycles_homologyπ_homologyMap`**).
-/

set_option autoImplicit false

open CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

section SC

variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  (S : ShortComplex C) (F : C ⥤ D) [F.PreservesZeroMorphisms]

set_option backward.isDefEq.respectTransparency false in
theorem homologyπ_mapHomologyIso_hom [S.HasHomology] [(S.map F).HasHomology] [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom = (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  rw [S.leftHomologyData.mapHomologyIso_eq F, S.leftHomologyData.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc,
    Category.assoc, ← F.map_comp]
  rw [← ShortComplex.LeftHomologyData.π_comp_homologyIso_inv, F.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem map_liftCycles_eq [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] {A : C} (k : A ⟶ S.X₂)
    (hk : k ≫ S.g = 0) (hk' : F.map k ≫ (S.map F).g = 0) :
    (S.map F).liftCycles (F.map k) hk' = F.map (S.liftCycles k hk) ≫ (S.mapCyclesIso F).inv := by
  rw [← cancel_mono (S.map F).iCycles, ShortComplex.liftCycles_i, Category.assoc, (Iso.inv_comp_eq _).mpr
    (S.mapCyclesIso_hom_iCycles F).symm, ← F.map_comp, ShortComplex.liftCycles_i]

set_option backward.isDefEq.respectTransparency false in
theorem map_liftCycles_homologyπ [S.HasHomology] [(S.map F).HasHomology] [F.PreservesLeftHomologyOf S] {A : C}
    (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) (hk' : F.map k ≫ (S.map F).g = 0) :
    F.map (S.liftCycles k hk ≫ S.homologyπ) ≫ (S.mapHomologyIso F).inv =
      (S.map F).liftCycles (F.map k) hk' ≫ (S.map F).homologyπ := by
  rw [Iso.comp_inv_eq, map_liftCycles_eq S F k hk hk', Category.assoc, homologyπ_mapHomologyIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, F.map_comp]

end SC

section Cx

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] (G : C ⥤ D) [G.Additive]
  [G.PreservesHomology]

set_option backward.isDefEq.respectTransparency false in
theorem map_liftCycles_homologyπ_cx (K : CochainComplex C ℕ) (i j : ℕ) (hj : (ComplexShape.up ℕ).next i = j)
    {A : C} (k : A ⟶ K.X i) (hk : k ≫ K.d i j = 0)
    (hk' : G.map k ≫ ((G.mapHomologicalComplex _).obj K).d i j = 0) :
    G.map (K.liftCycles k j hj hk ≫ K.homologyπ i) ≫ (EtLeray.homologyMapIso G K i).inv =
      ((G.mapHomologicalComplex _).obj K).liftCycles (G.map k) j hj hk' ≫
        ((G.mapHomologicalComplex _).obj K).homologyπ i := by
  subst hj
  rw [EtLeray.homologyMapIso, Iso.trans_inv, Iso.refl_inv, Category.comp_id]
  exact map_liftCycles_homologyπ (K.sc i) G k hk hk'

end Cx

theorem liftCycles_homologyπ_homologyMap {C : Type*} [Category C] [Abelian C] {K K' : CochainComplex C ℕ}
    (ψ : K ⟶ K') (i j : ℕ) (hj : (ComplexShape.up ℕ).next i = j) {A : C} (k : A ⟶ K.X i) (hk : k ≫ K.d i j = 0)
    (hk' : (k ≫ ψ.f i) ≫ K'.d i j = 0) :
    K.liftCycles k j hj hk ≫ K.homologyπ i ≫ HomologicalComplex.homologyMap ψ i =
      K'.liftCycles (k ≫ ψ.f i) j hj hk' ≫ K'.homologyπ i := by
  rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_ClsGen =====
section

/-!
# S4-EtPBC-C1, part 13: classes of cocycles under the base change morphism and `absRelGen` (generic)

* **`bcMorRes_cls`**: `a ≫ Ld([k] ≫ isoRD⁻¹) ≫ bcMorRes I J = [(a ≫ Ld k) ≫ β ≫ R'(lift)] ≫ isoRD⁻¹`.
* **`absRelGen_extMk`**: `absRelGen (I.extMk f) = [adj.homEquiv (e.hom ≫ f)]`.
* **`glue_gen`**: if `(a ≫ Ld k) ≫ β = adj.homEquiv (e.hom ≫ u ≫ Lc c)`, then
  `absRelGen (J.extMk (u ≫ Lc c ≫ lift)) ≫ isoRD_J⁻¹ = a ≫ Ld([k] ≫ isoRD_I⁻¹) ≫ bcMorRes I J`.
-/

set_option autoImplicit false

open CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

section BC

variable {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
  {C' : Type*} [Category C'] [Abelian C'] {D' : Type*} [Category D'] [Abelian D']
  (R : C ⥤ D) [R.Additive] (R' : C' ⥤ D') [R'.Additive]
  (Lc : C ⥤ C') [Lc.Additive] [Lc.PreservesHomology] [Lc.PreservesMonomorphisms]
  (Ld : D ⥤ D') [Ld.Additive] [Ld.PreservesHomology]
  (β : R ⋙ Ld ⟶ Lc ⋙ R') [HasInjectiveResolutions C] [HasInjectiveResolutions C']

set_option backward.isDefEq.respectTransparency false in
/-- **The base change morphism on the class of a cocycle.** -/
theorem bcMorRes_cls (p : ℕ) {X : C} (I : InjectiveResolution X) (J : InjectiveResolution (Lc.obj X))
    {A : D'} {Y : D} (a : A ⟶ Ld.obj Y) (k : Y ⟶ ((R.mapHomologicalComplex _).obj I.cocomplex).X (p + 1))
    (hk : k ≫ ((R.mapHomologicalComplex _).obj I.cocomplex).d (p + 1) (p + 1 + 1) = 0)
    (hk2 : ((a ≫ Ld.map k) ≫ β.app (I.cocomplex.X (p + 1)) ≫ R'.map ((liftLc Lc I J).f (p + 1))) ≫
      ((R'.mapHomologicalComplex _).obj J.cocomplex).d (p + 1) (p + 1 + 1) = 0) :
    a ≫ Ld.map (((R.mapHomologicalComplex _).obj I.cocomplex).liftCycles k (p + 1 + 1)
        (CochainComplex.next ℕ (p + 1)) hk ≫ ((R.mapHomologicalComplex _).obj I.cocomplex).homologyπ (p + 1) ≫
        (I.isoRightDerivedObj R (p + 1)).inv) ≫ bcMorRes R R' Lc Ld β (p + 1) I J =
      ((R'.mapHomologicalComplex _).obj J.cocomplex).liftCycles
        ((a ≫ Ld.map k) ≫ β.app (I.cocomplex.X (p + 1)) ≫ R'.map ((liftLc Lc I J).f (p + 1))) (p + 1 + 1)
        (CochainComplex.next ℕ (p + 1)) hk2 ≫ ((R'.mapHomologicalComplex _).obj J.cocomplex).homologyπ (p + 1) ≫
        (J.isoRightDerivedObj R' (p + 1)).inv := by
  have hk' : Ld.map k ≫ ((Ld.mapHomologicalComplex _).obj ((R.mapHomologicalComplex _).obj I.cocomplex)).d
      (p + 1) (p + 1 + 1) = 0 := by
    rw [Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp, hk, Functor.map_zero]
  have e1 := map_liftCycles_homologyπ_cx Ld ((R.mapHomologicalComplex _).obj I.cocomplex) (p + 1) (p + 1 + 1)
    (CochainComplex.next ℕ (p + 1)) k hk hk'
  have hψ : (a ≫ Ld.map k) ≫ (betaCx R R' Lc Ld β I.cocomplex ≫
      (R'.mapHomologicalComplex _).map (liftLc Lc I J)).f (p + 1) =
      (a ≫ Ld.map k) ≫ β.app (I.cocomplex.X (p + 1)) ≫ R'.map ((liftLc Lc I J).f (p + 1)) := by
    rw [HomologicalComplex.comp_f, betaCx_f, Functor.mapHomologicalComplex_map_f]
  have e2 := liftCycles_homologyπ_homologyMap (betaCx R R' Lc Ld β I.cocomplex ≫
      (R'.mapHomologicalComplex _).map (liftLc Lc I J)) (p + 1) (p + 1 + 1) (CochainComplex.next ℕ (p + 1))
    (a ≫ Ld.map k) (by rw [Category.assoc, hk', comp_zero]) (hψ ▸ hk2)
  rw [bcMorRes]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Ld.map_comp_assoc (I.isoRightDerivedObj R (p + 1)).inv, Iso.inv_hom_id, Ld.map_id, Category.id_comp,
    ← Ld.map_comp_assoc, reassoc_of% e1, ← Category.assoc a, HomologicalComplex.comp_liftCycles,
    reassoc_of% e2]
  exact congrArg (fun t => t ≫ ((R'.mapHomologicalComplex _).obj J.cocomplex).homologyπ (p + 1) ≫
    (J.isoRightDerivedObj R' (p + 1)).inv) (EtCompact.liftCycles_eq_of_eq _ _ _ _
      (by rw [HomologicalComplex.comp_f, betaCx_f, Functor.mapHomologicalComplex_map_f]) _ _)

end BC

section AR

universe w

end AR

section Glue

universe w

end Glue

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_Mor =====
section

/-!
# S4-EtPBC-C1, part 3: the base change morphism `g^* R^q f_! F ⟶ R^q f'_! g'^* F`

* `bcCell`: for a commutative square `h' ≫ ιY = ιX ≫ h` of schemes, the base change 2-cell
  `ιY^* h_* ⟶ h'_* ιX^*` (the mate of `sqQ`); `bcCell_counit`, `bcCell_app` (mate formula); `bcCell` is an iso for closed squares.
* `bcMorSq q G : ιY^* R^q h_* G ⟶ R^q h'_* ιX^* G` (`bcMorGen` for push/pull), natural in `G`.
* `itCpt c g`: the base change of a compactification `c : Cpt f` along ANY `g : B' ⟶ B` (iterated pullbacks;
  for `g = s.pt` it is `fibCpt c s`); `itExtNat : c.ext ⋙ gP^* ≅ gX^* ⋙ (itCpt c g).ext`.
* **`bcMor c g q F : g^* R^q f_! F ⟶ R^q f'_! gX^* F`**, natural in `F` (`bcMor_natural`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable (Λ : Type u) [CommRing Λ]

section Sq

variable {X Y Xs Ys : Scheme.{u}} (ιX : Xs ⟶ X) (ιY : Ys ⟶ Y) (h : X ⟶ Y) (h' : Xs ⟶ Ys)
  (w : h' ≫ ιY = ιX ≫ h)

/-- **The base change 2-cell** `h_* ⋙ ιY^* ⟶ ιX^* ⋙ h'_*` (the mate of `sqQ`). -/
def bcCell : push h Λ ⋙ pull ιY Λ ⟶ pull ιX Λ ⋙ push h' Λ :=
  (mateEquiv (pullAdj h Λ) (pullAdj h' Λ) (TwoSquare.mk _ _ _ _ (Mate.sqQ ιX ιY h h' w).hom)).natTrans

theorem bcCell_counit (G : EtSh Λ X) :
    (pull h' Λ).map ((bcCell Λ ιX ιY h h' w).app G) ≫ (pullAdj h' Λ).counit.app ((pull ιX Λ).obj G) =
      (Mate.sqQ ιX ιY h h' w).hom.app ((push h Λ).obj G) ≫ (pull ιX Λ).map ((pullAdj h Λ).counit.app G) :=
  mateEquiv_counit (pullAdj h Λ) (pullAdj h' Λ) _ G

set_option backward.isDefEq.respectTransparency false in
/-- The mate formula: `bcCell = η_{h'} ≫ h'_*(sqQ ≫ ιX^* ε_h)`. -/
theorem bcCell_app (G : EtSh Λ X) : (bcCell Λ ιX ιY h h' w).app G =
    (pullAdj h' Λ).unit.app ((pull ιY Λ).obj ((push h Λ).obj G)) ≫
      (push h' Λ).map ((Mate.sqQ ιX ιY h h' w).hom.app ((push h Λ).obj G) ≫
        (pull ιX Λ).map ((pullAdj h Λ).counit.app G)) :=
  calc (bcCell Λ ιX ιY h h' w).app G
      = (pullAdj h' Λ).homEquiv _ _ (((pullAdj h' Λ).homEquiv _ _).symm ((bcCell Λ ιX ιY h h' w).app G)) :=
        (Equiv.apply_symm_apply _ _).symm
    _ = (pullAdj h' Λ).homEquiv _ _ ((Mate.sqQ ιX ιY h h' w).hom.app ((push h Λ).obj G) ≫
          (pull ιX Λ).map ((pullAdj h Λ).counit.app G)) := by
        rw [Adjunction.homEquiv_counit, bcCell_counit]
        rfl
    _ = _ := Adjunction.homEquiv_unit _ _ _ _

/-- **Degree-`q` base change for a commutative square of schemes.** -/
def bcMorSq (q : ℕ) (G : EtSh Λ X) :
    (pull ιY Λ).obj (((push h Λ).rightDerived q).obj G) ⟶
      ((push h' Λ).rightDerived q).obj ((pull ιX Λ).obj G) :=
  bcMorGen (push h Λ) (push h' Λ) (pull ιX Λ) (pull ιY Λ) (bcCell Λ ιX ιY h h' w) q G

end Sq

section Closed

end Closed

section It

variable {X B B' : Scheme.{u}} {f : X ⟶ B} (c : Cpt f) (g : B' ⟶ B)

/-- `P' = P ×_B B'`. -/
abbrev itP : Scheme.{u} := pullback c.fbar g
/-- `P' ⟶ P`. -/
abbrev itgP : itP c g ⟶ c.P := pullback.fst c.fbar g
/-- `Z' = Z ×_P P'`. -/
abbrev itZ : Scheme.{u} := pullback c.i (itgP c g)
/-- `Z' ⟶ Z`. -/
abbrev itgZ : itZ c g ⟶ c.Z := pullback.fst c.i (itgP c g)
/-- `X' = X ×_Z Z'`. -/
abbrev itX : Scheme.{u} := pullback c.j (itgZ c g)
/-- `gX : X' ⟶ X`. -/
abbrev itgX : itX c g ⟶ X := pullback.fst c.j (itgZ c g)
/-- `f' : X' ⟶ B'`. -/
abbrev itf : itX c g ⟶ B' :=
  pullback.snd c.j (itgZ c g) ≫ pullback.snd c.i (itgP c g) ≫ pullback.snd c.fbar g

/-- **The base change of `c` along any `g : B' ⟶ B`** (for `g = s.pt` this is `fibCpt c s`). -/
abbrev itCpt : Cpt (itf c g) where
  P := itP c g
  Z := itZ c g
  j := pullback.snd c.j (itgZ c g)
  i := pullback.snd c.i (itgP c g)
  fbar := pullback.snd c.fbar g
  isOpenImmersion_j := inferInstance
  isClosedImmersion_i := inferInstance
  isProper_fbar := inferInstance
  comm := rfl

end It

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_SecA =====
section

/-!
# S4-EtPBC-C1, part 7: `bcCell` on pulled-back sections

For a commutative square `w : h' ≫ ιY = ιX ≫ h` and a section `x` of `h_* G` over `V`,
**`bcCell_pbSec`**: `bcCell_G (ιY^* x) = (ιX^* x)|_(κ V)`, with `κ V : h'⁻¹(ιY⁻¹ V) ⟶ ιX⁻¹(h⁻¹ V)` the canonical map
(`((etPullCompIso ιX h).hom.app V).op ≫ (etPullCongr w V).op ≫ ((etPullCompIso h' ιY).inv.app V).op`).
Also `counit_pbSec` (the counit of `f^* ⊣ f_*` on `f^* x`). Proof via the nested-typed `sqN` and the
`O`-form section lemmas, which keep the kernel away from unfolding `pull`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.EtMV

universe u

variable {Λ : Type u} [CommRing Λ]

/-- The counit of `f^* ⊣ f_*` sends `f^* x` to `x`. -/
theorem counit_pbSec {X Y : Scheme.{u}} (f : X ⟶ Y) (G : EtSh Λ X) {V : Y.Etale}
    (x : ((push f Λ).obj G).obj.obj (op V)) :
    (((pullAdj f Λ).counit.app G).hom.app (op ((etPull f).obj V))).hom (pbSec f x) = x := by
  have h := congrArg (fun φ => (φ.hom.app (op V)).hom x) ((pullAdj f Λ).right_triangle_components G)
  exact h

variable {X Y Xs Ys : Scheme.{u}} (ιX : Xs ⟶ X) (ιY : Ys ⟶ Y) (h : X ⟶ Y) (h' : Xs ⟶ Ys)
  (w : h' ≫ ιY = ιX ≫ h)

theorem unit_comp_push_apply {X' Y' : Scheme.{u}} (f : X' ⟶ Y') (A : EtSh Λ Y') (B : EtSh Λ X')
    (ψ : (pull f Λ).obj A ⟶ B) (W : Y'.Etale) (s : A.obj.obj (op W)) :
    ((((pullAdj f Λ).unit.app A ≫ (push f Λ).map ψ).hom.app (op W)).hom s) =
      (ψ.hom.app (op ((etPull f).obj W))).hom (pbSec f s) := rfl

theorem map_id_apply' {Z' : Scheme.{u}} (P : EtSh Λ Z') (W : Z'.Etaleᵒᵖ) (s : P.obj.obj W) :
    (P.obj.map (𝟙 W)).hom s = s := by
  rw [P.obj.map_id]; rfl

/-- **`bcCell` on pulled-back sections**: for a section `x` of `h_* G` over `V`, `bcCell_G (ιY^* x)` is
`ιX^* x` restricted along the canonical map `h'⁻¹ ιY⁻¹ V ⟶ ιX⁻¹ h⁻¹ V` (an opposite-category composite). -/
theorem bcCell_pbSec (G : EtSh Λ X) {V : Y.Etale} (x : ((push h Λ).obj G).obj.obj (op V)) :
    (((bcCell Λ ιX ιY h h' w).app G).hom.app (op ((etPull ιY).obj V))).hom (pbSec ιY x) =
      ((((pull ιX Λ).obj G).obj.map (Y := op ((etPull h').obj ((etPull ιY).obj V)))
        (((etPullCompIso ιX h).hom.app V).op ≫ (etPullCongr w V).op ≫
        ((etPullCompIso h' ιY).inv.app V).op)).hom (pbSec ιX (V := (etPull h).obj V) x)) := by
  rw [bcCell_app, unit_comp_push_apply, ← sqN_eq, sh_comp_apply,
    ← map_id_apply' ((pull h' Λ).obj ((pull ιY Λ).obj ((push h Λ).obj G))) _ (pbSec h' (pbSec ιY x)),
    sqN_pbSec, pullMap_pbSecO, counit_pbSec]
  exact map_congr_apply _ (congrArg _ (congrArg _ (Category.comp_id _))) _

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_StalkSec =====
section

/-!
# S4-EtPBC-C1, part 9: stalks as global sections of the pullback to the geometric point

For a geometric point `s : Spec Ω ⟶ S` and an etale sheaf `H` on `S`:
* `ptSec X x : Spec Ω ⟶ s⁻¹ X` (over `Spec Ω`), the section given by a point `x` of `X` over `s`; `ptSec_comp`.
* `ptRes H X x : H(X) ⟶ (s^* H)(Spec Ω)`, `z ↦ (s^* z)|_{ptSec X x}`; `ptRes_natural`.
* **`stalkSecL H : H_s ⟶ (s^* H)(Spec Ω)`** (a `ModuleCat` map, `presheafFiberDesc`), `stalkSecL_germ`, `stalkSecL_natural`.
* **`stalkSec H : H_s →+ (Λ_{Spec Ω} ⟶ s^* H)`**, `stalkSec_germ`, `stalkSec_natural`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.PtSec RamanujanPetersson.EtCompact.Supp

universe u

variable {Λ : Type u} [CommRing Λ] {S : Scheme.{u}} (s : GeomPt S)

/-- The section `Spec Ω ⟶ s⁻¹ X` given by a point `x` of `X` over `s`. -/
def ptSec (X : S.Etale) (x : s.point.fiber.obj X) :
    etId (Spec (CommRingCat.of s.Ω)) ⟶ (etPull s.pt).obj X :=
  MorphismProperty.Over.homMk (pullback.lift x.left (𝟙 _) ((Over.w x).trans (Category.id_comp _).symm))
    (pullback.lift_snd _ _ _)

theorem ptSec_left_fst (X : S.Etale) (x : s.point.fiber.obj X) :
    (ptSec s X x).left ≫ pullback.fst X.hom s.pt = x.left :=
  pullback.lift_fst _ _ _

theorem ptSec_comp {X Y : S.Etale} (f : X ⟶ Y) (x : s.point.fiber.obj X) :
    ptSec s X x ≫ (etPull s.pt).map f = ptSec s Y (s.point.fiber.map f x) :=
  etPull_hom_ext s.pt ((Category.assoc _ _ _).trans ((whisker_eq _ (etPull_map_left_fst s.pt f)).trans
    (((Category.assoc _ _ _).symm.trans (eq_whisker (ptSec_left_fst s X x) _)).trans
      ((show x.left ≫ f.left = (s.point.fiber.map f x).left from rfl).trans (ptSec_left_fst s Y _).symm))))

variable (H : EtSh Λ S)

/-- `z ↦ (s^* z)|_{ptSec X x}`. -/
def ptRes (X : S.Etale) (x : s.point.fiber.obj X) :
    H.obj.obj (op X) ⟶ ((pull s.pt Λ).obj H).obj.obj (op (etId (Spec (CommRingCat.of s.Ω)))) :=
  ((pullAdj s.pt Λ).unit.app H).hom.app (op X) ≫ ((pull s.pt Λ).obj H).obj.map (ptSec s X x).op

theorem ptRes_apply (X : S.Etale) (x : s.point.fiber.obj X) (z : H.obj.obj (op X)) :
    (ptRes s H X x).hom z = (((pull s.pt Λ).obj H).obj.map (ptSec s X x).op).hom (pbSec s.pt z) := by
  change (((pull s.pt Λ).obj H).obj.map (ptSec s X x).op).hom
    ((((pullAdj s.pt Λ).unit.app H).hom.app (op X)).hom z) = _
  rw [unit_pbSec]

theorem ptRes_natural {X Y : S.Etale} (f : X ⟶ Y) (x : s.point.fiber.obj X) :
    H.obj.map f.op ≫ ptRes s H X x = ptRes s H Y (s.point.fiber.map f x) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  change (ptRes s H X x).hom ((H.obj.map f.op).hom z) = (ptRes s H Y (s.point.fiber.map f x)).hom z
  rw [ptRes_apply, ptRes_apply, pbSec_restrict, mapMapApply, ptSec_comp]

/-- **The stalk of `H` at `s` mapped to the global sections of `s^* H`.** -/
def stalkSecL : (s.stalkF Λ).obj H ⟶ ((pull s.pt Λ).obj H).obj.obj (op (etId (Spec (CommRingCat.of s.Ω)))) :=
  s.point.presheafFiberDesc (ptRes s H) (fun _ _ f x => ptRes_natural s H f x)

theorem stalkSecL_germ (X : S.Etale) (x : s.point.fiber.obj X) :
    s.point.toPresheafFiber X x H.obj ≫ stalkSecL s H = ptRes s H X x :=
  GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc _ _ _ _ _

theorem stalkSecL_natural {H H' : EtSh Λ S} (φ : H ⟶ H') :
    (s.stalkF Λ).map φ ≫ stalkSecL s H' =
      stalkSecL s H ≫ ((pull s.pt Λ).map φ).hom.app (op (etId (Spec (CommRingCat.of s.Ω)))) := by
  refine s.point.presheafFiber_hom_ext (fun X x => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  change (stalkSecL s H').hom (((s.stalkF Λ).map φ).hom ((s.point.toPresheafFiber X x H.obj).hom z)) =
    (((pull s.pt Λ).map φ).hom.app (op (etId _))).hom
      ((stalkSecL s H).hom ((s.point.toPresheafFiber X x H.obj).hom z))
  have e1 : ((s.stalkF Λ).map φ).hom ((s.point.toPresheafFiber X x H.obj).hom z) =
      (s.point.toPresheafFiber X x H'.obj).hom ((φ.hom.app (op X)).hom z) :=
    congrArg (fun m => m.hom z) (GrothendieckTopology.Point.toPresheafFiber_naturality s.point φ.hom X x)
  have e2 : ∀ (G : EtSh Λ S) (w : G.obj.obj (op X)),
      (stalkSecL s G).hom ((s.point.toPresheafFiber X x G.obj).hom w) = (ptRes s G X x).hom w :=
    fun G w => congrArg (fun m => m.hom w) (stalkSecL_germ s G X x)
  rw [e1, e2, e2, ptRes_apply, ptRes_apply, pbSec_natural]
  exact congrArg (fun m => m.hom (pbSec s.pt z)) (((pull s.pt Λ).map φ).hom.naturality (ptSec s X x).op).symm

theorem ofSec_add {Y : Scheme.{u}} {F : EtSh Λ Y} (q q' : F.obj.obj (op (etId Y))) :
    ofSec (q + q') = ofSec q + ofSec q' := by
  conv_lhs => rw [← sc_ofSec q, ← sc_ofSec q', ← sc_add]
  exact ofSec_sc _

/-- **`H_s →+ Hom(Λ_{Spec Ω}, s^* H)`**: a germ `[z]` at `(X, x)` goes to the global section `(s^* z)|_{ptSec X x}`. -/
def stalkSec : (s.stalkF Λ).obj H →+ (unitSh Λ (Spec (CommRingCat.of s.Ω)) ⟶ (pull s.pt Λ).obj H) :=
  AddMonoidHom.mk' (fun y => ofSec ((stalkSecL s H).hom y)) (fun y y' => by rw [map_add, ofSec_add])

theorem stalkSec_apply (y : (s.stalkF Λ).obj H) : stalkSec s H y = ofSec ((stalkSecL s H).hom y) := by
  rw [stalkSec, AddMonoidHom.mk'_apply]

theorem stalkSec_germ (X : S.Etale) (x : s.point.fiber.obj X) (z : H.obj.obj (op X)) :
    stalkSec s H ((s.point.toPresheafFiber X x H.obj).hom z) =
      ofSec ((((pull s.pt Λ).obj H).obj.map (ptSec s X x).op).hom (pbSec s.pt z)) := by
  refine (stalkSec_apply s H _).trans ?_
  have e : (stalkSecL s H).hom ((s.point.toPresheafFiber X x H.obj).hom z) = (ptRes s H X x).hom z :=
    congrArg (fun m => m.hom z) (stalkSecL_germ s H X x)
  rw [e, ptRes_apply]

theorem stalkSec_natural {H H' : EtSh Λ S} (φ : H ⟶ H') (y : (s.stalkF Λ).obj H) :
    stalkSec s H' (((s.stalkF Λ).map φ).hom y) = stalkSec s H y ≫ (pull s.pt Λ).map φ := by
  have e : (stalkSecL s H').hom (((s.stalkF Λ).map φ).hom y) =
      (((pull s.pt Λ).map φ).hom.app (op (etId _))).hom ((stalkSecL s H).hom y) :=
    congrArg (fun m => m.hom y) (stalkSecL_natural s φ)
  rw [stalkSec_apply, stalkSec_apply, ofSec_comp, e]

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_Coc =====
section

/-!
# S4-EtPBC-C1, part 11: the cochain identity behind `pbcEquiv`

* `ptUnit s V v : Λ_{Spec Ω} ⟶ s^* Λ[V]`, the global section `(s^* taut)|_{ptSec V v}`; `sc_ptUnit_comp`.
* Generic square `w : h' ≫ ιY = ιX ≫ h` (kept generic so the kernel never unfolds `pull` on concrete pullbacks):
  `SecCompat` (a section `σ` of `ιY⁻¹ V` pulled back along `h'` is `τ`), `cocL_gen`, `cocR_gen`, and
  **`coc_gen`**: `a ≫ bcCell_N = (h'^* ⊣ h'_*).homEquiv ((pullUnit h').inv ≫ b)` when the global sections of `a`, `b`
  are `(ιY^* c)|_σ`, `(ιX^* c)|_τ`.
* `ptSec_kappa`: `ptSec` and `nbhdSec` satisfy `SecCompat` for the fibre square of `g` at `s`.
* **`coc_eq`**: `(ptUnit ≫ s^* ĉ') ≫ bcCell_N = (π^* ⊣ π_*).homEquiv ((pullUnit π).inv ≫ bcUnit j ≫ ι^* ĉ)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.PtSec RamanujanPetersson.EtCompact.Supp RamanujanPetersson.EtCompact.GalTrE
  RamanujanPetersson.EtPBC.GenAlg

universe u

variable {Λ : Type u} [CommRing Λ]

section Pt

variable {S : Scheme.{u}} (s : GeomPt S)

/-- `Λ_{Spec Ω} ⟶ s^* Λ[V]`, the global section `(s^* taut)|_{ptSec V v}`. -/
def ptUnit (V : S.Etale) (v : s.point.fiber.obj V) :
    unitSh Λ (Spec (CommRingCat.of s.Ω)) ⟶ (pull s.pt Λ).obj (freeSh Λ V) :=
  ofSec ((((pull s.pt Λ).obj (freeSh Λ V)).obj.map (ptSec s V v).op).hom (pbSec s.pt (taut Λ V)))

theorem sc_ptUnit (V : S.Etale) (v : s.point.fiber.obj V) :
    sc (ptUnit (Λ := Λ) s V v) (etId _) =
      (((pull s.pt Λ).obj (freeSh Λ V)).obj.map (ptSec s V v).op).hom (pbSec s.pt (taut Λ V)) :=
  sc_ofSec _

/-- `ptUnit ≫ s^* μ` is the global section `(s^* μ(taut))|_{ptSec}`. -/
theorem sc_ptUnit_comp {V : S.Etale} (v : s.point.fiber.obj V) {M : EtSh Λ S} (μ : freeSh Λ V ⟶ M) :
    sc (ptUnit s V v ≫ (pull s.pt Λ).map μ) (etId _) =
      (((pull s.pt Λ).obj M).obj.map (ptSec s V v).op).hom (pbSec s.pt ((μ.hom.app (op V)).hom (taut Λ V))) := by
  rw [sc_comp, sc_ptUnit, pbSec_natural]
  exact congrArg (fun m => m.hom (pbSec s.pt (taut Λ V))) (((pull s.pt Λ).map μ).hom.naturality (ptSec s V v).op)

end Pt

section Gen

variable {X Y Xs Ys : Scheme.{u}} (ιX : Xs ⟶ X) (ιY : Ys ⟶ Y) (h : X ⟶ Y) (h' : Xs ⟶ Ys)
  (w : h' ≫ ιY = ιX ≫ h)

theorem nat_apply {Z : Scheme.{u}} {F G : EtSh Λ Z} (τ : F ⟶ G) {U U' : Z.Etaleᵒᵖ} (f : U ⟶ U')
    (x : F.obj.obj U) : (τ.hom.app U').hom ((F.obj.map f).hom x) = (G.obj.map f).hom ((τ.hom.app U).hom x) :=
  congrArg (fun m => m.hom x) (τ.hom.naturality f)

theorem mapMapApplyO {Z : Scheme.{u}} (F : EtSh Λ Z) {A B C : Z.Etaleᵒᵖ} (a : A ⟶ B) (b : B ⟶ C)
    (x : F.obj.obj A) : (F.obj.map b).hom ((F.obj.map a).hom x) = (F.obj.map (a ≫ b)).hom x := by
  rw [Functor.map_comp]; rfl

/-- `σ` pulled back along `h'` is `τ` (through the canonical isos). -/
abbrev SecCompat (V : Y.Etale) (σ : etId Ys ⟶ (etPull ιY).obj V) (τ : etId Xs ⟶ (etPull ιX).obj ((etPull h).obj V)) :
    Prop :=
  (etIdPull h').hom ≫ (etPull h').map σ ≫ (etPullCompIso h' ιY).inv.app V ≫ etPullCongr w V ≫
    (etPullCompIso ιX h).hom.app V = τ

theorem secCompat_op (V : Y.Etale) (σ : etId Ys ⟶ (etPull ιY).obj V)
    (τ : etId Xs ⟶ (etPull ιX).obj ((etPull h).obj V)) (hστ : SecCompat ιX ιY h h' w V σ τ) :
    (((etPullCompIso ιX h).hom.app V).op ≫ (etPullCongr w V).op ≫ ((etPullCompIso h' ιY).inv.app V).op) ≫
      ((etPull h').map σ).op = ((etIdPull h').inv ≫ τ).op := by
  rw [← hστ, Iso.inv_hom_id_assoc]
  simp only [op_comp, Category.assoc]

theorem cocL_gen (N : EtSh Λ X) (V : Y.Etale) (c : ((push h Λ).obj N).obj.obj (op V))
    (σ : etId Ys ⟶ (etPull ιY).obj V) (a : unitSh Λ Ys ⟶ (pull ιY Λ).obj ((push h Λ).obj N))
    (ha : sc a (etId Ys) = (((pull ιY Λ).obj ((push h Λ).obj N)).obj.map σ.op).hom (pbSec ιY (V := V) c)) :
    sc (a ≫ (bcCell Λ ιX ιY h h' w).app N) (etId Ys) =
      (((pull ιX Λ).obj N).obj.map ((((etPullCompIso ιX h).hom.app V).op ≫ (etPullCongr w V).op ≫
        ((etPullCompIso h' ιY).inv.app V).op) ≫ ((etPull h').map σ).op)).hom
        (pbSec ιX (V := (etPull h).obj V) c) := by
  rw [sc_comp, ha, nat_apply, bcCell_pbSec]
  exact mapMapApplyO ((pull ιX Λ).obj N) _ ((etPull h').map σ).op _

theorem cocR_gen (N : EtSh Λ X) (b : unitSh Λ Xs ⟶ (pull ιX Λ).obj N) :
    sc ((pullAdj h' Λ).homEquiv _ _ ((pullUnit Λ h').inv ≫ b)) (etId Ys) =
      (((pull ιX Λ).obj N).obj.map (etIdPull h').inv.op).hom (sc b (etId Xs)) := by
  have h1 : sc ((pullAdj h' Λ).homEquiv _ _ ((pullUnit Λ h').inv ≫ b)) (etId Ys) =
      (((pullUnit Λ h').inv ≫ b).hom.app (op ((etPull h').obj (etId _)))).hom (pbSec h' (oneSec Λ _)) := by
    rw [Adjunction.homEquiv_unit]
    exact unit_comp_push_apply h' _ _ _ _ _
  have h2 : pbSec h' (oneSec Λ Ys) =
      ((((pull h' Λ).obj (unitSh Λ _)).obj.map (etIdPull h').inv.op).hom
        (((pullUnit Λ h').hom.hom.app (op (etId Xs))).hom (oneSec Λ Xs))) := by
    rw [pullUnit_one, mapMapApply, Iso.inv_hom_id, op_id, map_id_apply']
  have h4 : sc b (etId Xs) = ((((pullUnit Λ h').inv ≫ b).hom.app (op (etId Xs))).hom
      (((pullUnit Λ h').hom.hom.app (op (etId Xs))).hom (oneSec Λ Xs))) := by
    have e := sc_comp (pullUnit Λ h').hom ((pullUnit Λ h').inv ≫ b) (etId Xs)
    rw [Iso.hom_inv_id_assoc] at e
    exact e
  rw [h1, h2, nat_apply, h4]

/-- **The cochain identity**, for a generic square with matching point sections `σ`, `τ`. -/
theorem coc_gen (N : EtSh Λ X) (V : Y.Etale) (c : ((push h Λ).obj N).obj.obj (op V))
    (σ : etId Ys ⟶ (etPull ιY).obj V) (τ : etId Xs ⟶ (etPull ιX).obj ((etPull h).obj V))
    (hστ : SecCompat ιX ιY h h' w V σ τ) (a : unitSh Λ Ys ⟶ (pull ιY Λ).obj ((push h Λ).obj N))
    (ha : sc a (etId Ys) = (((pull ιY Λ).obj ((push h Λ).obj N)).obj.map σ.op).hom (pbSec ιY (V := V) c))
    (b : unitSh Λ Xs ⟶ (pull ιX Λ).obj N)
    (hb : sc b (etId Xs) = (((pull ιX Λ).obj N).obj.map τ.op).hom (pbSec ιX (V := (etPull h).obj V) c)) :
    a ≫ (bcCell Λ ιX ιY h h' w).app N = (pullAdj h' Λ).homEquiv _ _ ((pullUnit Λ h').inv ≫ b) := by
  refine (ofSec_sc _).symm.trans ((congrArg ofSec ?_).trans (ofSec_sc _))
  rw [cocL_gen ιX ιY h h' w N V c σ a ha, cocR_gen ιX h' N b, hb, mapMapApply]
  exact map_congr_apply _ (secCompat_op ιX ιY h h' w V σ τ hστ) _

end Gen

variable {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

theorem left_fst_snd {V : S.Etale} {Z : (fib g s).Etale} (a : Z ⟶ (etPull (fibι g s)).obj ((etPull g).obj V)) :
    a.left ≫ pullback.fst ((etPull g).obj V).hom (fibι g s) ≫ pullback.snd V.hom g = Z.hom ≫ fibι g s :=
  (whisker_eq _ pullback.condition).trans (MorphismProperty.Over.w_assoc a _)

set_option backward.isDefEq.respectTransparency false in
/-- The point section `ptSec` pulled back along `π` is the neighbourhood section `nbhdSec`. -/
theorem ptSec_kappa (j : Nbhd s) :
    (etIdPull (pullback.snd g s.pt)).hom ≫ (etPull (pullback.snd g s.pt)).map (ptSec s j.1 j.2) ≫
      (etPullCompIso (pullback.snd g s.pt) s.pt).inv.app j.1 ≫
      etPullCongr (pullback.condition (f := g) (g := s.pt)).symm j.1 ≫ (etPullCompIso (fibι g s) g).hom.app j.1 =
    nbhdSec g s j := by
  refine etPull_hom_ext (fibι g s) (pullback.hom_ext ?_ ?_)
  · change (etIdPull (pullback.snd g s.pt)).hom.left ≫ ((etPull (pullback.snd g s.pt)).map (ptSec s j.1 j.2)).left ≫
      ((etPullCompIso (pullback.snd g s.pt) s.pt).inv.app j.1).left ≫
      (etPullCongr (pullback.condition (f := g) (g := s.pt)).symm j.1).left ≫
      ((etPullCompIso (fibι g s) g).hom.app j.1).left ≫ pullback.fst ((etPull g).obj j.1).hom (fibι g s) ≫
      pullback.fst j.1.hom g = secL g s j ≫ pullback.fst ((etPull g).obj j.1).hom (fibι g s) ≫ pullback.fst j.1.hom g
    rw [etPullCompIso_hom_fst_fst, etPullCongr_left_fst, etPullCompIso_inv_fst, etPull_map_left_fst_r,
      ptSec_left_fst, etIdPull_hom_left_fst_r]
    exact ((secL_fst_assoc g s j _).trans (fibToNbhd_fst g s j)).symm
  · exact (Category.assoc _ _ _).trans ((left_fst_snd g s _).trans ((left_fst_snd g s _).symm.trans
      (Category.assoc _ _ _).symm))

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_ExtMap =====
section

/-!
# S4-EtPBC-C1, part 6: `Ext.mapExactFunctor` of an `extMk` class

For an exact functor `L : C ⥤ D`, an injective resolution `R` of `Y`, an injective resolution `R'` of `L Y` and a
morphism of complexes `φ : L R ⟶ R'` over `𝟙 (L Y)`:
**`mapExactFunctor_extMk`**: `(R.extMk f).mapExactFunctor L = R'.extMk (L f ≫ φ_n)`.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian Localization CochainComplex HomComplex

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

universe w w' v₁ v₂ u₁ u₂

section Small

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

theorem ssh_mk₀_comp {K₁ K₂ K₃ : CochainComplex D ℤ}
    [HasSmallLocalizedShiftedHom.{w'} (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) ℤ K₁ K₂]
    [HasSmallLocalizedShiftedHom.{w'} (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) ℤ K₂ K₃]
    [HasSmallLocalizedShiftedHom.{w'} (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) ℤ K₁ K₃]
    [HasSmallLocalizedShiftedHom.{w'} (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) ℤ K₃ K₃]
    (a : K₁ ⟶ K₂) (b : K₂ ⟶ K₃) :
    SmallShiftedHom.mk₀.{w'} (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) (0 : ℤ) rfl (a ≫ b) =
      (SmallShiftedHom.mk₀ _ (0 : ℤ) rfl a).comp (SmallShiftedHom.mk₀ _ (0 : ℤ) rfl b) (zero_add 0) := by
  let := HasDerivedCategory.standard D
  apply (SmallShiftedHom.equiv _ DerivedCategory.Q).injective
  simp [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀, ShiftedHom.mk₀_comp_mk₀]

theorem ssh_mk_comp_mk₀ {K₁ K₂ K₃ : CochainComplex D ℤ} {n : ℤ}
    [HasSmallLocalizedShiftedHom.{w'} (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) ℤ K₁ K₂]
    [HasSmallLocalizedShiftedHom.{w'} (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) ℤ K₂ K₃]
    [HasSmallLocalizedShiftedHom.{w'} (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) ℤ K₁ K₃]
    [HasSmallLocalizedShiftedHom.{w'} (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) ℤ K₃ K₃]
    (a : K₁ ⟶ K₂⟦n⟧) (b : K₂ ⟶ K₃) :
    (SmallShiftedHom.mk.{w'} (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) (a : ShiftedHom K₁ K₂ n)).comp
        (SmallShiftedHom.mk₀ _ (0 : ℤ) rfl b) (zero_add n) =
      SmallShiftedHom.mk _ ((a ≫ b⟦n⟧' : K₁ ⟶ K₃⟦n⟧) : ShiftedHom K₁ K₃ n) := by
  let := HasDerivedCategory.standard D
  apply (SmallShiftedHom.equiv _ DerivedCategory.Q).injective
  simp only [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀, SmallShiftedHom.equiv_mk,
    ShiftedHom.comp_mk₀, ShiftedHom.map, Functor.map_comp, Category.assoc]
  congr 1
  exact ((DerivedCategory.Q.commShiftIso n).hom.naturality b).symm

end Small

section ClassComp

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C] {X Y : C}
  (R : InjectiveResolution Y) {n : ℕ}

/-- Composing an `Ext` class with `R.ι'` gives its cohomology class. -/
theorem ext_comp_ι' (x : Ext.{w} X Y n) :
    SmallShiftedHom.comp (M := ℤ) x (SmallShiftedHom.mk₀ _ _ rfl R.ι') (zero_add _) =
      (R.extEquivCohomologyClass x).toSmallShiftedHom := by
  have h : (R.extEquivCohomologyClass x).toSmallShiftedHom =
      CohomologyClass.equivOfIsKInjective.{w} (R.extEquivCohomologyClass x) := rfl
  rw [h]
  show _ = CohomologyClass.equivOfIsKInjective.{w} (CohomologyClass.equivOfIsKInjective.{w}.symm
    (SmallShiftedHom.postcompEquiv.{w} R.ι' _ x))
  rw [Equiv.apply_symm_apply]
  rfl

end ClassComp

section Map

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  {X Y : C} (R : InjectiveResolution Y) (R' : InjectiveResolution (L.obj Y))
  (φ : (L.mapHomologicalComplex _).obj R.cocomplex ⟶ R'.cocomplex)

set_option backward.isDefEq.respectTransparency false in
/-- The `ℕ`-part of `L R.cochainComplex ⟶ R'.cocomplex`. -/
def liftZres : ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex).restriction
    ComplexShape.embeddingUpNat ⟶ R'.cocomplex where
  f i := L.map (R.cochainComplexXIso i i rfl).hom ≫ φ.f i
  comm' i j _ := by
    have := φ.comm i j
    simp only [Functor.mapHomologicalComplex_obj_d] at this
    change _ = L.map (R.cochainComplex.d i j) ≫ L.map (R.cochainComplexXIso j j rfl).hom ≫ φ.f j
    rw [R.cochainComplex_d i j i j rfl rfl]
    simp only [Functor.map_comp, Category.assoc]
    rw [← L.map_comp_assoc (R.cochainComplexXIso j j rfl).inv, Iso.inv_hom_id, L.map_id,
      Category.id_comp, ← this]

theorem liftZres_hasLift : ComplexShape.embeddingUpNat.HasLift (liftZres L R R' φ) := by
  intro j hj i' hi'
  apply IsZero.eq_of_src
  apply Functor.map_isZero
  have hj0 : j = 0 := by
    rcases j with _ | k
    · rfl
    · exact (hj.2 k (show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; rfl)).elim
  subst hj0
  exact CochainComplex.isZero_of_isStrictlyGE R.cochainComplex 0 i' (by
    have : i' + 1 = ((0 : ℕ) : ℤ) := hi'
    lia)

/-- **`φ` on the `ℤ`-indexed complexes**: `L R.cochainComplex ⟶ R'.cochainComplex`. -/
def liftZ : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex ⟶ R'.cochainComplex :=
  ComplexShape.embeddingUpNat.liftExtend (liftZres L R R' φ) (liftZres_hasLift L R R' φ)

set_option backward.isDefEq.respectTransparency false in
theorem liftZ_f (i : ℤ) (k : ℕ) (h : (k : ℤ) = i) :
    (liftZ L R R' φ).f i = L.map (R.cochainComplexXIso i k h).hom ≫ φ.f k ≫
      (R'.cochainComplexXIso i k h).inv := by
  subst h
  erw [ComplexShape.Embedding.liftExtend_f _ _ _ (rfl : ComplexShape.embeddingUpNat.f k = (k : ℤ))]
  simp only [liftZres, HomologicalComplex.restrictionXIso, InjectiveResolution.cochainComplexXIso, eqToIso.inv]
  exact (Category.id_comp _).trans (Category.assoc _ _ _)

variable (hφ : L.map (R.ι.f 0) ≫ φ.f 0 = R'.ι.f 0)
include hφ

set_option backward.isDefEq.respectTransparency false in
theorem ι'_liftZ : (L.mapCochainComplexSingleFunctor 0).inv.app Y ≫
    (L.mapHomologicalComplex _).map R.ι' ≫ liftZ L R R' φ = R'.ι' := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, liftZ_f L R R' φ 0 0 (by simp),
    InjectiveResolution.ι'_f_zero R', Functor.mapHomologicalComplex_map_f, InjectiveResolution.ι'_f_zero R]
  simp only [Functor.mapCochainComplexSingleFunctor, HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  have e1 : L.map (R.cochainComplexXIso 0 0 (by simp)).inv ≫ L.map (R.cochainComplexXIso 0 0 (by simp)).hom =
      𝟙 _ := by rw [← L.map_comp, Iso.inv_hom_id, L.map_id]
  have e2 : L.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).inv ≫
      L.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).hom = 𝟙 _ := by
    rw [← L.map_comp, Iso.inv_hom_id, L.map_id]
  simp only [Functor.map_comp, Category.assoc, reassoc_of% e1, reassoc_of% e2, reassoc_of% hφ]

end Map

section Coc

theorem homOf_f {E : Type*} [Category E] [Preadditive E] {A B : CochainComplex E ℤ} (z : Cocycle A B 0)
    (p : ℤ) : (Cocycle.homOf z).f p = (z : Cochain A B 0).v p p (add_zero p) := rfl

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

set_option backward.isDefEq.respectTransparency false in
/-- `L` applied to the morphism of a cocycle from a single complex. -/
theorem map_equivHomShift_fromSingleMk {X : C} {K : CochainComplex C ℤ} {n : ℤ} (f : X ⟶ K.X n) (m : ℤ)
    (hm : n + 1 = m) (hf : f ≫ K.d n m = 0) :
    (L.mapCochainComplexSingleFunctor 0).inv.app X ≫
      (L.mapHomologicalComplex _).map (Cocycle.equivHomShift.symm (Cocycle.fromSingleMk f (zero_add n) m hm hf)) ≫
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app K =
      Cocycle.equivHomShift.symm (Cocycle.fromSingleMk (L.map f) (zero_add n) m hm
        (by simp only [Functor.mapHomologicalComplex_obj_d]; rw [← L.map_comp, hf, L.map_zero])) := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f, Functor.mapCochainComplexSingleFunctor,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Cocycle.equivHomShift_symm_apply]
  erw [Category.comp_id]
  rw [homOf_f, homOf_f, Cocycle.rightShift_coe, Cocycle.rightShift_coe, Cocycle.fromSingleMk_coe,
    Cocycle.fromSingleMk_coe, Cochain.rightShift_v _ _ _ _ 0 0 (add_zero 0) n (zero_add n),
    Cochain.rightShift_v _ _ _ _ 0 0 (add_zero 0) n (zero_add n), Cochain.fromSingleMk_v, Cochain.fromSingleMk_v]
  simp [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq, eqToHom_map]

end Coc

section Main

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [HasExt.{w'} D] (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  {X Y : C} (R : InjectiveResolution Y) (R' : InjectiveResolution (L.obj Y))
  (φ : (L.mapHomologicalComplex _).obj R.cocomplex ⟶ R'.cocomplex)
  (hφ : L.map (R.ι.f 0) ≫ φ.f 0 = R'.ι.f 0)

theorem isLE_mapR : CochainComplex.IsLE ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex) 0 := by
  have : QuasiIso ((L.mapCochainComplexSingleFunctor 0).inv.app Y ≫ (L.mapHomologicalComplex _).map R.ι') :=
    inferInstance
  simp only [← HomologicalComplex.isSupported_iff_of_quasiIso
    ((L.mapCochainComplexSingleFunctor 0).inv.app Y ≫ (L.mapHomologicalComplex _).map R.ι')]
  exact inferInstanceAs (((CochainComplex.singleFunctor D 0).obj (L.obj Y)).IsLE 0)

set_option backward.isDefEq.respectTransparency false in
theorem extMk_cond {n : ℕ} (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hf : f ≫ R.cocomplex.d n m = 0) :
    (L.map f ≫ φ.f n) ≫ R'.cocomplex.d n m = 0 := by
  have := φ.comm n m
  simp only [Functor.mapHomologicalComplex_obj_d] at this
  rw [Category.assoc, this, ← L.map_comp_assoc, hf, L.map_zero, Limits.zero_comp]

include hφ

end Main
end RamanujanPetersson.EtPBC.C1
end

end

-- ===== S4.Def_RP_EtPBC_C1_StkHom =====
section

/-!
# S4-EtPBC-C1, part 12: a cocycle class in the stalk of `R^(p+1) g_* F`

For a complex `K` of etale sheaves on `P`, `g : P ⟶ S`, `V : S.Etale` and a cycle `cyc` of the section complex
`K(g⁻¹ V)` in degree `p + 1`:
* `freeCoc cyc : Λ[V] ⟶ (g_* K)^(p+1)` (the cocycle as a map from the free sheaf) and
  **`cocCls cyc : Λ[V] ⟶ H^(p+1)(g_* K)`** (its class);
* **`stalkHom_germ`**: `stalkHomologyIso` sends the germ of `cocCls cyc (taut)` to the germ of `[cyc]`;
* `stalkSec_germ_taut`: `stalkSec (germ μ(taut)) = ptUnit ≫ s^* μ`;
* **`stalkSec_rd`**: for `K = I^•`, `stalkSec (stalkRDIso⁻¹ (germ [cyc])) = ptUnit ≫ s^*(cocCls cyc ≫ isoRD⁻¹)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.PtSec RamanujanPetersson.EtCompact.Supp RamanujanPetersson.EtPBC.GenAlg
  RamanujanPetersson.EtCompact.GalTrE

universe u

section Gen

end Gen

set_option backward.isDefEq.respectTransparency false

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)
  (K : CochainComplex (EtSh Λ P) ℕ) (p : ℕ) {V : S.Etale}

/-- The pushed complex `g_* K`. -/
abbrev pushCx : CochainComplex (EtSh Λ S) ℕ := ((push g Λ).mapHomologicalComplex _).obj K

/-- A section cycle of `K(g⁻¹ V)` as a map `Λ[V] ⟶ (g_* K)^(p+1)`. -/
def freeCoc (cyc : ((secCx Λ K ((etPull g).obj V)).sc (p + 1)).cycles) :
    freeSh Λ V ⟶ (pushCx g K).X (p + 1) :=
  (freeEquiv Λ V ((pushCx g K).X (p + 1))).symm (((secCx Λ K ((etPull g).obj V)).sc (p + 1)).iCycles.hom cyc)

theorem freeCoc_taut (cyc : ((secCx Λ K ((etPull g).obj V)).sc (p + 1)).cycles) :
    ((freeCoc g K p cyc).hom.app (op V)).hom (taut Λ V) =
      ((secCx Λ K ((etPull g).obj V)).sc (p + 1)).iCycles.hom cyc :=
  freeEquiv_symm_taut Λ V _ _

variable {s} in
/-- `stalkSec (germ μ(taut)) = ptUnit ≫ s^* μ`. -/
theorem stalkSec_germ_taut (v : s.point.fiber.obj V) {M : EtSh Λ S} (μ : freeSh Λ V ⟶ M) :
    stalkSec s M ((s.point.toPresheafFiber V v M.obj).hom ((μ.hom.app (op V)).hom (taut Λ V))) =
      ptUnit s V v ≫ (pull s.pt Λ).map μ := by
  rw [stalkSec_germ, ← sc_ptUnit_comp, ofSec_sc]

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_PtProj =====
section

/-!
# S4-EtPBC-C1, part 8: `Λ` is projective on `Spec Ω`, `Ω` separably closed

**`unitSh_projective_spec`**: `Projective (unitSh Λ (Spec (CommRingCat.of Ω)))` for a separably closed field `Ω`
(the input `absRelEquiv` needs for the geometric fibre square). Via `EtCompact.unitSh_projective` at the
unique point `⊥` of `Spec Ω`, whose residue field is `Ω`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

/-- Separable closedness transfers along ring isomorphisms. -/
theorem isSepClosed_of_ringEquiv {k K : Type u} [Field k] [Field K] [IsSepClosed k] (e : k ≃+* K) :
    IsSepClosed K := by
  refine IsSepClosed.of_exists_root K (fun p hmo hirr hsep => ?_)
  set q : Polynomial k := p.map e.symm.toRingHom with hq
  have hdeg : q.degree ≠ 0 := by
    rw [hq, Polynomial.degree_map]
    exact fun h => hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr h)
  obtain ⟨r, hr⟩ := IsSepClosed.exists_root q hdeg (hsep.map)
  refine ⟨e r, ?_⟩
  have hp : p = q.map e.toRingHom := by
    rw [hq, Polynomial.map_map]
    simp
  rw [hp, Polynomial.eval_map]
  show Polynomial.eval₂ e.toRingHom (e.toRingHom r) q = 0
  rw [Polynomial.eval₂_hom, Polynomial.IsRoot.def.mp hr, map_zero]

variable (Ω : Type u) [Field Ω]

/-- The unique point `⊥` of `Spec Ω`. -/
def specPt : Spec (CommRingCat.of Ω) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω)

theorem specPt_asIdeal : (specPt Ω).asIdeal = ⊥ := rfl

instance specPt_isMaximal : (specPt Ω).asIdeal.IsMaximal := by
  rw [specPt_asIdeal]; exact Ideal.bot_isMaximal

theorem algebraMap_specPt_bijective :
    Function.Bijective (algebraMap Ω (specPt Ω).asIdeal.ResidueField) :=
  ⟨(algebraMap Ω _).injective, Ideal.algebraMap_residueField_surjective _⟩

instance isIso_fromSpecResidueField_specPt :
    IsIso ((Spec (CommRingCat.of Ω)).fromSpecResidueField (specPt Ω)) := by
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  have : IsIso (CommRingCat.ofHom (algebraMap Ω (specPt Ω).asIdeal.ResidueField)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (algebraMap_specPt_bijective Ω)
  infer_instance

/-- `Ω ≃+* κ(⊥)`. -/
def residueEquivSpecPt : Ω ≃+* (Spec (CommRingCat.of Ω)).residueField (specPt Ω) :=
  (RingEquiv.ofBijective _ (algebraMap_specPt_bijective Ω)).trans
    (Scheme.Spec.residueFieldIso (CommRingCat.of Ω) (specPt Ω)).symm.commRingCatIsoToRingEquiv

instance isSepClosed_residue_specPt [IsSepClosed Ω] :
    IsSepClosed ((Spec (CommRingCat.of Ω)).residueField (specPt Ω)) :=
  isSepClosed_of_ringEquiv (residueEquivSpecPt Ω)

/-- **`Λ` is projective on `Spec Ω`** for `Ω` separably closed. -/
theorem unitSh_projective_spec [IsSepClosed Ω] (Λ : Type u) [CommRing Λ] :
    Projective (unitSh Λ (Spec (CommRingCat.of Ω))) :=
  haveI := gal_subsingleton (specPt Ω)
  unitSh_projective (specPt Ω) Λ

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_PsiA =====
section

/-!
# S4-EtPBC-C1, part 14a: generic glue in `coc_gen` shape; the section cocycle on `P`

* `extMk_congr`, `extMk_succ`: bookkeeping for `InjectiveResolution.extMk`;
* `glue3`: the generic comparison (`glue_gen`) with its hypothesis in the shape of `coc_gen`
  (`k` into `R (I^(p+1))`, `e.inv`) and the cocycle `f` and class `m` given by defining equations;
* `freeCocP cyc : Λ[g⁻¹ V] ⟶ I^(p+1)`, its cocycle conditions, and `germExt_cyc`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtCompact.PtSec

section ExtMk

universe w

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w} C] {X Y : C} (R : InjectiveResolution Y) {n : ℕ}

theorem extMk_congr {f f' : X ⟶ R.cocomplex.X n} (h : f = f') (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) (hf' : f' ≫ R.cocomplex.d n m = 0) :
    R.extMk f m hm hf = R.extMk f' m hm hf' := by
  subst h
  rfl

theorem extMk_succ (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m) (hf : f ≫ R.cocomplex.d n m = 0)
    (hf' : f ≫ R.cocomplex.d n (n + 1) = 0) : R.extMk f m hm hf = R.extMk f (n + 1) rfl hf' := by
  subst hm
  rfl

end ExtMk

section G3

universe w

end G3

universe u

set_option backward.isDefEq.respectTransparency false

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S) {F : EtSh Λ P}
  (I : InjectiveResolution F) (J : InjectiveResolution ((pull (fibι g s) Λ).obj F)) (p : ℕ)

/-- The section cycle as `Λ[g⁻¹ V] ⟶ I^(p+1)` on `P`. -/
def freeCocP {V : S.Etale} (cyc : ((secCx Λ I.cocomplex ((etPull g).obj V)).sc (p + 1)).cycles) :
    freeSh Λ ((etPull g).obj V) ⟶ I.cocomplex.X (p + 1) :=
  (freeEquiv Λ ((etPull g).obj V) (I.cocomplex.X (p + 1))).symm
    (((secCx Λ I.cocomplex ((etPull g).obj V)).sc (p + 1)).iCycles.hom cyc)

end RamanujanPetersson.EtPBC.C1

end

end


