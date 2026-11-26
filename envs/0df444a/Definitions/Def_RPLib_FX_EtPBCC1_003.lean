-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC1_003
-- name    : RPLib_FX_EtPBCC1_003
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T18:44:15.367801+00:00
-- url     : https://prove2.me/theorems/ae8fd041-a050-518c-8479-2d1a7e1d67dd
-- title:
--   Proper base change with compact supports, library file 003
-- statement:
--   File 003 of the library for proper base change with compact supports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_CutMap`: S4-EtCompact, part 4: maps between cut sheaves
--   * `S4.Def_RP_EtSheaves_Cut`: S4-EtSheaves, part 19: `i_*` for closed immersions and the cut sequence
--   * `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
--   * `S4.Def_RP_EtCompact_Cpt`: S4-EtCompact, part 9: compactifications, `R^n f_!` and `H^n_c` (O6, first part)
--   * `S4.Def_RP_EtCompact_AbsRel`: S4-EtCompact, part 15: absolute = relative cohomology over a base with projective unit (O6d)
--   * `S4.Def_RP_EtPBC_B_BCc`: S4-EtPBC-B, D1a: base change for extension by zero and for closed push-forward
--   * `S4.Def_RP_EtPBC_C1_ClsGen`: S4-EtPBC-C1, part 13: classes of cocycles under the base change morphism and `absRelGen` (generic)
--   * `S4.Def_RP_EtPBC_C1_Mor`: S4-EtPBC-C1, part 3: the base change morphism `g^* R^q f_! F ⟶ R^q f'_! g'^* F`
--   * `S4.Def_RP_EtPBC_C1_ExtMap`: S4-EtPBC-C1, part 6: `Ext.mapExactFunctor` of an `extMk` class
--   * `S4.Def_RP_EtPBC_C1_StkHom`: S4-EtPBC-C1, part 12: a cocycle class in the stalk of `R^(p+1) g_* F`
--   * `S4.Def_RP_EtPBC_C1_PsiA`: S4-EtPBC-C1, part 14a: generic glue in `coc_gen` shape; the section cocycle on `P`
--   * `S4.Def_RP_EtPBC_C1_Zero`: S4-EtPBC-C1, part 17: the base change morphism in degree `0` (generic)
--   * `S4.Def_RP_EtPBC_C1_PsiEq`: S4-EtPBC-C1, part 14d: `absRelR` and the comparison `psi_germ` on germs
--   * `S4.Def_RP_EtPBC_C1_Psi`: S4-EtPBC-C1, part 15: the comparison `psi_all` for every stalk element
--   * `S4.Def_RP_EtPBC_C1_PbcS`: S4-EtPBC-C1, part 16: the named equivalence `pbcEquivS` (degrees `p + 1`)
--   * `S4.Def_RP_EtPBC_C1_NatF`: S4-EtPBC-C1, part 19: naturality in `F` of the named proper-base-change equivalences
--   * `S4.Def_RP_EtPBC_C1_PbcC`: S4-EtPBC-C1, part 20b: the named equivalence `pbcEquivC` for `R^q f_!`
--
--   **Formalization note.** One file of a library formalizing the canonical proper base change isomorphism for étale cohomology with compact supports: for $f : X \to S$ with a compactification $X \xrightarrow{j} Z \xrightarrow{i} P \xrightarrow{\bar f} S$ ($j$ an open immersion, $i$ a closed immersion, $\bar f$ proper), $R^q f_! = R^q \bar f_* \circ i_* j_!$, and a geometric point $s$ of $S$ at which $\bar f$ satisfies proper base change, the stalk $(R^q f_! F)_s$ is identified with $H^q_c(X_s, F|_{X_s})$ by a named isomorphism that is natural in the sheaf $F$ of $\Lambda$-modules (built from the base change morphism of the fibre square). It builds on the proper base change libraries for the projective line (`RPLib_FX_EtPBC_*`) and for iterated projective-line bundles (`RPLib_FX_EtPBCB_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre) and Exposé XVII, 5.2.8 (P. Deligne, changement de base pour R f_!), Lecture Notes in Math. 269, 270, 305, Springer (1972-73); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2-§3

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCC1_001

/-!
# Proper base change with compact supports, library file 003

Declarations of the formalization of the canonical proper base change isomorphism for compactly
supported étale cohomology (R^q f_! F)_s ≃ H^q_c(X_s, F|X_s), natural in F, for compactified X ⟶ S
(the base change morphism, its stalk form and its naturality), re-hosted declaration by declaration
from the library modules below, on top of the proper base change libraries RPLib_FX_EtPBC and
RPLib_FX_EtPBCB (projective line and iterated projective-line bundles). Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_CutMap`: S4-EtCompact, part 4: maps between cut sheaves
* `S4.Def_RP_EtSheaves_Cut`: S4-EtSheaves, part 19: `i_*` for closed immersions and the cut sequence
* `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
* `S4.Def_RP_EtCompact_Cpt`: S4-EtCompact, part 9: compactifications, `R^n f_!` and `H^n_c` (O6, first part)
* `S4.Def_RP_EtCompact_AbsRel`: S4-EtCompact, part 15: absolute = relative cohomology over a base with projective unit (O6d)
* `S4.Def_RP_EtPBC_B_BCc`: S4-EtPBC-B, D1a: base change for extension by zero and for closed push-forward
* `S4.Def_RP_EtPBC_C1_ClsGen`: S4-EtPBC-C1, part 13: classes of cocycles under the base change morphism and `absRelGen` (generic)
* `S4.Def_RP_EtPBC_C1_Mor`: S4-EtPBC-C1, part 3: the base change morphism `g^* R^q f_! F ⟶ R^q f'_! g'^* F`
* `S4.Def_RP_EtPBC_C1_ExtMap`: S4-EtPBC-C1, part 6: `Ext.mapExactFunctor` of an `extMk` class
* `S4.Def_RP_EtPBC_C1_StkHom`: S4-EtPBC-C1, part 12: a cocycle class in the stalk of `R^(p+1) g_* F`
* `S4.Def_RP_EtPBC_C1_PsiA`: S4-EtPBC-C1, part 14a: generic glue in `coc_gen` shape; the section cocycle on `P`
* `S4.Def_RP_EtPBC_C1_Zero`: S4-EtPBC-C1, part 17: the base change morphism in degree `0` (generic)
* `S4.Def_RP_EtPBC_C1_PsiEq`: S4-EtPBC-C1, part 14d: `absRelR` and the comparison `psi_germ` on germs
* `S4.Def_RP_EtPBC_C1_Psi`: S4-EtPBC-C1, part 15: the comparison `psi_all` for every stalk element
* `S4.Def_RP_EtPBC_C1_PbcS`: S4-EtPBC-C1, part 16: the named equivalence `pbcEquivS` (degrees `p + 1`)
* `S4.Def_RP_EtPBC_C1_NatF`: S4-EtPBC-C1, part 19: naturality in `F` of the named proper-base-change equivalences
* `S4.Def_RP_EtPBC_C1_PbcC`: S4-EtPBC-C1, part 20b: the named equivalence `pbcEquivC` for `R^q f_!`
-/

set_option autoImplicit false

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

section OpenLe

end OpenLe

section QuotLe

variable {V V' : X.Opens} (h : V ≤ V')

@[reassoc (attr := simp)]
theorem quotCutπ_comp_quotCutLe (G : EtSh Λ X) : quotCutπ Λ V G ≫ quotCutLe h G = quotCutπ Λ V' G :=
  cokernel.π_desc _ _ _

theorem isIso_stalk_quotCutLe (G : EtSh Λ X) (s : GeomPt X) (hs : s.center ∉ V') :
    IsIso ((s.stalkF Λ).map (quotCutLe h G)) := by
  have := isIso_stalk_quotCutπ V G s (fun hv => hs (h hv))
  have h2 := isIso_stalk_quotCutπ V' G s hs
  have : IsIso ((s.stalkF Λ).map (quotCutπ Λ V G) ≫ (s.stalkF Λ).map (quotCutLe h G)) := by
    rw [← Functor.map_comp, quotCutπ_comp_quotCutLe]; exact h2
  exact IsIso.of_isIso_comp_left ((s.stalkF Λ).map (quotCutπ Λ V G)) _

end QuotLe

section OpenMap

end OpenMap

theorem isZero_stalk_cutWV_of_not_mem {W V : X.Opens} (F : EtSh Λ X) (s : GeomPt X)
    (hs : s.center ∉ W) : IsZero ((s.stalkF Λ).obj (cutWV Λ W V F)) :=
  isZero_stalk_openCut W _ s hs

theorem isZero_stalk_cutWV_of_mem {W V : X.Opens} (F : EtSh Λ X) (s : GeomPt X)
    (hW : s.center ∈ W) (hV : s.center ∈ V) : IsZero ((s.stalkF Λ).obj (cutWV Λ W V F)) :=
  isZero_stalk_openCut_of W _ s hW (isZero_stalk_quotCut V F s hV)

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtSheaves_Cut =====
section

/-!
# S4-EtSheaves, part 19: `i_*` for closed immersions and the cut sequence

For a closed immersion `i : Z ⟶ X`, base change `etPull i` is locally full (part 16) and cover
dense (part 18). Hence `i_*` is fully faithful, `i^* i_* ≅ 𝟭`, the stalks of `F ⟶ i_* i^* F` at
the points of `Z` are isomorphisms, and `0 → j_! j^* F → F → i_* i^* F → 0` is exact for the
open complement `j` of `i`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ] {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- **Stalks of `F ⟶ i_* i^* F` at the points of `Z` are isomorphisms** (`i` a closed
immersion). -/
theorem isIso_closed_stalk_unit (t : GeomPt Z) (F : EtSh Λ X) :
    IsIso (((t.map i).stalkF Λ).map ((pullAdj i Λ).unit.app F)) :=
  isIso_stalk_unit Λ i t F

end RamanujanPetersson.EtSheaves

end

end

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

/-- The excision complex `cutWV (W ⊓ V') V F ⟶ cutWV W V F ⟶ cutWV W V' F`. -/
def excComplex : ShortComplex (EtSh Λ X) :=
  ShortComplex.mk (openCutLe (inf_le_left : W ⊓ V' ≤ W) (quotCut Λ V F))
    (openCutMap W (quotCutLe h F)) (by
      refine eq_zero_of_stalk _ (fun x => ?_)
      by_cases hx : x ∈ W ⊓ V'
      · have hW : x ∈ W := hx.1
        have hV' : x ∈ V' := hx.2
        exact (isZero_stalk_cutWV_of_mem F _ (mem_center_geomPtAt hW)
          (mem_center_geomPtAt hV')).eq_of_tgt _ _
      · exact (isZero_stalk_cutWV_of_not_mem F _ (not_mem_center_geomPtAt hx)).eq_of_src _ _)

theorem excComplex_f : (excComplex W h F).f = openCutLe (inf_le_left : W ⊓ V' ≤ W) (quotCut Λ V F) :=
  rfl

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

/-- The excision complex of `S ∩ O ⊆ S ⊇ S \ O` (canonical presentation of `S`), pushed by `E`. -/
abbrev excE (S : Set X) (O : X.Opens) : ShortComplex (EtSh Λ Y) :=
  (excComplex (cutOpen S) (le_sup_left : cutCompl S ≤ cutCompl S ⊔ O) F).map E

end ExcE

namespace Cpt

end Cpt

end RamanujanPetersson.EtCompact

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

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
  {L : D ⥤ C} {R : C ⥤ D} [R.Additive] (adj : L ⊣ R)
  {A : D} {X : C} (e : L.obj A ≅ X) {Y : C} (I : InjectiveResolution Y)

theorem toHomFun_extMk (p : ℕ) (f : X ⟶ I.cocomplex.X (p + 1))
    (hf : f ≫ I.cocomplex.d (p + 1) (p + 1 + 1) = 0) :
    toHomFun adj e I p (I.extMk f (p + 1 + 1) rfl hf) = clsOf adj e I p f hf := by
  have hs := I.extMk_surjective (I.extMk f (p + 1 + 1) rfl hf) (p + 1 + 1) rfl
  set f' := hs.choose with hf'def
  have hf' : f' ≫ I.cocomplex.d (p + 1) (p + 1 + 1) = 0 := hs.choose_spec.choose
  have heq : I.extMk f' (p + 1 + 1) rfl hf' = I.extMk f (p + 1 + 1) rfl hf := hs.choose_spec.choose_spec
  have h0 : I.extMk (f' - f) (p + 1 + 1) rfl (by simp [hf, hf']) = 0 := by
    rw [← I.sub_extMk f' f (p + 1 + 1) rfl hf' hf, heq, sub_self]
  obtain ⟨g, hg⟩ := (I.extMk_eq_zero_iff (f' - f) (p + 1 + 1) rfl (by simp [hf, hf']) p rfl).1 h0
  change clsOf adj e I p f' hf' = clsOf adj e I p f hf
  unfold clsOf
  apply liftCycles_homologyπ_congr _ p _ _ (flat adj e I g)
  rw [← flat_comp, ← flat_add, hg, add_sub_cancel]

theorem toHomFun_add (p : ℕ) (α β : Ext X Y (p + 1)) :
    toHomFun adj e I p (α + β) = toHomFun adj e I p α + toHomFun adj e I p β := by
  obtain ⟨f, hf, rfl⟩ := I.extMk_surjective α (p + 1 + 1) rfl
  obtain ⟨f', hf', rfl⟩ := I.extMk_surjective β (p + 1 + 1) rfl
  rw [I.add_extMk f f' (p + 1 + 1) rfl hf hf', toHomFun_extMk, toHomFun_extMk, toHomFun_extMk]
  unfold clsOf
  rw [← Preadditive.add_comp, ← liftCycles_add _ p (flat_cocycle adj e I hf) (flat_cocycle adj e I hf')
    (by rw [Preadditive.add_comp, flat_cocycle adj e I hf, flat_cocycle adj e I hf', add_zero])]
  exact congrArg (fun t => t ≫ (RI I (R := R)).homologyπ (p + 1))
    (liftCycles_eq_of_eq _ _ _ _ (flat_add adj e I f f') _ _)

/-- `Ext^(p+1)(X, Y) →+ Hom(A, H^(p+1)(R I))`. -/
def toHom (p : ℕ) : Ext X Y (p + 1) →+ (A ⟶ (RI I (R := R)).homology (p + 1)) :=
  AddMonoidHom.mk' (toHomFun adj e I p) (toHomFun_add adj e I p)

/-- **Absolute = relative (generic)**: `Ext^(p+1)(X, Y) ≃+ Hom(A, H^(p+1)(R I))` for `A` projective. -/
def absRelGen [Projective A] (p : ℕ) : Ext X Y (p + 1) ≃+ (A ⟶ (RI I (R := R)).homology (p + 1)) :=
  AddEquiv.ofBijective (toHom adj e I p) (by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro α hα
      obtain ⟨f, hf, rfl⟩ := I.extMk_surjective α (p + 1 + 1) rfl
      change toHomFun adj e I p _ = 0 at hα
      rw [toHomFun_extMk] at hα
      obtain ⟨g, hg⟩ := exists_boundary_of_projective (RI I (R := R)) p (flat adj e I f)
        (flat_cocycle adj e I hf) hα
      refine (I.extMk_eq_zero_iff f (p + 1 + 1) rfl hf p rfl).2 ⟨unflat adj e I g, ?_⟩
      apply flat_injective adj e I
      rw [flat_comp, flat_unflat, hg]
    · intro φ
      let ψ := Projective.factorThru φ ((RI I (R := R)).homologyπ (p + 1))
      let h := ψ ≫ (RI I (R := R)).iCycles (p + 1)
      have hh : unflat adj e I h ≫ I.cocomplex.d (p + 1) (p + 1 + 1) = 0 := by
        apply flat_injective adj e I
        rw [flat_comp, flat_unflat, flat_zero]
        change (ψ ≫ (RI I (R := R)).iCycles (p + 1)) ≫ (RI I (R := R)).d (p + 1) (p + 1 + 1) = 0
        rw [Category.assoc, HomologicalComplex.iCycles_d, comp_zero]
      refine ⟨I.extMk (unflat adj e I h) (p + 1 + 1) rfl hh, ?_⟩
      change toHomFun adj e I p _ = φ
      rw [toHomFun_extMk]
      unfold clsOf
      have hl : (RI I (R := R)).liftCycles (flat adj e I (unflat adj e I h)) (p + 1 + 1)
          (CochainComplex.next ℕ (p + 1)) (flat_cocycle adj e I hh) = ψ := by
        rw [← cancel_mono ((RI I (R := R)).iCycles (p + 1)), HomologicalComplex.liftCycles_i, flat_unflat]
      rw [hl]
      exact Projective.factorThru_comp _ _)

end Generic

section Sheaves

open AlgebraicGeometry RamanujanPetersson.EtSheaves

universe u

end Sheaves

end RamanujanPetersson.EtCompact

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

end Lsh

section Closed

variable {Λ : Type u} [CommRing Λ] {Z P P' : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i] (ιP : P' ⟶ P)

/-- `ιP^* i_* M` is supported on `Z ×_P P'`: the unit of `i' = pullback.snd i ιP` is an isomorphism. -/
theorem isIso_unit_closedBC (M : EtSh Λ Z) :
    IsIso ((pullAdj (pullback.snd i ιP) Λ).unit.app ((pull ιP Λ).obj ((push i Λ).obj M))) := by
  refine isIso_of_family (cutPts (pullback.snd i ιP)) (cutPts_cover (pullback.snd i ιP)) _ fun k => ?_
  rcases k with z | y
  · exact isIso_closed_stalk_unit Λ (pullback.snd i ιP) (geomPtAt z) _
  · change IsIso ((((geomPtAt y).map (complOpens (pullback.snd i ιP)).ι).stalkF Λ).map _)
    have hy : ((geomPtAt y).map (complOpens (pullback.snd i ιP)).ι).center ∉
        Set.range (pullback.snd i ιP) := by
      rw [center_map', center_geomPtAt]
      have h1 : (complOpens (pullback.snd i ιP)).ι y ∈ Set.range (complOpens (pullback.snd i ιP)).ι :=
        ⟨y, rfl⟩
      rw [range_complOpens_ι] at h1
      exact h1
    have hT : (((geomPtAt y).map (complOpens (pullback.snd i ιP)).ι).map ιP).center ∉ Set.range i := by
      rw [center_map']
      exact not_mem_range_comp i ιP hy
    have src : IsZero ((((geomPtAt y).map (complOpens (pullback.snd i ιP)).ι).stalkF Λ).obj
        ((pull ιP Λ).obj ((push i Λ).obj M))) :=
      (push_stalk_isZero_of_not_mem Λ i _ hT M).of_iso
        ((pullStalkIso ιP Λ ((geomPtAt y).map (complOpens (pullback.snd i ιP)).ι)).app ((push i Λ).obj M))
    have tgt := push_stalk_isZero_of_not_mem Λ (pullback.snd i ιP) _ hy
      ((pull (pullback.snd i ιP) Λ).obj ((pull ιP Λ).obj ((push i Λ).obj M)))
    exact isIso_of_source_target_iso_zero _ src.isoZero tgt.isoZero

end Closed

end RamanujanPetersson.EtPBC

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

end BC

section AR

universe w

variable {D : Type*} [Category D] [Abelian D] {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]
  {L : D ⥤ C} {R : C ⥤ D} [R.Additive] (adj : L ⊣ R)
  {A : D} {X : C} (e : L.obj A ≅ X) {Y : C} (I : InjectiveResolution Y)

/-- **`absRelGen` on `I.extMk f`**: the class of `adj.homEquiv (e.hom ≫ f)`. -/
theorem absRelGen_extMk [Projective A] (p : ℕ) (f : X ⟶ I.cocomplex.X (p + 1))
    (hf : f ≫ I.cocomplex.d (p + 1) (p + 1 + 1) = 0) :
    EtCompact.absRelGen adj e I p (I.extMk f (p + 1 + 1) rfl hf) =
      (EtCompact.RI I (R := R)).liftCycles (adj.homEquiv _ _ (e.hom ≫ f)) (p + 1 + 1)
        (CochainComplex.next ℕ (p + 1)) (EtCompact.flat_cocycle adj e I hf) ≫
        (EtCompact.RI I (R := R)).homologyπ (p + 1) :=
  EtCompact.toHomFun_extMk adj e I p f hf

end AR

section Glue

universe w

variable {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
  {C' : Type*} [Category C'] [Abelian C'] {D' : Type*} [Category D'] [Abelian D']
  (R : C ⥤ D) [R.Additive] (R' : C' ⥤ D') [R'.Additive]
  (Lc : C ⥤ C') [Lc.Additive] [Lc.PreservesHomology] [Lc.PreservesMonomorphisms]
  (Ld : D ⥤ D') [Ld.Additive] [Ld.PreservesHomology]
  (β : R ⋙ Ld ⟶ Lc ⋙ R') [HasInjectiveResolutions C] [HasInjectiveResolutions C'] [HasExt.{w} C']
  {L : D' ⥤ C'} (adj : L ⊣ R') {A : D'} {X₀ : C'} (e : L.obj A ≅ X₀) [Projective A]

set_option backward.isDefEq.respectTransparency false in
/-- **Generic comparison**: if `(a ≫ Ld k) ≫ β = adj.homEquiv (e.hom ≫ u ≫ Lc ĉ)`, then `absRelGen` of the class
`J.extMk (u ≫ Lc ĉ ≫ lift)` is `a ≫ Ld([k] ≫ isoRD⁻¹) ≫ bcMorRes I J` (after `isoRD_J⁻¹`). -/
theorem glue_gen (p : ℕ) {Xc : C} (I : InjectiveResolution Xc) (J : InjectiveResolution (Lc.obj Xc))
    {Y : D} {Y' : C} (a : A ⟶ Ld.obj Y) (k : Y ⟶ ((R.mapHomologicalComplex _).obj I.cocomplex).X (p + 1))
    (hk : k ≫ ((R.mapHomologicalComplex _).obj I.cocomplex).d (p + 1) (p + 1 + 1) = 0)
    (u : X₀ ⟶ Lc.obj Y') (c : Y' ⟶ I.cocomplex.X (p + 1))
    (H : (a ≫ Ld.map k) ≫ β.app (I.cocomplex.X (p + 1)) = adj.homEquiv _ _ (e.hom ≫ u ≫ Lc.map c))
    (hf : (u ≫ Lc.map c ≫ (liftLc Lc I J).f (p + 1)) ≫ J.cocomplex.d (p + 1) (p + 1 + 1) = 0) :
    EtCompact.absRelGen adj e J p (J.extMk (u ≫ Lc.map c ≫ (liftLc Lc I J).f (p + 1)) (p + 1 + 1) rfl hf) ≫
        (J.isoRightDerivedObj R' (p + 1)).inv =
      a ≫ Ld.map ((((R.mapHomologicalComplex _).obj I.cocomplex).liftCycles k (p + 1 + 1)
        (CochainComplex.next ℕ (p + 1)) hk ≫ ((R.mapHomologicalComplex _).obj I.cocomplex).homologyπ (p + 1)) ≫
        (I.isoRightDerivedObj R (p + 1)).inv) ≫ bcMorRes R R' Lc Ld β (p + 1) I J := by
  have hX : adj.homEquiv _ _ (e.hom ≫ u ≫ Lc.map c ≫ (liftLc Lc I J).f (p + 1)) =
      (a ≫ Ld.map k) ≫ β.app (I.cocomplex.X (p + 1)) ≫ R'.map ((liftLc Lc I J).f (p + 1)) := by
    have h1 := congrArg (fun t => t ≫ R'.map ((liftLc Lc I J).f (p + 1))) H
    simp only [Category.assoc] at h1 ⊢
    rw [h1, ← Adjunction.homEquiv_naturality_right]
    simp only [Category.assoc]
  have hk2 : ((a ≫ Ld.map k) ≫ β.app (I.cocomplex.X (p + 1)) ≫ R'.map ((liftLc Lc I J).f (p + 1))) ≫
      ((R'.mapHomologicalComplex _).obj J.cocomplex).d (p + 1) (p + 1 + 1) = 0 := by
    rw [← hX]
    exact EtCompact.flat_cocycle adj e J hf
  rw [absRelGen_extMk, Category.assoc, Category.assoc, bcMorRes_cls R R' Lc Ld β p I J a k hk hk2]
  exact congrArg (fun t => t ≫ ((R'.mapHomologicalComplex _).obj J.cocomplex).homologyπ (p + 1) ≫
    (J.isoRightDerivedObj R' (p + 1)).inv) (EtCompact.liftCycles_eq_of_eq _ _ _ _ hX _ _)

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

end Sq

section Closed

variable {Λ} {Z P P' : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i] (ιP : P' ⟶ P)

instance isIso_bcCell_closed :
    IsIso (bcCell Λ (pullback.fst i ιP) ιP i (pullback.snd i ιP) pullback.condition.symm) := by
  have : ∀ M, IsIso ((bcCell Λ (pullback.fst i ιP) ιP i (pullback.snd i ιP) pullback.condition.symm).app M) :=
    fun M => by
      have := isIso_unit_closedBC i ιP M
      have := isIso_closed_counit Λ i
      rw [bcCell_app]
      infer_instance
  exact NatIso.isIso_of_isIso_app _

end Closed

section It

variable {X B B' : Scheme.{u}} {f : X ⟶ B} (c : Cpt f) (g : B' ⟶ B)

/-- The closed base change natural isomorphism `i_* ⋙ gP^* ≅ gZ^* ⋙ i'_*`. -/
def itClosedNat : push c.i Λ ⋙ pull (itgP c g) Λ ≅ pull (itgZ c g) Λ ⋙ push (itCpt c g).i Λ :=
  asIso (bcCell Λ (pullback.fst c.i (itgP c g)) (itgP c g) c.i (pullback.snd c.i (itgP c g))
    pullback.condition.symm)

/-- **`c.ext ⋙ gP^* ≅ gX^* ⋙ (itCpt c g).ext`** (`i_* j_!` commutes with base change). -/
def itExtNat : c.ext Λ ⋙ pull (itgP c g) Λ ≅ pull (itgX c g) Λ ⋙ (itCpt c g).ext Λ :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (lsh c.j Λ) (itClosedNat Λ c g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (lshPullBC Λ c.j (itgZ c g)) (push (itCpt c g).i Λ) ≪≫
    Functor.associator _ _ _

end It

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

end Small

section ClassComp

end ClassComp

section Map

end Map

section Coc

end Coc

section Main

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [HasExt.{w'} D] (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  {X Y : C} (R : InjectiveResolution Y) (R' : InjectiveResolution (L.obj Y))
  (φ : (L.mapHomologicalComplex _).obj R.cocomplex ⟶ R'.cocomplex)
  (hφ : L.map (R.ι.f 0) ≫ φ.f 0 = R'.ι.f 0)

include hφ

set_option backward.isDefEq.respectTransparency false in
/-- **`Ext.mapExactFunctor` of an `extMk` class**: `(R.extMk f).mapExactFunctor L = R'.extMk (L f ≫ φ_n)`. -/
theorem mapExactFunctor_extMk {n : ℕ} (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) :
    (R.extMk f m hm hf).mapExactFunctor L =
      R'.extMk (L.map f ≫ φ.f n) m hm (extMk_cond L R R' φ f m hf) := by
  have := isLE_mapR L R
  apply (SmallShiftedHom.postcompEquiv.{w'} R'.ι' (by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance)
    (X := (CochainComplex.singleFunctor D 0).obj (L.obj X)) (a := (n : ℤ))).injective
  change SmallShiftedHom.comp (M := ℤ) _ (SmallShiftedHom.mk₀ _ _ rfl R'.ι') (zero_add _) =
    SmallShiftedHom.comp (M := ℤ) _ (SmallShiftedHom.mk₀ _ _ rfl R'.ι') (zero_add _)
  rw [ext_comp_ι' R' (R'.extMk (L.map f ≫ φ.f n) m hm (extMk_cond L R R' φ f m hf)),
    InjectiveResolution.extEquivCohomologyClass_extMk, CohomologyClass.toSmallShiftedHom_mk]
  rw [← ι'_liftZ L R R' φ hφ, ← Category.assoc, ssh_mk₀_comp,
    ← SmallShiftedHom.comp_assoc _ _ _ _ (zero_add _) (zero_add 0) (by simp)]
  have iX1 : CochainComplex.IsGE ((L ⋙ CochainComplex.singleFunctor D 0).obj X) 0 :=
    inferInstanceAs (CochainComplex.IsGE ((CochainComplex.singleFunctor D 0).obj (L.obj X)) 0)
  have iX2 : CochainComplex.IsLE ((L ⋙ CochainComplex.singleFunctor D 0).obj X) 0 :=
    inferInstanceAs (CochainComplex.IsLE ((CochainComplex.singleFunctor D 0).obj (L.obj X)) 0)
  have iR1 : CochainComplex.IsGE ((L.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).functor.obj R.cochainComplex) 0 :=
    inferInstanceAs (CochainComplex.IsGE ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex) 0)
  have iR2 : CochainComplex.IsLE ((L.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).functor.obj R.cochainComplex) 0 := isLE_mapR L R
  have i3 : HasSmallLocalizedShiftedHom.{w'} (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) ℤ
      ((L ⋙ CochainComplex.singleFunctor D 0).obj X) ((L.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).functor.obj R.cochainComplex) := HasExt.hasSmallLocalizedShiftedHom_of_isLE_of_isGE _ _ 0 0
  have i4 : HasSmallLocalizedShiftedHom.{w'} (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) ℤ
      ((L.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)).functor.obj R.cochainComplex)
      ((L.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)).functor.obj R.cochainComplex) :=
    HasExt.hasSmallLocalizedShiftedHom_of_isLE_of_isGE _ _ 0 0
  have i6 : HasSmallLocalizedShiftedHom.{w'} (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) ℤ
      ((L ⋙ CochainComplex.singleFunctor D 0).obj Y) ((L.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).functor.obj R.cochainComplex) :=
    @HasExt.hasSmallLocalizedShiftedHom_of_isLE_of_isGE _ _ _ _ _ _ 0 0
      (inferInstanceAs (CochainComplex.IsGE ((CochainComplex.singleFunctor D 0).obj (L.obj Y)) 0))
      (inferInstanceAs (CochainComplex.IsLE ((CochainComplex.singleFunctor D 0).obj (L.obj Y)) 0)) iR1 iR2
  have i5 : HasSmallLocalizedShiftedHom.{w'} (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) ℤ
      ((L ⋙ CochainComplex.singleFunctor D 0).obj X) ((L ⋙ CochainComplex.singleFunctor D 0).obj X) :=
    HasExt.hasSmallLocalizedShiftedHom_of_isLE_of_isGE _ _ 0 0
  have h1 : SmallShiftedHom.comp (M := ℤ) ((R.extMk f m hm hf).mapExactFunctor L)
      (SmallShiftedHom.mk₀ _ (0 : ℤ) rfl ((L.mapCochainComplexSingleFunctor 0).inv.app Y ≫
        (L.mapHomologicalComplex _).map R.ι')) (zero_add _) =
      (L.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)).smallShiftedHomMap
        ((L.mapCochainComplexSingleFunctor 0).app X) (Iso.refl _)
        (SmallShiftedHom.comp (M := ℤ) (R.extMk f m hm hf) (SmallShiftedHom.mk₀ _ _ rfl R.ι')
          (zero_add _)) := by
    rw [LocalizerMorphism.smallShiftedHomMap_comp
      (L.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ))
      ((L.mapCochainComplexSingleFunctor 0).app X) ((L.mapCochainComplexSingleFunctor 0).app Y) (Iso.refl _),
      LocalizerMorphism.smallShiftedHomMap_mk₀]
    simp only [Iso.refl_hom, Category.comp_id]
    rfl
  rw [h1, ext_comp_ι' R, InjectiveResolution.extEquivCohomologyClass_extMk,
    CohomologyClass.toSmallShiftedHom_mk, LocalizerMorphism.smallShiftedHomMap_mk, ssh_mk_comp_mk₀]
  have h2 : ((L.mapCochainComplexSingleFunctor 0).app X).inv ≫
      (L.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)).functor.map
        (Cocycle.equivHomShift.symm (Cocycle.fromSingleMk (f ≫ (R.cochainComplexXIso n n rfl).inv)
          (zero_add _) m (by lia) (by simp [R.cochainComplex_d _ _ n m rfl rfl, reassoc_of% hf]))) ≫
      (Functor.commShiftIso (L.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)).functor
        (n : ℤ)).hom.app R.cochainComplex =
      Cocycle.equivHomShift.symm (Cocycle.fromSingleMk (L.map (f ≫ (R.cochainComplexXIso n n rfl).inv))
        (zero_add _) m (by lia) (by
          show L.map _ ≫ L.map (R.cochainComplex.d n m) = 0
          rw [← L.map_comp, Category.assoc, R.cochainComplex_d _ _ n m rfl rfl]
          simp [reassoc_of% hf])) :=
    map_equivHomShift_fromSingleMk L _ _ _ _
  have key : L.map f ≫ φ.f n ≫ (R'.cochainComplexXIso n n rfl).inv =
      L.map (f ≫ (R.cochainComplexXIso n n rfl).inv) ≫ (liftZ L R R' φ).f n := by
    rw [liftZ_f L R R' φ n n rfl, L.map_comp]
    simp only [Category.assoc]
    rw [← L.map_comp_assoc (R.cochainComplexXIso n n rfl).inv, Iso.inv_hom_id, L.map_id,
      Category.id_comp]
  congr 1
  rw [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  simp only [ShiftedHom.map, Iso.refl_hom, Category.assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% h2, ← Cocycle.equivHomShift_symm_postcomp, ← Cocycle.fromSingleMk_postcomp]
  simp only [key]

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

variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D] [Abelian E]
  (Sh : ShortComplex C) (U : C ⥤ D) (pF : D ⥤ E) [U.PreservesZeroMorphisms] [pF.PreservesZeroMorphisms]
  [pF.PreservesHomology] [(U ⋙ pF).PreservesHomology]

set_option backward.isDefEq.respectTransparency false in
theorem stk_gen0 {A : C} (k : A ⟶ Sh.X₂) (hk : k ≫ Sh.g = 0) (hk' : U.map k ≫ (Sh.map U).g = 0) :
    (U ⋙ pF).map (Sh.liftCycles k hk ≫ Sh.homologyπ) ≫ (Sh.mapHomologyIso (U ⋙ pF)).inv ≫
        ((Sh.map U).mapHomologyIso pF).hom =
      pF.map ((Sh.map U).liftCycles (U.map k) hk' ≫ (Sh.map U).homologyπ) := by
  have h1 : (U ⋙ pF).map k ≫ (Sh.map (U ⋙ pF)).g = 0 := by
    simp only [ShortComplex.map_g, ← Functor.map_comp, hk, Functor.map_zero]
  have h2 : pF.map (U.map k) ≫ ((Sh.map U).map pF).g = 0 := by
    simp only [ShortComplex.map_g, ← Functor.map_comp, hk, Functor.map_zero]
  rw [← Category.assoc, map_liftCycles_homologyπ Sh (U ⋙ pF) k hk h1, ← Iso.eq_comp_inv,
    map_liftCycles_homologyπ (Sh.map U) pF (U.map k) hk' h2]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Generic form of `stk_E1`: two exact functors, `U ⋙ pF` and `pF`, send a class to the same class. -/
theorem stk_gen {A : C} (k : A ⟶ Sh.X₂) (hk : k ≫ Sh.g = 0) (hk' : U.map k ≫ (Sh.map U).g = 0) :
    (U ⋙ pF).map (Sh.liftCycles k hk ≫ Sh.homologyπ) ≫ ((Sh.mapHomologyIso (U ⋙ pF)).symm ≪≫
        (Iso.refl _ : _ ≅ ((Sh.map U).map pF).homology) ≪≫ (Sh.map U).mapHomologyIso pF).hom =
      pF.map ((Sh.map U).liftCycles (U.map k) hk' ≫ (Sh.map U).homologyπ) := by
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.refl_hom]
  exact (congrArg (fun t => (U ⋙ pF).map (Sh.liftCycles k hk ≫ Sh.homologyπ) ≫
    (Sh.mapHomologyIso (U ⋙ pF)).inv ≫ t) (Category.id_comp ((Sh.map U).mapHomologyIso pF).hom)).trans
    (stk_gen0 Sh U pF k hk hk')

end Gen

set_option backward.isDefEq.respectTransparency false

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)
  (K : CochainComplex (EtSh Λ P) ℕ) (p : ℕ) {V : S.Etale}

theorem freeCoc_d (cyc : ((secCx Λ K ((etPull g).obj V)).sc (p + 1)).cycles) :
    freeCoc g K p cyc ≫ (pushCx g K).d (p + 1) (p + 1 + 1) = 0 := by
  apply (freeEquiv Λ V _).injective
  rw [freeEquiv_comp, map_zero, freeCoc, AddEquiv.apply_symm_apply]
  have h := HomologicalComplex.iCycles_d (secCx Λ K ((etPull g).obj V)) (p + 1) (p + 1 + 1)
  exact congrArg (fun m => m.hom cyc) h

theorem freeCoc_d' (cyc : ((secCx Λ K ((etPull g).obj V)).sc (p + 1)).cycles) :
    (freeCoc g K p cyc).hom ≫ (preCx Λ g K).d (p + 1) (p + 1 + 1) = 0 := by
  have h := congrArg (sheafToPresheaf _ _).map (freeCoc_d g K p cyc)
  rw [Functor.map_comp, Functor.map_zero] at h
  exact h

theorem freeCoc_dV (cyc : ((secCx Λ K ((etPull g).obj V)).sc (p + 1)).cycles) :
    (freeCoc g K p cyc).hom.app (op V) ≫ (secCx Λ K ((etPull g).obj V)).d (p + 1) (p + 1 + 1) = 0 := by
  have h := congrArg (fun m => m.app (op V)) (freeCoc_d' g K p cyc)
  simp only [NatTrans.app_zero] at h
  exact h

/-- **The class `[cyc] : Λ[V] ⟶ H^(p+1)(g_* K)`**. -/
def cocCls (cyc : ((secCx Λ K ((etPull g).obj V)).sc (p + 1)).cycles) :
    freeSh Λ V ⟶ (pushCx g K).homology (p + 1) :=
  (pushCx g K).liftCycles (freeCoc g K p cyc) (p + 1 + 1) (CochainComplex.next ℕ (p + 1))
    (freeCoc_d g K p cyc) ≫ (pushCx g K).homologyπ (p + 1)

theorem stk_E1 (cyc : ((secCx Λ K ((etPull g).obj V)).sc (p + 1)).cycles) :
    s.point.presheafFiber.map (cocCls g K p cyc).hom ≫ (stalkHomologyIso Λ g s K (p + 1)).hom =
      s.point.presheafFiber.map ((preCx Λ g K).liftCycles (freeCoc g K p cyc).hom (p + 1 + 1)
        (CochainComplex.next ℕ (p + 1)) (freeCoc_d' g K p cyc) ≫ (preCx Λ g K).homologyπ (p + 1)) := by
  have : (sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} Λ) ⋙ s.point.presheafFiber).PreservesHomology :=
    (inferInstance : (s.stalkF Λ).PreservesHomology)
  have hk : freeCoc g K p cyc ≫ ((pushCx g K).sc (p + 1)).g = 0 := by
    change _ ≫ (pushCx g K).d (p + 1) ((ComplexShape.up ℕ).next (p + 1)) = 0
    rw [CochainComplex.next]
    exact freeCoc_d g K p cyc
  have hk' : (sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} Λ)).map (freeCoc g K p cyc) ≫
      (((pushCx g K).sc (p + 1)).map (sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} Λ))).g = 0 := by
    change (freeCoc g K p cyc).hom ≫ (preCx Λ g K).d (p + 1) ((ComplexShape.up ℕ).next (p + 1)) = 0
    rw [CochainComplex.next]
    exact freeCoc_d' g K p cyc
  exact stk_gen ((pushCx g K).sc (p + 1)) (sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
    s.point.presheafFiber (freeCoc g K p cyc) hk hk'

theorem stk_E2 (cyc : ((secCx Λ K ((etPull g).obj V)).sc (p + 1)).cycles) :
    ((preCx Λ g K).liftCycles (freeCoc g K p cyc).hom (p + 1 + 1) (CochainComplex.next ℕ (p + 1))
        (freeCoc_d' g K p cyc) ≫ (preCx Λ g K).homologyπ (p + 1)).app (op V) =
      ((secCx Λ K ((etPull g).obj V)).liftCycles ((freeCoc g K p cyc).hom.app (op V)) (p + 1 + 1)
        (CochainComplex.next ℕ (p + 1)) (freeCoc_dV g K p cyc) ≫
          (secCx Λ K ((etPull g).obj V)).homologyπ (p + 1)) ≫ (preHomologyObjIso Λ g K (p + 1) V).inv := by
  have h := map_liftCycles_homologyπ_cx ((evaluation _ _).obj (op V)) (preCx Λ g K) (p + 1) (p + 1 + 1)
    (CochainComplex.next ℕ (p + 1)) (freeCoc g K p cyc).hom (freeCoc_d' g K p cyc) (freeCoc_dV g K p cyc)
  rw [Iso.comp_inv_eq] at h
  refine h.trans ?_
  rw [EtLeray.homologyMapIso, preHomologyObjIso, Iso.trans_hom, Iso.trans_inv, Iso.refl_hom, Iso.refl_inv,
    Iso.symm_inv]
  rfl

theorem stk_E3 (cyc : ((secCx Λ K ((etPull g).obj V)).sc (p + 1)).cycles) :
    ((secCx Λ K ((etPull g).obj V)).liftCycles ((freeCoc g K p cyc).hom.app (op V)) (p + 1 + 1)
      (CochainComplex.next ℕ (p + 1)) (freeCoc_dV g K p cyc)).hom (taut Λ V) = cyc := by
  apply (ModuleCat.mono_iff_injective ((secCx Λ K ((etPull g).obj V)).iCycles (p + 1))).1 inferInstance
  have h := HomologicalComplex.liftCycles_i (secCx Λ K ((etPull g).obj V)) ((freeCoc g K p cyc).hom.app (op V))
    (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) (freeCoc_dV g K p cyc)
  refine (congrArg (fun m => m.hom (taut Λ V)) h).trans ?_
  exact freeCoc_taut g K p cyc

/-- **`stalkHomologyIso` sends the germ of `cocCls cyc (taut)` to the germ of `[cyc]`.** -/
theorem stalkHom_germ (v : s.point.fiber.obj V) (cyc : ((secCx Λ K ((etPull g).obj V)).sc (p + 1)).cycles) :
    (stalkHomologyIso Λ g s K (p + 1)).hom.hom
        ((s.point.toPresheafFiber V v ((pushCx g K).homology (p + 1)).obj).hom
          (((cocCls g K p cyc).hom.app (op V)).hom (taut Λ V))) =
      (s.point.toPresheafFiber V v ((preCx Λ g K).homology (p + 1))).hom
        ((preHomologyObjIso Λ g K (p + 1) V).inv.hom
          (((secCx Λ K ((etPull g).obj V)).sc (p + 1)).homologyπ.hom cyc)) := by
  have hm : (cocCls g K p cyc).hom.app (op V) ≫ s.point.toPresheafFiber V v ((pushCx g K).homology (p + 1)).obj ≫
      (stalkHomologyIso Λ g s K (p + 1)).hom =
      (((secCx Λ K ((etPull g).obj V)).liftCycles ((freeCoc g K p cyc).hom.app (op V)) (p + 1 + 1)
        (CochainComplex.next ℕ (p + 1)) (freeCoc_dV g K p cyc) ≫
          (secCx Λ K ((etPull g).obj V)).homologyπ (p + 1)) ≫ (preHomologyObjIso Λ g K (p + 1) V).inv) ≫
        s.point.toPresheafFiber V v ((preCx Λ g K).homology (p + 1)) := by
    rw [← Category.assoc, ← GrothendieckTopology.Point.toPresheafFiber_naturality, Category.assoc,
      stk_E1, GrothendieckTopology.Point.toPresheafFiber_naturality, stk_E2]
  have h := congrArg (fun m => m.hom (taut Λ V)) hm
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [stk_E3] at h
  exact h

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

end ExtMk

section G3

universe w

variable {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
  {C' : Type*} [Category C'] [Abelian C'] {D' : Type*} [Category D'] [Abelian D']
  (R : C ⥤ D) [R.Additive] (R' : C' ⥤ D') [R'.Additive]
  (Lc : C ⥤ C') [Lc.Additive] [Lc.PreservesHomology] [Lc.PreservesMonomorphisms]
  (Ld : D ⥤ D') [Ld.Additive] [Ld.PreservesHomology]
  (β : R ⋙ Ld ⟶ Lc ⋙ R') [HasInjectiveResolutions C] [HasInjectiveResolutions C'] [HasExt.{w} C']
  {L : D' ⥤ C'} (adj : L ⊣ R') {A : D'} {X₀ : C'} (e : X₀ ≅ L.obj A) [Projective A]

set_option backward.isDefEq.respectTransparency false in
/-- `glue_gen` in the shape used for the fibre square: the hypothesis `H` has the shape of `coc_gen`
(`k` into `R (I^(p+1))`, `e.inv`), and the cocycle `f` and the class `m` are given with defining equations. -/
theorem glue3 (p : ℕ) {Xc : C} (I : InjectiveResolution Xc) (J : InjectiveResolution (Lc.obj Xc))
    {Y : D} {Y' : C} (a : A ⟶ Ld.obj Y) (k : Y ⟶ R.obj (I.cocomplex.X (p + 1)))
    (hk : k ≫ R.map (I.cocomplex.d (p + 1) (p + 1 + 1)) = 0)
    (u : X₀ ⟶ Lc.obj Y') (c : Y' ⟶ I.cocomplex.X (p + 1))
    (H : (a ≫ Ld.map k) ≫ β.app (I.cocomplex.X (p + 1)) = adj.homEquiv _ _ (e.inv ≫ u ≫ Lc.map c))
    (f : X₀ ⟶ J.cocomplex.X (p + 1)) (hfu : u ≫ Lc.map c ≫ (liftLc Lc I J).f (p + 1) = f)
    (hf : f ≫ J.cocomplex.d (p + 1) (p + 1 + 1) = 0) (m : Y ⟶ (R.rightDerived (p + 1)).obj Xc)
    (hm : (((R.mapHomologicalComplex _).obj I.cocomplex).liftCycles k (p + 1 + 1)
        (CochainComplex.next ℕ (p + 1)) hk ≫ ((R.mapHomologicalComplex _).obj I.cocomplex).homologyπ (p + 1)) ≫
        (I.isoRightDerivedObj R (p + 1)).inv = m) :
    EtCompact.absRelGen adj e.symm J p (J.extMk f (p + 1 + 1) rfl hf) ≫ (J.isoRightDerivedObj R' (p + 1)).inv =
      (a ≫ Ld.map m) ≫ bcMorRes R R' Lc Ld β (p + 1) I J := by
  subst hfu hm
  exact (glue_gen R R' Lc Ld β adj e.symm p I J a k hk u c H hf).trans (Category.assoc _ _ _).symm

end G3

universe u

set_option backward.isDefEq.respectTransparency false

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S) {F : EtSh Λ P}
  (I : InjectiveResolution F) (J : InjectiveResolution ((pull (fibι g s) Λ).obj F)) (p : ℕ)

theorem freeCocP_d {V : S.Etale} (cyc : ((secCx Λ I.cocomplex ((etPull g).obj V)).sc (p + 1)).cycles) :
    freeCocP g I p cyc ≫ I.cocomplex.d (p + 1) (p + 1 + 1) = 0 := by
  apply (freeEquiv Λ ((etPull g).obj V) _).injective
  rw [freeEquiv_comp, map_zero, freeCocP, AddEquiv.apply_symm_apply]
  exact congrArg (fun m => m.hom cyc)
    (HomologicalComplex.iCycles_d (secCx Λ I.cocomplex ((etPull g).obj V)) (p + 1) (p + 1 + 1))

theorem freeCocP_cond (j : Nbhd s) (cyc : ((secCx Λ I.cocomplex ((etPull g).obj j.1)).sc (p + 1)).cycles) :
    (bcUnit Λ g s j ≫ (pull (fibι g s) Λ).map (freeCocP g I p cyc) ≫
      (liftLc (pull (fibι g s) Λ) I J).f (p + 1)) ≫ J.cocomplex.d (p + 1) (p + 1 + 1) = 0 := by
  have h := extMk_cond (pull (fibι g s) Λ) I J (liftLc (pull (fibι g s) Λ) I J) (freeCocP g I p cyc) (p + 1 + 1)
    (freeCocP_d g I p cyc)
  simp only [Category.assoc] at h ⊢
  rw [h, comp_zero]

theorem germExt_cyc (V : S.Etale) (cyc : ((secCx Λ I.cocomplex ((etPull g).obj V)).sc (p + 1)).cycles) :
    germExt Λ g I p V ((preHomologyObjIso Λ g I.cocomplex (p + 1) V).inv.hom
        (((secCx Λ I.cocomplex ((etPull g).obj V)).sc (p + 1)).homologyπ.hom cyc)) =
      I.extMk (freeCocP g I p cyc) (p + 1 + 1) rfl (freeCocP_d g I p cyc) := by
  have e2 : ∀ x, (preHomologyObjIso Λ g I.cocomplex (p + 1) V).hom.hom
      ((preHomologyObjIso Λ g I.cocomplex (p + 1) V).inv.hom x) = x := fun x => by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.inv_hom_id, ModuleCat.hom_id, LinearMap.id_apply]
  refine (germExt_apply Λ g I p V _).trans ?_
  refine (congrArg (secExt Λ I ((etPull g).obj V) p) (e2 _)).trans ?_
  refine (secExt_π Λ I ((etPull g).obj V) p cyc).trans ?_
  refine (cocExt_apply Λ I ((etPull g).obj V) p _).trans ?_
  refine (extMk_congr I (congrArg (freeEquiv Λ ((etPull g).obj V) (I.cocomplex.X (p + 1))).symm
    (cocSec_cycles Λ I ((etPull g).obj V) p cyc)) _ _ _ ?_).trans ?_
  · rw [CochainComplex.next]
    exact freeCocP_d g I p cyc
  exact extMk_succ I _ _ _ _ _

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_Zero =====
section

/-!
# S4-EtPBC-C1, part 17: the base change morphism in degree `0` (generic)

For additive `R : C ⥤ D`, `R' : C' ⥤ D'`, exact `Lc`, `Ld` and `β : R ⋙ Ld ⟶ Lc ⋙ R'`:
* `bcMorRes_cls0`: the degree-`0` analogue of `bcMorRes_cls` (classes of cycles in degree `0`);
* **`bcMorRes_zero`**: `Ld (R.toRightDerivedZero X) ≫ bcMorRes 0 I J = β_X ≫ R'.toRightDerivedZero (Lc X)`,
  i.e. in degree `0` the base change morphism is `β` itself; `bcMorGen_zero` for `bcMorGen`.
-/

set_option autoImplicit false

open CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

section BC0

variable {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
  {C' : Type*} [Category C'] [Abelian C'] {D' : Type*} [Category D'] [Abelian D']
  (R : C ⥤ D) [R.Additive] (R' : C' ⥤ D') [R'.Additive]
  (Lc : C ⥤ C') [Lc.Additive] [Lc.PreservesHomology] [Lc.PreservesMonomorphisms]
  (Ld : D ⥤ D') [Ld.Additive] [Ld.PreservesHomology]
  (β : R ⋙ Ld ⟶ Lc ⋙ R') [HasInjectiveResolutions C] [HasInjectiveResolutions C']

set_option backward.isDefEq.respectTransparency false in
/-- **The base change morphism on the class of a degree-`0` cycle.** -/
theorem bcMorRes_cls0 {X : C} (I : InjectiveResolution X) (J : InjectiveResolution (Lc.obj X))
    {A : D'} {Y : D} (a : A ⟶ Ld.obj Y) (k : Y ⟶ ((R.mapHomologicalComplex _).obj I.cocomplex).X 0)
    (hk : k ≫ ((R.mapHomologicalComplex _).obj I.cocomplex).d 0 1 = 0)
    (hk2 : ((a ≫ Ld.map k) ≫ β.app (I.cocomplex.X 0) ≫ R'.map ((liftLc Lc I J).f 0)) ≫
      ((R'.mapHomologicalComplex _).obj J.cocomplex).d 0 1 = 0) :
    a ≫ Ld.map (((R.mapHomologicalComplex _).obj I.cocomplex).liftCycles k 1
        (CochainComplex.next ℕ 0) hk ≫ ((R.mapHomologicalComplex _).obj I.cocomplex).homologyπ 0 ≫
        (I.isoRightDerivedObj R 0).inv) ≫ bcMorRes R R' Lc Ld β 0 I J =
      ((R'.mapHomologicalComplex _).obj J.cocomplex).liftCycles
        ((a ≫ Ld.map k) ≫ β.app (I.cocomplex.X 0) ≫ R'.map ((liftLc Lc I J).f 0)) 1
        (CochainComplex.next ℕ 0) hk2 ≫ ((R'.mapHomologicalComplex _).obj J.cocomplex).homologyπ 0 ≫
        (J.isoRightDerivedObj R' 0).inv := by
  have hk' : Ld.map k ≫ ((Ld.mapHomologicalComplex _).obj ((R.mapHomologicalComplex _).obj I.cocomplex)).d
      0 1 = 0 := by
    rw [Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp, hk, Functor.map_zero]
  have e1 := map_liftCycles_homologyπ_cx Ld ((R.mapHomologicalComplex _).obj I.cocomplex) 0 1
    (CochainComplex.next ℕ 0) k hk hk'
  have hψ : (a ≫ Ld.map k) ≫ (betaCx R R' Lc Ld β I.cocomplex ≫
      (R'.mapHomologicalComplex _).map (liftLc Lc I J)).f 0 =
      (a ≫ Ld.map k) ≫ β.app (I.cocomplex.X 0) ≫ R'.map ((liftLc Lc I J).f 0) := by
    rw [HomologicalComplex.comp_f, betaCx_f, Functor.mapHomologicalComplex_map_f]
  have e2 := liftCycles_homologyπ_homologyMap (betaCx R R' Lc Ld β I.cocomplex ≫
      (R'.mapHomologicalComplex _).map (liftLc Lc I J)) 0 1 (CochainComplex.next ℕ 0)
    (a ≫ Ld.map k) (by rw [Category.assoc, hk', comp_zero]) (hψ ▸ hk2)
  rw [bcMorRes]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Ld.map_comp_assoc (I.isoRightDerivedObj R 0).inv, Iso.inv_hom_id, Ld.map_id, Category.id_comp,
    ← Ld.map_comp_assoc, reassoc_of% e1, ← Category.assoc a, HomologicalComplex.comp_liftCycles,
    reassoc_of% e2]
  exact congrArg (fun t => t ≫ ((R'.mapHomologicalComplex _).obj J.cocomplex).homologyπ 0 ≫
    (J.isoRightDerivedObj R' 0).inv) (EtCompact.liftCycles_eq_of_eq _ _ _ _
      (by rw [HomologicalComplex.comp_f, betaCx_f, Functor.mapHomologicalComplex_map_f]) _ _)

set_option backward.isDefEq.respectTransparency false in
/-- **In degree `0` the base change morphism is `β`**:
`Ld (R.toRightDerivedZero X) ≫ bcMorRes 0 I J = β_X ≫ R'.toRightDerivedZero (Lc X)`. -/
theorem bcMorRes_zero {X : C} (I : InjectiveResolution X) (J : InjectiveResolution (Lc.obj X)) :
    Ld.map (R.toRightDerivedZero.app X) ≫ bcMorRes R R' Lc Ld β 0 I J =
      β.app X ≫ R'.toRightDerivedZero.app (Lc.obj X) := by
  have hk : R.map (I.ι.f 0) ≫ ((R.mapHomologicalComplex _).obj I.cocomplex).d 0 1 = 0 := by
    rw [Functor.mapHomologicalComplex_obj_d, ← R.map_comp, I.ι_f_zero_comp_complex_d, R.map_zero]
  have hβ : (𝟙 (Ld.obj (R.obj X)) ≫ Ld.map (R.map (I.ι.f 0))) ≫ β.app (I.cocomplex.X 0) ≫
      R'.map ((liftLc Lc I J).f 0) = β.app X ≫ R'.map (J.ι.f 0) := by
    have hn := β.naturality (I.ι.f 0)
    simp only [Functor.comp_map] at hn
    rw [Category.id_comp, ← Category.assoc, hn, Category.assoc, ← R'.map_comp, liftLc_f_zero]
    rfl
  have hk3 : R'.map (J.ι.f 0) ≫ ((R'.mapHomologicalComplex _).obj J.cocomplex).d 0 1 = 0 := by
    rw [Functor.mapHomologicalComplex_obj_d, ← R'.map_comp, J.ι_f_zero_comp_complex_d, R'.map_zero]
  have hk2 : ((𝟙 (Ld.obj (R.obj X)) ≫ Ld.map (R.map (I.ι.f 0))) ≫ β.app (I.cocomplex.X 0) ≫
      R'.map ((liftLc Lc I J).f 0)) ≫ ((R'.mapHomologicalComplex _).obj J.cocomplex).d 0 1 = 0 := by
    rw [hβ, Category.assoc, hk3, comp_zero]
  have h1 := (Category.id_comp _).symm.trans (bcMorRes_cls0 R R' Lc Ld β I J (𝟙 _) (R.map (I.ι.f 0)) hk hk2)
  rw [I.toRightDerivedZero_eq R, J.toRightDerivedZero_eq R']
  refine Eq.trans ?_ (h1.trans ?_)
  · rfl
  · rw [EtCompact.liftCycles_eq_of_eq _ _ _ _ hβ hk2 (by rw [Category.assoc, hk3, comp_zero]),
      ← HomologicalComplex.comp_liftCycles _ _ _ _ hk3]
    simp only [Category.assoc]
    rfl

/-- `bcMorRes_zero` for `bcMorGen`. -/
theorem bcMorGen_zero (X : C) :
    Ld.map (R.toRightDerivedZero.app X) ≫ bcMorGen R R' Lc Ld β 0 X =
      β.app X ≫ R'.toRightDerivedZero.app (Lc.obj X) := by
  rw [bcMorGen_eq R R' Lc Ld β 0 (injectiveResolution X) (injectiveResolution (Lc.obj X))]
  exact bcMorRes_zero R R' Lc Ld β _ _

end BC0

end RamanujanPetersson.EtPBC.C1

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

variable {D : Type u₂} [Category.{v₂} D] [Abelian D] {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
  [HasInjectiveResolutions C] {L : D ⥤ C} {R : C ⥤ D} [R.Additive] (adj : L ⊣ R)
  {A : D} {X : C} (e : L.obj A ≅ X) {Y : C} (I : InjectiveResolution Y)

/-- **`absRelR adj e I p : Ext^(p+1)(X, Y) ≃+ Hom(A, R^(p+1) R Y)`** (`A` projective). -/
def absRelR [Projective A] (p : ℕ) : Abelian.Ext X Y (p + 1) ≃+ (A ⟶ (R.rightDerived (p + 1)).obj Y) :=
  (absRelGen adj e I p).trans (homIsoRight A (I.isoRightDerivedObj R (p + 1)).symm)

theorem absRelR_apply [Projective A] (p : ℕ) (x : Abelian.Ext X Y (p + 1)) :
    absRelR adj e I p x = absRelGen adj e I p x ≫ (I.isoRightDerivedObj R (p + 1)).inv :=
  rfl

end GenR

universe u

set_option backward.isDefEq.respectTransparency false

end RamanujanPetersson.EtPBC.C1

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

variable {F} in
/-- Every element of the stalk of `Q` at `s` is a germ at some neighbourhood. -/
theorem exists_germ (Q : S.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ) (x : ToType (s.point.presheafFiber.obj Q)) :
    ∃ (j : Nbhd s) (z : ToType (Q.obj (op j.1))), (s.point.toPresheafFiber j.1 j.2 Q).hom z = x := by
  obtain ⟨X, v, z, hz⟩ := s.point.toPresheafFiber_jointly_surjective x
  exact ⟨⟨X, v⟩, z, hz⟩

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

/-- **`pbcEquivS hI hS : (R^(p+1) g_* F)_s ≃+ H^(p+1)(P_s, ι^* F)`**, the named proper-base-change equivalence
(`pbcEquivSucc` on the chosen injective resolution; `pbcEquivS_spec` describes it without resolutions). -/
def pbcEquivS (hI : BCInj Λ g s (p + 1) F) (hS : BCSurj Λ g s (p + 1) F) :
    ToType ((s.stalkF Λ).obj (((push g Λ).rightDerived (p + 1)).obj F)) ≃+ H Λ ((pull (fibι g s) Λ).obj F) (p + 1) :=
  pbcEquivSucc Λ g s (injectiveResolution F) p hI hS

end RamanujanPetersson.EtPBC.C1

end

end

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

variable {D : Type u₂} [Category.{v₂} D] [Abelian D] {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
  [HasInjectiveResolutions C] {L : D ⥤ C} {R : C ⥤ D} [R.Additive] (adj : L ⊣ R)
  {A : D} {X : C} {Y Y' : C}

/-- **Naturality of `absRelR`** in the second variable (any resolutions `I`, `I'`). -/
theorem absRelR_natural (e : L.obj A ≅ X) (I : InjectiveResolution Y) (I' : InjectiveResolution Y') [Projective A]
    (p : ℕ) (ψ : Y ⟶ Y') (x : Abelian.Ext X Y (p + 1)) :
    absRelR adj e I' p (x.comp (Abelian.Ext.mk₀ ψ) (add_zero (p + 1))) =
      absRelR adj e I p x ≫ (R.rightDerived (p + 1)).map ψ := by
  obtain ⟨f, hf, rfl⟩ := I.extMk_surjective x (p + 1 + 1) rfl
  rw [InjectiveResolution.extMk_comp_mk₀ (φ := ⟨InjectiveResolution.desc ψ I' I, by simp⟩), absRelR_apply,
    absRelR_apply, absRelGen_extMk, absRelGen_extMk, Category.assoc, Category.assoc,
    InjectiveResolution.isoRightDerivedObj_inv_naturality ψ I I' (InjectiveResolution.desc ψ I' I)
      (InjectiveResolution.desc_commutes_zero ψ I' I) R (p + 1)]
  have h : adj.homEquiv _ _ (e.hom ≫ f ≫ (InjectiveResolution.desc ψ I' I).f (p + 1)) =
      adj.homEquiv _ _ (e.hom ≫ f) ≫ ((R.mapHomologicalComplex _).map (InjectiveResolution.desc ψ I' I)).f (p + 1) := by
    rw [Functor.mapHomologicalComplex_map_f, ← adj.homEquiv_naturality_right, Category.assoc]
  simp only [Category.assoc, Functor.comp_map, HomologicalComplex.homologyFunctor_map,
    HomologicalComplex.homologyπ_naturality_assoc, HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  exact congrArg (fun t => t ≫ (RI I' (R := R)).homologyπ (p + 1) ≫ (I'.isoRightDerivedObj R (p + 1)).inv)
    (EtCompact.liftCycles_eq_of_eq _ _ _ _ h _ _)

end GenN

universe u

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

/-- The base change of the extension to the fibre, `ι^* (ext F) ≅ ext_s (F|X_s)` (`itExtNat` at `g = s.pt`). -/
def extFib (F : EtSh Λ X) : (pull (fibι c.fbar s) Λ).obj ((c.ext Λ).obj F) ≅
    ((fibCpt c s).ext Λ).obj ((pull (cptιX c s) Λ).obj F) :=
  (itExtNat Λ c s.pt).app F

theorem extFib_natural {F F' : EtSh Λ X} (φ : F ⟶ F') :
    (pull (fibι c.fbar s) Λ).map ((c.ext Λ).map φ) ≫ (extFib c s F').hom =
      (extFib c s F).hom ≫ ((fibCpt c s).ext Λ).map ((pull (cptιX c s) Λ).map φ) :=
  (itExtNat Λ c s.pt).hom.naturality φ

end Shriek

end RamanujanPetersson.EtPBC.C1

end

end


