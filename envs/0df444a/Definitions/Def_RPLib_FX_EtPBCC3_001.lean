-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC3_001
-- name    : RPLib_FX_EtPBCC3_001
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-27T05:58:44.030903+00:00
-- url     : https://prove2.me/theorems/450690be-f03b-5414-ade3-76ffc378ad13
-- title:
--   Compactly supported étale cohomology of affine space with Tate twists, library file 001
-- statement:
--   File 001 of the library for compactly supported étale cohomology of affine space with Tate twists: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtSheaves_CutSet`: S4-EtSheaves, part 21: `F_S` for a subset `S`
--   * `S4.Def_RP_EtSheaves_Closed`: S4-EtSheaves, part 14: `i_*` vanishes off `Z`
--   * `S4.Def_RP_EtSheaves_ClosedFF`: S4-EtSheaves, part 15: the cut sequence `0 → j_! j^* F → F → i_* i^* F → 0`
--   * `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
--   * `S4.Def_RP_EtCompact_Pres`: S4-EtCompact, part 8: presentations and the set-indexed `H^*_c`
--   * `S4.Def_RP_EtCompact_CutFun`: S4-EtCompact, part 6: `F ↦ F_{W ∩ Vᶜ}` is exact; long exact sequence in the sheaf variable
--   * `S4.Def_RP_EtCompact_A1`: S4-EtCompact, part 12: the affine line inside `P^1` (O6, explicit compactifications)
--   * `S4.Def_RP_EtCompact_P1Pts`: S4-EtCompact, part 27: points of `P^1_K` (O8a, file 1)
--   * `S4.Def_RP_EtCompact_Pt`: S4-EtCompact, part 14: cohomology of a separably closed point (O6d / O7 in dimension 0)
--   * `S4.Def_RP_EtCompact_P1Exc`: S4-EtCompact, part 28: excision on `P^1_K` at `∞` (O8a, file 2)
--   * `S4.Def_RP_EtCompact_A1Hc`: S4-EtCompact, part 29: `H^*_c(A^1, Λ)` inside `P^1` (O8a, file 3)
--   * `S4.Def_RP_EtCompact_P1H0`: S4-EtCompact, part 30: `H^0_c(A^1, Λ) = 0` and `H^1_c(A^1, Λ) ≃ H^1(P^1, Λ)` (O8a, file 4)
--   * `S4.Def_RP_EtPBC_B_Rsh`: S4-EtPBC-B, D1: stalks of `R^q f_!` are the compactly supported cohomology of the geometric fibre
--   * `S4.Def_RP_EtCompact_BC`: S4-EtCompact, part 13: base change and products of compactifications; `P^1`-bundles (O6)
--   * `S4.Def_RP_EtLeray_Shift`: S4-EtLeray, part 2: shifting an injective resolution (dimension shift for `R^q`)
--   * `S4.Def_RP_EtLeray_Low`: S4-EtLeray, part 3: `R¹ N` as a cokernel, and the low-degree consequences
--   * `S4.Def_RP_EtLeray_BCo`: S4-EtLeray, part 10: base change along arbitrary pullback squares
--   * `S4.Def_RP_EtLeray_Sq`: S4-EtLeray, part 11: the pullback squares relating `c0.prod d` and `c0.baseChange g`
--   * `S4.Def_RP_EtLeray_Bnd`: S4-EtLeray, part 9: boundary vanishing for compact supports
--   * `S4.Def_RP_EtLeray_Key`: S4-EtLeray, part 12: the key isomorphism `R^q π_* (prod.ext F) ≅ d.ext (R^q f_! F)`
--   * `S4.Def_RP_EtPBC_B_RshA`: S4-EtPBC-B, D2: `P4` for the relative affine line and the coordinate projections of `A^n`
--   * `S4.Def_RP_EtLeray_RelA`: S4-EtLeray, part 15: relative one-row Grothendieck, acyclic case and row `1`
--   * `S4.Def_RP_EtLin_Gen`: S4-EtLin, Gen: generic Λ-linearity (adjoints, homology, right derived functors, Ext upgrade lemmas)
--   * `S4.Def_RP_EtLin_ExtL`: S4-EtLin, ExtL: `Λ`-linear versions of the basic `Ext` / `H` maps
--   * `S4.Def_RP_EtLin_Fun`: S4-EtLin, Fun: the named functors on étale sheaves are `Λ`-linear
--
--   **Formalization note.** One file of a library formalizing the étale cohomology with compact supports of affine space over an algebraically closed field $K$ with Tate-twisted coefficients: for $\Lambda$ a finite ring with $\ell^m \Lambda = 0$ ($\ell$ invertible in $K$) and $\Lambda(k)$ the constant sheaf $(\Lambda \otimes \mu_{\ell^m})^{\otimes k}$, $H^q_c(\mathbb{A}^{n+1}_K, \Lambda(k)) = 0$ for $q \ne 2n+2$ and $H^{2n+2}_c(\mathbb{A}^{n+1}_K, \Lambda(n+1)) \cong \Lambda$ $\Lambda$-linearly, via $R^q \mathrm{pr}_!$ of the relative affine line and induction on the dimension. It builds on the proper base change libraries (`RPLib_FX_EtPBC_*`, `RPLib_FX_EtPBCB_*`, `RPLib_FX_EtPBCC1_*`, `RPLib_FX_EtPBCC2_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XVII (P. Deligne, cohomologie à supports propres) and Exposé XVIII, 2.9 (P. Deligne, morphisme trace), Lecture Notes in Math. 305, Springer (1973); P. Deligne, SGA 4 1/2, [Arcata], Lecture Notes in Math. 569 (1977); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCC1_010
import Definitions.Def_RPLib_FX_EtPBCC3_002

/-!
# Compactly supported étale cohomology of affine space with Tate twists, library file 001

Declarations of the formalization of compactly supported étale cohomology of affine space over an
algebraically closed field with Tate-twisted coefficients: H^q_c(A^(n+1), Λ(k)) = 0 for q ≠ 2n+2 and
H^(2n+2)_c(A^(n+1), Λ(n+1)) ≃ Λ, Λ-linearly, re-hosted declaration by declaration from the library
modules below, on top of the proper base change libraries RPLib_FX_EtPBC, RPLib_FX_EtPBCB,
RPLib_FX_EtPBCC1 and RPLib_FX_EtPBCC2. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtSheaves_CutSet`: S4-EtSheaves, part 21: `F_S` for a subset `S`
* `S4.Def_RP_EtSheaves_Closed`: S4-EtSheaves, part 14: `i_*` vanishes off `Z`
* `S4.Def_RP_EtSheaves_ClosedFF`: S4-EtSheaves, part 15: the cut sequence `0 → j_! j^* F → F → i_* i^* F → 0`
* `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
* `S4.Def_RP_EtCompact_Pres`: S4-EtCompact, part 8: presentations and the set-indexed `H^*_c`
* `S4.Def_RP_EtCompact_CutFun`: S4-EtCompact, part 6: `F ↦ F_{W ∩ Vᶜ}` is exact; long exact sequence in the sheaf variable
* `S4.Def_RP_EtCompact_A1`: S4-EtCompact, part 12: the affine line inside `P^1` (O6, explicit compactifications)
* `S4.Def_RP_EtCompact_P1Pts`: S4-EtCompact, part 27: points of `P^1_K` (O8a, file 1)
* `S4.Def_RP_EtCompact_Pt`: S4-EtCompact, part 14: cohomology of a separably closed point (O6d / O7 in dimension 0)
* `S4.Def_RP_EtCompact_P1Exc`: S4-EtCompact, part 28: excision on `P^1_K` at `∞` (O8a, file 2)
* `S4.Def_RP_EtCompact_A1Hc`: S4-EtCompact, part 29: `H^*_c(A^1, Λ)` inside `P^1` (O8a, file 3)
* `S4.Def_RP_EtCompact_P1H0`: S4-EtCompact, part 30: `H^0_c(A^1, Λ) = 0` and `H^1_c(A^1, Λ) ≃ H^1(P^1, Λ)` (O8a, file 4)
* `S4.Def_RP_EtPBC_B_Rsh`: S4-EtPBC-B, D1: stalks of `R^q f_!` are the compactly supported cohomology of the geometric fibre
* `S4.Def_RP_EtCompact_BC`: S4-EtCompact, part 13: base change and products of compactifications; `P^1`-bundles (O6)
* `S4.Def_RP_EtLeray_Shift`: S4-EtLeray, part 2: shifting an injective resolution (dimension shift for `R^q`)
* `S4.Def_RP_EtLeray_Low`: S4-EtLeray, part 3: `R¹ N` as a cokernel, and the low-degree consequences
* `S4.Def_RP_EtLeray_BCo`: S4-EtLeray, part 10: base change along arbitrary pullback squares
* `S4.Def_RP_EtLeray_Sq`: S4-EtLeray, part 11: the pullback squares relating `c0.prod d` and `c0.baseChange g`
* `S4.Def_RP_EtLeray_Bnd`: S4-EtLeray, part 9: boundary vanishing for compact supports
* `S4.Def_RP_EtLeray_Key`: S4-EtLeray, part 12: the key isomorphism `R^q π_* (prod.ext F) ≅ d.ext (R^q f_! F)`
* `S4.Def_RP_EtPBC_B_RshA`: S4-EtPBC-B, D2: `P4` for the relative affine line and the coordinate projections of `A^n`
* `S4.Def_RP_EtLeray_RelA`: S4-EtLeray, part 15: relative one-row Grothendieck, acyclic case and row `1`
* `S4.Def_RP_EtLin_Gen`: S4-EtLin, Gen: generic Λ-linearity (adjoints, homology, right derived functors, Ext upgrade lemmas)
* `S4.Def_RP_EtLin_ExtL`: S4-EtLin, ExtL: `Λ`-linear versions of the basic `Ext` / `H` maps
* `S4.Def_RP_EtLin_Fun`: S4-EtLin, Fun: the named functors on étale sheaves are `Λ`-linear
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

/-- **`F_S`**: `F` restricted to `S` and extended by zero. -/
def cut (S : Set X) (F : EtSh Λ X) : EtSh Λ X := openCut Λ (cutOpen S) (quotCut Λ (cutCompl S) F)

variable {Λ}

theorem mem_cutOpen {S : Set X} (hS : IsLocallyClosed S) {x : X} (hx : x ∈ S) : x ∈ cutOpen S := by
  change x ∈ interior (coborder S)
  rw [(isLocallyClosed_iff_isOpen_coborder.1 hS).interior_eq]
  exact subset_coborder hx

theorem mem_of_mem_cutOpen {S : Set X} {x : X} (h : x ∈ cutOpen S) (hc : x ∈ closure S) : x ∈ S := by
  by_contra hn
  exact (interior_subset h : x ∈ coborder S) ⟨hc, hn⟩

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_Closed =====
section

/-!
# S4-EtSheaves, part 14: `i_*` vanishes off `Z`

For `i : Z ⟶ X` and an etale `j : U ⟶ X` whose image misses the image of `i`, the restriction
`j^* i_* G` is the zero sheaf: its values are those of `G` on the empty schemes `W ×_X Z`.
Hence the stalks of `i_* G` vanish at geometric points outside the (closed) image of `i`, every
map `j_! G' ⟶ i_* G` is zero, and `j_! j^* F ⟶ F ⟶ i_* i^* F` is a complex.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ]

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [Etale j]

/-- Every map `j_! G' ⟶ H` with `j^* H = 0` is zero. -/
theorem lsh_hom_eq_zero {G' : EtSh Λ U} {H : EtSh Λ X} (hH : IsZero ((res j Λ).obj H))
    (φ : (lsh j Λ).obj G' ⟶ H) : φ = 0 :=
  ((lshAdj j Λ).homEquiv _ _).injective (hH.eq_of_tgt _ _)

/-- **`j_! j^* F ⟶ F ⟶ i_* i^* F` is zero** when the images of `j` and `i` are disjoint. -/
theorem counit_comp_unit (h : Disjoint (Set.range j) (Set.range i)) (F : EtSh Λ X) :
    (lshAdj j Λ).counit.app F ≫ (pullAdj i Λ).unit.app F = 0 :=
  lsh_hom_eq_zero Λ j (isZero_res_push Λ i j h _) _

/-- The complex `j_! j^* F ⟶ F ⟶ i_* i^* F`. -/
@[simps]
def cutComplex (h : Disjoint (Set.range j) (Set.range i)) (F : EtSh Λ X) :
    ShortComplex (EtSh Λ X) :=
  ShortComplex.mk ((lshAdj j Λ).counit.app F) ((pullAdj i Λ).unit.app F) (counit_comp_unit Λ i j h F)

end RamanujanPetersson.EtSheaves

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

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}} {ι : Type u} (s : ι → GeomPt X)
  (hs : ⋃ k, Set.range (s k).pt = Set.univ)

include hs

/-- Epimorphisms are detected on a covering family of geometric points. -/
theorem epi_of_family {F G : EtSh Λ X} (φ : F ⟶ G) (h : ∀ k, Epi (((s k).stalkF Λ).map φ)) :
    Epi φ := by
  have : ∀ i : (ObjectProperty.ofObj (fun k => (s k).point)).FullSubcategory,
      Epi ((i.obj.sheafFiber (A := ModuleCat.{u} Λ)).map φ) := by
    rintro ⟨Φ, hΦ⟩
    cases hΦ with
    | mk k => exact h k
  exact ((conservative_family s hs).jointlyReflectEpimorphisms (ModuleCat.{u} Λ)).epi φ

end Family

section Pts

end Pts

section CoverDense

end CoverDense

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

/-- Cohomology with compact supports of `W ∩ Vᶜ` computed on the ambient `X`. -/
abbrev HcWV (W V : X.Opens) (F : EtSh Λ X) (n : ℕ) : Type u := H Λ (cutWV Λ W V F) n

variable {Λ} (W : X.Opens) {V V' : X.Opens} (h : V ≤ V') (F : EtSh Λ X)

/-- The boundary map `H^n_c(Z) → H^(n+1)_c(U)` of the excision sequence. -/
def excδ (n : ℕ) : HcWV Λ W V' F n →+ HcWV Λ (W ⊓ V') V F (n + 1) :=
  (excComplex_shortExact W h F).extClass.postcomp _ rfl

/-- **Excision, exactness at `H^n_c(S)`**: `H^n_c(U) → H^n_c(S) → H^n_c(Z)`. -/
theorem exc_exact₂ (n : ℕ) :
    Function.Exact (Hmap Λ (excComplex W h F).f n) (Hmap Λ (excComplex W h F).g n) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Ext.covariant_sequence_exact₂' (unitSh Λ X) (excComplex_shortExact W h F) n)

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_Pres =====
section

/-!
# S4-EtCompact, part 8: presentations and the set-indexed `H^*_c`

`cutWV W V F` only depends on the locally closed set `W ∩ Vᶜ` (up to a canonical chain of stalkwise
isomorphisms). So `HcSet S F n := H^n(X, cut S F)` (`cut` from `Def_RP_EtSheaves_CutSet`, which is
`cutWV (cutOpen S) (cutCompl S)`) is computed by any presentation `S = W ∩ Vᶜ`, and the excision
long exact sequence holds for every locally closed `S` and open `O`:
`… → H^n_c(S ∩ O) → H^n_c(S) → H^n_c(S \ O) → H^(n+1)_c(S ∩ O) → …` (E0Probe P2 in subset form).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

/-- The locally closed set `W ∩ Vᶜ`. -/
def wvSet (W V : X.Opens) : Set X := (W : Set X) ∩ (V : Set X)ᶜ

theorem mem_wvSet {W V : X.Opens} {x : X} : x ∈ wvSet W V ↔ x ∈ W ∧ x ∉ V :=
  Iff.rfl

theorem isLocallyClosed_wvSet (W V : X.Opens) : IsLocallyClosed (wvSet W V) :=
  W.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed

theorem wvSet_inf_sup (W V O : X.Opens) : wvSet (W ⊓ (V ⊔ O)) V = wvSet W V ∩ (O : Set X) := by
  ext x
  simp only [wvSet, Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe, Opens.mem_inf,
    Opens.mem_sup]
  tauto

theorem wvSet_sup (W V O : X.Opens) : wvSet W (V ⊔ O) = wvSet W V \ (O : Set X) := by
  ext x
  simp only [wvSet, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff, SetLike.mem_coe,
    Opens.mem_sup]
  tauto

/-- A locally closed `S` is cut out by `(cutOpen S, cutCompl S)`. -/
theorem wvSet_cut {S : Set X} (hS : IsLocallyClosed S) : wvSet (cutOpen S) (cutCompl S) = S := by
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    exact mem_of_mem_cutOpen h1 (by_contra fun hc => h2 hc)
  · intro hx
    exact ⟨mem_cutOpen hS hx, fun h => h (subset_closure hx)⟩

section Pres

variable (F : EtSh Λ X)

/-- Shrinking `W` to `W'` without changing `W ∩ Vᶜ`. -/
theorem isIso_cutWV_shrinkW {W W' : X.Opens} (V : X.Opens) (h : W' ≤ W)
    (hS : ∀ x, x ∈ W → x ∉ W' → x ∈ V) : IsIso (openCutLe h (quotCut Λ V F)) := by
  rw [isIso_iff_stalk]
  intro x
  by_cases hx' : x ∈ W'
  · exact isIso_stalk_openCutLe h (quotCut Λ V F) _ (mem_center_geomPtAt hx')
  · refine isIso_of_zero_zero _ (isZero_stalk_cutWV_of_not_mem F _ (not_mem_center_geomPtAt hx')) ?_
    by_cases hx : x ∈ W
    · exact isZero_stalk_cutWV_of_mem F _ (mem_center_geomPtAt hx)
        (mem_center_geomPtAt (hS x hx hx'))
    · exact isZero_stalk_cutWV_of_not_mem F _ (not_mem_center_geomPtAt hx)

/-- Enlarging `V` to `V'` without changing `W ∩ Vᶜ`. -/
theorem isIso_cutWV_growV (W : X.Opens) {V V' : X.Opens} (h : V ≤ V')
    (hS : ∀ x, x ∈ W → x ∈ V' → x ∈ V) : IsIso (openCutMap W (quotCutLe h F)) := by
  rw [isIso_iff_stalk]
  intro x
  by_cases hW : x ∈ W
  · by_cases hV' : x ∈ V'
    · exact isIso_of_zero_zero _
        (isZero_stalk_cutWV_of_mem F _ (mem_center_geomPtAt hW) (mem_center_geomPtAt (hS x hW hV')))
        (isZero_stalk_cutWV_of_mem F _ (mem_center_geomPtAt hW) (mem_center_geomPtAt hV'))
    · exact isIso_stalk_openCutMap W (quotCutLe h F) _ (mem_center_geomPtAt hW)
        (isIso_stalk_quotCutLe h F _ (not_mem_center_geomPtAt hV'))
  · exact isIso_of_zero_zero _ (isZero_stalk_cutWV_of_not_mem F _ (not_mem_center_geomPtAt hW))
      (isZero_stalk_cutWV_of_not_mem F _ (not_mem_center_geomPtAt hW))

variable {W₁ V₁ W₂ V₂ : X.Opens} (hS : wvSet W₁ V₁ = wvSet W₂ V₂)

include hS in
theorem wv_cond₁ : ∀ x, x ∈ W₁ → x ∉ W₁ ⊓ W₂ → x ∈ V₁ := fun x hx1 hx12 =>
  by_contra fun hv => hx12 ⟨hx1, (mem_wvSet.1 ((Set.ext_iff.1 hS x).1 ⟨hx1, hv⟩)).1⟩

include hS in
theorem wv_cond₂ : ∀ x, x ∈ W₁ ⊓ W₂ → x ∈ V₁ ⊔ V₂ → x ∈ V₁ := fun x hx hv =>
  by_contra fun hv1 => by
    rcases Opens.mem_sup.1 hv with h | h
    · exact hv1 h
    · exact (mem_wvSet.1 ((Set.ext_iff.1 hS x).1 ⟨hx.1, hv1⟩)).2 h

/-- **Presentation independence**: `W₁ ∩ V₁ᶜ = W₂ ∩ V₂ᶜ` gives `cutWV W₁ V₁ F ≅ cutWV W₂ V₂ F`. -/
def cutWVIso : cutWV Λ W₁ V₁ F ≅ cutWV Λ W₂ V₂ F :=
  (@asIso _ _ _ _ (openCutLe (inf_le_left : W₁ ⊓ W₂ ≤ W₁) (quotCut Λ V₁ F))
      (isIso_cutWV_shrinkW F V₁ _ (wv_cond₁ hS))).symm ≪≫
    @asIso _ _ _ _ (openCutMap (W₁ ⊓ W₂) (quotCutLe (le_sup_left : V₁ ≤ V₁ ⊔ V₂) F))
      (isIso_cutWV_growV F _ _ (wv_cond₂ hS)) ≪≫
    (@asIso _ _ _ _ (openCutMap (W₁ ⊓ W₂) (quotCutLe (le_sup_right : V₂ ≤ V₁ ⊔ V₂) F))
      (isIso_cutWV_growV F _ _ (by
        have h := wv_cond₂ hS.symm
        intro x hx hv
        exact h x ⟨hx.2, hx.1⟩ (Opens.mem_sup.2 ((Opens.mem_sup.1 hv).symm))))).symm ≪≫
    @asIso _ _ _ _ (openCutLe (inf_le_right : W₁ ⊓ W₂ ≤ W₂) (quotCut Λ V₂ F))
      (isIso_cutWV_shrinkW F V₂ _ (by
        have h := wv_cond₁ hS.symm
        intro x hx hx12
        exact h x hx (fun hx' => hx12 ⟨hx'.2, hx'.1⟩)))

end Pres

section HcSet

variable (Λ) in
/-- **`H^n_c(S, F)`** for a locally closed `S` of the ambient `X` (the subset model). -/
abbrev HcSet (S : Set X) (F : EtSh Λ X) (n : ℕ) : Type u := H Λ (cut Λ S F) n

variable (F : EtSh Λ X)

theorem cut_eq_cutWV (S : Set X) : cut Λ S F = cutWV Λ (cutOpen S) (cutCompl S) F :=
  rfl

/-- `cut S F ≅ cutWV W V F` for any presentation `S = W ∩ Vᶜ`. -/
def cutIsoCutWV {S : Set X} {W V : X.Opens} (h : wvSet W V = S) : cut Λ S F ≅ cutWV Λ W V F :=
  cutWVIso F ((wvSet_cut (S := S) (h ▸ isLocallyClosed_wvSet W V)).trans h.symm)

end HcSet

section SetExc

theorem exact_conj {A B C A' B' C' : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C'] (e₁ : A' ≃+ A) (e₂ : B' ≃+ B)
    (e₃ : C' ≃+ C) {f : A →+ B} {g : B →+ C} (h : Function.Exact f g) :
    Function.Exact (fun x => e₂.symm (f (e₁ x))) (fun y => e₃.symm (g (e₂ y))) := by
  intro y
  constructor
  · intro hy
    have h0 : g (e₂ y) = 0 := by
      have := congrArg e₃ hy
      rwa [AddEquiv.apply_symm_apply, map_zero] at this
    obtain ⟨a, ha⟩ := (h (e₂ y)).1 h0
    refine ⟨e₁.symm a, ?_⟩
    show e₂.symm (f (e₁ (e₁.symm a))) = y
    rw [AddEquiv.apply_symm_apply, ha, AddEquiv.symm_apply_apply]
  · rintro ⟨x, rfl⟩
    show e₃.symm (g (e₂ (e₂.symm (f (e₁ x))))) = 0
    rw [AddEquiv.apply_symm_apply, h.apply_apply_eq_zero, map_zero]

variable (F : EtSh Λ X) {S : Set X} (hS : IsLocallyClosed S) (O : X.Opens)

include hS in
theorem wvSet_U : wvSet (cutOpen S ⊓ (cutCompl S ⊔ O)) (cutCompl S) = S ∩ (O : Set X) := by
  rw [wvSet_inf_sup, wvSet_cut hS]

include hS in
theorem wvSet_Z : wvSet (cutOpen S) (cutCompl S ⊔ O) = S \ (O : Set X) := by
  rw [wvSet_sup, wvSet_cut hS]

end SetExc

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_CutFun =====
section

/-!
# S4-EtCompact, part 6: `F ↦ F_{W ∩ Vᶜ}` is exact; long exact sequence in the sheaf variable

`quotFunctor V : F ↦ F / j_{V!} F|_V` and `cutWVFunctor W V = quotFunctor V ⋙ res ⋙ lsh` (whose
value at `F` is `cutWV W V F` by definition) are exact: `quotFunctor` is checked on stalks, the
other two factors are exact by `Def_RP_EtCompact_Exact`. Hence a short exact sequence
`0 → F' → F → F'' → 0` gives the long exact sequence
`… → H^n_c(S, F') → H^n_c(S, F) → H^n_c(S, F'') → H^(n+1)_c(S, F') → …`
(E0Probe amendment A7).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

section Quot

variable (V : X.Opens)

/-- Functoriality of `F ↦ F / j_{V!} F|_V`. -/
def quotMap {F G : EtSh Λ X} (φ : F ⟶ G) : quotCut Λ V F ⟶ quotCut Λ V G :=
  cokernel.map (openCutι Λ V F) (openCutι Λ V G) (openCutMap V φ) φ (openCutMap_comp V φ).symm

@[reassoc (attr := simp)]
theorem quotCutπ_comp_quotMap {F G : EtSh Λ X} (φ : F ⟶ G) :
    quotCutπ Λ V F ≫ quotMap V φ = φ ≫ quotCutπ Λ V G :=
  cokernel.π_desc _ _ _

end Quot

section SheafLES

end SheafLES

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_A1 =====
section

/-!
# S4-EtCompact, part 12: the affine line inside `P^1` (O6, explicit compactifications)

Mathlib has no dehomogenization, so we build `K[X₀, X₁]_(X₀) ≃+* K[t]` by hand: `dehom` (`X₀ ↦ 1`,
`X₁ ↦ t`) is injective on each homogeneous component (`eq_zero_of_dehom`), so the induced map
`awayDehom : Away 𝒜 X₀ →+* K[t]` is bijective (`awayEquivPoly`). Hence `chartA1 : A^1_K ⟶ P^1_K` is an open
immersion over `K` (`chartA1_toSpecK`), and `A1.cpt K : Cpt (A1.toSpecK K)` is the compactification
`A^1 ⊆ P^1 → Spec K` (closure `Z = P^1`).
-/

set_option autoImplicit false

open AlgebraicGeometry MvPolynomial CategoryTheory HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtCompact

universe u

variable {K : Type u} [Field K]

theorem awayDehom_fromZero (y : homogeneousSubmodule (Fin 2) K 0) :
    awayDehom (fromZeroRingHom (homogeneousSubmodule (Fin 2) K) _ y) = dehom y.1 := by
  have hy : (y.1 : MvPolynomial (Fin 2) K) ∈ homogeneousSubmodule (Fin 2) K (0 • 1) := by
    rw [zero_smul]
    exact y.2
  have he : fromZeroRingHom (homogeneousSubmodule (Fin 2) K) (Submonoid.powers (X 0 : MvPolynomial (Fin 2) K)) y =
      Away.mk (homogeneousSubmodule (Fin 2) K) (P1.X_mem K 0) 0 y.1 hy := by
    ext
    simp [fromZeroRingHom]
    rfl
  rw [he, awayDehom_mk]

variable (K) in
/-- The structure map `A^1_K ⟶ Spec K`. -/
def A1.toSpecK : A1 K ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : K →+* Polynomial K))

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_P1Pts =====
section

/-!
# S4-EtCompact, part 27: points of `P^1_K` (O8a, file 1)

* `P1.genPt K`: the generic point `(0)`; `closure {genPt} = univ`, so `P^1_K` is irreducible (hence connected).
* `P1.infPt K`: the point `∞ = (X₀)`; every point whose ideal contains `X₀` is `∞` (`P1.eq_infPt_of_X0_mem`).
* The image of the chart `chartA1 : A^1_K ⟶ P^1_K` is `D₊(X₀)`, its complement is `{∞}`, so `{∞}` is closed and
  `Spec κ(∞) ⟶ P^1_K` is a closed immersion; for algebraically closed `K`, `κ(∞) ≅ K` is algebraically closed.
-/

set_option autoImplicit false

open AlgebraicGeometry MvPolynomial CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtCompact

universe u

variable (K : Type u) [Field K]

/-! ### The generic point -/

/-! ### The point at infinity -/

/-! ### The chart `A^1_K ⊆ P^1_K` and its complement `{∞}` -/

theorem P1.compl_range_chartA1 : ((chartA1 K).opensRange : Set (P1 K))ᶜ = {P1.infPt K} := by
  ext x
  rw [Set.mem_compl_iff, SetLike.mem_coe, P1.mem_range_chartA1_iff, Set.mem_singleton_iff, not_not]

theorem P1.univ_diff_range_chartA1 :
    Set.univ \ ((chartA1 K).opensRange : Set (P1 K)) = {P1.infPt K} := by
  rw [← Set.compl_eq_univ_sdiff, P1.compl_range_chartA1]

theorem P1.isClosed_infPt : IsClosed ({P1.infPt K} : Set (P1 K)) := by
  rw [← P1.compl_range_chartA1]
  exact (chartA1 K).opensRange.isOpen.isClosed_compl

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

/-- **Cohomology of a separably closed point vanishes in positive degrees.** -/
theorem H_eq_zero_of_point [Subsingleton (Gal x0)] (F : EtSh Λ X) (n : ℕ) (e : H Λ F (n + 1)) : e = 0 := by
  have := unitSh_projective x0 Λ
  exact Abelian.Ext.eq_zero_of_projective e

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_P1Exc =====
section

/-!
# S4-EtCompact, part 28: excision on `P^1_K` at `∞` (O8a, file 2)

General facts:
* `Hmap_zero_injective`: `H^0(X, -)` sends monomorphisms to injections; so `extO` is injective in degree 0.
* `cutUnivIso : cut univ F ≅ F`; `cutRangeIso i F : cut (range i) F ≅ i_* i^* F` for a closed immersion `i`
  (from the EtSheaves cut sequence), hence `hcRangeEquiv : H^n_c(range i, F) ≃+ H^n(Z, i^* F)`.
* The point scheme `Spec κ(y)` of a point `y`: `Spec κ(y) ⟶ Spec κ(y)`'s residue map is an isomorphism and
  `κ(pt) ≅ κ(y)`; for `κ(y)` algebraically closed, `H^(n+1)(Spec κ(y), -) = 0` (`H_ptOf_eq_zero`), so
  `H^(n+1)_c({y}, F) = 0` for every closed point `y` with algebraically closed residue field (`hc_closedPt_eq_zero`).

On `P^1_K` (`K` algebraically closed), with `S = univ` and `O = A^1 = D₊(X₀)` (`S \ O = {∞}`), the excision sequence
gives: `extO : H^m_c(A^1 ⊆ P^1, F) → H^m(P^1, cut univ F)` is bijective for `m ≥ 2`, surjective for `m = 1` and
injective for `m = 0` (`P1.extO_bijective`, `P1.extO_one_surjective`, `extO_zero_injective`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section General

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

theorem isIso_openCutι_of_forall (W : X.Opens) (G : EtSh Λ X) (h : ∀ x : X, x ∈ W) :
    IsIso (openCutι Λ W G) := by
  rw [isIso_iff_stalk]
  intro x
  exact isIso_stalk_openCutι W G (geomPtAt x) (mem_center_geomPtAt (h x))

theorem isIso_quotCutπ_of_forall (V : X.Opens) (G : EtSh Λ X) (h : ∀ x : X, x ∉ V) :
    IsIso (quotCutπ Λ V G) := by
  rw [isIso_iff_stalk]
  intro x
  exact isIso_stalk_quotCutπ V G (geomPtAt x) (not_mem_center_geomPtAt (h x))

theorem mem_cutOpen_of_isClosed {S : Set X} (hS : IsClosed S) (x : X) : x ∈ cutOpen S := by
  show x ∈ interior (coborder S)
  rw [coborder_eq_univ_iff.mpr hS, interior_univ]
  exact Set.mem_univ x

/-- For closed `S`, `cut S F ≅ quotCut (cutCompl S) F`. -/
def cutClosedIso {S : Set X} (hS : IsClosed S) (F : EtSh Λ X) :
    cut Λ S F ≅ quotCut Λ (cutCompl S) F :=
  haveI := isIso_openCutι_of_forall (cutOpen S) (quotCut Λ (cutCompl S) F) (mem_cutOpen_of_isClosed hS)
  (asIso (openCutι Λ (cutOpen S) (quotCut Λ (cutCompl S) F)) :
    openCut Λ (cutOpen S) (quotCut Λ (cutCompl S) F) ≅ quotCut Λ (cutCompl S) F)

/-- **`cut univ F ≅ F`.** -/
def cutUnivIso (F : EtSh Λ X) : cut Λ Set.univ F ≅ F :=
  haveI := isIso_quotCutπ_of_forall (cutCompl (Set.univ : Set X)) F (fun x hx => by
    have h : x ∈ (closure (Set.univ : Set X))ᶜ := hx
    rw [closure_univ] at h
    exact h (Set.mem_univ x))
  cutClosedIso isClosed_univ F ≪≫ (asIso (quotCutπ Λ (cutCompl Set.univ) F)).symm

section Closed

variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

theorem cutCompl_range : cutCompl (Set.range i) = complOpens i := by
  apply TopologicalSpace.Opens.ext
  show (closure (Set.range i))ᶜ = (Set.range i)ᶜ
  rw [i.isClosedEmbedding.isClosed_range.closure_eq]

end Closed

end General

section Point

end Point

section P1

variable (K : Type u) [Field K] [IsAlgClosed K] (Λ : Type u) [CommRing Λ]

omit [IsAlgClosed K] in
theorem P1.isLocallyClosed_univ : IsLocallyClosed (Set.univ : Set (P1 K)) :=
  isClosed_univ.isLocallyClosed

end P1

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_A1Hc =====
section

/-!
# S4-EtCompact, part 29: `H^*_c(A^1, Λ)` inside `P^1` (O8a, file 3)

* `lshResIso j G : j_! j^* G ≅ openCut (range j) G` for any open immersion `j` (stalkwise, via `Abelian.monoLift`).
* `cutOpenIso O F : cut (univ ∩ O) F ≅ openCut O F`.
* `A1.hcEquiv : H^n_c(A^1, Λ) ≃+ H^n_c(univ ∩ A^1 ⊆ P^1, Λ_{P^1})` (the compactification `A1.cpt`).
* The comparison `A1.toP1 n : H^n_c(A^1, Λ) →+ H^n(P^1, Λ)` (extension by zero) is injective for `n = 0`, surjective
  for `n = 1` and bijective for `n ≥ 2` (`K` algebraically closed); `A1.hcEquivP1 : H^(n+2)_c(A^1, Λ) ≃+ H^(n+2)(P^1, Λ)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section OpenIm

end OpenIm

section OpenCut

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

theorem wvSet_bot (O : X.Opens) : wvSet O ⊥ = Set.univ ∩ (O : Set X) := by
  ext x
  rw [mem_wvSet, Set.univ_inter, SetLike.mem_coe]
  simp

/-- `cut (univ ∩ O) F ≅ openCut O F` for an open `O`. -/
def cutOpenIso (O : X.Opens) (F : EtSh Λ X) : cut Λ (Set.univ ∩ (O : Set X)) F ≅ openCut Λ O F :=
  haveI := isIso_quotCutπ_of_forall (⊥ : X.Opens) F (fun x hx => by simp at hx)
  cutIsoCutWV F (wvSet_bot O) ≪≫ (lsh O.ι Λ).mapIso ((res O.ι Λ).mapIso (asIso (quotCutπ Λ ⊥ F)).symm)

end OpenCut

section A1

variable (K : Type u) [Field K] (Λ : Type u) [CommRing Λ]

/-- `j^* Λ_{P^1} ≅ Λ_{A^1}` along the chart. -/
def A1.resUnitIso : (res (chartA1 K) Λ).obj (unitSh Λ (P1 K)) ≅ unitSh Λ (A1 K) :=
  ((pullIsoRes (chartA1 K) Λ).app _).symm ≪≫ pullConst Λ (chartA1 K) (ModuleCat.of Λ Λ)

/-- The sheaf `i_* j_! (cut univ Λ_{A^1})` of the compactification is `cut (univ ∩ A^1) Λ_{P^1}`. -/
def A1.lshIso : (lsh (chartA1 K) Λ).obj (cut Λ Set.univ (unitSh Λ (A1 K))) ≅
    cut Λ (Set.univ ∩ ((chartA1 K).opensRange : Set (P1 K))) (unitSh Λ (P1 K)) :=
  (lsh (chartA1 K) Λ).mapIso (cutUnivIso _ ≪≫ (A1.resUnitIso K Λ).symm) ≪≫
    lshResIso (chartA1 K) _ ≪≫ (cutOpenIso _ _).symm

end A1

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_P1H0 =====
section

/-!
# S4-EtCompact, part 30: `H^0_c(A^1, Λ) = 0` and `H^1_c(A^1, Λ) ≃ H^1(P^1, Λ)` (O8a, file 4)

* `smulEnd r F : F ⟶ F` (multiplication by `r : Λ`); its stalk maps are `r • 𝟙` (`stalk_smulEnd`).
* `exists_lift_unitSh`: if `ρ : A ⟶ B` is epi, `A ≅ Λ_X` and `B` has zero stalks off one point `x0`, every
  `ψ : Λ_X ⟶ B` lifts through `ρ` (stalk at `x0` is cyclic on `1`).
* `resC_zero_surjective`: `H^0_c(S) → H^0_c(S \ O)` is onto when `cut S F ≅ Λ_X` and `S \ O` is at most a point;
  hence `extO` is injective in degree `1` (`extO_one_injective_of`).
* `P1.hcA1_zero_eq_zero`, **`A1.hc_zero_eq_zero`**: `H^0_c(A^1, Λ) = 0` (any field).
* **`A1.hcEquivP1One`**: `H^1_c(A^1, Λ) ≃+ H^1(P^1, Λ)` (`K` algebraically closed).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section Smul

end Smul

section Lift

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}}

/-- **Lifting through an epi with point-supported target**: if `ρ : A ⟶ B` is epi, `Λ_X ≅ A`, and the stalks of
`B` vanish off `x0`, then every `ψ : Λ_X ⟶ B` factors through `ρ`. -/
theorem exists_lift_unitSh {A B : EtSh Λ X} (ρ : A ⟶ B) [Epi ρ] (e : unitSh Λ X ≅ A) (x0 : X)
    (hB : ∀ x : X, x ≠ x0 → IsZero (((geomPtAt x).stalkF Λ).obj B)) (ψ : unitSh Λ X ⟶ B) :
    ∃ f : unitSh Λ X ⟶ A, f ≫ ρ = ψ := by
  have hepi : Epi (((geomPtAt x0).stalkF Λ).map ρ) := inferInstance
  obtain ⟨a', ha'⟩ := (ModuleCat.epi_iff_surjective _).1 hepi ((((geomPtAt x0).stalkF Λ).map ψ).hom (oneAt Λ x0))
  have h2 : (((geomPtAt x0).stalkF Λ).map e.hom).hom ((((geomPtAt x0).stalkF Λ).map e.inv).hom a') = a' := by
    rw [← ModuleCat.comp_apply, ← CategoryTheory.Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id,
      ModuleCat.id_apply]
  refine ⟨smulEnd ((constStalkIso Λ (geomPtAt x0) (ModuleCat.of Λ Λ)).hom.hom
    ((((geomPtAt x0).stalkF Λ).map e.inv).hom a')) _ ≫ e.hom, hom_ext_stalk Λ (fun x => ?_)⟩
  by_cases hx : x = x0
  · rw [hx]
    refine unitSh_stalk_hom_ext Λ x0 ?_
    rw [Functor.map_comp, Functor.map_comp, ModuleCat.comp_apply, ModuleCat.comp_apply, smulEnd_stalk_apply,
      smul_oneAt, h2]
    exact ha'
  · exact (hB x hx).eq_of_tgt _ _

end Lift

section Res

end Res

section P1

end P1

end RamanujanPetersson.EtCompact

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

variable (Λ : Type u) [CommRing Λ]

/-- `ι_P^* (i_* j_! F) ≅ i_{s*} j_{s!} (ι_X^* F)`. -/
def extBC (F : EtSh Λ X) :
    (pull (fibι c.fbar s) Λ).obj ((c.ext Λ).obj F) ≅ ((fibCpt c s).ext Λ).obj ((pull (cptιX c s) Λ).obj F) :=
  closedBC c.i (fibι c.fbar s) ((lsh c.j Λ).obj F) ≪≫
    (push (pullback.snd c.i (fibι c.fbar s)) Λ).mapIso ((lshPullBC Λ c.j (cptιZ c s)).app F)

end Fib

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtCompact_BC =====
section

/-!
# S4-EtCompact, part 13: base change and products of compactifications; `P^1`-bundles (O6)

* `Cpt.baseChange c g : Cpt (pullback.snd f g)`: a compactification `X ⊆ Z ⊆ P → B` of `f` gives
  `X ×_B B' ⊆ Z ×_B B' ⊆ P ×_B B' → B'` (open immersions, closed immersions and proper maps are stable under
  base change).
* `Cpt.prod c₁ c₂ : Cpt (pullback.snd f₁ f₂ ≫ f₂)`: `X₁ ×_B X₂ ⊆ Z₁ ×_B Z₂ ⊆ P₁ ×_B P₂ → B`.
* `A1.cptOver K g : Cpt (pullback.snd (A1.toSpecK K) g)`: the relative affine line `A^1_S ⊆ P^1_S → S` for any
  `g : S ⟶ Spec K` (the `P^1`-bundle compactification used for relative curves; `A^{m+1} → A^m` is the case
  `S = A^m`).
* `Cpt.closedExt c k`, `Cpt.RshriekCl`, `Cpt.HcCl`: for a closed immersion `k : Y ⟶ X`, `R(k ≫ f)_! := R f_! ∘ k_*`
  and `H^n_c(Y, G) := H^n_c(X, k_* G)` (closed subschemes of a compactified `X`, e.g. of `A^n`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ]

/-- Closed immersions are stable under composition (as a `MorphismProperty` instance, found explicitly). -/
instance closedImm_stableComp : MorphismProperty.IsStableUnderComposition (@IsClosedImmersion : MorphismProperty Scheme.{u}) :=
  ⟨fun f g hf hg => @IsClosedImmersion.comp _ _ _ f g hf hg⟩

namespace Cpt

variable {X B : Scheme.{u}} {f : X ⟶ B} (c : Cpt f)

theorem comm' : f = c.j ≫ c.i ≫ c.fbar := c.comm.symm

/-- **Base change of a compactification** along `g : B' ⟶ B`. -/
def baseChange {B' : Scheme.{u}} (g : B' ⟶ B) : Cpt (pullback.snd f g) where
  P := pullback c.fbar g
  Z := pullback (c.i ≫ c.fbar) g
  j := pullback.map f g (c.i ≫ c.fbar) g c.j (𝟙 _) (𝟙 _)
    ((Category.comp_id _).trans c.comm') ((Category.comp_id _).trans (Category.id_comp _).symm)
  i := pullback.map (c.i ≫ c.fbar) g c.fbar g c.i (𝟙 _) (𝟙 _)
    ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans (Category.id_comp _).symm)
  fbar := pullback.snd c.fbar g
  isOpenImmersion_j := MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstance : IsOpenImmersion c.j) (inferInstance : IsOpenImmersion (𝟙 B')) c.comm'
    (Category.id_comp _).symm
  isClosedImmersion_i := MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstance : IsClosedImmersion c.i) (inferInstance : IsClosedImmersion (𝟙 B')) rfl
    (Category.id_comp _).symm
  isProper_fbar := inferInstance
  comm := by
    simp only [pullback.map, Category.comp_id]
    erw [pullback.lift_snd, pullback.lift_snd]

/-- **Product of compactifications** over `B`. -/
def prod {X₂ : Scheme.{u}} {f₂ : X₂ ⟶ B} (c₂ : Cpt f₂) : Cpt (pullback.snd f f₂ ≫ f₂) where
  P := pullback c.fbar c₂.fbar
  Z := pullback (c.i ≫ c.fbar) (c₂.i ≫ c₂.fbar)
  j := pullback.map f f₂ (c.i ≫ c.fbar) (c₂.i ≫ c₂.fbar) c.j c₂.j (𝟙 _)
    ((Category.comp_id _).trans c.comm') ((Category.comp_id _).trans c₂.comm')
  i := pullback.map (c.i ≫ c.fbar) (c₂.i ≫ c₂.fbar) c.fbar c₂.fbar c.i c₂.i (𝟙 _)
    ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans rfl)
  fbar := pullback.snd c.fbar c₂.fbar ≫ c₂.fbar
  isOpenImmersion_j := MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstance : IsOpenImmersion c.j) (inferInstance : IsOpenImmersion c₂.j) c.comm' c₂.comm'
  isClosedImmersion_i := MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstance : IsClosedImmersion c.i) (inferInstance : IsClosedImmersion c₂.i) rfl rfl
  isProper_fbar := inferInstance
  comm := by
    simp only [pullback.map, Category.comp_id]
    erw [pullback.lift_snd_assoc]
    rw [Category.assoc]
    erw [pullback.lift_snd_assoc]
    rw [Category.assoc, c₂.comm]

end Cpt

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtLeray_Shift =====
section

/-!
# S4-EtLeray, part 2: shifting an injective resolution (dimension shift for `R^q`)

For an injective resolution `P` of `N` put `Qc P := coker(N → P⁰)`. Then `P^(•+1)` with the induced
`Qc P ↪ P¹` is an injective resolution `shRes P` of `Qc P`, and for any additive `R`
* **`dsIso P R q`**: `R^(q+1)(Qc P) ≅ R^(q+2) N`.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtLeray

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {N : C} (P : InjectiveResolution N)

/-- The short exact sequence `N → P⁰ → Qc P`. -/
abbrev presQ : ShortComplex C := ShortComplex.mk (P.ι.f 0) (cokernel.π (P.ι.f 0)) (cokernel.condition _)

theorem presQ_shortExact : (presQ P).ShortExact where
  exact := ShortComplex.exact_cokernel (P.ι.f 0)

/-- `Qc P ↪ P¹`. -/
def dQ : Qc P ⟶ P.cocomplex.X 1 := cokernel.desc _ (P.cocomplex.d 0 1) P.ι_f_zero_comp_complex_d

instance mono_dQ : Mono (dQ P) := P.exact₀.mono_cokernelDesc

/-- The shifted complex `P^(•+1)`. -/
def shCx : CochainComplex C ℕ :=
  CochainComplex.of (fun q => P.cocomplex.X (q + 1)) (fun q => P.cocomplex.d (q + 1) (q + 2))
    (fun _ => P.cocomplex.d_comp_d _ _ _)

theorem shCx_d (q : ℕ) : (shCx P).d q (q + 1) = P.cocomplex.d (q + 1) (q + 2) := by
  simp [shCx]

theorem shCx_d' (q : ℕ) : (shCx P).d (q + 1) (q + 2) = P.cocomplex.d (q + 2) (q + 3) :=
  shCx_d P (q + 1)

theorem shCx_d01 : (shCx P).d 0 1 = P.cocomplex.d 1 2 := shCx_d P 0

theorem shCx_exactAt_succ (n : ℕ) : (shCx P).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)]
  refine (ShortComplex.exact_iff_of_iso ?_).2 (P.exact_succ (n + 1))
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans ((shCx_d P n).symm.trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans ((shCx_d' P n).symm.trans (Category.comp_id _).symm))

end RamanujanPetersson.EtLeray

end

end

-- ===== S4.Def_RP_EtLeray_Low =====
section

/-!
# S4-EtLeray, part 3: `R¹ N` as a cokernel, and the low-degree consequences

`P` an injective resolution of `N`, `R` additive and left exact. With `Rπ := R(P⁰ → Qc P)`:
* **`r1Iso P R`**: `R¹ N ≅ coker(Rπ)` (via left homology data of `R P⁰ → R P¹ → R P²` with cycles `R(Qc P)`);
* `baseSC`: `0 → im(Rπ) → R(Qc P) → coker(Rπ) → 0` short exact;
* `imSC`: `0 → R N → R P⁰ → im(Rπ) → 0` short exact;
* **`presQ_map_shortExact`**: `R¹ N = 0` ⇒ `R(N → P⁰ → Qc P)` short exact;
* `injective_im`, **`injective_RQc`**: `R N` injective ⇒ `im(Rπ)` injective, and with `R¹ N = 0`, `R(Qc P)` injective.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtLeray

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
variable [HasInjectiveResolutions C] {N : C} (P : InjectiveResolution N) (R : C ⥤ D) [R.Additive]
  [PreservesFiniteLimits R]

/-- `R(dQ) : R(Qc P) → R(P¹)`, typed into `S01`. -/
def RdQ : R.obj (Qc P) ⟶ (S01 P R).X₂ := R.map (dQ P)

/-- `Rπ : R P⁰ → R(Qc P)`. -/
abbrev Rπ : R.obj (P.cocomplex.X 0) ⟶ R.obj (Qc P) := R.map (cokernel.π (P.ι.f 0))

theorem presQ_map_exact : ((presQ P).map R).Exact :=
  (presQ_shortExact P).exact.map_of_mono_of_preservesKernel R inferInstance inferInstance

/-- `((presQ P).map R).X₁ = R N` is injective when `R N` is. -/
theorem injective_presQR_X₁ [Injective (R.obj N)] : Injective ((presQ P).map R).X₁ := by
  change Injective (R.obj N); infer_instance

end RamanujanPetersson.EtLeray

end

end

-- ===== S4.Def_RP_EtLeray_BCo =====
section

/-!
# S4-EtLeray, part 10: base change along arbitrary pullback squares

For a pullback square `IsPullback a b f g` (`a ≫ f = b ≫ g`):
* **`pullPushSq`** (`f` a closed immersion): `g^* f_* M ≅ b_* a^* M`;
* **`pullLshSq`** (`f` étale): `g^* f_! F ≅ b_! a^* F`;
* **`pullRDerSq`** (`g` étale): `g^* (R^q f_* Y) ≅ R^q b_* (a^* Y)`.
Helpers: `pushPullIso`/`lshPullIso` (`e_* e^* ≅ 𝟭`, `e_! e^* ≅ 𝟭` for an isomorphism `e`), `lshCompIso`.
-/

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace RamanujanPetersson.EtLeray

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC

universe u

variable {Λ : Type u} [CommRing Λ]

section Iso

variable {W W' : Scheme.{u}} (e : W ⟶ W') [IsIso e]

/-- `e_! e^* X ≅ X` for an isomorphism `e`. -/
def lshPullIso (X : EtSh Λ W') : (lsh e Λ).obj ((pull e Λ).obj X) ≅ X :=
  haveI : (pull e Λ).IsEquivalence := (pullAdj e Λ).isEquivalence_left_of_isEquivalence_right
  asIso ((lshPullAdj e Λ).counit.app X)

end Iso

/-- `(a ≫ b)_! ≅ a_! ⋙ b_!`. -/
def lshCompIso {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) [Etale a] [Etale b] :
    lsh (a ≫ b) Λ ≅ lsh a Λ ⋙ lsh b Λ :=
  (lshPullAdj (a ≫ b) Λ).leftAdjointUniq
    (((lshPullAdj a Λ).comp (lshPullAdj b Λ)).ofNatIsoRight (pullCompIso Λ a b).symm)

/-- `f_* ≅ f'_*` for `f = f'`. -/
def pushCongr {A B : Scheme.{u}} {f f' : A ⟶ B} (h : f = f') : push f Λ ≅ push f' Λ :=
  eqToIso (by rw [h])

/-- `f_! ≅ f'_!` for `f = f'`. -/
def lshCongr {A B : Scheme.{u}} {f f' : A ⟶ B} [Etale f] [Etale f'] (h : f = f') : lsh f Λ ≅ lsh f' Λ :=
  (lshPullAdj f Λ).leftAdjointUniq ((lshPullAdj f' Λ).ofNatIsoRight (pullCongr Λ h).symm)

/-- **Closed base change for a pullback square**: `g^* f_* M ≅ b_* a^* M`. -/
def pullPushSq {Z P P' W : Scheme.{u}} {f : Z ⟶ P} [IsClosedImmersion f] {g : P' ⟶ P} {a : W ⟶ Z}
    {b : W ⟶ P'} (sq : IsPullback a b f g) (M : EtSh Λ Z) :
    (pull g Λ).obj ((push f Λ).obj M) ≅ (push b Λ).obj ((pull a Λ).obj M) :=
  closedBC f g M ≪≫
    (push (pullback.snd f g) Λ).mapIso (pushPullIso sq.isoPullback.hom _).symm ≪≫
    (pushCompIso Λ sq.isoPullback.hom (pullback.snd f g)).app _ ≪≫
    (pushCongr sq.isoPullback_hom_snd).app _ ≪≫
    (push b Λ).mapIso ((pullCompIso Λ sq.isoPullback.hom (pullback.fst f g)).symm.app M ≪≫
      (pullCongr Λ sq.isoPullback_hom_fst).app M)

/-- **`f_!` base change for a pullback square**: `g^* f_! F ≅ b_! a^* F` (`f` étale). -/
def pullLshSq {U X V W : Scheme.{u}} {f : U ⟶ X} [Etale f] {g : V ⟶ X} {a : W ⟶ U} {b : W ⟶ V} [Etale b]
    (sq : IsPullback a b f g) (F : EtSh Λ U) :
    (pull g Λ).obj ((lsh f Λ).obj F) ≅ (lsh b Λ).obj ((pull a Λ).obj F) :=
  (lshPullBC Λ f g).app F ≪≫
    (lsh (pullback.snd f g) Λ).mapIso (lshPullIso sq.isoPullback.hom _).symm ≪≫
    (lshCompIso sq.isoPullback.hom (pullback.snd f g)).symm.app _ ≪≫
    (lshCongr sq.isoPullback_hom_snd).app _ ≪≫
    (lsh b Λ).mapIso ((pullCompIso Λ sq.isoPullback.hom (pullback.fst f g)).symm.app F ≪≫
      (pullCongr Λ sq.isoPullback_hom_fst).app F)

end RamanujanPetersson.EtLeray

end

end

-- ===== S4.Def_RP_EtLeray_Sq =====
section

/-!
# S4-EtLeray, part 11: the pullback squares relating `c0.prod d` and `c0.baseChange g`

`c0 : Cpt f0` (`f0 : X0 ⟶ S`), `d : Cpt g` (`g : Y ⟶ S`), `zd := d.i ≫ d.fbar`, `z0 := c0.i ≫ c0.fbar`.
The maps of `c0.prod d` and `c0.baseChange g` are named explicitly (`prodJ`, `prodI`, `bcJ`, `bcI`; they are
definitionally the structure fields), together with
* `mapJ d p : A ×_S Y ⟶ A ×_S Zd` (induced by `d.j`), **`isPullback_mapJ`**: it is the base change of `d.j`;
* `iP c0 d : Z0 ×_S Zd ⟶ P0 ×_S Zd`, `iD c0 d : P0 ×_S Zd ⟶ P0 ×_S Pd`, **`iP_comp`**: `iP ≫ iD = prodI`;
* **`lsqP`**, **`lsqZ`**, **`lsqX`**: the squares `bc.P → P0 ×_S Zd` over `d.j`, `bc.Z → Z0 ×_S Zd` over
  `bc.P → P0 ×_S Zd`, `X → X` over `bc.Z → Z0 ×_S Zd` are pullbacks.
-/

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace RamanujanPetersson.EtLeray

open RamanujanPetersson.EtCompact

universe u

variable {S X0 Y : Scheme.{u}} {f0 : X0 ⟶ S} {g : Y ⟶ S} (c0 : Cpt f0) (d : Cpt g)

/-- `A ×_S Y ⟶ A ×_S Zd` induced by `d.j`. -/
def mapJ {A : Scheme.{u}} (p : A ⟶ S) : pullback p g ⟶ pullback p (d.i ≫ d.fbar) :=
  pullback.map p g p (d.i ≫ d.fbar) (𝟙 A) d.j (𝟙 S) ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans d.comm')

@[reassoc]
theorem mapJ_fst {A : Scheme.{u}} (p : A ⟶ S) :
    mapJ d p ≫ pullback.fst p (d.i ≫ d.fbar) = pullback.fst p g :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
theorem mapJ_snd {A : Scheme.{u}} (p : A ⟶ S) :
    mapJ d p ≫ pullback.snd p (d.i ≫ d.fbar) = pullback.snd p g ≫ d.j :=
  pullback.lift_snd _ _ _

theorem isPullback_mapJ {A : Scheme.{u}} (p : A ⟶ S) :
    IsPullback (mapJ d p) (pullback.snd p g) (pullback.snd p (d.i ≫ d.fbar)) d.j := by
  refine IsPullback.of_right (h₁₂ := pullback.fst p (d.i ≫ d.fbar)) (h₂₂ := d.i ≫ d.fbar) (v₁₃ := p) ?_
    (mapJ_snd d p) (IsPullback.of_hasPullback _ _)
  rw [mapJ_fst, ← d.comm']
  exact IsPullback.of_hasPullback p g

instance isOpenImmersion_mapJ {A : Scheme.{u}} (p : A ⟶ S) : IsOpenImmersion (mapJ d p) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_mapJ d p).flip inferInstance

/-- `(c0.baseChange g).j`, explicitly. -/
def bcJ : pullback f0 g ⟶ pullback (c0.i ≫ c0.fbar) g :=
  pullback.map f0 g (c0.i ≫ c0.fbar) g c0.j (𝟙 _) (𝟙 _)
    ((Category.comp_id _).trans c0.comm') ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- `(c0.baseChange g).i`, explicitly. -/
def bcI : pullback (c0.i ≫ c0.fbar) g ⟶ pullback c0.fbar g :=
  pullback.map (c0.i ≫ c0.fbar) g c0.fbar g c0.i (𝟙 _) (𝟙 _)
    (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)

theorem bcJ_eq : bcJ c0 (g := g) = (c0.baseChange g).j := rfl
theorem bcI_eq : bcI c0 (g := g) = (c0.baseChange g).i := rfl

instance : IsOpenImmersion (bcJ c0 (g := g)) := (c0.baseChange g).isOpenImmersion_j
instance : IsClosedImmersion (bcI c0 (g := g)) := (c0.baseChange g).isClosedImmersion_i

@[reassoc]
theorem bcJ_fst : bcJ c0 (g := g) ≫ pullback.fst (c0.i ≫ c0.fbar) g = pullback.fst f0 g ≫ c0.j :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem bcJ_snd : bcJ c0 (g := g) ≫ pullback.snd (c0.i ≫ c0.fbar) g = pullback.snd f0 g :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

@[reassoc]
theorem bcI_fst : bcI c0 (g := g) ≫ pullback.fst c0.fbar g = pullback.fst (c0.i ≫ c0.fbar) g ≫ c0.i :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem bcI_snd : bcI c0 (g := g) ≫ pullback.snd c0.fbar g = pullback.snd (c0.i ≫ c0.fbar) g :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- `(c0.prod d).j`, explicitly. -/
def prodJ : pullback f0 g ⟶ pullback (c0.i ≫ c0.fbar) (d.i ≫ d.fbar) :=
  pullback.map f0 g (c0.i ≫ c0.fbar) (d.i ≫ d.fbar) c0.j d.j (𝟙 _)
    ((Category.comp_id _).trans c0.comm') ((Category.comp_id _).trans d.comm')

/-- `(c0.prod d).i`, explicitly. -/
def prodI : pullback (c0.i ≫ c0.fbar) (d.i ≫ d.fbar) ⟶ pullback c0.fbar d.fbar :=
  pullback.map (c0.i ≫ c0.fbar) (d.i ≫ d.fbar) c0.fbar d.fbar c0.i d.i (𝟙 _)
    (Category.comp_id _) (Category.comp_id _)

theorem prodJ_eq : prodJ c0 d = (c0.prod d).j := rfl
theorem prodI_eq : prodI c0 d = (c0.prod d).i := rfl

instance : IsOpenImmersion (prodJ c0 d) := (c0.prod d).isOpenImmersion_j
instance : IsClosedImmersion (prodI c0 d) := (c0.prod d).isClosedImmersion_i

@[reassoc]
theorem prodJ_fst : prodJ c0 d ≫ pullback.fst (c0.i ≫ c0.fbar) (d.i ≫ d.fbar) = pullback.fst f0 g ≫ c0.j :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem prodJ_snd : prodJ c0 d ≫ pullback.snd (c0.i ≫ c0.fbar) (d.i ≫ d.fbar) = pullback.snd f0 g ≫ d.j :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem prodI_fst : prodI c0 d ≫ pullback.fst c0.fbar d.fbar = pullback.fst (c0.i ≫ c0.fbar) (d.i ≫ d.fbar) ≫ c0.i :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem prodI_snd : prodI c0 d ≫ pullback.snd c0.fbar d.fbar = pullback.snd (c0.i ≫ c0.fbar) (d.i ≫ d.fbar) ≫ d.i :=
  pullback.lift_snd _ _ _

/-- `Z0 ×_S Zd ⟶ P0 ×_S Zd` induced by `c0.i`. -/
def iP : pullback (c0.i ≫ c0.fbar) (d.i ≫ d.fbar) ⟶ pullback c0.fbar (d.i ≫ d.fbar) :=
  pullback.map (c0.i ≫ c0.fbar) (d.i ≫ d.fbar) c0.fbar (d.i ≫ d.fbar) c0.i (𝟙 _) (𝟙 S)
    (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)

@[reassoc]
theorem iP_fst : iP c0 d ≫ pullback.fst c0.fbar (d.i ≫ d.fbar) = pullback.fst (c0.i ≫ c0.fbar) (d.i ≫ d.fbar) ≫ c0.i :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem iP_snd : iP c0 d ≫ pullback.snd c0.fbar (d.i ≫ d.fbar) = pullback.snd (c0.i ≫ c0.fbar) (d.i ≫ d.fbar) :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- `P0 ×_S Zd ⟶ P0 ×_S Pd` induced by `d.i` (a closed immersion). -/
def iD : pullback c0.fbar (d.i ≫ d.fbar) ⟶ pullback c0.fbar d.fbar :=
  pullback.map c0.fbar (d.i ≫ d.fbar) c0.fbar d.fbar (𝟙 _) d.i (𝟙 S)
    ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _)

@[reassoc]
theorem iD_fst : iD c0 d ≫ pullback.fst c0.fbar d.fbar = pullback.fst c0.fbar (d.i ≫ d.fbar) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
theorem iD_snd : iD c0 d ≫ pullback.snd c0.fbar d.fbar = pullback.snd c0.fbar (d.i ≫ d.fbar) ≫ d.i :=
  pullback.lift_snd _ _ _

/-- `c0.prod d`'s closed immersion factors through `iP`. -/
theorem iP_comp : iP c0 d ≫ iD c0 d = prodI c0 d := by
  apply pullback.hom_ext
  · simp only [Category.assoc, iD_fst, iP_fst, prodI_fst]
  · simp only [Category.assoc, iD_snd, iP_snd_assoc, prodI_snd]

/-- `bc.P → P0 ×_S Zd` over `d.j`. -/
theorem lsqP : IsPullback (mapJ d c0.fbar) (pullback.snd c0.fbar g) (pullback.snd c0.fbar (d.i ≫ d.fbar)) d.j :=
  isPullback_mapJ d c0.fbar

/-- `bc.Z → Z0 ×_S Zd` over `bc.P → P0 ×_S Zd`. -/
theorem lsqZ : IsPullback (mapJ d (c0.i ≫ c0.fbar)) (bcI c0 (g := g)) (iP c0 d) (mapJ d c0.fbar) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd c0.fbar g) (v₂₂ := pullback.snd c0.fbar (d.i ≫ d.fbar))
    (h₃₁ := d.j) ?_ ?_ (lsqP c0 d)
  · rw [bcI_snd, iP_snd]
    exact isPullback_mapJ d (c0.i ≫ c0.fbar)
  · apply pullback.hom_ext
    · simp only [Category.assoc, iP_fst, mapJ_fst_assoc, mapJ_fst, bcI_fst]
    · simp only [Category.assoc, iP_snd, mapJ_snd, bcI_snd_assoc]

/-- `X → X` over `bc.Z → Z0 ×_S Zd`. -/
theorem lsqX : IsPullback (𝟙 (pullback f0 g)) (bcJ c0 (g := g)) (prodJ c0 d) (mapJ d (c0.i ≫ c0.fbar)) := by
  refine IsPullback.of_horiz_isIso_mono ⟨?_⟩
  apply pullback.hom_ext
  · simp only [Category.id_comp, Category.assoc, prodJ_fst, mapJ_fst, bcJ_fst]
  · simp only [Category.id_comp, Category.assoc, prodJ_snd, mapJ_snd, bcJ_snd_assoc]

end RamanujanPetersson.EtLeray

end

end

-- ===== S4.Def_RP_EtLeray_Bnd =====
section

/-!
# S4-EtLeray, part 9: boundary vanishing for compact supports

* `isZero_lsh_of_isEmpty`: `j_! F = 0` when the source of `j` is empty;
* **`isZero_pull_push_lsh`**: `ι^* i_* j_! F = 0` when no point of `U` meets the image of `ι` in `P`;
* **`isZero_stalk_rder`**: if proper base change holds at `s` (`PBCGood`) and `N` restricts to zero on the fibre
  over `s`, then `(R^q g_* N)_s = 0`;
* **`isIso_counit_of_closed`**: over a scheme of finite type over a field, if the stalks of `M` at the closed
  points off an open `U` vanish, then `j_! j^* M ⟶ M` is an isomorphism.
-/

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace RamanujanPetersson.EtLeray

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC

universe u

variable {Λ : Type u} [CommRing Λ]

/-- `j_! F = 0` when the source of `j` is empty. -/
theorem isZero_lsh_of_isEmpty {U X : Scheme.{u}} [IsEmpty U] (j : U ⟶ X) [IsOpenImmersion j]
    (F : EtSh Λ U) : IsZero ((lsh j Λ).obj F) :=
  (isZero_iff_stalk (F := (lsh j Λ).obj F)).2 fun x =>
    lsh_stalk_isZero (j := j) (Λ := Λ) (geomPtAt x) (fun ⟨a, _⟩ => isEmptyElim a) F

/-- **`ι^* i_* j_! F = 0`** when no point of `U` meets the image of `ι`. -/
theorem isZero_pull_push_lsh {U Z P P' : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i] (j : U ⟶ Z)
    [IsOpenImmersion j] (ι : P' ⟶ P) (F : EtSh Λ U) (h : ∀ (a : U) (b : P'), i (j a) ≠ ι b) :
    IsZero ((pull ι Λ).obj ((push i Λ).obj ((lsh j Λ).obj F))) := by
  have hE : IsEmpty ((pullback j (pullback.fst i ι) : Scheme.{u})) := by
    refine ⟨fun p => h (pullback.fst j (pullback.fst i ι) p)
      (pullback.snd i ι (pullback.snd j (pullback.fst i ι) p)) ?_⟩
    have e1 := congrArg (fun φ : pullback j (pullback.fst i ι) ⟶ Z => φ p)
      (pullback.condition (f := j) (g := pullback.fst i ι))
    have e2 := congrArg (fun φ : pullback i ι ⟶ P => φ (pullback.snd j (pullback.fst i ι) p))
      (pullback.condition (f := i) (g := ι))
    simp only [Scheme.Hom.comp_apply] at e1 e2
    rw [e1, e2]
  refine IsZero.of_iso ?_ (closedBC i ι ((lsh j Λ).obj F))
  refine Functor.map_isZero _ (IsZero.of_iso ?_ ((lshPullBC Λ j (pullback.fst i ι)).app F))
  exact isZero_lsh_of_isEmpty _ _

end RamanujanPetersson.EtLeray

end

end

-- ===== S4.Def_RP_EtLeray_Key =====
section

/-!
# S4-EtLeray, part 12: the key isomorphism `R^q π_* (prod.ext F) ≅ d.ext (R^q f_! F)`

`c0 : Cpt f0`, `d : Cpt g`, `X := X0 ×_S Y`, `π := P0 ×_S Pd ⟶ Pd`, `π' := P0 ×_S Zd ⟶ Zd` (`prZ`),
`N' := iP_* prodJ_! F` (`midSh`), `M_q := R^q π'_* N'` (`midR`), `bc := c0.baseChange g`.
* `rderIso`: `R^n F ≅ R^n G` for `F ≅ G`; `pullIdIso`: `(𝟙 X)^* ≅ 𝟭`;
* **`closedKeyIso`** (closed part): `R^q π_* (prod.ext F) ≅ d.i_* M_q`;
* **`openKeyIso`** (base change): `d.j^* M_q ≅ R^q f_! F`;
* **`isIso_counit_midR`** (boundary): `d.j_! d.j^* M_q ≅ M_q` when `Zd` is of finite type over a field and
  proper base change holds for `π'` at the closed points of `Zd` off `Y`;
* **`keyIso`**: `R^q π_* (prod.ext F) ≅ d.ext (R^q f_! F)`.
-/

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace RamanujanPetersson.EtLeray

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC

universe u

/-- `R^n F ≅ R^n G` for an isomorphism `F ≅ G` of additive functors. -/
def rderIso {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] [HasInjectiveResolutions C]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G) (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived e.hom n
  inv := NatTrans.rightDerived e.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

variable {Λ : Type u} [CommRing Λ]

variable (Λ) in
/-- `(𝟙 X)^* ≅ 𝟭`. -/
def pullIdIso (X : Scheme.{u}) : pull (𝟙 X) Λ ≅ 𝟭 (EtSh Λ X) :=
  (pullAdj (𝟙 X) Λ).leftAdjointUniq (Adjunction.id.ofNatIsoRight (EtPBC.EtMV.pushId Λ X).symm)

variable {S X0 Y : Scheme.{u}} {f0 : X0 ⟶ S} {g : Y ⟶ S} (c0 : Cpt f0) (d : Cpt g)

instance isClosedImmersion_iP : IsClosedImmersion (iP c0 d) :=
  (c0.baseChange (d.i ≫ d.fbar)).isClosedImmersion_i

instance isClosedImmersion_iD : IsClosedImmersion (iD c0 d) :=
  MorphismProperty.pullbackMap (P := @IsClosedImmersion) (f := c0.fbar) (g := d.i ≫ d.fbar) (f' := c0.fbar)
    (g' := d.fbar) (i₁ := 𝟙 c0.P) (i₂ := d.i) inferInstance inferInstance (Category.id_comp _).symm rfl

/-- `π' : P0 ×_S Zd ⟶ Zd`. -/
abbrev prZ : pullback c0.fbar (d.i ≫ d.fbar) ⟶ d.Z := pullback.snd c0.fbar (d.i ≫ d.fbar)

/-- `N' := iP_* prodJ_! F` on `P0 ×_S Zd`. -/
abbrev midSh (F : EtSh Λ (pullback f0 g)) : EtSh Λ (pullback c0.fbar (d.i ≫ d.fbar)) :=
  (push (iP c0 d) Λ).obj ((lsh (prodJ c0 d) Λ).obj F)

/-- `M_q := R^q π'_* N'` on `Zd`. -/
abbrev midR (q : ℕ) (F : EtSh Λ (pullback f0 g)) : EtSh Λ d.Z :=
  ((push (prZ c0 d) Λ).rightDerived q).obj (midSh c0 d F)

end RamanujanPetersson.EtLeray

end

end

-- ===== S4.Def_RP_EtPBC_B_RshA =====
section

/-!
# S4-EtPBC-B, D2: `P4` for the relative affine line and the coordinate projections of `A^n`

* `rshriek_stalk_A1`: `(R^q f_! F)_s ≃+ H^q_c(X_s, F|X_s)` for `f : A^1_S ⟶ S` with its compactification
  `A1.cptOver K gS` (`P^1_S`), at `K`-rational `s` (`good_qV`);
* instances `IsNoetherian (An K n)`, `LocallyOfFiniteType (An.toSpecK K n)`;
* **`rshriek_stalk_An`**: the same for the coordinate projection `A^(n+1) ⟶ A^n` (`An.projCpt`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

section A1

end A1

section An

variable (K : Type) [Field K]

instance locallyOfFiniteType_A1_toSpecK : LocallyOfFiniteType (A1.toSpecK K) := by
  have h : (algebraMap K (Polynomial K)).FiniteType := RingHom.finiteType_algebraMap.mpr inferInstance
  rw [Polynomial.algebraMap_eq] at h
  exact HasRingHomProperty.Spec_iff.mpr h

end An

section AnProj

end AnProj

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtLeray_RelA =====
section

/-!
# S4-EtLeray, part 15: relative one-row Grothendieck, acyclic case and row `1`

`F₁ : C ⥤ D` additive, left exact, preserving injectives; `F₂ : D ⥤ E` additive, left exact.
* `rightDerived_additive`: `R^n F` is additive;
* `mapRes P hN`: for `F₁`-acyclic `N`, `F₁ P` is an injective resolution of `F₁ N`;
* **`acycIso`**: `F₁`-acyclic `N` ⇒ `R^m(F₁ ⋙ F₂) N ≅ R^m F₂ (F₁ N)`;
* `isIso_rder_g`: `R^(m+1) F₂` inverts the epi of a short exact sequence with injective kernel;
* **`row1Iso`**: `F₁ N` injective, `R^q F₁ N = 0` for `q ≥ 2` ⇒ `R^(m+1)(F₁ ⋙ F₂) N ≅ R^m F₂ (R¹ F₁ N)`.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtLeray

universe v u v' u' v'' u''

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable {E : Type u''} [Category.{v''} E] [Abelian E]

/-- Right derived functors are additive. -/
instance rightDerived_additive [HasInjectiveResolutions C] (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.rightDerived n).Additive where
  map_add {X Y f g} := by
    rw [F.rightDerived_map_eq n (f + g) (P := injectiveResolution X) (Q := injectiveResolution Y)
        (InjectiveResolution.desc f _ _ + InjectiveResolution.desc g _ _)
        (by rw [Preadditive.comp_add, InjectiveResolution.desc_commutes,
          InjectiveResolution.desc_commutes, (CochainComplex.single₀ C).map_add, Preadditive.add_comp]),
      F.rightDerived_map_eq n f (InjectiveResolution.desc f _ _) (InjectiveResolution.desc_commutes f _ _),
      F.rightDerived_map_eq n g (InjectiveResolution.desc g _ _) (InjectiveResolution.desc_commutes g _ _),
      (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map_add,
      Preadditive.add_comp, Preadditive.comp_add]

section MapRes

variable [HasInjectiveResolutions C]
variable (F1 : C ⥤ D) [F1.Additive] [PreservesFiniteLimits F1] [F1.PreservesInjectiveObjects]
variable {N : C} (P : InjectiveResolution N)

omit [HasInjectiveResolutions C] [PreservesFiniteLimits F1] [F1.PreservesInjectiveObjects] in
theorem mapRes_ι_d : F1.map (P.ι.f 0) ≫ ((F1.mapHomologicalComplex _).obj P.cocomplex).d 0 1 = 0 :=
  (F1.map_comp (P.ι.f 0) (P.cocomplex.d 0 1)).symm.trans
    ((congrArg F1.map P.ι_f_zero_comp_complex_d).trans (F1.map_zero _ _))

set_option backward.isDefEq.respectTransparency false in
theorem mapRes_ι_f0 : ((CochainComplex.fromSingle₀Equiv ((F1.mapHomologicalComplex _).obj P.cocomplex)
    (F1.obj N)).symm ⟨F1.map (P.ι.f 0), mapRes_ι_d F1 P⟩).f 0 = F1.map (P.ι.f 0) :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

end MapRes

variable [HasInjectiveResolutions C] [HasInjectiveResolutions D]
variable (F1 : C ⥤ D) [F1.Additive] [PreservesFiniteLimits F1] [F1.PreservesInjectiveObjects]
variable (F2 : D ⥤ E) [F2.Additive] [PreservesFiniteLimits F2]

omit [PreservesFiniteLimits F2] in
/-- `R^(m+1) F₂` inverts `S.g` for a short exact `S` with `S.X₁` injective. -/
theorem isIso_rder_g (S : ShortComplex D) (hS : S.ShortExact) [Injective S.X₁] (m : ℕ) :
    IsIso ((F2.rightDerived (m + 1)).map S.g) :=
  ((hS.splittingOfInjective.map (F2.rightDerived (m + 1))).shortExact.isIso_g_iff).2
    (F2.isZero_rightDerived_obj_injective_succ m S.X₁)

end RamanujanPetersson.EtLeray

end

end

-- ===== S4.Def_RP_EtLin_Gen =====
section

/-!
# S4-EtLin, Gen: generic Λ-linearity (adjoints, homology, right derived functors, Ext upgrade lemmas)

* `leftAdjoint_linear` / `rightAdjoint_linear`: an adjoint of a linear functor is linear;
* `homologyMap_smul'`, instance `homologyFunctor_linear'` (`HomologicalComplex.homologyFunctor` is linear);
* instance **`rightDerived_linear`**: `R^n F` is `R`-linear for a linear additive `F`;
* **upgrade lemmas** `ext_map_smul`, `ext_map_smul_nat`, `ext_toMod_smul`, `mod_toExt_smul`: an additive map out
  of `Ext A N n` (or out of `S.obj N` for a linear `S : C ⥤ ModuleCat R`) that is natural in `N` is `R`-linear
  (`Ext.smul_eq_comp_mk₀`); `extLinearMap`, `extLinearEquiv` package them.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtLin

universe w w' v u v' u'

section Adj

variable {R : Type*} [Semiring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear R D]

/-- **A left adjoint of a linear functor is linear.** -/
theorem leftAdjoint_linear {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G) [G.Linear R] : L.Linear R := by
  rw [Functor.linear_iff]
  intro X r
  apply (adj.homEquiv X (L.obj X)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.unit_naturality, Functor.map_smul,
    CategoryTheory.Functor.map_id]
  simp

end Adj

section Homology

variable {R : Type*} [Semiring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {ι : Type*} {c : ComplexShape ι}

theorem homologyMap_smul' {K L : HomologicalComplex C c} (r : R) (φ : K ⟶ L) (i : ι) [K.HasHomology i]
    [L.HasHomology i] : HomologicalComplex.homologyMap (r • φ) i = r • HomologicalComplex.homologyMap φ i :=
  ShortComplex.homologyMap_smul ((HomologicalComplex.shortComplexFunctor C c i).map φ) r

instance homologyFunctor_linear' [CategoryWithHomology C] (i : ι) :
    (HomologicalComplex.homologyFunctor C c i).Linear R where
  map_smul f r := homologyMap_smul' r f i

end Homology

section RDer

variable {R : Type*} [Semiring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [Linear R D]

theorem conj_smul_id {X Y : D} (e : X ≅ Y) (r : R) : e.hom ≫ (r • 𝟙 Y) ≫ e.inv = r • 𝟙 X := by
  simp

/-- **Right derived functors of a linear functor are linear.** -/
instance rightDerived_linear [HasInjectiveResolutions C] (F : C ⥤ D) [F.Additive] [F.Linear R] (n : ℕ) :
    (F.rightDerived n).Linear R := by
  rw [Functor.linear_iff]
  intro X r
  have w : (injectiveResolution X).ι ≫ (r • 𝟙 (injectiveResolution X).cocomplex) =
      (CochainComplex.single₀ C).map (r • 𝟙 X) ≫ (injectiveResolution X).ι := by
    apply HomologicalComplex.from_single_hom_ext
    simp only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero, HomologicalComplex.smul_f_apply,
      Linear.comp_smul, Category.comp_id]
    erw [Linear.smul_comp, Category.id_comp]
  rw [F.rightDerived_map_eq n (r • 𝟙 X) _ w, Functor.map_smul, CategoryTheory.Functor.map_id]
  exact conj_smul_id _ r

end RDer

section ExtUp

end ExtUp

section ExtMod

end ExtMod

section ExtPack

end ExtPack

end RamanujanPetersson.EtLin

end

end

-- ===== S4.Def_RP_EtLin_ExtL =====
section

/-!
# S4-EtLin, ExtL: `Λ`-linear versions of the basic `Ext` / `H` maps

Generic (any `Λ`-linear abelian category, `HasExt` implicit): `extIsoLeftL`, `extIsoRightL`, `extAdjMap_smul`,
`extAdjEquivL` (for `L ⊣ R` with `R` linear). Étale: `HmapL`, `HisoL`. Each `…L` has `…L_apply` (`rfl`) to the
additive original.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtLin

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe w v u v' u'

section Gen

variable {Λ : Type*} [Ring Λ] {C : Type u} [Category.{v} C] [Abelian C] [Linear Λ C] {hC : HasExt.{w} C}

variable (Λ) in
/-- `extIsoRight` is `Λ`-linear. -/
def extIsoRightL (A : C) {B B' : C} (e : B ≅ B') (n : ℕ) : Ext A B n ≃ₗ[Λ] Ext A B' n :=
  (extIsoRight A e n).toLinearEquiv (fun r x => Ext.smul_comp x _ (add_zero n) r)

theorem extIsoRightL_apply (A : C) {B B' : C} (e : B ≅ B') (n : ℕ) (x : Ext A B n) :
    extIsoRightL Λ A e n x = extIsoRight A e n x :=
  rfl

end Gen

section Adj

variable {Λ : Type*} [Ring Λ] {C : Type u} [Category.{v} C] [Abelian C] [Linear Λ C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [Linear Λ D] {hC : HasExt.{w} C} {hD : HasExt.{w} D}
  {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [G.Linear Λ]

theorem extAdjMap_smul (A : C) (B : D) (n : ℕ) (r : Λ) (e : Ext (L.obj A) B n) :
    extAdjMap adj A B n (r • e) = r • extAdjMap adj A B n e := by
  rw [extAdjMap_apply, extAdjMap_apply, Functor.mapExactFunctor_smul, Ext.comp_smul]

variable (Λ) in
/-- **`Ext (L A) B n ≃ₗ[Λ] Ext A (G B) n`** for `L ⊣ G` with `G` exact and linear. -/
def extAdjEquivL [EnoughInjectives D] [L.PreservesMonomorphisms] (A : C) (B : D) (n : ℕ) :
    Ext (L.obj A) B n ≃ₗ[Λ] Ext A (G.obj B) n :=
  (extAdjEquiv adj A B n).toLinearEquiv (fun r e => extAdjMap_smul adj A B n r e)

theorem extAdjEquivL_apply [EnoughInjectives D] [L.PreservesMonomorphisms] (A : C) (B : D) (n : ℕ)
    (e : Ext (L.obj A) B n) : extAdjEquivL Λ adj A B n e = extAdjEquiv adj A B n e :=
  rfl

end Adj

section Et

end Et

end RamanujanPetersson.EtLin

end

end

-- ===== S4.Def_RP_EtLin_Fun =====
section

/-!
# S4-EtLin, Fun: the named functors on étale sheaves are `Λ`-linear

`Functor.Linear Λ` for `push`, `res` (pushforwards along continuous functors), `pull`, `lsh` (left adjoints),
the stalk functors `stalkF`, `quotFunctor`, `cutWVFunctor`, `cutFunctor`, `Cpt.ext` and `Cpt.Rshriek`
(`R^n` of a linear functor, `EtLin.rightDerived_linear`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtLin

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe w v u v' u' v'' u''

section Site

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (G : C ⥤ D)
  {A : Type u''} [Category.{v''} A] [Preadditive A] {R : Type*} [Semiring R] [Linear R A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [G.IsContinuous J K]

/-- **Pushforward of sheaves along a continuous functor is linear.** -/
instance sheafPushforwardContinuous_linear : (G.sheafPushforwardContinuous A J K).Linear R where
  map_smul _ _ := rfl

end Site

variable {Λ : Type u} [CommRing Λ]

instance push_linear {X Y : Scheme.{u}} (f : X ⟶ Y) : (push f Λ).Linear Λ :=
  sheafPushforwardContinuous_linear _ _ _

instance res_linear {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] : (res g Λ).Linear Λ :=
  sheafPushforwardContinuous_linear _ _ _

instance pull_linear {X Y : Scheme.{u}} (f : X ⟶ Y) : (pull f Λ).Linear Λ :=
  leftAdjoint_linear (pullAdj f Λ)

instance lsh_linear {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] : (lsh j Λ).Linear Λ :=
  leftAdjoint_linear (lshAdj j Λ)

instance ext_linear {X B : Scheme.{u}} {f : X ⟶ B} (c : Cpt f) : (c.ext Λ).Linear Λ := inferInstance

instance rshriek_linear {X B : Scheme.{u}} {f : X ⟶ B} (c : Cpt f) (n : ℕ) : (c.Rshriek Λ n).Linear Λ := by
  unfold Cpt.Rshriek
  infer_instance

end RamanujanPetersson.EtLin

end

end


