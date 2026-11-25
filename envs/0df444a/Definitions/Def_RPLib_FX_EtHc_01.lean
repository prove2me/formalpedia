-- Prove2me | Definitions.Def_RPLib_FX_EtHc_01
-- name    : RPLib_FX_EtHc_01
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T13:28:48.60904+00:00
-- url     : https://prove2.me/theorems/e8813168-c91a-401b-b695-c96181b25f6b
-- title:
--   Compactly supported étale cohomology of the affine line, extension file 01 of 11
-- statement:
--   Extension file 01 of 11 for the compactly supported cohomology of the affine line, stacked on the projective-line library files it imports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_P1`: S4-EtCompact, part 11: the projective line `P^1_K = Proj K[X₀, X₁]` (O6, explicit compactifications)
--   * `S4.Def_RP_EtSheaves_CutSet`: S4-EtSheaves, part 21: `F_S` for a subset `S`
--   * `S4.Def_RP_EtCompact_CutMap`: S4-EtCompact, part 4: maps between cut sheaves
--   * `S4.Def_RP_EtSheaves_Closed`: S4-EtSheaves, part 14: `i_*` vanishes off `Z`
--   * `S4.Def_RP_EtSheaves_ClosedFF`: S4-EtSheaves, part 15: the cut sequence `0 → j_! j^* F → F → i_* i^* F → 0`
--   * `S4.Def_RP_EtSheaves_Cut`: S4-EtSheaves, part 19: `i_*` for closed immersions and the cut sequence
--   * `S4.Def_RP_EtCompact_Coh`: S4-EtCompact, part 3: etale cohomology as `Ext` from the constant sheaf
--   * `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
--   * `S4.Def_RP_EtCompact_Pres`: S4-EtCompact, part 8: presentations and the set-indexed `H^*_c`
--   * `S4.Def_RP_EtCompact_P1Pts`: S4-EtCompact, part 27: points of `P^1_K` (O8a, file 1)
--
--   **Formalization note.** Extension of the `RPLib_FX_EtP1` library (étale cohomology of the projective line) to the compactly supported cohomology of the affine line $\mathbf A^1_k = D_+(X_0) \subseteq \mathbf P^1_k$ over an algebraically closed field $k$, with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): the cut sheaves $F_S$ for locally closed $S$, the excision sequence $0 \to F_{S \cap O} \to F_S \to F_{S \setminus O} \to 0$ and its long exact sequence, the vanishing of the higher cohomology of a separably closed point, and the resulting comparison $H^n_c(\mathbf A^1, \Lambda) \to H^n(\mathbf P^1, \Lambda)$ (injective for $n = 1$, bijective for $n \ge 2$) with $H^0_c(\mathbf A^1, \Lambda) = 0$. The declarations of each library module are re-hosted verbatim, except that the three excision exactness proofs `exc_exact₁/₂/₃` are re-proved element-wise (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter II, §3 (extension by zero) and Chapter VI, §1-§3 (cohomology of curves, cohomology with compact support); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapters IV-V

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_35
import Definitions.Def_RPLib_FX_EtP1_20

/-!
# Compactly supported étale cohomology of the affine line, extension file 01 of 11

Declarations of the formalization of the compactly supported étale cohomology of the affine line
`A¹ = D₊(X₀) ⊆ P¹` over an algebraically closed field (the excision sequence for `j_! Λ ⊆ Λ ↠ i_* Λ`
and its consequences), stacked on the `RPLib_FX_EtP1` files it imports and re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_P1`: S4-EtCompact, part 11: the projective line `P^1_K = Proj K[X₀, X₁]` (O6, explicit compactifications)
* `S4.Def_RP_EtSheaves_CutSet`: S4-EtSheaves, part 21: `F_S` for a subset `S`
* `S4.Def_RP_EtCompact_CutMap`: S4-EtCompact, part 4: maps between cut sheaves
* `S4.Def_RP_EtSheaves_Closed`: S4-EtSheaves, part 14: `i_*` vanishes off `Z`
* `S4.Def_RP_EtSheaves_ClosedFF`: S4-EtSheaves, part 15: the cut sequence `0 → j_! j^* F → F → i_* i^* F → 0`
* `S4.Def_RP_EtSheaves_Cut`: S4-EtSheaves, part 19: `i_*` for closed immersions and the cut sequence
* `S4.Def_RP_EtCompact_Coh`: S4-EtCompact, part 3: etale cohomology as `Ext` from the constant sheaf
* `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
* `S4.Def_RP_EtCompact_Pres`: S4-EtCompact, part 8: presentations and the set-indexed `H^*_c`
* `S4.Def_RP_EtCompact_P1Pts`: S4-EtCompact, part 27: points of `P^1_K` (O8a, file 1)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_P1 =====
section

/-!
# S4-EtCompact, part 11: the projective line `P^1_K = Proj K[X₀, X₁]` (O6, explicit compactifications)

`P1 K := Proj (homogeneousSubmodule (Fin 2) K)` with the standard grading of `MvPolynomial (Fin 2) K`.
The degree-0 part is `K` (`bij0`), the structure map `P1 K ⟶ Spec K` is proper (`P1.toSpecK`), and the
standard chart `D₊(X₀) = Spec (K[X₀, X₁]_(X₀)) ⟶ P1 K` is an open immersion (`P1.chart0`).
-/

set_option autoImplicit false

open AlgebraicGeometry MvPolynomial CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtCompact

universe u

variable (K : Type u) [Field K]

/-- The degree-0 part of `K[X₀, X₁]` is `K`. -/
theorem P1.bij0 : Function.Bijective (algebraMap K (homogeneousSubmodule (Fin 2) K 0)) := by
  constructor
  · intro a b h
    have h' := congrArg Subtype.val h
    exact (algebraMap K (MvPolynomial (Fin 2) K)).injective h'
  · rintro ⟨y, hy⟩
    rw [homogeneousSubmodule_zero, Submodule.mem_one] at hy
    obtain ⟨r, rfl⟩ := hy
    exact ⟨r, rfl⟩

/-- `K ≃+* (K[X₀, X₁])₀`. -/
def P1.equiv0 : K ≃+* homogeneousSubmodule (Fin 2) K 0 :=
  RingEquiv.ofBijective (algebraMap K (homogeneousSubmodule (Fin 2) K 0)) (P1.bij0 K)

instance P1.isIso_ofHom0 :
    IsIso (CommRingCat.ofHom (algebraMap K (homogeneousSubmodule (Fin 2) K 0))) :=
  (RingEquiv.toCommRingCatIso (P1.equiv0 K)).isIso_hom

/-- The structure map `P^1_K ⟶ Spec K`. -/
def P1.toSpecK : P1 K ⟶ Spec (CommRingCat.of K) :=
  Proj.toSpecZero (homogeneousSubmodule (Fin 2) K) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (homogeneousSubmodule (Fin 2) K 0)))

/-- **`P^1_K` is proper over `K`.** -/
instance P1.isProper_toSpecK : IsProper (P1.toSpecK K) := by
  unfold P1.toSpecK
  infer_instance

end RamanujanPetersson.EtCompact

end

end

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

theorem isIso_stalk_quotCutπ (V : X.Opens) (F : EtSh Λ X) (s : GeomPt X) (hs : s.center ∉ V) :
    IsIso ((s.stalkF Λ).map (quotCutπ Λ V F)) := by
  have h0 : (s.stalkF Λ).map (openCutι Λ V F) = 0 := (isZero_stalk_openCut V F s hs).eq_of_src _ _
  have := cokernel.π_of_zero h0
  have : IsIso ((s.stalkF Λ).map (quotCutπ Λ V F) ≫
      (PreservesCokernel.iso (s.stalkF Λ) (openCutι Λ V F)).hom) := by
    rw [PreservesCokernel.π_iso_hom]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (PreservesCokernel.iso (s.stalkF Λ) (openCutι Λ V F)).hom

/-- **Stalks of `F_S` off `S` vanish** (any `S`). -/
theorem isZero_stalk_cut (S : Set X) (F : EtSh Λ X) (s : GeomPt X) (hs : s.center ∉ S) :
    IsZero ((s.stalkF Λ).obj (cut Λ S F)) := by
  by_cases h : s.center ∈ cutOpen S
  · have hc : s.center ∈ cutCompl S := fun hcl => hs (mem_of_mem_cutOpen h hcl)
    exact (isZero_stalk_quotCut (cutCompl S) F s hc).of_iso
      (@asIso _ _ _ _ ((s.stalkF Λ).map (openCutι Λ (cutOpen S) (quotCut Λ (cutCompl S) F)))
        (isIso_stalk_openCutι (cutOpen S) (quotCut Λ (cutCompl S) F) s h))
  · exact isZero_stalk_openCut (cutOpen S) _ s h

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

theorem isZero_stalk_cutWV_of_not_mem {W V : X.Opens} (F : EtSh Λ X) (s : GeomPt X)
    (hs : s.center ∉ W) : IsZero ((s.stalkF Λ).obj (cutWV Λ W V F)) :=
  isZero_stalk_openCut W _ s hs

theorem isZero_stalk_cutWV_of_mem {W V : X.Opens} (F : EtSh Λ X) (s : GeomPt X)
    (hW : s.center ∈ W) (hV : s.center ∈ V) : IsZero ((s.stalkF Λ).obj (cutWV Λ W V F)) :=
  isZero_stalk_openCut_of W _ s hW (isZero_stalk_quotCut V F s hV)

end RamanujanPetersson.EtCompact

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

/-- The cut complex is exact on stalks over `U` (`j` mono): its left map is an iso there. -/
theorem cutComplex_stalk_exact [Mono j] (h : Disjoint (Set.range j) (Set.range i)) (F : EtSh Λ X)
    (t : GeomPt U) : ((cutComplex Λ i j h F).map ((t.map j).stalkF Λ)).Exact := by
  have hI : IsIso (((t.map j).stalkF Λ).map ((lshAdj j Λ).counit.app F)) := isIso_stalk_counit j Λ t F
  have hZ : HasZeroObject (ModuleCat.{u} Λ) := inferInstance
  exact (ShortComplex.exact_iff_epi (C := ModuleCat.{u} Λ) _
    ((push_stalk_isZero Λ i j h t _).eq_of_tgt _ _)).2 (@IsIso.epi_of_iso _ _ _ _ _ hI)

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

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

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

variable [IsClosedImmersion i]

/-- The cut complex on stalks at the points of `cutPts`: exact, with an epimorphism on the right. -/
theorem cut_stalk (F : EtSh Λ X) (k : Z ⊕ (complOpens i).toScheme) :
    ((cutComplex Λ i (complOpens i).ι (disjoint_complOpens i) F).map
        ((cutPts i k).stalkF Λ)).Exact ∧
      Epi (((cutPts i k).stalkF Λ).map ((pullAdj i Λ).unit.app F)) := by
  have hZ : HasZeroObject (ModuleCat.{u} Λ) := inferInstance
  rcases k with z | y
  · have hI := isIso_stalk_unit Λ i (geomPtAt z) F
    have hc : ((geomPtAt z).map i).center ∉ Set.range (complOpens i).ι := by
      rw [range_complOpens_ι, Set.notMem_compl_iff]
      refine ⟨z, ?_⟩
      show i z = ((geomPtAt z).pt ≫ i) default
      rw [Scheme.Hom.comp_apply]
      exact (congrArg i (center_geomPtAt z)).symm
    have h0 := lsh_stalk_isZero (complOpens i).ι Λ ((geomPtAt z).map i) hc
      ((res (complOpens i).ι Λ).obj F)
    refine ⟨(ShortComplex.exact_iff_mono (C := ModuleCat.{u} Λ) _ (h0.eq_of_src _ _)).2
      (@IsIso.mono_of_iso _ _ _ _ _ hI), @IsIso.epi_of_iso _ _ _ _ _ hI⟩
  · refine ⟨cutComplex_stalk_exact Λ i (complOpens i).ι (disjoint_complOpens i) F (geomPtAt y), ?_⟩
    exact (push_stalk_isZero Λ i (complOpens i).ι (disjoint_complOpens i) (geomPtAt y) _).epi _

/-- **The cut sequence** `0 → j_! j^* F → F → i_* i^* F → 0` (`j` the open complement of `i`). -/
theorem cut_shortExact (F : EtSh Λ X) :
    (cutComplex Λ i (complOpens i).ι (disjoint_complOpens i) F).ShortExact :=
  ShortComplex.ShortExact.mk'
    (exact_of_family Λ (cutPts i) (cutPts_cover i) _ (fun k => (cut_stalk Λ i F k).1))
    (mono_lshAdj_counit (complOpens i).ι Λ F)
    (epi_of_family Λ (cutPts i) (cutPts_cover i) _ (fun k => (cut_stalk Λ i F k).2))

end CoverDense

end RamanujanPetersson.EtSheaves

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

/-- **The cut sequence** `0 → j_! j^* F → F → i_* i^* F → 0` for a closed immersion `i` with
open complement `j`. -/
theorem cut_exact (F : EtSh Λ X) :
    (cutComplex Λ i (complOpens i).ι (disjoint_complOpens i) F).ShortExact :=
  cut_shortExact Λ i F

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

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

end ExtIso

variable (Λ : Type u) [CommRing Λ]

/-- Functoriality of `H^n(X, -)`. -/
def Hmap {X : Scheme.{u}} {F G : EtSh Λ X} (φ : F ⟶ G) (n : ℕ) : H Λ F n →+ H Λ G n where
  toFun x := x.comp (Ext.mk₀ φ) (add_zero n)
  map_zero' := by simp
  map_add' x y := by simp [Ext.add_comp]

section Closed

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

end Closed

section Open

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

end Open

end RamanujanPetersson.EtCompact

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

theorem mono_excComplex_f : Mono (excComplex W h F).f := by
  rw [mono_iff_stalk]
  intro x
  by_cases hx : x ∈ W ⊓ V'
  · have : IsIso (((geomPtAt x).stalkF Λ).map (excComplex W h F).f) :=
      isIso_stalk_openCutLe (inf_le_left : W ⊓ V' ≤ W) (quotCut Λ V F) _ (mem_center_geomPtAt hx)
    exact IsIso.mono_of_iso _
  · exact (isZero_stalk_cutWV_of_not_mem F _ (not_mem_center_geomPtAt hx)).mono _

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

theorem exact_excComplex : (excComplex W h F).Exact := by
  rw [exact_iff_stalk]
  intro x
  by_cases hW : x ∈ W
  · by_cases hV : x ∈ V
    · exact ShortComplex.exact_of_isZero_X₂ _
        (isZero_stalk_cutWV_of_mem F _ (mem_center_geomPtAt hW) (mem_center_geomPtAt hV))
    · by_cases hV' : x ∈ V'
      · have : IsIso (((geomPtAt x).stalkF Λ).map (excComplex W h F).f) :=
          isIso_stalk_openCutLe (inf_le_left : W ⊓ V' ≤ W) (quotCut Λ V F) _
            (mem_center_geomPtAt (show x ∈ W ⊓ V' from ⟨hW, hV'⟩))
        refine (ShortComplex.exact_iff_epi _ ((isZero_stalk_cutWV_of_mem F _
          (mem_center_geomPtAt hW) (mem_center_geomPtAt hV')).eq_of_tgt _ _)).2 ?_
        exact IsIso.epi_of_iso ((((geomPtAt x).stalkF Λ)).map (excComplex W h F).f)
      · have : IsIso (((geomPtAt x).stalkF Λ).map (excComplex W h F).g) :=
          isIso_stalk_openCutMap W (quotCutLe h F) _ (mem_center_geomPtAt hW)
            (isIso_stalk_quotCutLe h F _ (not_mem_center_geomPtAt hV'))
        refine (ShortComplex.exact_iff_mono _ ((isZero_stalk_cutWV_of_not_mem F _
          (not_mem_center_geomPtAt (fun hx : x ∈ W ⊓ V' => hV' hx.2))).eq_of_src _ _)).2 ?_
        exact IsIso.mono_of_iso ((((geomPtAt x).stalkF Λ)).map (excComplex W h F).g)
  · exact ShortComplex.exact_of_isZero_X₂ _
      (isZero_stalk_cutWV_of_not_mem F _ (not_mem_center_geomPtAt hW))

/-- **The excision short exact sequence** `0 → F_U → F_S → F_Z → 0`. -/
theorem excComplex_shortExact : (excComplex W h F).ShortExact :=
  ShortComplex.ShortExact.mk' (exact_excComplex W h F) (mono_excComplex_f W h F)
    (epi_excComplex_g W h F)

end RamanujanPetersson.EtCompact


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

/-- `cut S F ≅ cutWV W V F` for any presentation `S = W ∩ Vᶜ`. -/
def cutIsoCutWV {S : Set X} {W V : X.Opens} (h : wvSet W V = S) : cut Λ S F ≅ cutWV Λ W V F :=
  cutWVIso F ((wvSet_cut (S := S) (h ▸ isLocallyClosed_wvSet W V)).trans h.symm)

end HcSet

section SetExc

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

end RamanujanPetersson.EtCompact

end

end


