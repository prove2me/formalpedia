-- Prove2me | Definitions.Def_RPLib_S4_EtShClosed
-- name    : RPLib_S4_EtShClosed
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:32:29.894081+00:00
-- url     : https://prove2.me/theorems/5fbc7b00-3018-48ed-b53d-a630e1173f3a
-- title:
--   The pushforward $i_*$ vanishes off the image of $i$
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. For $i : Z \to X$ and an etale $j : U \to X$ whose image misses the image of $i$, the restriction $j^* i_* G$ is the zero sheaf (its values are those of $G$ on the empty schemes $W \times_X Z$). Hence the stalks of $i_* G$ vanish at geometric points outside the image of $i$, every map $j_! G' \to i_* G$ is zero, and $j_! j^* F \to F \to i_* i^* F$ is a complex.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose IV, Section 14; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter II

import Mathlib
import Definitions.Def_RPLib_S4_EtShLshFF

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

/-- On an etale scheme with empty underlying space, every sheaf has zero value. -/
theorem isZero_obj_of_isEmpty {Y : Scheme.{u}} (G : EtSh Λ Y) (V : Y.Etale)
    (hV : IsEmpty V.left) : IsZero (G.obj.obj (op V)) := by
  have h : (⊥ : Sieve V) ∈ Y.smallEtaleTopology V :=
    (mem_smallEtale_iff V ⊥).2 (fun x => (hV.false x).elim)
  exact (IsZero.iff_id_eq_zero _).2 ((Sheaf.isTerminalOfBotCover G V h).hom_ext _ _)

/-- A sheaf all of whose values are zero is zero. -/
theorem isZero_of_isZero_obj {Y : Scheme.{u}} (G : EtSh Λ Y)
    (h : ∀ V : Y.Etale, IsZero (G.obj.obj (op V))) : IsZero G := by
  rw [IsZero.iff_id_eq_zero]
  exact Sheaf.hom_ext (NatTrans.ext (funext fun V => (h V.unop).eq_of_src _ _))

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [Etale j]

/-- `W ×_X Z` is empty when the images of `W ⟶ U ⟶ X` and `i` are disjoint. -/
theorem isEmpty_etPull_etComp (h : Disjoint (Set.range j) (Set.range i)) (W : U.Etale) :
    IsEmpty ((etPull i).obj ((etComp j).obj W)).left := by
  refine ⟨fun z => ?_⟩
  have hz : (pullback.fst ((etComp j).obj W).hom i ≫ W.hom ≫ j) z =
      (pullback.snd ((etComp j).obj W).hom i ≫ i) z :=
    congrArg (fun φ : pullback ((etComp j).obj W).hom i ⟶ X => φ z) pullback.condition
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hz
  exact Set.disjoint_left.1 h ⟨_, rfl⟩ ⟨_, hz.symm⟩

/-- **`j^* i_* G = 0`** when the images of `j` and `i` are disjoint. -/
theorem isZero_res_push (h : Disjoint (Set.range j) (Set.range i)) (G : EtSh Λ Z) :
    IsZero ((res j Λ).obj ((push i Λ).obj G)) :=
  isZero_of_isZero_obj Λ _ (fun W => isZero_obj_of_isEmpty Λ G _ (isEmpty_etPull_etComp i j h W))

/-- **Stalks of `i_*` vanish over `U`** (`j` an etale mono whose image misses that of `i`). -/
theorem push_stalk_isZero [Mono j] (h : Disjoint (Set.range j) (Set.range i)) (t : GeomPt U)
    (G : EtSh Λ Z) : IsZero (((t.map j).stalkF Λ).obj ((push i Λ).obj G)) :=
  (Functor.map_isZero (t.stalkF Λ) (isZero_res_push Λ i j h G)).of_iso
    ((resStalkIso j Λ t).app ((push i Λ).obj G)).symm

/-- The open complement of a closed immersion. -/
def complOpens [IsClosedImmersion i] : X.Opens :=
  ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩

theorem range_complOpens_ι [IsClosedImmersion i] :
    Set.range (complOpens i).ι = (Set.range i)ᶜ := Scheme.Opens.range_ι _

theorem disjoint_complOpens [IsClosedImmersion i] :
    Disjoint (Set.range (complOpens i).ι) (Set.range i) := by
  rw [range_complOpens_ι]
  exact disjoint_compl_left

/-- **Stalks of `i_* G` vanish off the image of a closed immersion `i`.** -/
theorem push_stalk_isZero_of_not_mem [IsClosedImmersion i] (s : GeomPt X)
    (hs : s.center ∉ Set.range i) (G : EtSh Λ Z) : IsZero ((s.stalkF Λ).obj ((push i Λ).obj G)) := by
  obtain ⟨t, rfl⟩ := exists_map_eq (complOpens i).ι s (by rw [range_complOpens_ι]; exact hs)
  exact push_stalk_isZero Λ i (complOpens i).ι (disjoint_complOpens i) t G

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


