-- Prove2me | Definitions.Def_RPLib_S4_EtShLshFF
-- name    : RPLib_S4_EtShLshFF
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:31:40.402625+00:00
-- url     : https://prove2.me/theorems/d74128b7-a977-4638-8dfa-ad89eb30bfcd
-- title:
--   $j_!$ is fully faithful for an open immersion
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. For an etale monomorphism $j : U \to X$, composition with $j$ is fully faithful on etale sites, so the counit of $j^* \dashv j_*$ is an isomorphism, and by the adjoint triple $j_! \dashv j^* \dashv j_*$ the unit $G \to j^* j_! G$ is an isomorphism. Hence $j^*$ of the counit $j_! j^* F \to F$ is an isomorphism, its stalks at geometric points over $U$ are isomorphisms, and the counit is a monomorphism when $j$ is an open immersion.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose IV, Section 11; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter II

import Mathlib
import Definitions.Def_RPLib_S4_EtShLsh
import Definitions.Def_RPLib_S4_EtShHomLoc

/-!
# S4-EtSheaves, part 13: `j_!` is fully faithful for a monomorphism `j`

For an etale monomorphism `j : U ⟶ X` (an open immersion), `etComp j` is fully faithful, so the
counit of `res j ⊣ j_*` is an isomorphism; by the adjoint triple `j_! ⊣ j^* ⊣ j_*` the unit
`G ⟶ j^* j_! G` is an isomorphism. Hence `j^*` of the counit `j_! j^* F ⟶ F` is an isomorphism,
and so is its stalk at every geometric point over `U`; the counit is a monomorphism when `j` is
an open immersion (its stalks off `U` vanish).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

section Mono

variable [Mono j]

instance etComp_full : (etComp j).Full where
  map_surjective {W W'} φ := by
    have h : (φ.left ≫ W'.hom) ≫ j = W.hom ≫ j :=
      (Category.assoc _ _ _).trans (MorphismProperty.Over.w φ)
    exact ⟨MorphismProperty.Over.homMk φ.left ((cancel_mono j).1 h) trivial,
      MorphismProperty.Over.Hom.ext rfl⟩

variable (Λ : Type u) [CommRing Λ]

instance isIso_resAdj_counit : IsIso (resAdj j Λ).counit := by
  have := Functor.isContinuous_comp (etComp j) (etPull j) U.smallEtaleTopology
    X.smallEtaleTopology U.smallEtaleTopology
  exact (resAdj j Λ).isIso_counit_of_iso
    (Functor.sheafPushforwardContinuousId' (asIso (etCompAdj j).unit).symm (ModuleCat.{u} Λ)
      U.smallEtaleTopology)

/-- The adjoint triple `j_! ⊣ j^* ⊣ j_*` (with `j^* = res j`). -/
def lshTriple : Adjunction.Triple (lsh j Λ) (res j Λ) (push j Λ) := ⟨lshAdj j Λ, resAdj j Λ⟩

instance isIso_lshAdj_unit : IsIso (lshAdj j Λ).unit :=
  (lshTriple j Λ).isIso_unit_iff_isIso_counit.2 (isIso_resAdj_counit j Λ)

/-- `j_!` is fully faithful for an etale monomorphism `j`. -/
def lshFullyFaithful : (lsh j Λ).FullyFaithful := (lshAdj j Λ).fullyFaithfulLOfIsIsoUnit

theorem isIso_res_counit (F : EtSh Λ X) :
    IsIso ((res j Λ).map ((lshAdj j Λ).counit.app F)) := by
  have h := (lshAdj j Λ).right_triangle_components F
  have : IsIso ((lshAdj j Λ).unit.app ((res j Λ).obj F) ≫
      (res j Λ).map ((lshAdj j Λ).counit.app F)) := by
    rw [h]; exact IsIso.id _
  exact IsIso.of_isIso_comp_left ((lshAdj j Λ).unit.app ((res j Λ).obj F)) _

/-- Stalks of restriction: `(res j F)_t ≅ F_(t ≫ j)`, naturally in `F`. -/
def resStalkIso (t : GeomPt U) : res j Λ ⋙ t.stalkF Λ ≅ (t.map j).stalkF Λ :=
  Functor.isoWhiskerRight (pullIsoRes j Λ).symm _ ≪≫ pullStalkIso j Λ t

/-- **The counit `j_! j^* F ⟶ F` is an isomorphism on stalks over `U`.** -/
theorem isIso_stalk_counit (t : GeomPt U) (F : EtSh Λ X) :
    IsIso (((t.map j).stalkF Λ).map ((lshAdj j Λ).counit.app F)) := by
  have := isIso_res_counit j Λ F
  have : IsIso ((res j Λ ⋙ t.stalkF Λ).map ((lshAdj j Λ).counit.app F)) :=
    Functor.map_isIso (t.stalkF Λ) ((res j Λ).map ((lshAdj j Λ).counit.app F))
  exact (NatIso.isIso_map_iff (resStalkIso j Λ t) _).1 this

end Mono

section OpenImm

variable [IsOpenImmersion j]

/-- A geometric point whose centre lies in the open `U` comes from `U`. -/
theorem exists_map_eq (s : GeomPt X) (hs : s.center ∈ Set.range j) :
    ∃ t : GeomPt U, t.map j = s := by
  obtain ⟨Ω, pt⟩ := s
  have h : Set.range pt ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  exact ⟨⟨Ω, IsOpenImmersion.lift j pt h⟩, by
    simp only [GeomPt.map, IsOpenImmersion.lift_fac]⟩

variable (Λ : Type u) [CommRing Λ]

/-- Stalks of the counit `j_! j^* F ⟶ F` are monomorphisms (isomorphisms over `U`, zero source off `U`). -/
theorem mono_stalk_counit (F : EtSh Λ X) (s : GeomPt X) :
    Mono ((s.stalkF Λ).map ((lshAdj j Λ).counit.app F)) := by
  rcases em (s.center ∈ Set.range j) with hs | hs
  · obtain ⟨t, rfl⟩ := exists_map_eq j s hs
    have := isIso_stalk_counit j Λ t F
    exact IsIso.mono_of_iso _
  · exact ⟨fun _ _ _ => (lsh_stalk_isZero j Λ s hs ((res j Λ).obj F)).eq_of_tgt _ _⟩

/-- **`j_! j^* F ⟶ F` is a monomorphism** for an open immersion `j`. -/
theorem mono_lshAdj_counit (F : EtSh Λ X) : Mono ((lshAdj j Λ).counit.app F) :=
  (mono_iff_stalk Λ ((lshAdj j Λ).counit.app F)).2 (fun x => mono_stalk_counit j Λ F (geomPtAt x))

end OpenImm

end RamanujanPetersson.EtSheaves


