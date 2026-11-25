-- Prove2me | Definitions.Def_RPLib_FX_EtP1_35
-- name    : RPLib_FX_EtP1_35
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T03:56:02.10375+00:00
-- url     : https://prove2.me/theorems/9e95f509-f5fe-5f02-8ed7-7e9f31f4a6c7
-- title:
--   Étale cohomology of the projective line, library file 35 (an extra file from a re-cut)
-- statement:
--   File 35 (an extra file from a re-cut) of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtSheaves_Closed`: S4-EtSheaves, part 14: `i_*` vanishes off `Z`
--   * `S4.Def_RP_EtSheaves_LiftRing`: S4-EtSheaves, part 17: lifting standard etale algebras along a surjection
--   * `S4.Def_RP_EtSheaves_LiftFull`: S4-EtSheaves, part 16: base change along a closed immersion is locally full
--   * `S4.Def_RP_EtSheaves_LiftSch`: S4-EtSheaves, part 18: base change along a closed immersion is cover dense
--   * `S4.Def_RP_EtSheaves_ClosedFF`: S4-EtSheaves, part 15: the cut sequence `0 → j_! j^* F → F → i_* i^* F → 0`
--   * `S4.Def_RP_EtSheaves_Cut`: S4-EtSheaves, part 19: `i_*` for closed immersions and the cut sequence
--   * `S4.Def_RP_EtCompact_Exact`: S4-EtCompact, part 2: exactness of `f^*`, `i_*` (closed) and `j_!` (open)
--   * `S4.Def_RP_EtSheaves_SpecPt`: S4-EtSheaves, part 29: geometric points of the spectrum of a field
--   * `S4.Def_RP_CdOne_Field`: S4-PD (3), field layer: `HypL` for `Gal(Ω/E₀)` from Tsen + Kummer
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_12

/-!
# Étale cohomology of the projective line, library file 35 (extra file from a re-cut)

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtSheaves_Closed`: S4-EtSheaves, part 14: `i_*` vanishes off `Z`
* `S4.Def_RP_EtSheaves_LiftRing`: S4-EtSheaves, part 17: lifting standard etale algebras along a surjection
* `S4.Def_RP_EtSheaves_LiftFull`: S4-EtSheaves, part 16: base change along a closed immersion is locally full
* `S4.Def_RP_EtSheaves_LiftSch`: S4-EtSheaves, part 18: base change along a closed immersion is cover dense
* `S4.Def_RP_EtSheaves_ClosedFF`: S4-EtSheaves, part 15: the cut sequence `0 → j_! j^* F → F → i_* i^* F → 0`
* `S4.Def_RP_EtSheaves_Cut`: S4-EtSheaves, part 19: `i_*` for closed immersions and the cut sequence
* `S4.Def_RP_EtCompact_Exact`: S4-EtCompact, part 2: exactness of `f^*`, `i_*` (closed) and `j_!` (open)
* `S4.Def_RP_EtSheaves_SpecPt`: S4-EtSheaves, part 29: geometric points of the spectrum of a field
* `S4.Def_RP_CdOne_Field`: S4-PD (3), field layer: `HypL` for `Gal(Ω/E₀)` from Tsen + Kummer
-/

set_option autoImplicit false

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

theorem disjoint_complOpens [IsClosedImmersion i] :
    Disjoint (Set.range (complOpens i).ι) (Set.range i) := by
  rw [range_complOpens_ι]
  exact disjoint_compl_left

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_LiftRing =====
section

/-!
# S4-EtSheaves, part 17: lifting standard etale algebras along a surjection

If `A → R` is surjective and `S` is a standard etale `R`-algebra, there is a standard etale
`A`-algebra `P.Ring` with `S ≃ₐ[R] R ⊗[A] P.Ring`: lift `f` to a monic `F`, lift `g` to any `G`
and use the pair `(F, G * F')`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial TensorProduct

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]
  (hφ : Function.Surjective (algebraMap A R)) (Q : StandardEtalePair R)

include hφ

theorem liftPair_map_g : ((liftPair hφ Q).map (algebraMap A R)).g = Q.g * derivative Q.f := by
  simp only [StandardEtalePair.map_g, liftPair, Polynomial.map_mul,
    (map_surjective _ hφ Q.g).choose_spec]
  rw [← derivative_map, (exists_monic_lift hφ Q).choose_spec.1]

/-- `(P.map φ).Ring ≃ₐ[R] Q.Ring`. -/
def liftEquiv : ((liftPair hφ Q).map (algebraMap A R)).Ring ≃ₐ[R] Q.Ring := by
  set P := (liftPair hφ Q).map (algebraMap A R)
  have h1 : Q.HasMap P.X := by
    have h := P.hasMap_X
    refine ⟨?_, ?_⟩
    · rw [← liftPair_map_f hφ Q]; exact h.1
    · have h2 := h.2
      rw [liftPair_map_g hφ Q, map_mul] at h2
      exact isUnit_of_mul_isUnit_left h2
  have h2 : P.HasMap Q.X := by
    have h := Q.hasMap_X
    refine ⟨?_, ?_⟩
    · rw [liftPair_map_f hφ Q]; exact h.1
    · rw [liftPair_map_g hφ Q, map_mul]
      exact h.2.mul h.isUnit_derivative_f
  exact AlgEquiv.ofAlgHom (P.lift Q.X h2) (Q.lift P.X h1)
    (Q.hom_ext (by simp)) (P.hom_ext (by simp))

/-- **Lifting standard etale algebras along a surjection.** -/
theorem exists_lift_standardEtale (S : Type u) [CommRing S] [Algebra R S]
    [Algebra.IsStandardEtale R S] :
    ∃ P : StandardEtalePair A, Nonempty (S ≃ₐ[R] R ⊗[A] P.Ring) := by
  let Q' : StandardEtalePresentation R S :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  let P := liftPair hφ Q'.P
  let Pp : StandardEtalePresentation A P.Ring :=
    ⟨P, P.X, P.hasMap_X, by simpa [StandardEtalePair.lift_X_left] using Function.bijective_id⟩
  exact ⟨P, ⟨Q'.equivRing.trans ((liftEquiv hφ Q'.P).symm.trans
    (Pp.baseChange (T := R)).equivRing.symm)⟩⟩

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_LiftFull =====
section

/-!
# S4-EtSheaves, part 16: base change along a closed immersion is locally full

Let `i : Z ⟶ X` be a closed immersion and `f : U_Z ⟶ V_Z` a morphism of etale `Z`-schemes between
base changes of etale `X`-schemes. The graph of `f` is a section of the etale map
`(U ×_X V)_Z ⟶ U_Z`, hence an open immersion. Its image is open in the closed subscheme
`(U ×_X V)_Z` of `U ×_X V`, so it is cut out by an open `O ⊆ U ×_X V`. Over `O` the two
projections to `U` and `V` restrict on `O_Z` to `τ` and `τ ≫ f`, and `τ` is surjective. Hence
`etPull i` is locally full for the small etale topology of `Z`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

instance hasOfPostcomp_isOpenImmersion :
    MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
      (@LocallyOfFiniteType ⊓ @FormallyUnramified) := by
  rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
  intro X Y f ⟨hft, hfu⟩
  exact inferInstanceAs <| IsOpenImmersion (pullback.diagonal f)

/-- A section of an etale morphism is an open immersion. -/
theorem isOpenImmersion_of_section {A B : Scheme.{u}} (σ : A ⟶ B) (p : B ⟶ A) [Etale p]
    (h : σ ≫ p = 𝟙 A) : IsOpenImmersion σ := by
  have : IsOpenImmersion (σ ≫ p) := by rw [h]; infer_instance
  exact MorphismProperty.of_postcomp (W := @IsOpenImmersion)
    (W' := @LocallyOfFiniteType ⊓ @FormallyUnramified) σ p ⟨inferInstance, inferInstance⟩ this

theorem apply_eq_of_eq {A B : Scheme.{u}} {φ ψ : A ⟶ B} (h : φ = ψ) (a : A) : φ a = ψ a := by
  rw [h]

variable {Z X : Scheme.{u}} (i : Z ⟶ X) {U V : X.Etale}
  (f : (etPull i).obj U ⟶ (etPull i).obj V)

theorem etPull_hom_w : f.left ≫ pullback.snd V.hom i = pullback.snd U.hom i :=
  MorphismProperty.Over.w f

/-- The structure map of `U ×_X V`. -/
abbrev prodHom (U V : X.Etale) : pullback U.hom V.hom ⟶ X := pullback.fst U.hom V.hom ≫ U.hom

/-- The graph of `f`, a section of `(U ×_X V)_Z ⟶ U_Z`. -/
def graphSec : pullback U.hom i ⟶ pullback (prodHom U V) i :=
  pullback.lift (pullback.lift (pullback.fst U.hom i) (f.left ≫ pullback.fst V.hom i)
      (pullback.condition.trans (by
        rw [← etPull_hom_w i f, Category.assoc, Category.assoc, ← pullback.condition])))
    (pullback.snd U.hom i) (by
      show _ ≫ pullback.fst U.hom V.hom ≫ U.hom = _
      rw [← Category.assoc, pullback.lift_fst]
      exact pullback.condition)

/-- The projection `(U ×_X V)_Z ⟶ U_Z`. -/
def prU (U V : X.Etale) : pullback (prodHom U V) i ⟶ pullback U.hom i :=
  pullback.lift (pullback.fst _ i ≫ pullback.fst U.hom V.hom) (pullback.snd _ i) (by
    rw [Category.assoc]; exact pullback.condition)

/-- The projection `(U ×_X V)_Z ⟶ V_Z`. -/
def prV (U V : X.Etale) : pullback (prodHom U V) i ⟶ pullback V.hom i :=
  pullback.lift (pullback.fst _ i ≫ pullback.snd U.hom V.hom) (pullback.snd _ i) (by
    rw [Category.assoc, ← pullback.condition (f := U.hom) (g := V.hom)]; exact pullback.condition)

theorem graphSec_prU : graphSec i f ≫ prU i U V = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, prU, pullback.lift_fst, ← Category.assoc, graphSec, pullback.lift_fst,
      pullback.lift_fst, Category.id_comp]
  · rw [Category.assoc, prU, pullback.lift_snd, graphSec, pullback.lift_snd, Category.id_comp]

theorem graphSec_prV : graphSec i f ≫ prV i U V = f.left := by
  apply pullback.hom_ext
  · rw [Category.assoc, prV, pullback.lift_fst, ← Category.assoc, graphSec, pullback.lift_fst,
      pullback.lift_snd]
  · rw [Category.assoc, prV, pullback.lift_snd, graphSec, pullback.lift_snd, etPull_hom_w i f]

instance (U V : X.Etale) : Etale (prU i U V) := by
  have : Etale (prU i U V ≫ pullback.snd U.hom i) := by
    rw [prU, pullback.lift_snd]; infer_instance
  exact Etale.of_comp (f := prU i U V) (g := pullback.snd U.hom i)

instance : IsOpenImmersion (graphSec i f) :=
  isOpenImmersion_of_section _ (prU i U V) (graphSec_prU i f)

variable [IsClosedImmersion i]

theorem exists_opens_graph : ∃ O : (pullback U.hom V.hom).Opens,
    pullback.fst (prodHom U V) i ⁻¹' SetLike.coe O = Set.range (graphSec i f) := by
  obtain ⟨t, ht, he⟩ := (pullback.fst (prodHom U V) i).isClosedEmbedding.isInducing.isOpen_iff.1
    (graphSec i f).isOpenEmbedding.isOpen_range
  exact ⟨⟨t, ht⟩, he⟩

/-- The open `O ⊆ U ×_X V` cutting out the graph of `f`. -/
def graphOpens : (pullback U.hom V.hom).Opens := (exists_opens_graph i f).choose

theorem graphOpens_spec :
    pullback.fst (prodHom U V) i ⁻¹' SetLike.coe (graphOpens i f) =
      Set.range (graphSec i f) :=
  (exists_opens_graph i f).choose_spec

/-- `O` as an etale `X`-scheme. -/
abbrev graphEt : X.Etale :=
  MorphismProperty.Over.mk ⊤ ((graphOpens i f).ι ≫ prodHom U V) inferInstance

/-- `O ⟶ U`. -/
def graphL : graphEt i f ⟶ U :=
  MorphismProperty.Over.homMk ((graphOpens i f).ι ≫ pullback.fst U.hom V.hom) (by
    rw [Category.assoc]; rfl)

/-- `O ⟶ V`. -/
def graphR : graphEt i f ⟶ V :=
  MorphismProperty.Over.homMk ((graphOpens i f).ι ≫ pullback.snd U.hom V.hom) (by
    rw [Category.assoc, ← pullback.condition]; rfl)

/-- `O_Z ⟶ (U ×_X V)_Z`. -/
def graphRho : pullback (graphEt i f).hom i ⟶ pullback (prodHom U V) i :=
  pullback.lift (pullback.fst _ i ≫ (graphOpens i f).ι) (pullback.snd _ i) (by
    rw [Category.assoc]; exact pullback.condition)

theorem map_graphL_left : ((etPull i).map (graphL i f)).left = graphRho i f ≫ prU i U V := by
  rw [etPull_map_left]
  apply pullback.hom_ext
  · simp [graphRho, prU, graphL]
  · simp [graphRho, prU]

theorem map_graphR_left : ((etPull i).map (graphR i f)).left = graphRho i f ≫ prV i U V := by
  rw [etPull_map_left]
  apply pullback.hom_ext
  · simp [graphRho, prV, graphR]
  · simp [graphRho, prV]

theorem range_graphRho : Set.range (graphRho i f) ⊆ Set.range (graphSec i f) := by
  rintro _ ⟨y, rfl⟩
  rw [← graphOpens_spec i f, Set.mem_preimage, ← Scheme.Hom.comp_apply, graphRho,
    pullback.lift_fst, Scheme.Hom.comp_apply, ← Scheme.Opens.range_ι]
  exact ⟨_, rfl⟩

/-- `O_Z ⟶ U_Z`. -/
def graphTau : pullback (graphEt i f).hom i ⟶ pullback U.hom i :=
  IsOpenImmersion.lift (graphSec i f) (graphRho i f) (range_graphRho i f)

theorem graphTau_fac : graphTau i f ≫ graphSec i f = graphRho i f :=
  IsOpenImmersion.lift_fac _ _ _

theorem map_graphL_left' : ((etPull i).map (graphL i f)).left = graphTau i f := by
  rw [map_graphL_left, ← graphTau_fac, Category.assoc, graphSec_prU, Category.comp_id]

theorem map_graphR_eq : (etPull i).map (graphR i f) = (etPull i).map (graphL i f) ≫ f := by
  apply MorphismProperty.Over.Hom.ext
  rw [MorphismProperty.Comma.comp_left, map_graphR_left, map_graphL_left', ← graphTau_fac,
    Category.assoc, graphSec_prV]

theorem exists_graphTau_eq (x : ↥(pullback U.hom i)) : ∃ w, graphTau i f w = x := by
  have hx : pullback.fst (prodHom U V) i (graphSec i f x) ∈ SetLike.coe (graphOpens i f) := by
    rw [← Set.mem_preimage, graphOpens_spec]; exact ⟨x, rfl⟩
  rw [← Scheme.Opens.range_ι] at hx
  obtain ⟨o, ho⟩ := hx
  have h : (graphEt i f).hom o = i (pullback.snd (prodHom U V) i (graphSec i f x)) := by
    show ((graphOpens i f).ι ≫ prodHom U V) o = _
    rw [Scheme.Hom.comp_apply, ho, ← Scheme.Hom.comp_apply, pullback.condition,
      Scheme.Hom.comp_apply]
  obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback o _ h
  refine ⟨w, (graphSec i f).isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, graphTau_fac]
  apply (pullback.fst (prodHom U V) i).isClosedEmbedding.injective
  rw [← Scheme.Hom.comp_apply, graphRho, pullback.lift_fst, Scheme.Hom.comp_apply]
  exact (congrArg (graphOpens i f).ι hw1).trans ho

/-- **Base change along a closed immersion is locally full** on small etale sites. -/
instance etPull_isLocallyFull : (etPull i).IsLocallyFull Z.smallEtaleTopology where
  functorPushforward_imageSieve_mem {U V} f := by
    rw [mem_smallEtale_iff]
    intro x
    obtain ⟨w, hw⟩ := exists_graphTau_eq i f x
    refine ⟨(etPull i).obj (graphEt i f), (etPull i).map (graphL i f), w,
      Sieve.image_mem_functorPushforward _ _ ⟨graphR i f, map_graphR_eq i f⟩, ?_⟩
    rw [map_graphL_left']
    exact hw

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_LiftSch =====
section

/-!
# S4-EtSheaves, part 18: base change along a closed immersion is cover dense

Let `i : Z ⟶ X` be a closed immersion. Every etale `Z`-scheme `W` is covered by images of
base changes `V ×_X Z` of etale `X`-schemes `V`. Around a point `w` of `W`: choose an affine
chart `Spec A ⟶ X`, so `Z ∩ Spec A = Spec (A ⧸ I)`; an affine chart `Spec B` of `W` over it; a
standard etale localisation `B_g` at `w` (`Algebra.IsEtaleAt.exists_isStandardEtale`); lift it to
a standard etale `A`-algebra `P` with `B_g ≃ (A ⧸ I) ⊗[A] P` (`exists_lift_standardEtale`) and
take `V = Spec P`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Limits Opposite TensorProduct

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

section Local

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  {A : Type u} [CommRing A] (e : Spec (.of A) ⟶ X) [IsOpenImmersion e]
  (I : Ideal A) (eR : pullback e i ≅ Spec (.of (A ⧸ I)))
  (hfst : pullback.fst e i =
    eR.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I))))
  (P : StandardEtalePair A)

/-- `Spec P ⟶ Spec A ⟶ X`. -/
abbrev hP : Spec (.of P.Ring) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap A P.Ring)) ≫ e

instance : Etale (Spec.map (CommRingCat.ofHom (algebraMap A P.Ring))) :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).2 (RingHom.etale_algebraMap.2 inferInstance)

instance : Etale (hP e P) := by
  dsimp only [hP]; infer_instance

/-- `Spec P` as an etale `X`-scheme. -/
abbrev liftEt : X.Etale := MorphismProperty.Over.mk ⊤ (hP e P) inferInstance

/-- `V_Z ⟶ Z ∩ Spec A`. -/
def toZ0 : pullback (hP e P) i ⟶ pullback e i :=
  pullback.lift (pullback.fst _ i ≫ Spec.map (CommRingCat.ofHom (algebraMap A P.Ring)))
    (pullback.snd _ i) (by rw [Category.assoc]; exact pullback.condition)

/-- `V_Z ⟶ Spec (A ⧸ I) ×_{Spec A} Spec P`. -/
def toPB : pullback (hP e P) i ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I))))
    (Spec.map (CommRingCat.ofHom (algebraMap A P.Ring))) :=
  pullback.lift (toZ0 i e P ≫ eR.hom) (pullback.fst _ i) (by
    rw [Category.assoc, ← hfst, toZ0, pullback.lift_fst])

omit [IsClosedImmersion i] [IsOpenImmersion e] in
@[reassoc]
theorem toPB_fst : toPB i e I eR hfst P ≫ pullback.fst _ _ = toZ0 i e P ≫ eR.hom :=
  pullback.lift_fst _ _ _

omit [IsClosedImmersion i] [IsOpenImmersion e] in
theorem toPB_snd : toPB i e I eR hfst P ≫ pullback.snd _ _ = pullback.fst _ i :=
  pullback.lift_snd _ _ _

omit [IsClosedImmersion i] [IsOpenImmersion e] in
include hfst in
theorem eR_inv_snd_i : eR.inv ≫ pullback.snd e i ≫ i =
    Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I))) ≫ e := by
  rw [← pullback.condition, hfst, Category.assoc, Iso.inv_hom_id_assoc]

theorem toPB_surjective : Function.Surjective (toPB i e I eR hfst P) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I)))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  intro y
  have h1 := apply_eq_of_eq (eR_inv_snd_i i e I eR hfst) (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I))))
    (Spec.map (CommRingCat.ofHom (algebraMap A P.Ring))) y)
  have h2 := apply_eq_of_eq (pullback.condition (f := Spec.map (CommRingCat.ofHom
    (algebraMap A (A ⧸ I)))) (g := Spec.map (CommRingCat.ofHom (algebraMap A P.Ring)))) y
  simp only [Scheme.Hom.comp_apply] at h1 h2
  have hy : (hP e P) (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I)))) (Spec.map (CommRingCat.ofHom (algebraMap A P.Ring))) y) =
      i (pullback.snd e i (eR.inv (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I)))) (Spec.map (CommRingCat.ofHom (algebraMap A P.Ring))) y))) := by
    rw [h1, h2, Scheme.Hom.comp_apply]
  obtain ⟨v, hv, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := hP e P) (g := i) _ _ hy
  refine ⟨v, (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I))))
    (Spec.map (CommRingCat.ofHom (algebraMap A P.Ring)))).isClosedEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, toPB_snd]
  exact hv

variable {B : Type u} [CommRing B] [Algebra (A ⧸ I) B] (W : Z.Etale)
  (b0 : Spec (.of B) ⟶ W.left)
  (hb : b0 ≫ W.hom = Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ I) B)) ≫ eR.inv ≫
    pullback.snd e i)
  (g : B) (E : Localization.Away g ≃ₐ[A ⧸ I] (A ⧸ I) ⊗[A] P.Ring)

/-- The map `V_Z ⟶ W`. -/
def liftMap : pullback (hP e P) i ⟶ W.left :=
  toPB i e I eR hfst P ≫ (pullbackSpecIso A (A ⧸ I) P.Ring).hom ≫
    Spec.map (CommRingCat.ofHom E.toAlgHom.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g))) ≫ b0

theorem ring_comp :
    CommRingCat.ofHom (algebraMap (A ⧸ I) B) ≫
      CommRingCat.ofHom (algebraMap B (Localization.Away g)) ≫
        CommRingCat.ofHom E.toAlgHom.toRingHom =
      CommRingCat.ofHom (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] P.Ring)) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  show E (algebraMap B (Localization.Away g) (algebraMap (A ⧸ I) B r)) = _
  rw [← IsScalarTower.algebraMap_apply, E.commutes]
  rfl

@[reassoc]
theorem spec_comp :
    Spec.map (CommRingCat.ofHom E.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ I) B)) =
      Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] P.Ring))) := by
  rw [← ring_comp I P g E, Spec.map_comp, Spec.map_comp, Category.assoc]

include hb in
theorem liftMap_w : liftMap i e I eR hfst P W b0 g E ≫ W.hom = pullback.snd (hP e P) i := by
  simp only [liftMap, Category.assoc]
  rw [hb, spec_comp_assoc, pullbackSpecIso_hom_fst'_assoc, toPB_fst_assoc, Iso.hom_inv_id_assoc,
    toZ0, pullback.lift_snd]

theorem liftMap_hit (q : Spec (.of B)) (hq : g ∉ q.asIdeal) :
    ∃ v, liftMap i e I eR hfst P W b0 g E v = b0 q := by
  have hr := PrimeSpectrum.localization_away_comap_range (Localization.Away g) g
  obtain ⟨c, hc⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away g))) := by
    rw [hr]; exact hq
  have hE : Spec.map (CommRingCat.ofHom E.symm.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom E.toAlgHom.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    show E.symm (E x) = x
    exact E.symm_apply_apply x
  have hd : Spec.map (CommRingCat.ofHom E.toAlgHom.toRingHom)
      (Spec.map (CommRingCat.ofHom E.symm.toAlgHom.toRingHom) c) = c := by
    rw [← Scheme.Hom.comp_apply, hE]; rfl
  obtain ⟨v, hv⟩ := toPB_surjective i e I eR hfst P
    ((pullbackSpecIso A (A ⧸ I) P.Ring).inv (Spec.map (CommRingCat.ofHom E.symm.toAlgHom.toRingHom) c))
  refine ⟨v, ?_⟩
  rw [liftMap, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
    Scheme.Hom.comp_apply, hv, Scheme.inv_hom_apply, hd]
  exact congrArg b0 hc

end Local

section Global

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- **Pointwise cover density**: every point of an etale `Z`-scheme is hit by a map from the
base change of an etale `X`-scheme. -/
theorem exists_etPull_hit (W : Z.Etale) (w : W.left) :
    ∃ (V : X.Etale) (a : (etPull i).obj V ⟶ W) (v : ((etPull i).obj V).left), a.left v = w := by
  let 𝒰 := X.affineOpenCover
  set j := 𝒰.idx (i (W.hom w)) with hj
  obtain ⟨a0, ha0⟩ := 𝒰.covers (i (W.hom w))
  let e := 𝒰.f j
  obtain ⟨I, eR, hfst⟩ := IsClosedImmersion.Spec_iff.1
    (inferInstance : IsClosedImmersion (pullback.fst e i))
  have hfst' : pullback.fst e i =
      eR.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (𝒰.X j) (𝒰.X j ⧸ I))) := by
    rw [hfst, Ideal.Quotient.algebraMap_eq]
  obtain ⟨z0, hz0, hz0'⟩ := Scheme.Pullback.exists_preimage_pullback (f := e) (g := i) a0
    (W.hom w) ha0
  obtain ⟨w0, hw0, hw0'⟩ := Scheme.Pullback.exists_preimage_pullback (f := W.hom)
    (g := pullback.snd e i) w z0 hz0'.symm
  let 𝒱 := (pullback W.hom (pullback.snd e i)).affineOpenCover
  set k := 𝒱.idx w0 with hk
  obtain ⟨q, hq⟩ := 𝒱.covers w0
  let b1 := 𝒱.f k
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (b1 ≫ pullback.snd _ _ ≫ eR.hom)
  let _ : Algebra (𝒰.X j ⧸ I) (𝒱.X k) := ψ.hom.toAlgebra
  have hEt : Etale (Spec.map ψ) := by rw [hψ]; infer_instance
  have : Algebra.Etale (𝒰.X j ⧸ I) (𝒱.X k) :=
    RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 hEt)
  have hqe : q ∈ Algebra.etaleLocus (𝒰.X j ⧸ I) (𝒱.X k) := by
    rw [Algebra.etaleLocus_eq_univ_iff_etale.2 inferInstance]; trivial
  have : Algebra.IsEtaleAt (𝒰.X j ⧸ I) q.asIdeal := hqe
  obtain ⟨g, hg, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := 𝒰.X j ⧸ I) q.asIdeal
  obtain ⟨P, ⟨E⟩⟩ := exists_lift_standardEtale (A := 𝒰.X j)
    (R := 𝒰.X j ⧸ I) Ideal.Quotient.mk_surjective (Localization.Away g)
  let b0 := b1 ≫ pullback.fst W.hom (pullback.snd e i)
  have hb : b0 ≫ W.hom = Spec.map (CommRingCat.ofHom (algebraMap (𝒰.X j ⧸ I) (𝒱.X k))) ≫
      eR.inv ≫ pullback.snd e i := by
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap (𝒰.X j ⧸ I) (𝒱.X k))) = Spec.map ψ := rfl
    rw [h1, hψ]
    simp only [b0, Category.assoc, pullback.condition, Iso.hom_inv_id_assoc]
  obtain ⟨v, hv⟩ := liftMap_hit (A := 𝒰.X j) (B := 𝒱.X k) i e I eR hfst' P W b0 g E q hg
  refine ⟨liftEt e P, MorphismProperty.Over.homMk (liftMap (A := 𝒰.X j) (B := 𝒱.X k) i e I eR hfst' P W b0 g E)
    (liftMap_w (A := 𝒰.X j) (B := 𝒱.X k) i e I eR hfst' P W b0 hb g E), v, ?_⟩
  show liftMap (A := 𝒰.X j) (B := 𝒱.X k) i e I eR hfst' P W b0 g E v = w
  rw [hv]
  show (b1 ≫ pullback.fst W.hom (pullback.snd e i)) q = w
  rw [Scheme.Hom.comp_apply]
  exact (congrArg (pullback.fst W.hom (pullback.snd e i)) hq).trans hw0

/-- **Base change along a closed immersion is cover dense** on small etale sites. -/
instance etPull_isCoverDense : (etPull i).IsCoverDense Z.smallEtaleTopology where
  is_cover W := by
    rw [mem_smallEtale_iff]
    intro w
    obtain ⟨V, a, v, h⟩ := exists_etPull_hit i W w
    exact ⟨_, a, v, Presieve.in_coverByImage _ a, h⟩

end Global

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

/-- A family of geometric points whose images cover `X` is conservative. -/
theorem conservative_family :
    (ObjectProperty.ofObj (fun k => (s k).point)).IsConservativeFamilyOfPoints :=
  Scheme.isConservative_pointSmallEtale (Ω := fun k => (s k).Ω) (fun k => (s k).pt) hs

/-- Zero objects are detected on a covering family of geometric points. -/
theorem isZero_of_family (F : EtSh Λ X) (h : ∀ k, IsZero (((s k).stalkF Λ).obj F)) :
    IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  refine ((conservative_family s hs).jointlyFaithful (ModuleCat.{u} Λ)).map_injective ?_
  rintro ⟨Φ, hΦ⟩
  cases hΦ with
  | mk k => exact (h k).eq_of_src _ _

/-- Exactness is detected on a covering family of geometric points. -/
theorem exact_of_family (S : ShortComplex (EtSh Λ X))
    (h : ∀ k, (S.map ((s k).stalkF Λ)).Exact) : S.Exact := by
  rw [S.exact_iff_isZero_homology]
  refine isZero_of_family Λ s hs _ (fun k => ?_)
  exact ((ShortComplex.exact_iff_isZero_homology _).1 (h k)).of_iso (S.mapHomologyIso _).symm

end Family

section Pts

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Geometric points over `Z` and over the open complement of `Z`. -/
def cutPts : Z ⊕ (complOpens i).toScheme → GeomPt X :=
  Sum.elim (fun z => (geomPtAt z).map i) (fun y => (geomPtAt y).map (complOpens i).ι)

theorem cutPts_cover : ⋃ k, Set.range (cutPts i k).pt = Set.univ := by
  refine Set.eq_univ_of_forall (fun x => Set.mem_iUnion.2 ?_)
  by_cases hx : x ∈ Set.range i
  · obtain ⟨z, rfl⟩ := hx
    refine ⟨.inl z, default, ?_⟩
    show ((geomPtAt z).pt ≫ i) default = i z
    rw [Scheme.Hom.comp_apply]
    exact congrArg i (center_geomPtAt z)
  · have hx' : x ∈ Set.range (complOpens i).ι := by rw [range_complOpens_ι]; exact hx
    obtain ⟨y, rfl⟩ := hx'
    refine ⟨.inr y, default, ?_⟩
    show ((geomPtAt y).pt ≫ (complOpens i).ι) default = (complOpens i).ι y
    rw [Scheme.Hom.comp_apply]
    exact congrArg (complOpens i).ι (center_geomPtAt y)

end Pts

section CoverDense

variable (Λ : Type u) [CommRing Λ] {Z X : Scheme.{u}} (i : Z ⟶ X)
  [(etPull i).IsCoverDense Z.smallEtaleTopology] [(etPull i).IsLocallyFull Z.smallEtaleTopology]

instance push_full : (push i Λ).Full := inferInstance

instance push_faithful : (push i Λ).Faithful := inferInstance

/-- `i^* i_* ⟶ 𝟭` is an isomorphism. -/
instance isIso_pullAdj_counit : IsIso (pullAdj i Λ).counit := inferInstance

variable [IsClosedImmersion i]

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

/-- `i^* i_* ⟶ 𝟭` is an isomorphism for a closed immersion `i`. -/
theorem isIso_closed_counit : IsIso (pullAdj i Λ).counit := isIso_pullAdj_counit Λ i

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtCompact_Exact =====
section

/-!
# S4-EtCompact, part 2: exactness of `f^*`, `i_*` (closed) and `j_!` (open)

Exactness is detected on stalks (`exact_iff_stalk`, `exact_of_family`):
* `f^*` for every `f`: `(f^*F)_s ≅ F_(s ≫ f)` (`pullStalkIso`);
* `i_*` for a closed immersion `i`: at points of `Z`, `i_* ⋙ (t ≫ i)-stalk ≅ t-stalk` (counit iso),
  off `Z` the stalks vanish;
* `j_!` for an open immersion `j`: `lshStalkIso` on the image, zero stalks off it.
Each functor is additive and preserves homology, hence preserves finite limits and colimits.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ]

section Pull

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance pull_preservesMonomorphisms : (pull f Λ).PreservesMonomorphisms :=
  Functor.preservesMonomorphisms_of_map_exact _ (pull_map_exact Λ f)

end Pull

section Closed

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Stalks of `i_*` at the points of `Z`: `i_* ⋙ (t ≫ i)-stalk ≅ t-stalk`. -/
def pushStalkIso (t : GeomPt Z) : push i Λ ⋙ (t.map i).stalkF Λ ≅ t.stalkF Λ :=
  have := isIso_closed_counit Λ i
  Functor.isoWhiskerLeft (push i Λ) (pullStalkIso i Λ t).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (pullAdj i Λ).counit) (t.stalkF Λ) ≪≫ Functor.leftUnitor _

/-- `i_*` is exact for a closed immersion `i`. -/
theorem push_map_exact (S : ShortComplex (EtSh Λ Z)) (hS : S.Exact) :
    (S.map (push i Λ)).Exact := by
  refine exact_of_family Λ (cutPts i) (cutPts_cover i) _ (fun k => ?_)
  rcases k with z | y
  · exact exact_stalk_of_natIso Λ _ _ (pushStalkIso Λ i (geomPtAt z)) S hS
  · exact exact_stalk_of_isZero Λ _
      (fun G => push_stalk_isZero Λ i (complOpens i).ι (disjoint_complOpens i) (geomPtAt y) G) S

instance push_preservesHomology : (push i Λ).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (push_map_exact Λ i)

instance push_preservesFiniteColimits : PreservesFiniteColimits (push i Λ) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

end Closed

section Open

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

instance lsh_preservesMonomorphisms : (lsh j Λ).PreservesMonomorphisms :=
  Functor.preservesMonomorphisms_of_map_exact _ (lsh_map_exact Λ j)

end Open

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtSheaves_SpecPt =====
section

/-!
# S4-EtSheaves, part 29: geometric points of the spectrum of a field

Let `X` be a scheme with `X.fromSpecResidueField x0` an isomorphism ("`X = Spec κ(x0)`"), `Ω` the separable closure
of `κ(x0)` and `Γ = Gal(Ω/κ(x0))`, acting on the fibre functor of `geomPtAt x0` by `a ↦ Spec σ ≫ a` (`galAct`).
For an etale `X`-scheme `Spec R` with `R` a field, `Γ` acts transitively on the fibre (`fiber_transitive`: lifts are
`κ(x0)`-embeddings `R → Ω`, which differ by an automorphism of the normal extension `Ω`). Every fibre element over `U`
comes from the residue-field object `Spec κ(u) → U` (`exists_nbhd`), and a finite subextension `E ⊆ Ω` gives the
etale object `specObj E` whose base point `specPt E` is fixed only by the fixing subgroup of `E`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

/-- A finite separable field extension gives an etale morphism of spectra. -/
theorem etale_specMap_field (K E : Type u) [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
    [Algebra.IsSeparable K E] : Etale (Spec.map (CommRingCat.ofHom (algebraMap K E))) :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).2 (RingHom.etale_algebraMap.2
    ⟨Algebra.FormallyEtale.of_isSeparable K E, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩)

/-- **The residue field extension of an etale morphism is etale** (finite separable). -/
theorem etale_residueFieldMap {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (x : X) :
    Etale (Spec.map (f.residueFieldMap x)) := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have : Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact AlgebraicGeometry.FormallyUnramified.stalkMap f x
  have e : algebraMap (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) = (f.residueFieldMap x).hom := by
    ext r
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    rfl
  have h2 : (algebraMap (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x))).Etale := RingHom.etale_algebraMap.2
    ⟨Algebra.FormallyEtale.of_isSeparable _ _, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  rw [e] at h2
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).2 h2

/-- A scheme isomorphic to the spectrum of a residue field has one point. -/
theorem subsingleton_of_isIso {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] : Subsingleton X :=
  ⟨fun y z => by
    rw [← Scheme.inv_hom_apply (asIso (X.fromSpecResidueField x0)) y,
      ← Scheme.inv_hom_apply (asIso (X.fromSpecResidueField x0)) z,
      Subsingleton.elim ((asIso (X.fromSpecResidueField x0)).inv y) ((asIso (X.fromSpecResidueField x0)).inv z)]⟩

theorem isIso_fromSpecResidueField {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] (y : X) :
    IsIso (X.fromSpecResidueField y) := by
  haveI := subsingleton_of_isIso x0
  obtain rfl : y = x0 := Subsingleton.elim y x0
  infer_instance

variable {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)]

variable (E : IntermediateField (X.residueField x0) (SeparableClosure (X.residueField x0)))
  [FiniteDimensional (X.residueField x0) E]

theorem etale_specObj : Etale (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x0) E)) ≫
    X.fromSpecResidueField x0) := by
  haveI := etale_specMap_field (X.residueField x0) E
  infer_instance

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_CdOne_Field =====
section

/-!
# S4-PD (3), field layer: `HypL` for `Gal(Ω/E₀)` from Tsen + Kummer

Let `Ω/E₀` be a (possibly infinite) Galois extension with a primitive `l`-th root of unity in `E₀`, such that every
finite subextension `E/E₀` is C1 and satisfies the **Kummer closure** property: if `L/E` is a finite Galois
subextension and `b ∈ Lˣ` has `σ b / b ∈ Lˣˡ` for all `σ ∈ Gal(L/E)`, then some `a·b` (`a ∈ Eˣ`) has an `l`-th root
in `Ω` (for `Ω` the maximal unramified extension this is where `Pic(V̄)/l = 0` enters). Then `HypL l Gal(Ω/E₀)`
holds (`hypL_of_field`): for open `N ⊴ Q` with `Q/N` an `l`-group, `E := Ω^Q`, `L := Ω^N`, a `ℤ/l`-valued
2-cocycle on `Q` factoring through `Q/N = Gal(L/E)` is killed in `Gal(Ω/E) = Q` by `exists_kummer_data` and
`emb_coboundary`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open IntermediateField RamanujanPetersson.Tsen Topology

variable {E₀ Ω : Type*} [Field E₀] [Field Ω] [Algebra E₀ Ω] [IsGalois E₀ Ω]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **`HypL` from field theory.** If every finite subextension of `Ω/E₀` is C1 and has the Kummer closure
property, and `E₀` contains a primitive `l`-th root of unity, then `Gal(Ω/E₀)` satisfies `HypL l`. -/
theorem hypL_of_field (l : ℕ) [hl : Fact l.Prime] {ζ : E₀} (hζ : IsPrimitiveRoot ζ l)
    (hC1 : ∀ E : IntermediateField E₀ Ω, FiniteDimensional E₀ E → IsC1 E)
    (hKum : ∀ (E : IntermediateField E₀ Ω) (L : IntermediateField E Ω), FiniteDimensional E₀ E →
      FiniteDimensional E L → IsGalois E L → ∀ b : Lˣ, (∀ σ : Gal(L/E), ∃ c : Lˣ, σ • b / b = c ^ l) →
      ∃ a : E, a ≠ 0 ∧ ∃ y : Ω, y ^ l = algebraMap E Ω a * ((b : L) : Ω)) :
    HypL l Gal(Ω/E₀) := by
  classical
  intro Q N hQ hN hNQ hnorm hlq f hf hc hinv
  have hQE : (fixedField Q).fixingSubgroup = Q := fix_fixed_of_isOpen Q hQ
  have hNL : (fixedField N).fixingSubgroup = N := fix_fixed_of_isOpen N hN
  have hEL : fixedField Q ≤ fixedField N := fixedField_le hNQ
  have hfinE : FiniteDimensional E₀ (fixedField Q) := finiteDimensional_fixedField_of_isOpen Q hQ
  have : FiniteDimensional E₀ (fixedField N) := finiteDimensional_fixedField_of_isOpen N hN
  have : FiniteDimensional (fixedField Q) (extendScalars hEL) := finiteDimensional_extendScalars hEL
  have hGal : IsGalois (fixedField Q) (extendScalars hEL) := isGalois_extendScalars hQ hN hnorm hEL
  set E := fixedField Q with hE
  set L := extendScalars hEL with hL
  set ρ : Gal(Ω/E) →* Gal(L/E) := AlgEquiv.restrictNormalHom (K₁ := Ω) L with hρ
  have hρs : Function.Surjective ρ := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := L) Ω
  let ι : Q ≃* Gal(Ω/E) := (MulEquiv.subgroupCongr hQE.symm).trans (fixingSubgroupEquiv E)
  let π : Q →* Gal(L/E) := ρ.comp ι.toMonoidHom
  have hπs : Function.Surjective π := hρs.comp ι.surjective
  have hπx : ∀ (σ : Q) (x : L), ((π σ x : L) : Ω) = (σ : Gal(Ω/E₀)) x := fun σ x =>
    AlgEquiv.restrictNormalHom_apply L (ι σ) x
  -- the kernel of `π` is `N`
  have hker : ∀ σ τ : Q, π σ = π τ → (τ : Gal(Ω/E₀))⁻¹ * σ ∈ N := by
    intro σ τ hστ
    rw [← hNL, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h1 := hπx σ ⟨x, hx⟩
    rw [hστ, hπx τ ⟨x, hx⟩] at h1
    rw [AlgEquiv.mul_apply, ← h1, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have hN1 : ∀ σ : Q, (σ : Gal(Ω/E₀)) ∈ N → π σ = 1 := by
    intro σ hσ
    rw [← hNL, IntermediateField.mem_fixingSubgroup_iff] at hσ
    ext x
    rw [hπx]
    exact hσ x x.2
  have hinv' : ∀ σ σ' τ τ' : Q, π σ = π σ' → π τ = π τ' →
      f ((σ : Gal(Ω/E₀)), (τ : Gal(Ω/E₀))) = f ((σ' : Gal(Ω/E₀)), (τ' : Gal(Ω/E₀))) := by
    intro σ σ' τ τ' h1 h2
    have := hinv σ' σ'.2 τ' τ'.2 _ (hker σ σ' h1) _ (hker τ τ' h2)
    simpa only [mul_inv_cancel_left] using this
  -- the descended cocycle on `Gal(L/E)`
  let lift : Gal(L/E) → Q := Function.surjInv hπs
  have hlift : ∀ s, π (lift s) = s := Function.surjInv_eq hπs
  let fb : Gal(L/E) × Gal(L/E) → ZMod l := fun p => f ((lift p.1 : Gal(Ω/E₀)), (lift p.2 : Gal(Ω/E₀)))
  have hfb : ∀ σ τ : Q, fb (π σ, π τ) = f ((σ : Gal(Ω/E₀)), (τ : Gal(Ω/E₀))) := fun σ τ =>
    hinv' _ _ _ _ (hlift _) (hlift _)
  have hcoc : ∀ g h j, fb (g * h, j) + fb (g, h) = fb (h, j) + fb (g, h * j) := by
    intro g h j
    obtain ⟨a, rfl⟩ := hπs g
    obtain ⟨b, rfl⟩ := hπs h
    obtain ⟨c, rfl⟩ := hπs j
    rw [← map_mul, ← map_mul, hfb, hfb, hfb, hfb]
    exact hc a a.2 b b.2 c c.2
  have hG : IsPGroup l Gal(L/E) := by
    intro s
    obtain ⟨σ, rfl⟩ := hπs s
    obtain ⟨k, hk⟩ := hlq σ σ.2
    refine ⟨k, ?_⟩
    rw [← map_pow]
    exact hN1 _ (by rw [SubmonoidClass.coe_pow]; exact hk)
  have hζE : IsPrimitiveRoot (algebraMap E₀ E ζ) l := hζ.map_of_injective (algebraMap E₀ E).injective
  have hζE0 : algebraMap E₀ E ζ ≠ 0 := hζE.ne_zero hl.out.ne_zero
  obtain ⟨β, b, hβ, hb⟩ := exists_kummer_data (hC1 E hfinE) l hG hζE hζE0 fb hcoc
  obtain ⟨a, ha, y, hy⟩ := hKum E L hfinE inferInstance hGal b (fun σ => ⟨β σ, hb σ⟩)
  obtain ⟨γ₀, hγ₀, hγ₀'⟩ := emb_coboundary L hζE hζE0 fb β b hβ hb a ha y hy
  -- the cochain on `Gal(Ω/E₀)`
  let γ : Gal(Ω/E₀) → ZMod l := fun g => if h : g ∈ Q then γ₀ (ι ⟨g, h⟩) else 0
  have hstab : IsOpen (MulAction.stabilizer Gal(Ω/E₀) y : Set Gal(Ω/E₀)) :=
    stabilizer_isOpen_of_isIntegral y
  refine ⟨γ, lc_of_coset (N ⊓ MulAction.stabilizer Gal(Ω/E₀) y) (hN.inter hstab) γ ?_, ?_⟩
  · intro g w hw
    have hwN : w ∈ N := (Subgroup.mem_inf.mp hw).1
    have hwy : w y = y := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hw).2
    by_cases hg : g ∈ Q
    · have hgw : g * w ∈ Q := Q.mul_mem hg (hNQ hwN)
      rw [show γ (g * w) = γ₀ (ι ⟨g * w, hgw⟩) from dif_pos hgw,
        show γ g = γ₀ (ι ⟨g, hg⟩) from dif_pos hg]
      apply hγ₀'
      · show π ⟨g * w, hgw⟩ = π ⟨g, hg⟩
        rw [show (⟨g * w, hgw⟩ : Q) = ⟨g, hg⟩ * ⟨w, hNQ hwN⟩ from rfl, map_mul,
          hN1 ⟨w, hNQ hwN⟩ hwN, mul_one]
      · show (g * w) y = g y
        rw [AlgEquiv.mul_apply, hwy]
    · have hgw : g * w ∉ Q := fun h => hg (by simpa using Q.mul_mem h (Q.inv_mem (hNQ hwN)))
      rw [show γ (g * w) = 0 from dif_neg hgw, show γ g = 0 from dif_neg hg]
  · intro g hg h hh
    rw [show γ g = γ₀ (ι ⟨g, hg⟩) from dif_pos hg, show γ h = γ₀ (ι ⟨h, hh⟩) from dif_pos hh,
      show γ (g * h) = γ₀ (ι ⟨g * h, Q.mul_mem hg hh⟩) from dif_pos (Q.mul_mem hg hh)]
    have := hγ₀ (ι ⟨g, hg⟩) (ι ⟨h, hh⟩)
    rw [← map_mul] at this
    rw [← hfb ⟨g, hg⟩ ⟨h, hh⟩]
    exact this

end RamanujanPetersson.CdOne


end


