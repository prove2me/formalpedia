-- Prove2me | Definitions.Def_RPLib_S4_CDPack42
-- name    : RPLib_S4_CDPack42
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:39:05.601645+00:00
-- url     : https://prove2.me/theorems/e120072d-26d9-4634-aa67-67f06e2638a2
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 42 of 71
-- statement:
--   Part 42 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacSymB_Glue`: S4-JacSymB, file G1: gluing the charts `Sym^g B_A` to `Sym^g X` (L12)
--   * `Def_RP_JacSymB_Cover`: S4-JacSymB, file G2: the structure morphism `Sym^g X → Spec k`, finite type, quasi-compact (L12)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack37
import Definitions.Def_RPLib_S4_CDPack25

/-!
# Curve-duality library package, part 42 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacSymB_Glue`: S4-JacSymB, file G1: gluing the charts `Sym^g B_A` to `Sym^g X` (L12)
* `Def_RP_JacSymB_Cover`: S4-JacSymB, file G2: the structure morphism `Sym^g X → Spec k`, finite type, quasi-compact (L12)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacSymB_Glue =====
section

/-!
# S4-JacSymB, file G1: gluing the charts `Sym^g B_A` to `Sym^g X` (L12)

The charts `Spec Sym^g B_A` (`A` a nonempty finite subset of `k`) form a diagram of open immersions
(`Sym^g B_A' = (Sym^g B_A)[1/N w]`, file SymLoc), and the diagram is locally directed: a prime of `Sym^g B_K` that
avoids `N w_{K,I}` and `N w_{K,J}` avoids `N w_{K,I ∪ J}`, because `w_{K,I} w_{K,J} = w_{K,I ∪ J} w_{K,(I∖K) ∩ (J∖K)}`.
`Sym^g X` is the colimit (Mathlib's locally directed gluing).
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite

namespace RamanujanPetersson.JacSym

section GlueAlg

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F] {x : F} {g : ℕ}

variable (x g) in
/-- The restriction map `Sym^g B_A → Sym^g B_A'` for `A ⊆ A'`. -/
noncomputable def chartMap {A A' : Finset k} (h : A ⊆ A') :
    SymRing k (chartRing x A) g →ₐ[k] SymRing k (chartRing x A') g :=
  symMap (Subalgebra.inclusion (chartRing_mono x h))

theorem chartMap_refl {A : Finset k} (h : A ⊆ A) : chartMap x g h = AlgHom.id k _ := by
  rw [chartMap, Subalgebra.inclusion_self, symMap_id]

theorem chartMap_trans {A A' A'' : Finset k} (h1 : A ⊆ A') (h2 : A' ⊆ A'') :
    (chartMap x g h2).comp (chartMap x g h1) = chartMap x g (h1.trans h2) := by
  have e : (Subalgebra.inclusion (chartRing_mono x h2)).comp (Subalgebra.inclusion (chartRing_mono x h1)) =
      Subalgebra.inclusion (chartRing_mono x (h1.trans h2)) :=
    AlgHom.ext fun y => Subalgebra.inclusion_inclusion (chartRing_mono x h1) (chartRing_mono x h2) y
  rw [chartMap, chartMap, chartMap, ← symMap_comp, e]

theorem isUnit_inclusion_wt [DecidableEq k] (hx : Transcendental k x) {A A' : Finset k} (h : A ⊆ A') {c0 : k} (hc0 : c0 ∈ A) :
    IsUnit (Subalgebra.inclusion (chartRing_mono x h) ⟨wt x c0 (A' \ A), wt_mem_chartRing hx hc0 _⟩) :=
  IsUnit.of_mul_eq_one ⟨(wt x c0 (A' \ A))⁻¹, wt_inv_mem_chartRing hx Finset.sdiff_subset c0⟩
    (Subtype.ext (mul_inv_cancel₀ (wt_ne_zero hx c0 _)))

theorem isLocalization_chartMap [DecidableEq k] (hx : Transcendental k x) {A A' : Finset k} (h : A ⊆ A') {c0 : k}
    (hc0 : c0 ∈ A) :
    letI := (chartMap x g h).toRingHom.toAlgebra
    IsLocalization.Away (normS k (g := g) (⟨wt x c0 (A' \ A), wt_mem_chartRing hx hc0 _⟩ : chartRing x A))
      (SymRing k (chartRing x A') g) :=
  isLocalization_symMap _ (Subalgebra.inclusion_injective _) _ (isUnit_inclusion_wt hx h hc0) fun b' => by
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartRing hx hc0 b'.2
    exact ⟨n, ⟨_, hn⟩, Subtype.ext (by simp)⟩

theorem mem_basicOpen_of_comap [DecidableEq k] (hx : Transcendental k x) {A A' : Finset k} (h : A ⊆ A') {c0 : k}
    (hc0 : c0 ∈ A) (p : PrimeSpectrum (SymRing k (chartRing x A') g)) :
    normS k (g := g) (⟨wt x c0 (A' \ A), wt_mem_chartRing hx hc0 _⟩ : chartRing x A) ∉
      (PrimeSpectrum.comap (chartMap x g h).toRingHom p).asIdeal := by
  letI := (chartMap x g h).toRingHom.toAlgebra
  haveI := isLocalization_chartMap (g := g) hx h hc0
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe,
    ← PrimeSpectrum.localization_away_comap_range (SymRing k (chartRing x A') g)]
  exact ⟨p, rfl⟩

/-- Local directedness of the chart diagram, on prime spectra. -/
theorem exists_prime_glue [DecidableEq k] (hx : Transcendental k x) {K I J : Finset k} (hK : K.Nonempty)
    (hKI : K ⊆ I) (hKJ : K ⊆ J) (p : PrimeSpectrum (SymRing k (chartRing x I) g))
    (p' : PrimeSpectrum (SymRing k (chartRing x J) g))
    (h : PrimeSpectrum.comap (chartMap x g hKI).toRingHom p = PrimeSpectrum.comap (chartMap x g hKJ).toRingHom p') :
    ∃ P : PrimeSpectrum (SymRing k (chartRing x (I ∪ J)) g),
      PrimeSpectrum.comap (chartMap x g (Finset.subset_union_left : I ⊆ I ∪ J)).toRingHom P = p ∧
      PrimeSpectrum.comap (chartMap x g (Finset.subset_union_right : J ⊆ I ∪ J)).toRingHom P = p' := by
  obtain ⟨c0, hc0⟩ := hK
  have hKL : K ⊆ I ∪ J := hKI.trans Finset.subset_union_left
  set q := PrimeSpectrum.comap (chartMap x g hKI).toRingHom p with hq
  have hI := mem_basicOpen_of_comap (g := g) (A := K) (A' := I) hx hKI hc0 p
  have hJ := mem_basicOpen_of_comap (g := g) (A := K) (A' := J) hx hKJ hc0 p'
  rw [← h] at hJ
  have hprod : (⟨wt x c0 (I \ K), wt_mem_chartRing hx hc0 _⟩ : chartRing x K) *
      ⟨wt x c0 (J \ K), wt_mem_chartRing hx hc0 _⟩ = ⟨wt x c0 ((I ∪ J) \ K), wt_mem_chartRing hx hc0 _⟩ *
      ⟨wt x c0 ((I \ K) ∩ (J \ K)), wt_mem_chartRing hx hc0 _⟩ := by
    apply Subtype.ext
    change wt x c0 (I \ K) * wt x c0 (J \ K) = wt x c0 ((I ∪ J) \ K) * wt x c0 ((I \ K) ∩ (J \ K))
    rw [Finset.union_sdiff_distrib, wt, wt, wt, wt, Finset.prod_union_inter]
  have hL : normS k (g := g) (⟨wt x c0 ((I ∪ J) \ K), wt_mem_chartRing hx hc0 _⟩ : chartRing x K) ∉ q.asIdeal := by
    intro hmem
    have := q.asIdeal.mul_mem_right
      (normS k (g := g) (⟨wt x c0 ((I \ K) ∩ (J \ K)), wt_mem_chartRing hx hc0 _⟩ : chartRing x K)) hmem
    rw [← normS_mul, ← hprod, normS_mul] at this
    rcases q.isPrime.mem_or_mem this with h1 | h1
    · exact hI h1
    · exact hJ h1
  obtain ⟨P, hP⟩ : q ∈ Set.range (PrimeSpectrum.comap (chartMap x g hKL).toRingHom) := by
    letI := (chartMap x g hKL).toRingHom.toAlgebra
    haveI := isLocalization_chartMap (g := g) hx hKL hc0
    change q ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (SymRing k (chartRing x K) g) (SymRing k (chartRing x (I ∪ J)) g)))
    rw [PrimeSpectrum.localization_away_comap_range (SymRing k (chartRing x (I ∪ J)) g)
      (normS k (g := g) (⟨wt x c0 ((I ∪ J) \ K), wt_mem_chartRing hx hc0 _⟩ : chartRing x K)), SetLike.mem_coe,
      PrimeSpectrum.mem_basicOpen]
    exact hL
  have hinjI : Function.Injective (PrimeSpectrum.comap (chartMap x g hKI).toRingHom) := by
    letI := (chartMap x g hKI).toRingHom.toAlgebra
    haveI := isLocalization_chartMap (g := g) hx hKI hc0
    exact PrimeSpectrum.localization_comap_injective (SymRing k (chartRing x I) g)
      (Submonoid.powers (normS k (g := g) (⟨wt x c0 (I \ K), wt_mem_chartRing hx hc0 _⟩ : chartRing x K)))
  have hinjJ : Function.Injective (PrimeSpectrum.comap (chartMap x g hKJ).toRingHom) := by
    letI := (chartMap x g hKJ).toRingHom.toAlgebra
    haveI := isLocalization_chartMap (g := g) hx hKJ hc0
    exact PrimeSpectrum.localization_comap_injective (SymRing k (chartRing x J) g)
      (Submonoid.powers (normS k (g := g) (⟨wt x c0 (J \ K), wt_mem_chartRing hx hc0 _⟩ : chartRing x K)))
  refine ⟨P, hinjI ?_, hinjJ ?_⟩
  · rw [← PrimeSpectrum.comap_comp_apply]
    change PrimeSpectrum.comap ((chartMap x g (Finset.subset_union_left : I ⊆ I ∪ J)).comp
      (chartMap x g hKI)).toRingHom P = _
    rw [chartMap_trans]
    exact hP
  · rw [← PrimeSpectrum.comap_comp_apply]
    change PrimeSpectrum.comap ((chartMap x g (Finset.subset_union_right : J ⊆ I ∪ J)).comp
      (chartMap x g hKJ)).toRingHom P = _
    rw [chartMap_trans, ← h]
    exact hP

end GlueAlg

section GlueScheme

universe u

variable {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]

/-- Index category of the charts: nonempty finite subsets of `k`. -/
abbrev ChartIdx (k : Type u) : Type u := {A : Finset k // A.Nonempty}

variable (k) in
/-- The chart rings as a functor `A ↦ Sym^g B_A`. -/
noncomputable def chartRingFunctor (x : F) (g : ℕ) : ChartIdx k ⥤ CommRingCat.{u} where
  obj A := CommRingCat.of (SymRing k (chartRing x A.1) g)
  map {A A'} h := CommRingCat.ofHom (chartMap x g (show A.1 ⊆ A'.1 from leOfHom h)).toRingHom
  map_id A := by
    rw [chartMap_refl]
    rfl
  map_comp {A A' A''} h1 h2 := by
    rw [← chartMap_trans (show A.1 ⊆ A'.1 from leOfHom h1) (show A'.1 ⊆ A''.1 from leOfHom h2)]
    rfl

variable (k) in
/-- The chart diagram `A ↦ Spec Sym^g B_A`. -/
noncomputable def symDiagram (x : F) (g : ℕ) : (ChartIdx k)ᵒᵖ ⥤ Scheme.{u} :=
  (chartRingFunctor k x g).op ⋙ Scheme.Spec

variable (k) (x : F) (g : ℕ) [hx : Fact (Transcendental k x)]

instance isOpenImmersion_symDiagram {i j : (ChartIdx k)ᵒᵖ} (f : i ⟶ j) :
    IsOpenImmersion ((symDiagram k x g).map f) := by
  classical
  obtain ⟨c0, hc0⟩ := j.unop.2
  have h : j.unop.1 ⊆ i.unop.1 := leOfHom f.unop
  letI := (chartMap x g h).toRingHom.toAlgebra
  haveI := isLocalization_chartMap (g := g) hx.out h hc0
  exact IsOpenImmersion.of_isLocalization
    (normS k (g := g) (⟨wt x c0 (i.unop.1 \ j.unop.1), wt_mem_chartRing hx.out hc0 _⟩ : chartRing x j.unop.1))

instance isLocallyDirected_symDiagram : (symDiagram k x g ⋙ Scheme.forget).IsLocallyDirected where
  cond {i j l} fi fj xi xj hij := by
    classical
    obtain ⟨P, hP1, hP2⟩ := exists_prime_glue (g := g) hx.out l.unop.2 (show l.unop.1 ⊆ i.unop.1 from leOfHom fi.unop)
      (show l.unop.1 ⊆ j.unop.1 from leOfHom fj.unop) xi xj hij
    exact ⟨op ⟨i.unop.1 ∪ j.unop.1, i.unop.2.mono Finset.subset_union_left⟩,
      (homOfLE (show i.unop ≤ ⟨i.unop.1 ∪ j.unop.1, i.unop.2.mono Finset.subset_union_left⟩ from
        Finset.subset_union_left)).op,
      (homOfLE (show j.unop ≤ ⟨i.unop.1 ∪ j.unop.1, i.unop.2.mono Finset.subset_union_left⟩ from
        Finset.subset_union_right)).op, P, hP1, hP2⟩

/-- `Sym^g X`: the charts `Spec Sym^g B_A` glued along their common opens. -/
noncomputable def SymX : Scheme.{u} := Limits.colimit (symDiagram k x g)

instance isOpenImmersion_ι (A : (ChartIdx k)ᵒᵖ) : IsOpenImmersion (Limits.colimit.ι (symDiagram k x g) A) :=
  inferInstance

end GlueScheme

end RamanujanPetersson.JacSym

end

-- ===== S4.Def_RP_JacSymB_Cover =====
section

/-!
# S4-JacSymB, file G2: the structure morphism `Sym^g X → Spec k`, finite type, quasi-compact (L12)

`toSpecK` is induced by the `k`-algebra structures of the charts. It is locally of finite type (the chart rings are
finitely generated). `Sym^g X` is quasi-compact: for any `g + 1` distinct `c_j ∈ k` the singleton charts `{c_j}` cover
it. Algebraic core: for a prime `p` of `Sym^g B_A` some `N w_{c_j} ∉ p`, because a prime of `B_A` contains at most one of
the elements `w_c = (x - c)/(x - c0) = 1 + (c0 - c)/(x - c0)` (lying over + pigeonhole on the `g` factors).
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite Limits

namespace RamanujanPetersson.JacSym

section CoverAlg

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F] {x : F} {g : ℕ}

theorem wt_singleton_eq (hx : Transcendental k x) (c0 c : k) :
    wt x c0 {c} = 1 + algebraMap k F (c0 - c) * uc x c0 := by
  rw [wt, Finset.prod_singleton, sub_mul_uc hx]

theorem exists_not_mem_normS (hx : Transcendental k x) {A : Finset k} {c0 : k} (hc0 : c0 ∈ A) (C : Finset k)
    (hC : g < C.card) (p : Ideal (SymRing k (chartRing x A) g)) [p.IsPrime] :
    ∃ c ∈ C, normS k (g := g) (⟨wt x c0 {c}, wt_mem_chartRing hx hc0 _⟩ : chartRing x A) ∉ p := by
  classical
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal (XPow k (chartRing x A) g))
    (Ideal.comap_bot_le_of_injective _ (fun a b h => Subtype.ext h))
  by_contra H
  push Not at H
  have H' : ∀ c : C, ∃ l : Fin g, inc l (⟨wt x c0 {c.1}, wt_mem_chartRing hx hc0 _⟩ : chartRing x A) ∈ Q := by
    intro c
    have h1 := H c.1 c.2
    rw [← hQp, Ideal.mem_comap] at h1
    have h2 : (∏ l, inc l (⟨wt x c0 {c.1}, wt_mem_chartRing hx hc0 _⟩ : chartRing x A)) ∈ Q := h1
    obtain ⟨l, -, hl⟩ := Ideal.IsPrime.prod_mem_iff.mp h2
    exact ⟨l, hl⟩
  choose f hf using H'
  obtain ⟨c, c', hne, hcc⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simpa using hC)
  let q : Ideal (chartRing x A) := Q.comap (inc (f c) : chartRing x A →ₐ[k] XPow k (chartRing x A) g)
  have hq : q.IsPrime := Ideal.comap_isPrime _ Q
  have h1 : (⟨wt x c0 {c.1}, wt_mem_chartRing hx hc0 _⟩ : chartRing x A) ∈ q := hf c
  have h2 : (⟨wt x c0 {c'.1}, wt_mem_chartRing hx hc0 _⟩ : chartRing x A) ∈ q := by
    change _ ∈ Q.comap _
    rw [Ideal.mem_comap, hcc]
    exact hf c'
  have hu : (⟨uc x c0, polyA_le_chartRing x A (uc_mem_polyA x hc0)⟩ : chartRing x A) ∈ q := by
    have hd := q.sub_mem h1 h2
    have e : (⟨wt x c0 {c.1}, wt_mem_chartRing hx hc0 _⟩ : chartRing x A) - ⟨wt x c0 {c'.1}, wt_mem_chartRing hx hc0 _⟩ =
        algebraMap k (chartRing x A) (c'.1 - c.1) * ⟨uc x c0, polyA_le_chartRing x A (uc_mem_polyA x hc0)⟩ := by
      apply Subtype.ext
      simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
      rw [wt_singleton_eq hx, wt_singleton_eq hx, map_sub, map_sub, map_sub]
      ring
    rw [e] at hd
    have hne' : c'.1 - c.1 ≠ 0 := sub_ne_zero.mpr (fun h => hne (Subtype.ext h.symm))
    have := q.mul_mem_left (algebraMap k (chartRing x A) (c'.1 - c.1)⁻¹) hd
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hne', map_one, one_mul] at this
  have h1' : (1 : chartRing x A) ∈ q := by
    have e : (1 : chartRing x A) = ⟨wt x c0 {c.1}, wt_mem_chartRing hx hc0 _⟩ -
        algebraMap k (chartRing x A) (c0 - c.1) * ⟨uc x c0, polyA_le_chartRing x A (uc_mem_polyA x hc0)⟩ := by
      apply Subtype.ext
      simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, OneMemClass.coe_one]
      rw [wt_singleton_eq hx]
      ring
    rw [e]
    exact q.sub_mem h1 (q.mul_mem_left _ hu)
  exact hq.ne_top ((Ideal.eq_top_iff_one _).mpr h1')

end CoverAlg

section CoverScheme

universe u

variable (k : Type u) [Field k] {F : Type u} [Field F] [Algebra k F] (x : F) (g : ℕ) [hx : Fact (Transcendental k x)]

/-- The cocone `Spec Sym^g B_A → Spec k`. -/
noncomputable def toSpecKCocone : Cocone (symDiagram k x g) where
  pt := Spec (CommRingCat.of k)
  ι :=
    { app := fun A => Spec.map (CommRingCat.ofHom (algebraMap k (SymRing k (chartRing x A.unop.1) g)))
      naturality := fun A A' f => by
        dsimp [symDiagram, chartRingFunctor]
        rw [Category.comp_id, ← Spec.map_comp]
        congr 1
        ext r
        simp }

/-- The structure morphism `Sym^g X → Spec k`. -/
noncomputable def toSpecK : SymX k x g ⟶ Spec (CommRingCat.of k) := colimit.desc _ (toSpecKCocone k x g)

@[reassoc]
theorem ι_toSpecK (A : (ChartIdx k)ᵒᵖ) : colimit.ι (symDiagram k x g) A ≫ toSpecK k x g =
    Spec.map (CommRingCat.ofHom (algebraMap k (SymRing k (chartRing x A.unop.1) g))) :=
  colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency.types false in
instance locallyOfFiniteType_toSpecK [FiniteDimensional (IntermediateField.adjoin k {x}) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k {x}) F] : LocallyOfFiniteType (toSpecK k x g) := by
  change @LocallyOfFiniteType (colimit (symDiagram k x g)) _ (toSpecK k x g)
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType)
    (Scheme.IsLocallyDirected.openCover (symDiagram k x g))]
  intro (A : (ChartIdx k)ᵒᵖ)
  have h : LocallyOfFiniteType (colimit.ι (symDiagram k x g) A ≫ toSpecK k x g) := by
    rw [ι_toSpecK]
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k (SymRing k (chartRing x A.unop.1) g))))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    have := finiteType_chartRing (k := k) hx.out A.unop.2
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  exact h

theorem exists_mem_range_ι_single (C : Finset k) (hC : g < C.card) (P : SymX k x g) :
    ∃ c ∈ C, P ∈ Set.range (colimit.ι (symDiagram k x g) (op ⟨{c}, Finset.singleton_nonempty c⟩)) := by
  classical
  obtain ⟨A, p, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (symDiagram k x g) P
  by_cases hCA : ∃ c ∈ C, c ∈ A.unop.1
  · obtain ⟨c, hcC, hcA⟩ := hCA
    refine ⟨c, hcC, (symDiagram k x g).map (homOfLE (show (⟨{c}, Finset.singleton_nonempty c⟩ : ChartIdx k) ≤ A.unop
      from Finset.singleton_subset_iff.mpr hcA)).op p, ?_⟩
    rw [← Scheme.Hom.comp_apply, colimit.w]
  · push Not at hCA
    obtain ⟨c0, hc0⟩ := A.unop.2
    let p' : PrimeSpectrum (SymRing k (chartRing x A.unop.1) g) := p
    haveI := p'.isPrime
    obtain ⟨c, hcC, hc⟩ := exists_not_mem_normS (g := g) hx.out hc0 C hC p'.asIdeal
    let A' : ChartIdx k := ⟨A.unop.1 ∪ {c}, A.unop.2.mono Finset.subset_union_left⟩
    have hsub : A.unop.1 ⊆ A'.1 := Finset.subset_union_left
    have e : A'.1 \ A.unop.1 = {c} := by
      change (A.unop.1 ∪ {c}) \ A.unop.1 = {c}
      rw [Finset.union_sdiff_left, Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_singleton_left]
      exact hCA c hcC
    have e' : (⟨wt x c0 (A'.1 \ A.unop.1), wt_mem_chartRing hx.out hc0 _⟩ : chartRing x A.unop.1) =
        ⟨wt x c0 {c}, wt_mem_chartRing hx.out hc0 _⟩ := Subtype.ext (by rw [e])
    obtain ⟨q, hq⟩ : p' ∈ Set.range (PrimeSpectrum.comap (chartMap x g hsub).toRingHom) := by
      letI := (chartMap x g hsub).toRingHom.toAlgebra
      haveI := isLocalization_chartMap (g := g) hx.out hsub hc0
      change p' ∈ Set.range (PrimeSpectrum.comap
        (algebraMap (SymRing k (chartRing x A.unop.1) g) (SymRing k (chartRing x A'.1) g)))
      rw [PrimeSpectrum.localization_away_comap_range (SymRing k (chartRing x A'.1) g)
        (normS k (g := g) (⟨wt x c0 (A'.1 \ A.unop.1), wt_mem_chartRing hx.out hc0 _⟩ : chartRing x A.unop.1)),
        SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, e']
      exact hc
    let q' : (symDiagram k x g).obj (op A') := q
    have hp : (symDiagram k x g).map (homOfLE (show A.unop ≤ A' from hsub)).op q' = p := hq
    refine ⟨c, hcC, (symDiagram k x g).map (homOfLE (show (⟨{c}, Finset.singleton_nonempty c⟩ : ChartIdx k) ≤ A'
      from Finset.subset_union_right)).op q', ?_⟩
    rw [← hp, ← Scheme.Hom.comp_apply, colimit.w, ← Scheme.Hom.comp_apply, colimit.w]

instance compactSpace_symX [Infinite k] : CompactSpace (SymX k x g) := by
  classical
  obtain ⟨C, hC⟩ := Infinite.exists_subset_card_eq k (g + 1)
  have hcov : (Set.univ : Set (SymX k x g)) =
      ⋃ c ∈ C, Set.range (colimit.ι (symDiagram k x g) (op ⟨{c}, Finset.singleton_nonempty c⟩)) := by
    ext P
    simp only [Set.mem_univ, true_iff]
    obtain ⟨c, hc, h⟩ := exists_mem_range_ι_single k x g C (by omega) P
    exact Set.mem_iUnion₂.mpr ⟨c, hc, h⟩
  rw [← isCompact_univ_iff, hcov]
  refine C.isCompact_biUnion fun c _ => ?_
  haveI : CompactSpace ((symDiagram k x g).obj (op ⟨{c}, Finset.singleton_nonempty c⟩)) :=
    inferInstanceAs (CompactSpace (PrimeSpectrum (SymRing k (chartRing x {c}) g)))
  exact isCompact_range (colimit.ι (symDiagram k x g) _).continuous

set_option backward.isDefEq.respectTransparency.types false in
instance quasiCompact_toSpecK [Infinite k] : QuasiCompact (toSpecK k x g) :=
  HasAffineProperty.iff_of_isAffine.mpr (compactSpace_symX k x g)

end CoverScheme

end RamanujanPetersson.JacSym

end


