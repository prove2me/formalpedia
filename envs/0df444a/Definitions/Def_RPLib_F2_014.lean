-- Prove2me | Definitions.Def_RPLib_F2_014
-- name    : RPLib_F2_014
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T09:09:46.737033+00:00
-- url     : https://prove2.me/theorems/3c401942-ae50-4c7b-bb27-f00443a8bc13
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 014 of 70
-- statement:
--   File 014 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacComplete_AJGlue`: The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces
--   * `S4.Def_RP_JacSymB_Glue`: S4-JacSymB, file G1: gluing the charts `Sym^g B_A` to `Sym^g X` (L12)
--   * `S4.Def_RP_JacSymB_Cover`: S4-JacSymB, file G2: the structure morphism `Sym^g X → Spec k`, finite type, quasi-compact (L12)
--   * `S4.Def_RP_JacSymB_Sep`: S4-JacSymB, file H1: `Sym^g X → Spec k` is separated (L12)
--   * `S4.Def_RP_JacComplete_AJCo`: The Jacobian (unit S4-JacComplete), part `AJCo`: the Abel-Jacobi map on the curve `X1 = Sym¹ X`
--   * `S4.Def_RP_JacComplete_AJSurj`: The Jacobian (unit S4-JacComplete), part `AJSurj` (L19 route AJ: K-point surjectivity of `Σ [Q_i] - g [P0]`)
--   * `S4.Def_RP_JacSymB_GenInt`: S4-JacSymB, file H2d: integrality of `X^g(B)` over the coefficients of `E(w)` (L12, valuative criterion)
--   * `S4.Def_RP_JacSymB_ValAlg`: S4-JacSymB, file H2a: a valuation-ring lemma for the valuative criterion (L12)
--   * `S4.Def_RP_JacSymB_ExistAlg`: S4-JacSymB, file H2c: ring-level valuative existence for `Sym^g X` (L12)
--   * `S4.Def_RP_JacComplete_Proper`: The Jacobian (unit S4-JacComplete), part `Proper`: **L19, the Jacobian is proper**
--   * `S4.Def_RP_CoreB_Dim`: Core B, O1: the heights on the Jacobian are bounded
--   * `S4.Def_RP_JacAlg_Defs`: Core B algebra, part 1: the `DegreeData` interface (unit S4-JacAlg, lemma L1)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_013

/-!
# Ramanujan-Petersson curve library (flat edition), file 014 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacComplete_AJGlue`: The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces
* `S4.Def_RP_JacSymB_Glue`: S4-JacSymB, file G1: gluing the charts `Sym^g B_A` to `Sym^g X` (L12)
* `S4.Def_RP_JacSymB_Cover`: S4-JacSymB, file G2: the structure morphism `Sym^g X → Spec k`, finite type, quasi-compact (L12)
* `S4.Def_RP_JacSymB_Sep`: S4-JacSymB, file H1: `Sym^g X → Spec k` is separated (L12)
* `S4.Def_RP_JacComplete_AJCo`: The Jacobian (unit S4-JacComplete), part `AJCo`: the Abel-Jacobi map on the curve `X1 = Sym¹ X`
* `S4.Def_RP_JacComplete_AJSurj`: The Jacobian (unit S4-JacComplete), part `AJSurj` (L19 route AJ: K-point surjectivity of `Σ [Q_i] - g [P0]`)
* `S4.Def_RP_JacSymB_GenInt`: S4-JacSymB, file H2d: integrality of `X^g(B)` over the coefficients of `E(w)` (L12, valuative criterion)
* `S4.Def_RP_JacSymB_ValAlg`: S4-JacSymB, file H2a: a valuation-ring lemma for the valuative criterion (L12)
* `S4.Def_RP_JacSymB_ExistAlg`: S4-JacSymB, file H2c: ring-level valuative existence for `Sym^g X` (L12)
* `S4.Def_RP_JacComplete_Proper`: The Jacobian (unit S4-JacComplete), part `Proper`: **L19, the Jacobian is proper**
* `S4.Def_RP_CoreB_Dim`: Core B, O1: the heights on the Jacobian are bounded
* `S4.Def_RP_JacAlg_Defs`: Core B algebra, part 1: the `DegreeData` interface (unit S4-JacAlg, lemma L1)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_AJGlue =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces

`B' = Rfin (SynF K F c0)`.
* `locallyOfFiniteType_sR`; the piece index `PIdx K F c0` and the open immersions `pj c0 i : Spec LocR → Spec B'`.
* `pj_kpt` (closed points), `pj_cov` (the pieces cover the closed points), `pj_over`.
The glued map `ajChart` is in part `AJGlue2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
-- the instance diamonds on the nested localizations need nested synthPending (diagnostics, session 20)
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Glue

open Classical
open CategoryTheory AlgebraicGeometry

variable {K : Type u} [Field K]

variable [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (K F) in
/-- The index type of the AJ pieces on the chart `c0`. -/
abbrev PIdx (c0 : K) : Type u :=
  Σ r : ℕ, Σ _ : NuData K (SynF K F c0) (1 + r), Fin r → (Rfin K (SynF K F c0) →ₐ[K] K)

variable (P0 : Place K F) (c0 : K)

end Glue

end RamanujanPetersson.JacComplete


end

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

-- ===== S4.Def_RP_JacSymB_Sep =====
section

/-!
# S4-JacSymB, file H1: `Sym^g X → Spec k` is separated (L12)

Template: Mathlib `ProjectiveSpectrum/Proper.lean` (`isSeparated`). For charts `A, A'` the overlap of `Spec S_A` and
`Spec S_A'` in `Sym^g X` is `Spec S_{A ∪ A'}` (`isPullback_ι_ι`, from `ι_eq_ι_iff`), and
`S_A ⊗_k S_A' → S_{A ∪ A'}` is surjective: `S_{A ∪ A'} = S_A[1/N w]` and `1/N w = N(1/w)` comes from `S_A'`.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite Limits

open scoped TensorProduct

namespace RamanujanPetersson.JacSym

section SepAlg

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F] {x : F} {g : ℕ}

omit [Field k] in
theorem sdiff_subset_union_right [DecidableEq k] (A A' : Finset k) : (A ∪ A') \ A ⊆ A' := by
  intro d hd
  rw [Finset.mem_sdiff, Finset.mem_union] at hd
  tauto

theorem chartMap_normS_inv_mul [DecidableEq k] (hx : Transcendental k x) {A A' : Finset k} {c0 : k} (hc0 : c0 ∈ A) :
    chartMap x g (Finset.subset_union_right : A' ⊆ A ∪ A')
      (normS k (⟨(wt x c0 ((A ∪ A') \ A))⁻¹, wt_inv_mem_chartRing hx (sdiff_subset_union_right A A') c0⟩ :
        chartRing x A')) *
    chartMap x g (Finset.subset_union_left : A ⊆ A ∪ A')
      (normS k (⟨wt x c0 ((A ∪ A') \ A), wt_mem_chartRing hx hc0 _⟩ : chartRing x A)) = 1 := by
  rw [chartMap, chartMap, symMap_normS, symMap_normS, ← normS_mul, ← normS_one (k := k) (g := g)]
  congr 1
  apply Subtype.ext
  simp only [Subalgebra.coe_inclusion, MulMemClass.coe_mul, OneMemClass.coe_one]
  exact inv_mul_cancel₀ (wt_ne_zero hx c0 _)

theorem lift_chartMap_surjective [DecidableEq k] (hx : Transcendental k x) {A A' : Finset k} (hA : A.Nonempty) :
    Function.Surjective (Algebra.TensorProduct.lift (chartMap x g (Finset.subset_union_left : A ⊆ A ∪ A'))
      (chartMap x g (Finset.subset_union_right : A' ⊆ A ∪ A')) (fun _ _ => Commute.all _ _)) := by
  obtain ⟨c0, hc0⟩ := hA
  let _ := (chartMap x g (Finset.subset_union_left : A ⊆ A ∪ A')).toRingHom.toAlgebra
  have _ := isLocalization_chartMap (g := g) hx (Finset.subset_union_left : A ⊆ A ∪ A') hc0
  intro z
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (Submonoid.powers (normS k (g := g)
    (⟨wt x c0 ((A ∪ A') \ A), wt_mem_chartRing hx hc0 _⟩ : chartRing x A))) z
  obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp s.2
  change z * chartMap x g (Finset.subset_union_left : A ⊆ A ∪ A') s =
    chartMap x g (Finset.subset_union_left : A ⊆ A ∪ A') a at h
  rw [← hn, map_pow] at h
  refine ⟨a ⊗ₜ ((normS k (⟨(wt x c0 ((A ∪ A') \ A))⁻¹, wt_inv_mem_chartRing hx (sdiff_subset_union_right A A') c0⟩ :
        chartRing x A')) ^ n), ?_⟩
  have h1 := chartMap_normS_inv_mul (g := g) (A' := A') hx hc0
  rw [mul_comm] at h1
  simp only [Algebra.TensorProduct.lift_tmul, map_pow]
  rw [← h, mul_assoc, ← mul_pow, h1, one_pow, mul_one]

end SepAlg

section SepScheme

universe u

variable (k : Type u) [Field k] {F : Type u} [Field F] [Algebra k F] (x : F) (g : ℕ) [hx : Fact (Transcendental k x)]

/-- The chart `A ∪ A'`, i.e. the overlap of the charts `A` and `A'`. -/
abbrev unionIdx [DecidableEq k] (i j : (ChartIdx k)ᵒᵖ) : ChartIdx k :=
  ⟨i.unop.1 ∪ j.unop.1, i.unop.2.mono Finset.subset_union_left⟩

omit hx in
theorem symDiagram_map {i j : (ChartIdx k)ᵒᵖ} (f : i ⟶ j) :
    (symDiagram k x g).map f = Spec.map (CommRingCat.ofHom (chartMap x g (leOfHom f.unop)).toRingHom) :=
  rfl

theorem isPullback_ι_ι [DecidableEq k] (i j : (ChartIdx k)ᵒᵖ) :
    IsPullback ((symDiagram k x g).map (homOfLE (show i.unop ≤ unionIdx k i j from Finset.subset_union_left)).op)
      ((symDiagram k x g).map (homOfLE (show j.unop ≤ unionIdx k i j from Finset.subset_union_right)).op)
      (colimit.ι (symDiagram k x g) i) (colimit.ι (symDiagram k x g) j) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (by rw [colimit.w, colimit.w]) ?_
  apply TopologicalSpace.Opens.ext
  ext P
  simp only [Scheme.Hom.coe_preimage, Scheme.Hom.coe_opensRange, Set.mem_preimage, Set.mem_range]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨l, fi, fj, y, hy1, hy2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (symDiagram k x g)).mp hq
    have hU : unionIdx k i j ≤ l.unop := Finset.union_subset (leOfHom fi.unop) (leOfHom fj.unop)
    refine ⟨(symDiagram k x g).map (homOfLE hU).op y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp]
    have e : (homOfLE hU).op ≫ (homOfLE (show j.unop ≤ unionIdx k i j from Finset.subset_union_right)).op = fj :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [e, hy2]
  · rintro ⟨y, rfl⟩
    exact ⟨(symDiagram k x g).map (homOfLE (show i.unop ≤ unionIdx k i j from Finset.subset_union_left)).op y, by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, colimit.w, colimit.w]⟩

/-- `S_A ⊗_k S_A' → S_{A ∪ A'}` (surjective, `lift_chartMap_surjective`). -/
noncomputable def overlapHom [DecidableEq k] (i j : (ChartIdx k)ᵒᵖ) :
    CommRingCat.of (SymRing k (chartRing x i.unop.1) g ⊗[k] SymRing k (chartRing x j.unop.1) g) ⟶
      CommRingCat.of (SymRing k (chartRing x (i.unop.1 ∪ j.unop.1)) g) :=
  CommRingCat.ofHom (Algebra.TensorProduct.lift (chartMap x g (Finset.subset_union_left : i.unop.1 ⊆ i.unop.1 ∪ j.unop.1))
    (chartMap x g (Finset.subset_union_right : j.unop.1 ⊆ i.unop.1 ∪ j.unop.1)) (fun _ _ => Commute.all _ _)).toRingHom

omit hx in
theorem overlap_fst [DecidableEq k] (i j : (ChartIdx k)ᵒᵖ) :
    (symDiagram k x g).map (homOfLE (show i.unop ≤ unionIdx k i j from Finset.subset_union_left)).op =
      Spec.map (CommRingCat.ofHom ((overlapHom k x g i j).hom.comp Algebra.TensorProduct.includeLeftRingHom)) := by
  rw [symDiagram_map]
  congr 1
  ext a
  simp [overlapHom]

omit hx in
theorem overlap_snd [DecidableEq k] (i j : (ChartIdx k)ᵒᵖ) :
    (symDiagram k x g).map (homOfLE (show j.unop ≤ unionIdx k i j from Finset.subset_union_right)).op =
      Spec.map (CommRingCat.ofHom ((overlapHom k x g i j).hom.comp (Algebra.TensorProduct.includeRight :
        SymRing k (chartRing x j.unop.1) g →ₐ[k] _).toRingHom)) := by
  rw [symDiagram_map]
  congr 1
  ext a
  simp [overlapHom]

/-- Generic closing step: a map into `Spec S ×_{Spec R} Spec T` that is `Spec` of a surjection `S ⊗_R T → U` on both
factors is a closed immersion. Stated with bare variables so all tensor-product instances are the canonical ones. -/
theorem isClosedImmersion_of_tensor {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] (F : S ⊗[R] T →+* U) (hF : Function.Surjective F)
    (f : Spec (.of S) ⟶ Spec (.of R)) (f' : Spec (.of T) ⟶ Spec (.of R))
    (hf : f = Spec.map (CommRingCat.ofHom (algebraMap R S))) (hf' : f' = Spec.map (CommRingCat.ofHom (algebraMap R T)))
    {P : Scheme.{u}} (e : P ≅ Spec (.of U)) (m : P ⟶ pullback f f')
    (h1 : m ≫ pullback.fst f f' = e.hom ≫ Spec.map (CommRingCat.ofHom (F.comp Algebra.TensorProduct.includeLeftRingHom)))
    (h2 : m ≫ pullback.snd f f' = e.hom ≫ Spec.map (CommRingCat.ofHom (F.comp
      (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom))) :
    IsClosedImmersion m := by
  subst hf hf'
  have hm : m = e.hom ≫ Spec.map (CommRingCat.ofHom F) ≫ (pullbackSpecIso R S T).inv := by
    apply pullback.hom_ext
    · rw [h1, Category.assoc, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
      rfl
    · rw [h2, Category.assoc, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
      rfl
  have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom F) hF
  rw [hm]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
instance isSeparated_toSpecK : IsSeparated (toSpecK k x g) := by
  classical
  change @IsSeparated (colimit (symDiagram k x g)) _ (toSpecK k x g)
  refine ⟨IsZariskiLocalAtTarget.of_openCover (Scheme.Pullback.openCoverOfLeftRight
    (Scheme.IsLocallyDirected.openCover (symDiagram k x g)) (Scheme.IsLocallyDirected.openCover (symDiagram k x g))
    _ _) ?_⟩
  rintro ⟨(i : (ChartIdx k)ᵒᵖ), (j : (ChartIdx k)ᵒᵖ)⟩
  dsimp [Scheme, Scheme.Cover.pullbackHom]
  refine (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (f := (pullbackDiagonalMapIdIso ..).inv) _).mp ?_
  change IsClosedImmersion ((pullbackDiagonalMapIdIso (colimit.ι (symDiagram k x g) i)
    (colimit.ι (symDiagram k x g) j) (toSpecK k x g)).inv ≫ pullback.snd _ _)
  have hP := isPullback_ι_ι k x g i j
  refine isClosedImmersion_of_tensor (S := SymRing k (chartRing x i.unop.1) g) (T := SymRing k (chartRing x j.unop.1) g)
    (U := SymRing k (chartRing x (i.unop.1 ∪ j.unop.1)) g) (overlapHom k x g i j).hom
    (lift_chartMap_surjective (g := g) hx.out i.unop.2) _ _ (ι_toSpecK k x g i) (ι_toSpecK k x g j)
    hP.isoPullback.symm _ ?_ ?_
  · refine (Category.assoc _ _ _).trans ((pullbackDiagonalMapIdIso_inv_snd_fst _ _ _).trans ?_)
    refine (Iso.eq_inv_comp hP.isoPullback).mpr ?_
    exact hP.isoPullback_hom_fst.trans (overlap_fst k x g i j)
  · refine (Category.assoc _ _ _).trans ((pullbackDiagonalMapIdIso_inv_snd_snd _ _ _).trans ?_)
    refine (Iso.eq_inv_comp hP.isoPullback).mpr ?_
    exact hP.isoPullback_hom_snd.trans (overlap_snd k x g i j)

end SepScheme

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacComplete_AJCo =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJCo`: the Abel-Jacobi map on the curve `X1 = Sym¹ X`

`X1 K F = SymX K x 1` (`x = algebraMap K[X] F X`): the charts `Spec Sym¹ B_A` glued (JacSymB).
* `diag1 : B →ₐ Sym¹ B` (the single tensor factor) and its naturality `symMap_diag1`;
* `isReduced_X1`; `plA A θ`, the center of a `K`-point `θ` of `B_A` (`isCenter_plA`, `plA_restrict`);
* `chartAJ P0 A : chart A ⟶ J` (`Rfin (SynF c) ≅ B_{c} ⊆ B_A → Sym¹ B_A`, then `ajChart P0 c`), value `chartAJ_kpt`;
* **`ajX1 P0 : X1 K F ⟶ J`** glued (`JacChunk.glueY`); `ajX1_over`, **`ajX1_apply`**: the value at the closed
  point `colimit.ι A (kpt ψ)` is `ajPt P0 (plA A (ψ.comp diag1))` (class `[Q] - [P0]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
-- the instance diamonds on the nested localizations need nested synthPending (diagnostics, session 20)
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Diag

variable {k : Type*} [CommRing k] {B : Type*} [CommRing B] [Algebra k B]

/-- `B → Sym¹ B`: the single tensor factor (every element of `X¹` is `S_1`-invariant). -/
noncomputable def diag1 : B →ₐ[k] SymRing k B 1 :=
  (inc (k := k) (B := B) (g := 1) 0).codRestrict (SymRing k B 1) (fun b => by
    rw [mem_symRing]
    intro σ
    rw [Subsingleton.elim σ 1, one_smul])

theorem diag1_coe (b : B) : (diag1 (k := k) b : XPow k B 1) = inc 0 b := rfl

theorem symMap_diag1 {B' : Type*} [CommRing B'] [Algebra k B'] (f : B →ₐ[k] B') :
    (symMap (g := 1) f).comp diag1 = diag1.comp f :=
  AlgHom.ext fun b => Subtype.ext (by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, symMap_coe, diag1_coe, diag1_coe, ← AlgHom.comp_apply, xMap_inc,
      AlgHom.comp_apply])

end Diag

section AJ1

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

instance fact_transcendental_xF : Fact (Transcendental K (algebraMap K[X] F X)) := ⟨transcendental_xF K F⟩

instance finiteType_chartIdx (A : ChartIdx K) : Algebra.FiniteType K (chartRing (algebraMap K[X] F X) A.1) :=
  finiteType_chartRing (transcendental_xF K F) A.2

variable (K F) in
/-- The curve `X1 = Sym¹ X`. -/
noncomputable abbrev X1 : Scheme.{u} := SymX K (algebraMap K[X] F X) 1

variable (K F) in
/-- The chart `A` of `X1`, `Spec Sym¹ B_A`. -/
noncomputable abbrev cht (A : (ChartIdx K)ᵒᵖ) : Scheme.{u} :=
  Spec (.of (SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1))

instance isReduced_cht (A : (ChartIdx K)ᵒᵖ) : IsReduced (cht K F A) := by
  show IsReduced (Spec (CommRingCat.of (SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1)))
  infer_instance

instance isReduced_X1 : IsReduced (X1 K F) := by
  have : ∀ t : X1 K F, _root_.IsReduced ((X1 K F).presheaf.stalk t) := fun t => by
    obtain ⟨A, z, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (symDiagram K (algebraMap K[X] F X) 1) t
    have e := (asIso ((colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A).stalkMap z)).commRingCatIsoToRingEquiv
    have : IsReduced ((symDiagram K (algebraMap K[X] F X) 1).obj A) := isReduced_cht (K := K) (F := F) A
    exact isReduced_of_injective e.toRingHom e.injective
  exact isReduced_of_isReduced_stalk (X1 K F)

/-- The center of a `K`-point `θ` of `B_A` (the chart-`{c}` center for the chosen `c ∈ A`). -/
noncomputable def plA (A : ChartIdx K) (θ : chartRing (algebraMap K[X] F X) A.1 →ₐ[K] K) : Place K F :=
  plc A.2.choose (θ.comp (Subalgebra.inclusion (chartRing_mono _ (Finset.singleton_subset_iff.2 A.2.choose_spec))))

theorem isCenter_plA (A : ChartIdx K) (θ : chartRing (algebraMap K[X] F X) A.1 →ₐ[K] K) :
    IsCenter (plA A θ) θ :=
  isCenter_plc_of_mem A.2.choose_spec θ

theorem plA_eq_of_isCenter (A : ChartIdx K) {θ : chartRing (algebraMap K[X] F X) A.1 →ₐ[K] K} {R : Place K F}
    (hR : IsCenter R θ) : plA A θ = R :=
  isCenter_unique A.2.choose_spec (isCenter_plA A θ) hR

/-- The center does not depend on the chart. -/
theorem plA_restrict {A A' : ChartIdx K} (h : A.1 ⊆ A'.1) (θ : chartRing (algebraMap K[X] F X) A'.1 →ₐ[K] K) :
    plA A (θ.comp (Subalgebra.inclusion (chartRing_mono _ h))) = plA A' θ :=
  (plA_eq_of_isCenter A' (isCenter_extend h A.2.choose_spec θ (isCenter_plA A _))).symm

variable (K F) in
/-- `Rfin (SynF c) ≅ B_{c} ⊆ B_A → Sym¹ B_A` for the chosen `c ∈ A`. -/
noncomputable def cPt (A : ChartIdx K) :
    Rfin K (SynF K F A.2.choose) →ₐ[K] SymRing K (chartRing (algebraMap K[X] F X) A.1) 1 :=
  diag1.comp ((Subalgebra.inclusion (chartRing_mono _ (Finset.singleton_subset_iff.2 A.2.choose_spec))).comp
    (rfinG A.2.choose).symm.toAlgHom)

variable (P0 : Place K F)

theorem cht_cov (t : X1 K F) (_ : IsClosed ({t} : Set (X1 K F))) :
    ∃ A : (ChartIdx K)ᵒᵖ, ∃ p : cht K F A, colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A p = t :=
  Scheme.IsLocallyDirected.ι_jointly_surjective (symDiagram K (algebraMap K[X] F X) 1) t

instance isOpenImmersion_ιX1 (A : (ChartIdx K)ᵒᵖ) :
    IsOpenImmersion (X := cht K F A) (Y := X1 K F) (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A) :=
  JacSym.isOpenImmersion_ι K (algebraMap K[X] F X) 1 A

end AJ1

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJSurj =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJSurj` (L19 route AJ: K-point surjectivity of `Σ [Q_i] - g [P0]`)

Over an algebraically closed `K`, with `g` the genus:
* `exists_sum_single_of_nonneg`: an effective divisor of degree `n` is a sum of `n` places;
* **`exists_eff_rep P0 hc`**: every class `c ∈ Pic⁰` is `Σ_{i < g} [t_i] - g • [P0]` (Riemann's inequality).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Module

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.JacLaw RamanujanPetersson.RR

section AJSurj

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- An effective divisor of degree `n` is a sum of `n` places. -/
theorem exists_sum_single_of_nonneg : ∀ (n : ℕ) {D : Places.Divisor K F}, 0 ≤ D → D.deg = n →
    ∃ t : Fin n → Places.Place K F, D = ∑ i, Finsupp.single (t i) (1 : ℤ)
  | 0, D, hD, hd => ⟨Fin.elim0, by
      rw [eq_zero_of_nonneg_of_deg hD (by simpa using hd)]; simp⟩
  | n + 1, D, hD, hd => by
    classical
    have hne : D ≠ 0 := by
      rintro rfl
      rw [deg_zero'] at hd
      omega
    obtain ⟨v, hv⟩ : ∃ v, D v ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (Finsupp.ext h)
    have hv0 : 0 ≤ D v := by
      have := Finsupp.le_def.1 hD v
      simpa using this
    have hD' : 0 ≤ D - Finsupp.single v 1 := by
      rw [Finsupp.le_def]
      intro w
      have hw0 := Finsupp.le_def.1 hD w
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_sub, Pi.sub_apply] at hw0 ⊢
      by_cases hw : w = v
      · subst hw
        rw [Finsupp.single_eq_same]
        omega
      · rw [Finsupp.single_apply, if_neg (Ne.symm hw)]
        omega
    have hd' : (D - Finsupp.single v 1).deg = ((n : ℕ) : ℤ) := by
      rw [PlacesK.Divisor.deg_sub, hd, deg_single_one]
      push_cast
      ring
    obtain ⟨t, ht⟩ := exists_sum_single_of_nonneg n hD' hd'
    refine ⟨Fin.cons v t, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← ht]
    abel

/-- **Every class in `Pic⁰` is `Σ_{i < g} [t_i] - g • [P0]`** (Riemann's inequality `ℓ(D + g P0) ≥ 1`). -/
theorem exists_eff_rep (P0 : Places.Place K F) {c : PicK K F} (hc : c ∈ Pic0K K F) :
    ∃ t : Fin (genusFK K F) → Places.Place K F,
      c = ∑ i, clsK K F (Finsupp.single (t i) 1) -
        (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1) := by
  obtain ⟨D0, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hD0 : D0.deg = 0 := by rw [← degPicK_clsK]; exact (mem_Pic0K K F).1 hc
  set E : Places.Divisor K F := D0 + Finsupp.single P0 (genusFK K F : ℤ) with hEdef
  have hdE : E.deg = genusFK K F := by
    rw [hEdef, PlacesK.Divisor.deg_add, hD0, deg_single', zero_add]
  have hk := constField_eq_bot' (K := K) (F := F)
  have hell := riemann_inequalityFK' hk E
  have hpos : LFK K F E ≠ ⊥ := by
    intro hb
    have e := ellFK_def (K := K) (F := F) E
    rw [hb, finrank_bot] at e
    rw [hdE, e] at hell
    push_cast at hell
    omega
  obtain ⟨f, hfE, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpos
  have hD := (mem_LFK hf0).1 hfE
  obtain ⟨t, ht⟩ := exists_sum_single_of_nonneg (genusFK K F) hD
    (by rw [PlacesK.Divisor.deg_add, PlacesK.deg_div hf0, hdE, zero_add])
  refine ⟨t, ?_⟩
  have hadd : ∀ A B : Places.Divisor K F, clsK K F (A + B) = clsK K F A + clsK K F B :=
    fun A B => QuotientAddGroup.mk_add _ A B
  have h1 : clsK K F (PlacesK.div f) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).2 (div_mem_PrincK K F hf0)
  have h2 : clsK K F (∑ i, Finsupp.single (t i) (1 : ℤ)) = ∑ i, clsK K F (Finsupp.single (t i) 1) :=
    map_sum (QuotientAddGroup.mk' (PrincK K F)) _ _
  have h3 : clsK K F (Finsupp.single P0 (genusFK K F : ℤ)) =
      (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1) := by
    rw [← Finsupp.smul_single_one]
    exact map_zsmul (QuotientAddGroup.mk' (PrincK K F)) _ _
  have h4 : clsK K F (PlacesK.div f + E) =
      clsK K F D0 + (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1) := by
    rw [hadd, h1, zero_add, hEdef, hadd, h3]
  rw [ht, h2] at h4
  rw [h4]
  abel

end AJSurj

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacSymB_GenInt =====
section

/-!
# S4-JacSymB, file H2d: integrality of `X^g(B)` over the coefficients of `E(w)` (L12, valuative criterion)

If every `b ∈ B` is integral over `k[w]`, then every element of `X^g(B)` is a root of a monic polynomial whose
coefficients are polynomials (over `k`) in the coefficients of `E(w)`: the `w_l` are roots of
`reflect g E(w) = ∏ (X - w_l)`, the `b_l` are integral over `k[w_l]`, and the `b_l` generate `X^g(B)`.
`mem_range_of_monic`: such an element is sent into `O` by any ring map to `Frac O` that sends `k` and the coefficients
into the valuation ring `O`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacSym

section GenInt

open Polynomial

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {g : ℕ}

theorem exists_monic_genE (w : B)
    (hint : ∀ b : B, ∃ p : (Polynomial k)[X], p.Monic ∧ p.eval₂ (Polynomial.aeval w).toRingHom b = 0)
    (t : XPow k B g) :
    ∃ p : (MvPolynomial ℕ k)[X], p.Monic ∧
      p.eval₂ (MvPolynomial.aeval fun j => (genE (k := k) (g := g) w).coeff j).toRingHom t = 0 := by
  classical
  set β : MvPolynomial ℕ k →ₐ[k] XPow k B g := MvPolynomial.aeval fun j => (genE (k := k) (g := g) w).coeff j
    with hβ
  rcases subsingleton_or_nontrivial (XPow k B g) with hT | hT
  · exact ⟨X, monic_X, Subsingleton.elim _ _⟩
  let _ : Algebra (MvPolynomial ℕ k) (XPow k B g) := β.toRingHom.toAlgebra
  set IC := integralClosure (MvPolynomial ℕ k) (XPow k B g) with hIC
  have hA : ∀ l : Fin g, inc l w ∈ IC := by
    intro l
    have hR : (∏ m : Fin g, (X - C (inc (k := k) m w))) ∈ lifts β.toRingHom := by
      rw [lifts_iff_coeff_lifts]
      intro i
      rw [← reflect_genE, coeff_reflect]
      exact ⟨MvPolynomial.X _, MvPolynomial.aeval_X _ _⟩
    obtain ⟨q, hq, -, hqm⟩ :=
      lifts_and_degree_eq_and_monic hR (monic_prod_of_monic _ _ fun m _ => monic_X_sub_C _)
    rw [mem_integralClosure_iff]
    refine ⟨q, hqm, ?_⟩
    change q.eval₂ β.toRingHom (inc l w) = 0
    rw [← eval_map, hq, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ l) (by simp)
  have hk : ∀ c : k, algebraMap k (XPow k B g) c ∈ IC := fun c => by
    have : algebraMap k (XPow k B g) c = algebraMap (MvPolynomial ℕ k) (XPow k B g) (MvPolynomial.C c) :=
      (MvPolynomial.aeval_C _ c).symm
    rw [this]
    exact IC.algebraMap_mem _
  have hB : ∀ (l : Fin g) (b : B), inc l b ∈ IC := by
    intro l b
    obtain ⟨p, hpm, hp⟩ := hint b
    let φ : Polynomial k →+* IC :=
      Polynomial.eval₂RingHom ((algebraMap (MvPolynomial ℕ k) IC).comp MvPolynomial.C) ⟨inc l w, hA l⟩
    have hφ : (algebraMap IC (XPow k B g)).comp φ = (inc l).toRingHom.comp (Polynomial.aeval w).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro c
        rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, eval₂_C, RingHom.comp_apply]
        change β (MvPolynomial.C c) = inc l (Polynomial.aeval w (Polynomial.C c))
        rw [MvPolynomial.aeval_C, Polynomial.aeval_C, AlgHom.commutes]
      · rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, eval₂_X]
        change inc l w = inc l (Polynomial.aeval w Polynomial.X)
        rw [Polynomial.aeval_X]
    have hint' : IsIntegral IC (inc (k := k) (g := g) l b) := by
      refine ⟨p.map φ, hpm.map φ, ?_⟩
      rw [eval₂_map, hφ]
      exact (hom_eval₂ p (Polynomial.aeval (R := k) w).toRingHom (inc (k := k) (g := g) l).toRingHom b).symm.trans (by rw [hp, map_zero])
    have hmem : inc (k := k) (g := g) l b ∈ integralClosure IC (XPow k B g) := hint'
    rw [integralClosure_idem, Algebra.mem_bot] at hmem
    obtain ⟨y, hy⟩ := hmem
    rw [← hy]
    exact y.2
  have hC : ∀ t : XPow k B g, t ∈ IC := by
    intro t
    induction t using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      rw [← prod_inc, Algebra.smul_def]
      exact IC.mul_mem (hk r) (prod_mem fun l _ => hB l (f l))
    | add x y hx hy => exact IC.add_mem hx hy
  obtain ⟨p, hpm, hp⟩ := (mem_integralClosure_iff _ _).mp (hC t)
  exact ⟨p, hpm, hp⟩

/-- The valuation step: an element satisfying a monic equation over `k[e_j]` maps into `O` when `k` and the `e_j` do. -/
theorem mem_range_of_monic {O K S : Type*} [CommRing S] [Algebra k S] [CommRing O] [IsDomain O] [ValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] (μ : k →+* O) (Φ : S →+* K)
    (hμ : ∀ c, algebraMap O K (μ c) = Φ (algebraMap k S c)) (e : ℕ → S) (o : ℕ → O)
    (ho : ∀ j, algebraMap O K (o j) = Φ (e j)) (s : S)
    (hs : ∃ p : (MvPolynomial ℕ k)[X], p.Monic ∧ p.eval₂ (MvPolynomial.aeval e).toRingHom s = 0) :
    ∃ y : O, algebraMap O K y = Φ s := by
  obtain ⟨p, hpm, hp⟩ := hs
  let ψ : MvPolynomial ℕ k →+* O := MvPolynomial.eval₂Hom μ o
  have hψ : (algebraMap O K).comp ψ = Φ.comp (MvPolynomial.aeval e).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, hμ]
      change Φ (algebraMap k S c) = Φ (MvPolynomial.aeval e (MvPolynomial.C c))
      rw [MvPolynomial.aeval_C]
    · intro j
      rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, ho]
      change Φ (e j) = Φ (MvPolynomial.aeval e (MvPolynomial.X j))
      rw [MvPolynomial.aeval_X]
  have hint : IsIntegral O (Φ s) := by
    refine ⟨p.map ψ, hpm.map ψ, ?_⟩
    rw [eval₂_map, hψ]
    exact (hom_eval₂ p (MvPolynomial.aeval e).toRingHom Φ s).symm.trans (by rw [hp, map_zero])
  have hv : (ValuationRing.valuation O K).Integers O :=
    { hom_inj := IsFractionRing.injective O K
      map_le_one := fun r => (Valuation.mem_integer_iff _ _).mp ((ValuationRing.mem_integer_iff O K _).mpr ⟨r, rfl⟩)
      exists_of_le_one := fun r hr => (ValuationRing.mem_integer_iff O K r).mp ((Valuation.mem_integer_iff _ _).mpr hr) }
  exact (ValuationRing.mem_integer_iff O K _).mp (hv.mem_of_integral hint)

end GenInt

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacSymB_ValAlg =====
section

/-!
# S4-JacSymB, file H2a: a valuation-ring lemma for the valuative criterion (L12)

`O` a valuation ring with fraction field `K`, `μ : k →+* O` with `k` an infinite field. For a nonzero `p : K[X]` there is
`t : k` such that, with `λ = μ t ∈ O ⊆ K`, `p(λ) ≠ 0` and every coefficient of the Taylor shift `p(X + λ)` is an
`O`-multiple of `p(λ)`. Proof: scale `p` so its largest coefficient (for the valuation) is `1`; then it lies in `O[X]`
with nonzero reduction mod the maximal ideal, and an infinite field `k ⊆ O/𝔪` contains a non-root `t`, so `p(μ t)` is a
unit of `O` after scaling.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacSym

section ValAlg

open Polynomial

theorem exists_taylor_integral {k O K : Type*} [Field k] [Infinite k] [CommRing O] [IsDomain O] [ValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] (μ : k →+* O) (p : K[X]) (hp : p ≠ 0) :
    ∃ t : k, p.eval (algebraMap O K (μ t)) ≠ 0 ∧
      ∀ j, ∃ o : O, algebraMap O K o * p.eval (algebraMap O K (μ t)) = (taylor (algebraMap O K (μ t)) p).coeff j := by
  classical
  set v := ValuationRing.valuation O K
  obtain ⟨j0, hj0, hmax⟩ := Finset.exists_max_image p.support (fun j => v (p.coeff j))
    (Finset.nonempty_of_ne_empty (by simpa using hp))
  set a := p.coeff j0 with ha_def
  have ha : a ≠ 0 := mem_support_iff.mp hj0
  have hle : ∀ j, v (a⁻¹ * p.coeff j) ≤ 1 := by
    intro j
    by_cases hj : j ∈ p.support
    · rw [map_mul, map_inv₀]
      have hva : v a ≠ 0 := by simpa using ha
      calc (v a)⁻¹ * v (p.coeff j) ≤ (v a)⁻¹ * v a := by gcongr; exact hmax j hj
        _ = 1 := inv_mul_cancel₀ hva
    · rw [notMem_support_iff.mp hj, mul_zero, map_zero]; exact zero_le
  have hlift : C a⁻¹ * p ∈ lifts (algebraMap O K) := by
    rw [lifts_iff_coeff_lifts]
    intro j
    rw [coeff_C_mul]
    obtain ⟨o, ho⟩ := (ValuationRing.mem_integer_iff O K _).mp ((Valuation.mem_integer_iff _ _).mpr (hle j))
    exact ⟨o, ho⟩
  obtain ⟨q0, hq0⟩ := (mem_lifts _).mp hlift
  have hq0j : q0.coeff j0 = 1 := by
    apply IsFractionRing.injective O K
    rw [map_one, ← coeff_map, hq0, coeff_C_mul, ← ha_def, inv_mul_cancel₀ ha]
  have hp_eq : p = C a * q0.map (algebraMap O K) := by
    rw [hq0, ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]
  set ρ : O →+* IsLocalRing.ResidueField O := IsLocalRing.residue O
  have hqbar : q0.map ρ ≠ 0 := by
    intro h
    have := congrArg (fun r => r.coeff j0) h
    simp only [coeff_map, hq0j, map_one, coeff_zero] at this
    exact one_ne_zero this
  obtain ⟨t, ht⟩ : ∃ t : k, (q0.map ρ).eval (ρ (μ t)) ≠ 0 := by
    by_contra! H
    apply hqbar
    apply eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := Set.range (ρ.comp μ)) ?_ (Set.infinite_range_of_injective (ρ.comp μ).injective)
    rintro _ ⟨t, rfl⟩
    exact H t
  rw [eval_map, eval₂_hom, IsLocalRing.residue_ne_zero_iff_isUnit] at ht
  obtain ⟨u, hu⟩ := ht
  refine ⟨t, ?_, fun j => ⟨(taylor (μ t) q0).coeff j * ↑u⁻¹, ?_⟩⟩
  · rw [hp_eq, eval_mul, eval_C, eval_map, eval₂_hom, ← hu]
    exact mul_ne_zero ha ((IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero u.ne_zero)))
  · rw [hp_eq, taylor_mul, taylor_C, coeff_C_mul, ← map_taylor, coeff_map, eval_mul, eval_C, eval_map, eval₂_hom, ← hu,
      map_mul]
    have h1 : algebraMap O K (↑u⁻¹ : O) * algebraMap O K (↑u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    linear_combination (algebraMap O K ((taylor (μ t) q0).coeff j) * a) * h1

end ValAlg

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacSymB_ExistAlg =====
section

/-!
# S4-JacSymB, file H2c: ring-level valuative existence for `Sym^g X` (L12)

Given a ring map `φ : Sym^g B_{c} → K` (`K = Frac O`, `O` a valuation ring) compatible with `μ : k → O`, there is
`d = c + t` such that `φ` extends to `φ' : Sym^g B_{c,d} → K` and `φ' ∘ (Sym^g B_{d} → Sym^g B_{c,d})` lands in `O`.
Proof: `t` from `exists_taylor_integral` applied to `P = φ(E(u_c))`; the Taylor identity `N(1 - t u_c) E(u_d) =
E(u_c)(X + t)` puts the coefficients of `E(u_d)` into `O`; `Sym^g B_d` is integral over them (`exists_monic_genE`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacSym

section ExistAlg

open Polynomial

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F] {x : F} {g : ℕ}

/-- The coordinate `u_c = 1/(x - c)` as an element of the chart ring `B_A` (`c ∈ A`). -/
noncomputable def ucB (x : F) {A : Finset k} {c : k} (hc : c ∈ A) : chartRing x A :=
  ⟨uc x c, polyA_le_chartRing x A (uc_mem_polyA x hc)⟩

/-- Elements of `B_{d}` are integral over `k[u_d]`. -/
theorem hint_chartRing_single (d : k) (b : chartRing x {d}) :
    ∃ p : (Polynomial k)[X], p.Monic ∧
      p.eval₂ (Polynomial.aeval (R := k) (ucB x (Finset.mem_singleton_self d))).toRingHom b = 0 := by
  classical
  let u : polyA x {d} := ⟨uc x d, uc_mem_polyA x (Finset.mem_singleton_self d)⟩
  have hπ : Function.Surjective (Polynomial.aeval (R := k) u).toRingHom := by
    intro y
    have hy : (y : F) ∈ Algebra.adjoin k {uc x d} := by
      rw [← polyA_singleton]
      exact y.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, hp⟩ := (AlgHom.mem_range _).mp hy
    exact ⟨p, Subtype.ext ((Polynomial.aeval_subalgebra_coe p _ u).trans hp)⟩
  obtain ⟨q, hqm, hq⟩ := (mem_chartRing (x := x) (A := {d})).mp b.2
  obtain ⟨p, hpq, -, hpm⟩ := lifts_and_degree_eq_and_monic (mem_lifts_of_surjective hπ q) hqm
  refine ⟨p, hpm, Subtype.val_injective ?_⟩
  have e : (chartRing x {d}).val.toRingHom.comp
      (Polynomial.aeval (R := k) (ucB x (Finset.mem_singleton_self d))).toRingHom =
      (algebraMap (polyA x {d}) F).comp (Polynomial.aeval (R := k) u).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C]
      rfl
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X]
      rfl
  change (chartRing x {d}).val.toRingHom (p.eval₂ _ b) = (chartRing x {d}).val.toRingHom 0
  rw [Polynomial.hom_eval₂, e, ← Polynomial.eval₂_map, hpq, map_zero]
  exact hq

theorem genPoly_eval_zero {B : Type*} [CommRing B] [Algebra k B] (w : B) :
    (genPoly (k := k) (g := g) w).eval 0 = 1 := by
  have h := genPoly_eval (k := k) (g := g) w 0
  simp only [map_zero, zero_mul, sub_zero, normS_one] at h
  exact h

variable [DecidableEq k]

theorem wt_pair_eq (hx : Transcendental k x) (c t : k) :
    wt x c ({c, c + t} \ {c}) = 1 - algebraMap k F t * uc x c := by
  by_cases ht : t = 0
  · subst ht
    simp [wt]
  · have hs : ({c, c + t} \ {c} : Finset k) = {c + t} := by
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd h1 h2
        · exact h1
      · rintro rfl
        exact ⟨Or.inr rfl, fun h => ht (by simpa using h)⟩
    rw [hs, wt_singleton_eq hx, show c - (c + t) = -t by ring, map_neg]
    ring

/-- Ring-level valuative existence: `φ : Sym^g B_{c} → K` extends over `B_{c,d}` with `Sym^g B_{d}` landing in `O`. -/
theorem exists_valuative_lift [Infinite k] (hx : Transcendental k x) (c : k) {O K : Type*} [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (μ : k →+* O)
    (φ : SymRing k (chartRing x {c}) g →+* K) (hμ : ∀ a, algebraMap O K (μ a) = φ (algebraMap k _ a)) :
    ∃ (d : k) (φ' : SymRing k (chartRing x {c, d}) g →+* K) (φ'' : SymRing k (chartRing x {d}) g →+* O),
      φ'.comp (chartMap x g (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self c {d}))).toRingHom = φ ∧
      (algebraMap O K).comp φ'' = φ'.comp (chartMap x g (Finset.singleton_subset_iff.mpr
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self d)))).toRingHom ∧
      φ''.comp (algebraMap k _) = μ := by
  set w := ucB x (Finset.mem_singleton_self c) with hw
  set P : K[X] := (genPoly (k := k) (g := g) w).map φ with hP
  have hP0 : P.eval 0 = 1 := by rw [hP, eval_zero_map, genPoly_eval_zero, map_one]
  have hPne : P ≠ 0 := fun h => by
    rw [h, eval_zero] at hP0
    exact zero_ne_one hP0
  obtain ⟨t, hev, hcoef⟩ := exists_taylor_integral μ P hPne
  simp only [hμ] at hev hcoef
  choose o ho using hcoef
  have h1 : ({c} : Finset k) ⊆ {c, c + t} := Finset.singleton_subset_iff.mpr (Finset.mem_insert_self c _)
  have h2 : ({c + t} : Finset k) ⊆ {c, c + t} :=
    Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  let _ := (chartMap x g h1).toRingHom.toAlgebra
  have := isLocalization_chartMap (g := g) hx h1 (Finset.mem_singleton_self c)
  set Nw := normS k (g := g)
    (⟨wt x c ({c, c + t} \ {c}), wt_mem_chartRing hx (Finset.mem_singleton_self c) _⟩ : chartRing x {c}) with hNdef
  have hNw : Nw = normS k (1 - algebraMap k (chartRing x {c}) t * w) := by
    rw [hNdef]
    congr 1
    exact Subtype.ext ((wt_pair_eq hx c t).trans rfl)
  have hφN : φ Nw = P.eval (φ (algebraMap k _ t)) := by
    rw [hNw, ← genPoly_eval, hP, eval_map, eval₂_hom]
  have hunit : IsUnit (φ Nw) := by
    rw [hφN]
    exact hev.isUnit
  let φ' : SymRing k (chartRing x {c, c + t}) g →+* K := IsLocalization.Away.lift Nw hunit
  have hφ'c : φ'.comp (chartMap x g h1).toRingHom = φ := IsLocalization.Away.lift_comp Nw hunit
  -- the Taylor identity on `B_{c,d}`
  set a := ucB x (h1 (Finset.mem_singleton_self c)) with ha
  set wd := ucB x (Finset.mem_singleton_self (c + t)) with hwd
  set b := ucB x (h2 (Finset.mem_singleton_self (c + t))) with hb
  have hab : (1 - algebraMap k (chartRing x {c, c + t}) t * a) * b = a := by
    apply Subtype.ext
    change (1 - algebraMap k F t * uc x c) * uc x (c + t) = uc x c
    have hc0 := sub_ne_zero_of_tr hx c
    have hd0 := sub_ne_zero_of_tr hx (c + t)
    rw [map_add] at hd0
    simp only [uc, map_add]
    field_simp
    ring
  have hT := congrArg (Polynomial.map φ') (genPoly_taylor (k := k) (g := g) a b t hab)
  have hNa : φ' (normS k (g := g) (1 - algebraMap k (chartRing x {c, c + t}) t * a)) = φ Nw := by
    have e : normS k (g := g) (1 - algebraMap k (chartRing x {c, c + t}) t * a) = chartMap x g h1 Nw := by
      rw [hNw, chartMap, symMap_normS]
      congr 1
    rw [e]
    exact DFunLike.congr_fun hφ'c Nw
  have hPa : (genPoly (k := k) (g := g) a).map φ' = P := by
    have e : genPoly (k := k) (g := g) a = (genPoly w).map (chartMap x g h1).toRingHom :=
      (symMap_genPoly (Subalgebra.inclusion (chartRing_mono x h1)) w).symm
    rw [e, Polynomial.map_map, hφ'c]
  have hlam : φ' (algebraMap k (SymRing k (chartRing x {c, c + t}) g) t) = φ (algebraMap k _ t) := by
    rw [← AlgHom.commutes (chartMap x g h1) t]
    exact DFunLike.congr_fun hφ'c _
  rw [Polynomial.map_mul, map_C, map_taylor, hNa, hPa, hlam, hφN] at hT
  have eb : genPoly (k := k) (g := g) b = (genPoly wd).map (chartMap x g h2).toRingHom :=
    (symMap_genPoly (Subalgebra.inclusion (chartRing_mono x h2)) wd).symm
  have hQ : ∀ j, algebraMap O K (o j) = φ' (chartMap x g h2 ((genPoly (k := k) (g := g) wd).coeff j)) := by
    intro j
    have e1 := congrArg (fun p => p.coeff j) hT
    simp only [coeff_C_mul] at e1
    rw [← ho j] at e1
    have e2 := mul_left_cancel₀ hev (e1.trans (mul_comm _ _))
    rw [← e2, coeff_map, eb, coeff_map]
    rfl
  have hΦk : ∀ a, algebraMap O K (μ a) = (φ'.comp (chartMap x g h2).toRingHom) (algebraMap k _ a) := by
    intro a
    rw [hμ]
    change _ = φ' (chartMap x g h2 (algebraMap k _ a))
    rw [AlgHom.commutes, ← AlgHom.commutes (chartMap x g h1) a]
    exact (DFunLike.congr_fun hφ'c _).symm
  have hs : ∀ s : SymRing k (chartRing x {c + t}) g, ∃ p : (MvPolynomial ℕ k)[X], p.Monic ∧
      p.eval₂ (MvPolynomial.aeval fun j => (genPoly (k := k) (g := g) wd).coeff j).toRingHom s = 0 := by
    intro s
    obtain ⟨p, hpm, hp⟩ := exists_monic_genE (k := k) (g := g) wd (hint_chartRing_single (x := x) (c + t)) s.1
    refine ⟨p, hpm, Subtype.val_injective ?_⟩
    have e : (SymRing k (chartRing x {c + t}) g).val.toRingHom.comp
        (MvPolynomial.aeval (R := k) fun j => (genPoly (k := k) (g := g) wd).coeff j).toRingHom =
        (MvPolynomial.aeval (R := k) fun j => (genE (k := k) (g := g) wd).coeff j).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C]
        rfl
      · intro j
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
        exact coeff_genPoly wd j
    change (SymRing k (chartRing x {c + t}) g).val.toRingHom (p.eval₂ _ s) =
      (SymRing k (chartRing x {c + t}) g).val.toRingHom 0
    rw [Polynomial.hom_eval₂, e, map_zero]
    exact hp
  have hrange : (φ'.comp (chartMap x g h2).toRingHom).range ≤ (algebraMap O K).range := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨y, hy⟩ := mem_range_of_monic μ _ hΦk _ o hQ s (hs s)
    exact ⟨y, hy⟩
  let e : O ≃+* (algebraMap O K).range :=
    (AlgEquiv.ofInjective (Algebra.ofId O K) (IsFractionRing.injective _ _)).toRingEquiv
  let φ'' := e.symm.toRingHom.comp ((Subring.inclusion hrange).comp (RingHom.rangeRestrict _))
  have hφ'' : (algebraMap O K).comp φ'' = φ'.comp (chartMap x g h2).toRingHom := by
    ext s
    exact congr_arg Subtype.val (e.apply_symm_apply _)
  refine ⟨c + t, φ', φ'', hφ'c, hφ'', ?_⟩
  ext a
  apply IsFractionRing.injective O K
  rw [hΦk a]
  exact DFunLike.congr_fun hφ'' (algebraMap k _ a)

end ExistAlg

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacComplete_Proper =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `Proper`: **L19, the Jacobian is proper**

Route AJ (NOTES, session 6 decision): the Abel-Jacobi map `ajX1 P0 : X1 = Sym¹ X ⟶ J` (AJCo) gives
`Φ_n : X1^n ⟶ J`, `(Q_1, …, Q_n) ↦ Σ ([Q_i] - [P0])` (products in `Over (Spec K)`, hom-group law of `J`).
* `exists_inl`, `exists_plc`, `exists_chartPt`: every place of `F` is the center of a `K`-point of a chart of `X1`;
* `X1O`, `ιO`, `ajO P0 : X1O ⟶ J`, `exists_kX1`: every `ajK P0 Q` is the image of a `K`-point of `X1`;
* `PP n = X1^n` (`isProper_PP`), `PhiN P0 n : PP n ⟶ J`, `exists_pt`: the value `Σ ajCls P0 (t i)` is attained;
* `surjective_PhiN`: `Φ_g` is surjective (closed image, contains every closed point by `exists_eff_rep`, `J` Jacobson);
* **`isProper_Jac : IsProper (Jac K F).hom`** (`UniversallyClosed.of_comp_surjective`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Proper

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (K F) in
/-- `X1` as an object over `Spec K`. -/
noncomputable abbrev X1O : Over (Spec (.of K)) := Over.mk (toSpecK K (algebraMap K[X] F X) 1)

variable (K F) in
/-- The chart `A` of `X1` as a map over `Spec K`. -/
noncomputable def ιO (A : (ChartIdx K)ᵒᵖ) :
    specO K (SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1) ⟶ X1O K F :=
  Over.homMk (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A) (ι_toSpecK K _ 1 A)

variable (P0 : Place K F)

variable (K F) in
/-- `X1^n` over `Spec K`. -/
noncomputable def PP : ℕ → Over (Spec (.of K))
  | 0 => 𝟙_ (Over (Spec (.of K)))
  | n + 1 => PP n ⊗ X1O K F

end Proper

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_CoreB_Dim =====
section

/-!
# Core B, O1: the heights on the Jacobian are bounded

* `ringKrullDim_le_of_finiteType`: a finite type algebra over a field has finite Krull dimension.
* `exists_coheight_le_of_isAffineOpen`: on an affine open of a scheme locally of finite type over a field,
  the coheights are bounded.
* `exists_height_le`: a quasi-compact scheme locally of finite type over a field has bounded heights
  (for the specialization order).
* `exists_height_max`: a bound on heights is attained by a least bound `g`.
* `exists_dim_Jac`: `∃ g, (∀ x, height x ≤ g) ∧ ∃ x, g ≤ height x` on `Jac K F`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CoreB

open CategoryTheory AlgebraicGeometry Order

universe u

lemma exists_coheight_le_of_isAffineOpen {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ n : ℕ, ∀ x ∈ U, coheight x ≤ n := by
  have h1 : (f.appLE ⊤ U le_top).hom.FiniteType :=
    (HasRingHomProperty.iff_appLE (P := @LocallyOfFiniteType) (f := f)).1 inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have hs : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective
  obtain ⟨n, hn⟩ := ringKrullDim_le_of_finiteType _
    (h1.comp (RingHom.FiniteType.of_surjective _ hs))
  refine ⟨n, fun x hx => ?_⟩
  rw [← SetLike.mem_coe, ← hU.range_fromSpec] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [coheight_eq_of_isOpenImmersion hU.fromSpec, ← idealHeight_eq_coheight]
  have : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y
  have h2 := (Ideal.height_le_ringKrullDim_of_isPrime (I := y.asIdeal)).trans hn
  exact_mod_cast h2

lemma exists_height_le {X : Scheme.{u}} {K : Type u} [Field K] [CompactSpace X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] : ∃ N : ℕ, ∀ x : X, height x ≤ N := by
  have hV : ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) := fun x => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨U, hU⟩, hxU⟩
  choose V hxV using hV
  choose n hn using fun x => exists_coheight_le_of_isAffineOpen f (V x).2
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun x => ((V x : X.Opens) : Set X))
    (fun x => (V x : X.Opens).isOpen.mem_nhds (hxV x))
  have hcoh : ∀ x : X, coheight x ≤ (t.sup n : ℕ) := fun x => by
    have hx : x ∈ ⋃ y ∈ t, ((V y : X.Opens) : Set X) := by rw [ht]; trivial
    simp only [Set.mem_iUnion] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact (hn y x hxy).trans (by exact_mod_cast Finset.le_sup (f := n) hy)
  refine ⟨t.sup n, fun x => ?_⟩
  have h1 : krullDim X ≤ (t.sup n : ℕ) := by
    rw [krullDim_eq_iSup_coheight]
    exact iSup_le fun a => by exact_mod_cast hcoh a
  have h2 := (height_le_krullDim x).trans h1
  exact_mod_cast h2

lemma exists_height_max {α : Type*} [Preorder α] [Nonempty α] (N : ℕ) (h : ∀ x : α, height x ≤ N) :
    ∃ g : ℕ, (∀ x : α, height x ≤ g) ∧ ∃ x : α, (g : ℕ∞) ≤ height x := by
  let S : Set ℕ := {n | ∃ x : α, (n : ℕ∞) ≤ height x}
  have hbdd : BddAbove S := ⟨N, fun n ⟨x, hx⟩ => by exact_mod_cast hx.trans (h x)⟩
  have h0 : S.Nonempty := ⟨0, Classical.arbitrary α, by simp⟩
  refine ⟨sSup S, fun x => ?_, Nat.sSup_mem h0 hbdd⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, height x = k :=
    ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top N) (h x)) |>.imp fun _ h => h.symm
  rw [hk]
  exact_mod_cast le_csSup hbdd ⟨x, hk.ge⟩

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

end RamanujanPetersson.CoreB


end

-- ===== S4.Def_RP_JacAlg_Defs =====
section

/-!
# Core B algebra, part 1: the `DegreeData` interface (unit S4-JacAlg, lemma L1)

`A` is an abelian group (in the application `Pic⁰(X̄) = J(F̄_q)`), `π` an additive endomorphism of `A`
(the arithmetic Frobenius) and `deg F` the degree of the endomorphism `F(π_J)` of the Jacobian, for
`F ∈ ℤ[X]`. The fields are (D1)-(D3) of `S4_COREB_ROUTE.md` (reduction F1):
* (D1) `deg` is multiplicative with `deg 1 = 1`;
* (D2) `deg (n • F + G)` is a polynomial in `n ∈ ℤ` of degree `≤ 2g`, and `deg n = n ^ (2g)`;
* (D3) `deg F = 0` iff `Ker F(π)` is infinite, and `deg F = #Ker F(π)` when `p ∤ F(0)`.
Every geometric Core B unit delivers exactly this structure.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacAlg

open Polynomial

/-- Degree data on `ℤ[π]` (S4_COREB_ROUTE.md, F1). -/
structure DegreeData {A : Type*} [AddCommGroup A] (π : Module.End ℤ A) (g p : ℕ) where
  /-- `deg F` = degree of the isogeny `F(π)` (`0` if `F(π)` is not an isogeny). -/
  deg : ℤ[X] → ℕ
  deg_one : deg 1 = 1
  deg_mul : ∀ F G : ℤ[X], deg (F * G) = deg F * deg G
  deg_natCast : ∀ n : ℕ, deg (n : ℤ[X]) = n ^ (2 * g)
  deg_poly : ∀ F G : ℤ[X], ∃ P : ℚ[X], P.natDegree ≤ 2 * g ∧
    ∀ n : ℤ, (deg (n • F + G) : ℚ) = P.eval (n : ℚ)
  deg_eq_zero_iff : ∀ F : ℤ[X], deg F = 0 ↔ (LinearMap.ker (aeval π F) : Set A).Infinite
  deg_eq_card_ker : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 →
    deg F = Nat.card (LinearMap.ker (aeval π F))

namespace DegreeData

variable {A : Type*} [AddCommGroup A] {π : Module.End ℤ A} {g p : ℕ} (D : DegreeData π g p)

theorem deg_neg_one : D.deg (-1) = 1 := by
  have h := D.deg_mul (-1) (-1)
  rw [neg_one_mul, neg_neg, D.deg_one] at h
  exact Nat.eq_one_of_mul_eq_one_right h.symm

theorem deg_neg (F : ℤ[X]) : D.deg (-F) = D.deg F := by
  rw [← neg_one_mul, D.deg_mul, D.deg_neg_one, one_mul]

/-- The polynomial of (D2) for the pencil `n • F + G`. -/
noncomputable def polyOf (F G : ℤ[X]) : ℚ[X] := Classical.choose (D.deg_poly F G)

theorem polyOf_natDegree_le (F G : ℤ[X]) : (D.polyOf F G).natDegree ≤ 2 * g :=
  (Classical.choose_spec (D.deg_poly F G)).1

end DegreeData

end RamanujanPetersson.JacAlg


end


