-- Prove2me | Definitions.Def_FiniteFields_Dwork_Devissage
-- name    : FiniteFields_Dwork_Devissage
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T01:39:31.342205+00:00
-- url     : https://prove2.me/theorems/313f45e0-481d-4b97-8d30-df5f68175940
-- title:
--   Coordinate strata, affine zero loci, open–closed pieces and finite affine covers for Dwork's reduction to hypersurfaces
-- statement:
--   Let $k$ be a finite field with $q$ elements and $\mathbb F_{q^s}$ its extension of degree $s\ge1$. This file provides the geometric objects that reduce the zeta function of a separated finite-type $k$-scheme to toric hypersurfaces.
--
--   1. **Coordinate strata.** For an injection $\iota:\{1,\dots,e\}\to\{1,\dots,d\}$, the restriction $f|_\iota$ of a polynomial $f$ in $d$ variables has, at $x^v$, the coefficient of $x^{\iota_*v}$ in $f$. For $S\subseteq\{1,\dots,d\}$, $f_S$ is the restriction to the variables in $S$, and the coordinate support of a tuple $x\in\mathbb F_{q^s}^d$ is $\{i : x_i\neq0\}$. The file also gives the bijection
--   $$\{x\in\mathbb F_{q^s}^d : f(x)=0,\ \{i:x_i\neq0\}=S\}\ \cong\ \{y\in(\mathbb F_{q^s}^{\times})^{S} : f_S(y)=0\}.$$
--   2. **Affine zero loci.** For a finite set $F$ of polynomials over $k$, $V(F)=\operatorname{Spec}k[x_1,\dots,x_d]/(F)$. Its $\mathbb F_{q^s}$-points are identified with the common solutions in $\mathbb F_{q^s}^d$, and the file defines its point counts and its zeta series $\exp\big(\sum_{s\ge1}N_s(V(F))t^s/s\big)$.
--   3. **Transport of points.** A $k$-algebra isomorphism induces an isomorphism of spectra, and an isomorphism of schemes over $k$ induces a bijection of $\mathbb F_{q^s}$-points. Such points are finite for spectra of finite-type $k$-algebras.
--   4. **Points along immersions.** Each $\mathbb F_{q^s}$-point $P$ has an image point in $X$, the image of the closed point. For a preimmersion $Y\to X$, the $\mathbb F_{q^s}$-points of $Y$ correspond bijectively to the $\mathbb F_{q^s}$-points of $X$ whose image point lies in the image of $Y$.
--   5. **Open–closed decomposition.** For an open $U\subseteq X$, the complement $X\setminus U$ carries its reduced induced closed subscheme structure, and both pieces have finitely many $\mathbb F_{q^s}$-points when $X$ does.
--   6. **Finite affine covers.** A *finite affine intersection cover* of $X$ is a finite family of open subschemes $(U_i)_{i\in I}$ covering $X$ such that every nonempty finite intersection $U_S=\bigcap_{i\in S}U_i$ is affine. The file constructs such a cover for every quasi-compact separated $X$ over $k$.
--   7. **Reduction and general zeta series.** The reduction $X_{\mathrm{red}}$ is the closed subscheme defined by the nilradical, with a bijection $X_{\mathrm{red}}(\mathbb F_{q^s})\cong X(\mathbb F_{q^s})$. For $X$ of finite type over $k$,
--   $$Z(X;t)=\exp\Big(\sum_{s\ge1}\frac{\#X(\mathbb F_{q^s})}{s}\,t^s\Big)\in\mathbb Q[[t]].$$
--
--   The file also contains the structural lemmas these constructions require, such as the evaluation identity for restricted polynomials, reducedness of the closed complements and of $X_{\mathrm{red}}$, and finiteness of point sets of opens and closed complements.
--
--   These objects carry out the reductions of Dwork's paper: the passage from affine algebraic sets to hypersurfaces and from hypersurfaces to their toric strata (§3, (15)), and the extension to abstract varieties by a finite affine cover and inclusion–exclusion (§5, Application 2). The series $Z(X;t)$ is the zeta function of the Introduction for a separated finite-type scheme over $k$.
--
--   **Formalization Note** Point counts are indexed from $0$ in Lean (index $n$ refers to degree $n+1$), and the zeta series uses the count at index $s-1$ for the coefficient of $t^s$. The general zeta series is defined for any finite-type structure morphism; separatedness is needed only for the cover construction and for the rationality theorems.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, Introduction (definition of $\zeta(V;t)$); §3, reductions (15) to toric hypersurfaces; §5, Application 2 (abstract varieties via a finite affine covering and inclusion–exclusion). Lean: ported from the `finite_fields` project (commit e8b5bf14), modules `WeilConjectures/Dwork/AffineHypersurfaceRationality/PolynomialRestriction.lean`, `WeilConjectures/Dwork/AffineHypersurfaceRationality/CoordinateStrata.lean`, `WeilConjectures/Dwork/AffineDevissage/ZeroLocusGeometry.lean`, `WeilConjectures/Dwork/AffineDevissage/Presentation.lean`, `WeilConjectures/Dwork/LocallyClosedDevissage/PreimmersionPoints.lean`, `WeilConjectures/Dwork/LocallyClosedDevissage/OpenComplement.lean`, `WeilConjectures/Dwork/AffineCoverDevissage/Cover.lean`, `WeilConjectures/Dwork/AffineCoverDevissage/Construction.lean`, `WeilConjectures/Dwork/GeneralRationality.lean`.

import Mathlib
import Definitions.Def_FiniteFields_Dwork_Meromorphy

section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
section Restriction
variable {k : Type} [CommRing k] {d e : ℕ}
def monomialExtend (ι : Fin e → Fin d) (v : MonomialIndex e) : MonomialIndex d :=
  Finsupp.mapDomain ι v
theorem monomialExtend_injective {ι : Fin e → Fin d} (hι : Function.Injective ι) :
    Function.Injective (monomialExtend ι) := Finsupp.mapDomain_injective hι
theorem monomialExtend_apply_of_not_mem {ι : Fin e → Fin d} (v : MonomialIndex e) {i : Fin d}
    (hi : i ∉ Set.range ι) : monomialExtend ι v i = 0 :=
  Finsupp.mapDomain_notin_range (f := ι) v i hi
theorem monomialExtend_apply {ι : Fin e → Fin d} (hι : Function.Injective ι)
    (v : MonomialIndex e) (j : Fin e) : monomialExtend ι v (ι j) = v j := by
  rw [monomialExtend, Finsupp.mapDomain_apply hι]
def restrictPoly {ι : Fin e → Fin d} (hι : Function.Injective ι) (f : MonomialIndex d →₀ k) :
    MonomialIndex e →₀ k :=
  Finsupp.comapDomain (monomialExtend ι) f ((monomialExtend_injective hι).injOn)
@[simp]
theorem restrictPoly_apply {ι : Fin e → Fin d} (hι : Function.Injective ι)
    (f : MonomialIndex d →₀ k) (v : MonomialIndex e) :
    restrictPoly hι f v = f (monomialExtend ι v) := rfl
theorem mem_support_restrictPoly {ι : Fin e → Fin d} (hι : Function.Injective ι)
    (f : MonomialIndex d →₀ k) (v : MonomialIndex e) :
    v ∈ (restrictPoly hι f).support ↔ monomialExtend ι v ∈ f.support := by
  classical
  rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff, restrictPoly_apply]
theorem monomialExtend_comapDomain {ι : Fin e → Fin d} (hι : Function.Injective ι)
    (u : MonomialIndex d) (hu : ∀ i, i ∉ Set.range ι → u i = 0) :
    monomialExtend ι (Finsupp.comapDomain ι u hι.injOn) = u := by
  ext i
  by_cases hi : i ∈ Set.range ι
  · obtain ⟨j, rfl⟩ := hi
    rw [monomialExtend_apply hι, Finsupp.comapDomain_apply]
  · rw [monomialExtend_apply_of_not_mem _ hi, hu i hi]
variable {K : Type} [CommRing K] [Algebra k K]
theorem prod_monomialExtend {ι : Fin e → Fin d} (hι : Function.Injective ι)
    (v : MonomialIndex e) (x : Fin d → K) :
    ∏ i, x i ^ (monomialExtend ι v) i = ∏ j, x (ι j) ^ v j := by
  classical
  have himg : ∏ i ∈ Finset.univ.image ι, x i ^ (monomialExtend ι v) i
      = ∏ j : Fin e, x (ι j) ^ v j := by
    rw [Finset.prod_image (fun a _ b _ h ↦ hι h)]
    exact Finset.prod_congr rfl fun j _ ↦ by rw [monomialExtend_apply hι]
  rw [← himg]
  refine (Finset.prod_subset (Finset.subset_univ _) ?_).symm
  intro i _ hi
  have hnot : i ∉ Set.range ι := by
    rintro ⟨j, rfl⟩
    exact hi (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  rw [monomialExtend_apply_of_not_mem v hnot, pow_zero]
theorem finitePolynomialEval_restrictPoly {ι : Fin e → Fin d} (hι : Function.Injective ι)
    (f : MonomialIndex d →₀ k) (x : Fin d → K)
    (hx : ∀ i, i ∉ Set.range ι → x i = 0) :
    finitePolynomialEval k K f x
      = finitePolynomialEval k K (restrictPoly hι f) (fun j ↦ x (ι j)) := by
  classical
  rw [finitePolynomialEval_eq_sum, finitePolynomialEval_eq_sum]
  set A : Finset (MonomialIndex d) := (restrictPoly hι f).support.image (monomialExtend ι) with hA
  have hAsub : A ⊆ f.support := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact (mem_support_restrictPoly hι f v).mp hv
  have hvanish : ∀ u ∈ f.support, u ∉ A →
      algebraMap k K (f u) * ∏ i, x i ^ u i = 0 := by
    intro u hu hnot
    have hexists : ∃ i, i ∉ Set.range ι ∧ u i ≠ 0 := by
      by_contra hcon
      have hcon' : ∀ i, i ∉ Set.range ι → u i = 0 := by
        intro i hi
        by_contra hui
        exact hcon ⟨i, hi, hui⟩
      have hext := monomialExtend_comapDomain hι u hcon'
      refine hnot (Finset.mem_image.mpr ⟨Finsupp.comapDomain ι u hι.injOn, ?_, hext⟩)
      rw [mem_support_restrictPoly, hext]
      exact hu
    obtain ⟨i, hi, hui⟩ := hexists
    have hzero : ∏ i', x i' ^ u i' = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hx i hi, zero_pow hui])
    rw [hzero, mul_zero]
  rw [← Finset.sum_subset hAsub hvanish, hA,
    Finset.sum_image (fun a _ b _ h ↦ monomialExtend_injective hι h)]
  exact Finset.sum_congr rfl fun v _ ↦ by rw [restrictPoly_apply, prod_monomialExtend hι]
end Restriction
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
section EvalBridge
theorem aeval_eq_finitePolynomialEval {R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] {d : ℕ} (f : MvPolynomial (Fin d) R) (x : Fin d → A) :
    MvPolynomial.aeval x f = finitePolynomialEval R A (AddMonoidAlgebra.coeff f) x := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', finitePolynomialEval_eq_sum]
  rfl
end EvalBridge
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
section Strata
variable {d : ℕ}
def stratumIndex (S : Finset (Fin d)) : Fin S.card → Fin d :=
  fun j ↦ ((S.orderIsoOfFin rfl) j : Fin d)
theorem stratumIndex_injective (S : Finset (Fin d)) : Function.Injective (stratumIndex S) :=
  (S.orderEmbOfFin rfl).injective
theorem stratumIndex_mem (S : Finset (Fin d)) (j : Fin S.card) : stratumIndex S j ∈ S :=
  S.orderEmbOfFin_mem rfl j
theorem range_stratumIndex (S : Finset (Fin d)) :
    Set.range (stratumIndex S) = (S : Set (Fin d)) :=
  S.range_orderEmbOfFin rfl
theorem stratumIndex_orderIso_symm {S : Finset (Fin d)} {i : Fin d} (hi : i ∈ S) :
    stratumIndex S ((S.orderIsoOfFin rfl).symm ⟨i, hi⟩) = i :=
  congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨i, hi⟩)
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
def stratumPoly (f : MvPolynomial (Fin d) k) (S : Finset (Fin d)) : MonomialIndex S.card →₀ k :=
  restrictPoly (stratumIndex_injective S) (AddMonoidAlgebra.coeff f)
open scoped Classical in
def coordinateSupport {n : ℕ} (x : Fin d → Extension k p n) : Finset (Fin d) :=
  Finset.univ.filter fun i ↦ x i ≠ 0
omit [Finite k] in
theorem mem_coordinateSupport {n : ℕ} (x : Fin d → Extension k p n) (i : Fin d) :
    i ∈ coordinateSupport k p x ↔ x i ≠ 0 := by
  classical
  simp [coordinateSupport]
omit [Finite k] in
theorem eq_zero_of_not_mem_coordinateSupport {n : ℕ} {x : Fin d → Extension k p n} {i : Fin d}
    (hi : i ∉ coordinateSupport k p x) : x i = 0 := by
  by_contra h
  exact hi ((mem_coordinateSupport k p x i).mpr h)
def stratumExtend {n : ℕ} (S : Finset (Fin d)) (y : Fin S.card → Extension k p n) :
    Fin d → Extension k p n :=
  fun i ↦ if h : i ∈ S then y ((S.orderIsoOfFin rfl).symm ⟨i, h⟩) else 0
omit [Finite k] in
theorem stratumExtend_of_mem {n : ℕ} (S : Finset (Fin d)) (y : Fin S.card → Extension k p n)
    {i : Fin d} (hi : i ∈ S) :
    stratumExtend k p S y i = y ((S.orderIsoOfFin rfl).symm ⟨i, hi⟩) := dif_pos hi
omit [Finite k] in
theorem stratumExtend_of_not_mem {n : ℕ} (S : Finset (Fin d)) (y : Fin S.card → Extension k p n)
    {i : Fin d} (hi : i ∉ S) : stratumExtend k p S y i = 0 := dif_neg hi
omit [Finite k] in
@[simp]
theorem stratumExtend_stratumIndex {n : ℕ} (S : Finset (Fin d))
    (y : Fin S.card → Extension k p n) (j : Fin S.card) :
    stratumExtend k p S y (stratumIndex S j) = y j := by
  rw [stratumExtend_of_mem k p S y (stratumIndex_mem S j)]
  congr 1
  have hsub : (⟨stratumIndex S j, stratumIndex_mem S j⟩ : {a // a ∈ S})
      = (S.orderIsoOfFin rfl) j := rfl
  rw [hsub, OrderIso.symm_apply_apply]
omit [Finite k] in
theorem coordinateSupport_stratumExtend {n : ℕ} (S : Finset (Fin d))
    (y : Fin S.card → Extension k p n) (hy : ∀ j, y j ≠ 0) :
    coordinateSupport k p (stratumExtend k p S y) = S := by
  ext i
  rw [mem_coordinateSupport]
  constructor
  · intro h
    by_contra hi
    exact h (stratumExtend_of_not_mem k p S y hi)
  · intro hi
    rw [stratumExtend_of_mem k p S y hi]
    exact hy _
omit [Finite k] in
theorem stratumExtend_eq_self {n : ℕ} {S : Finset (Fin d)} {x : Fin d → Extension k p n}
    (hx : ∀ i, i ∉ S → x i = 0) :
    stratumExtend k p S (fun j ↦ x (stratumIndex S j)) = x := by
  funext i
  by_cases hi : i ∈ S
  · rw [stratumExtend_of_mem k p S _ hi, stratumIndex_orderIso_symm hi]
  · rw [stratumExtend_of_not_mem k p S _ hi, hx i hi]
theorem aeval_eq_stratum_eval {n : ℕ} (f : MvPolynomial (Fin d) k) (S : Finset (Fin d))
    {x : Fin d → Extension k p n} (hx : ∀ i, i ∉ S → x i = 0) :
    MvPolynomial.aeval x f
      = finitePolynomialEval k (Extension k p n) (stratumPoly k f S)
          (fun j ↦ x (stratumIndex S j)) := by
  rw [aeval_eq_finitePolynomialEval, stratumPoly,
    finitePolynomialEval_restrictPoly (stratumIndex_injective S) _ x
      (fun i hi ↦ hx i fun h ↦ hi ((range_stratumIndex S) ▸ Finset.mem_coe.mpr h))]
def stratumEquiv (f : MvPolynomial (Fin d) k) (n : ℕ) (S : Finset (Fin d)) :
    {x : AffineHypersurfaceTuples k p f n // coordinateSupport k p x.1 = S}
      ≃ toricHypersurfacePoint k p (stratumPoly k f S) n where
  toFun x :=
    ⟨⟨fun j ↦ x.1.1 (stratumIndex S j), fun j ↦ by
        refine (mem_coordinateSupport k p x.1.1 (stratumIndex S j)).mp ?_
        rw [x.2]
        exact stratumIndex_mem S j⟩, by
      have hx : ∀ i, i ∉ S → x.1.1 i = 0 := by
        intro i hi
        exact eq_zero_of_not_mem_coordinateSupport k p (by rw [x.2]; exact hi)
      rw [← aeval_eq_stratum_eval k p f S hx]
      exact x.1.2⟩
  invFun y :=
    ⟨⟨stratumExtend k p S y.1.1, by
        have hy : (fun j ↦ stratumExtend k p S y.1.1 (stratumIndex S j)) = y.1.1 := by
          funext j
          exact stratumExtend_stratumIndex k p S y.1.1 j
        rw [aeval_eq_stratum_eval k p f S
          (fun i hi ↦ stratumExtend_of_not_mem k p S _ hi), hy]
        exact y.2⟩,
      coordinateSupport_stratumExtend k p S _ y.1.2⟩
  left_inv x := by
    refine Subtype.ext (Subtype.ext ?_)
    exact stratumExtend_eq_self k p fun i hi ↦
      eq_zero_of_not_mem_coordinateSupport k p (by rw [x.2]; exact hi)
  right_inv y := by
    refine Subtype.ext (Subtype.ext ?_)
    funext j
    exact stratumExtend_stratumIndex k p S y.1.1 j
end Strata
end FiniteFields.Dwork
end
end

section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ}
abbrev AffineZeroLocusRing (F : Finset (MvPolynomial (Fin d) k)) : Type :=
  MvPolynomial (Fin d) k ⧸ Ideal.span (F : Set (MvPolynomial (Fin d) k))
def affineZeroLocusScheme (F : Finset (MvPolynomial (Fin d) k)) : Scheme :=
  Spec (.of (AffineZeroLocusRing k F))
def affineZeroLocusHom (F : Finset (MvPolynomial (Fin d) k)) :
    affineZeroLocusScheme k F ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (AffineZeroLocusRing k F)))
omit [Finite k] in
theorem aeval_eq_zero_of_mem_span {F : Finset (MvPolynomial (Fin d) k)} {K : Type} [CommRing K]
    [Algebra k K] {x : Fin d → K} (hx : ∀ g ∈ F, MvPolynomial.aeval x g = 0)
    {a : MvPolynomial (Fin d) k} (ha : a ∈ Ideal.span (F : Set (MvPolynomial (Fin d) k))) :
    MvPolynomial.aeval x a = 0 := by
  have hle : Ideal.span (F : Set (MvPolynomial (Fin d) k))
      ≤ RingHom.ker ((MvPolynomial.aeval x : MvPolynomial (Fin d) k →ₐ[k] K) : _ →+* K) :=
    Ideal.span_le.mpr fun g hg ↦ RingHom.mem_ker.mpr (hx g (Finset.mem_coe.mp hg))
  exact RingHom.mem_ker.mp (hle ha)
omit [Finite k] in
def zeroLocusAlgHomEquiv (F : Finset (MvPolynomial (Fin d) k)) (K : Type) [CommRing K]
    [Algebra k K] :
    (AffineZeroLocusRing k F →ₐ[k] K)
      ≃ {x : Fin d → K // ∀ g ∈ F, MvPolynomial.aeval x g = 0} where
  toFun φ :=
    ⟨fun i => φ (Ideal.Quotient.mk _ (MvPolynomial.X i)), by
      intro g hg
      have hcomp : (MvPolynomial.aeval fun i => φ (Ideal.Quotient.mk _ (MvPolynomial.X i)))
          = φ.comp (Ideal.Quotient.mkₐ k (Ideal.span (F : Set (MvPolynomial (Fin d) k)))) := by
        apply MvPolynomial.algHom_ext
        intro i
        simp
      have hg' := DFunLike.congr_fun hcomp g
      rw [hg']
      show φ (Ideal.Quotient.mk _ g) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Finset.mem_coe.mpr hg)),
        map_zero]⟩
  invFun x :=
    Ideal.Quotient.liftₐ _ (MvPolynomial.aeval x.1) fun _ ha ↦
      aeval_eq_zero_of_mem_span k x.2 ha
  left_inv φ := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.liftₐ_apply]
    erw [Ideal.Quotient.lift_mk]
    simp
  right_inv x := by
    ext i
    simp only [Ideal.Quotient.liftₐ_apply]
    erw [Ideal.Quotient.lift_mk]
    simp
def affineZeroLocusExtensionPointEquiv (F : Finset (MvPolynomial (Fin d) k)) (n : ℕ) :
    ExtensionPoint (k := k) (p := p) (affineZeroLocusScheme k F) (affineZeroLocusHom k F) n
      ≃ {x : Fin d → Extension k p n // ∀ g ∈ F, MvPolynomial.aeval x g = 0} :=
  (specRationalPointAlgHomEquiv k (AffineZeroLocusRing k F) (Extension k p n)).trans
    (zeroLocusAlgHomEquiv k F (Extension k p n))
abbrev AffineZeroLocusTuples (F : Finset (MvPolynomial (Fin d) k)) (n : ℕ) : Type :=
  {x : Fin d → Extension k p n // ∀ g ∈ F, MvPolynomial.aeval x g = 0}
instance finite_affineZeroLocusExtensionPoint (F : Finset (MvPolynomial (Fin d) k)) (n : ℕ) :
    Finite (ExtensionPoint (k := k) (p := p) (affineZeroLocusScheme k F)
      (affineZeroLocusHom k F) n) :=
  Finite.of_equiv _ (affineZeroLocusExtensionPointEquiv k p F n).symm
def affineZeroLocusPointCount (F : Finset (MvPolynomial (Fin d) k)) (n : ℕ) : ℕ :=
  pointCount (k := k) (p := p) (affineZeroLocusScheme k F) (affineZeroLocusHom k F) n
end FiniteFields.Dwork
end
end

section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ}
section ZetaProduct
def affineZeroLocusZetaSeries (F : Finset (MvPolynomial (Fin d) k)) : ℚ⟦X⟧ :=
  zetaSeriesOf (affineZeroLocusPointCount k p F)
end ZetaProduct
end FiniteFields.Dwork
end
end

section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ}
section Presentation
variable {A B : Type} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
omit [Finite k] [Fact p.Prime] [CharP k p] in
def specAlgEquiv (e : A ≃ₐ[k] B) : Spec (.of B) ≅ Spec (.of A) where
  hom := Spec.map (CommRingCat.ofHom (e.toAlgHom.toRingHom))
  inv := Spec.map (CommRingCat.ofHom (e.symm.toAlgHom.toRingHom))
  hom_inv_id := by
    have hcomp : CommRingCat.ofHom (e.symm.toAlgHom.toRingHom)
        ≫ CommRingCat.ofHom (e.toAlgHom.toRingHom) = 𝟙 (CommRingCat.of B) := by
      ext b
      exact e.apply_symm_apply b
    rw [← Spec.map_comp, hcomp, Spec.map_id]
  inv_hom_id := by
    have hcomp : CommRingCat.ofHom (e.toAlgHom.toRingHom)
        ≫ CommRingCat.ofHom (e.symm.toAlgHom.toRingHom) = 𝟙 (CommRingCat.of A) := by
      ext a
      exact e.symm_apply_apply a
    rw [← Spec.map_comp, hcomp, Spec.map_id]
def extensionPointCongr {X Y : Scheme} {πX : X ⟶ Spec (.of k)} {πY : Y ⟶ Spec (.of k)}
    (ι : X ≅ Y) (hι : ι.hom ≫ πY = πX) (n : ℕ) :
    ExtensionPoint (k := k) (p := p) X πX n ≃ ExtensionPoint (k := k) (p := p) Y πY n where
  toFun P :=
    ⟨P.hom ≫ ι.hom, by rw [Category.assoc, hι]; exact P.over_base⟩
  invFun Q :=
    ⟨Q.hom ≫ ι.inv, by
      have hinv : ι.inv ≫ πX = πY := by
        rw [← hι, Iso.inv_hom_id_assoc]
      rw [Category.assoc, hinv]
      exact Q.over_base⟩
  left_inv := by
    rintro ⟨hom, hb⟩
    have h : (hom ≫ ι.hom) ≫ ι.inv = hom := by
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simp only [h]
  right_inv := by
    rintro ⟨hom, hb⟩
    have h : (hom ≫ ι.inv) ≫ ι.hom = hom := by
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simp only [h]
instance finite_extensionPoint_of_finiteType (A : Type) [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (n : ℕ) :
    Finite (ExtensionPoint (k := k) (p := p) (Spec (.of A))
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) n) := by
  obtain ⟨m, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType k A)
  have hpoly : Finite (MvPolynomial (Fin m) k →ₐ[k] Extension k p n) := by
    refine Finite.of_injective
      (fun φ : MvPolynomial (Fin m) k →ₐ[k] Extension k p n ↦ fun i ↦ φ (MvPolynomial.X i)) ?_
    intro φ ψ h
    exact MvPolynomial.algHom_ext fun i ↦ congrFun h i
  have halg : Finite (A →ₐ[k] Extension k p n) := by
    refine Finite.of_injective (fun φ : A →ₐ[k] Extension k p n ↦ φ.comp f) ?_
    intro φ ψ h
    ext a
    obtain ⟨q, rfl⟩ := hf a
    exact congrArg (fun g : MvPolynomial (Fin m) k →ₐ[k] Extension k p n ↦ g q) h
  exact Finite.of_equiv _ (specRationalPointAlgHomEquiv k A (Extension k p n)).symm
end Presentation
end FiniteFields.Dwork
end
end

section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
section Preimmersion
instance isIso_residueFieldMap_of_surjectiveOnStalks {X Y : Scheme} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : IsIso (f.residueFieldMap x) := by
  refine (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(f.residueFieldMap x).hom.injective, fun z ↦ ?_⟩
  obtain ⟨w, hw⟩ := X.residue_surjective x z
  obtain ⟨v, hv⟩ := f.stalkMap_surjective x w
  refine ⟨Y.residue (f.base x) v, ?_⟩
  have hc := congrArg (fun m : Y.presheaf.stalk (f.base x) ⟶ X.residueField x ↦ m v)
    (Scheme.residue_residueFieldMap f x)
  simp only [CommRingCat.comp_apply] at hc
  rw [hc, hv, hw]
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
def extensionPointBase {X : Scheme} {π : X ⟶ Spec (.of k)} {n : ℕ}
    (P : ExtensionPoint (k := k) (p := p) X π n) : X :=
  P.hom.base (IsLocalRing.closedPoint (Extension k p n))
def extensionPointAlong {X Y : Scheme} (f : Y ⟶ X) [IsPreimmersion f]
    (π : X ⟶ Spec (.of k)) (n : ℕ) :
    ExtensionPoint (k := k) (p := p) Y (f ≫ π) n
      ≃ {P : ExtensionPoint (k := k) (p := p) X π n //
          extensionPointBase k p P ∈ Set.range f.base} := by
  classical
  refine Equiv.ofBijective
    (fun Q ↦ ⟨⟨Q.hom ≫ f, by rw [Category.assoc]; exact Q.over_base⟩,
      ⟨Q.hom.base (IsLocalRing.closedPoint (Extension k p n)), rfl⟩⟩) ⟨?_, ?_⟩
  · rintro ⟨h₁, hb₁⟩ ⟨h₂, hb₂⟩ he
    have hcomp : h₁ ≫ f = h₂ ≫ f := congrArg (fun r ↦ r.val.hom) he
    have h12 : h₁ = h₂ := (cancel_mono f).mp hcomp
    simp only [h12]
  · rintro ⟨P, y, hy⟩
    have hy' : f.base y = P.hom.base (IsLocalRing.closedPoint (Extension k p n)) := hy
    have hP := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField
      (Extension k p n) X P.hom
    have hgf : (Spec.map (inv (f.residueFieldMap y) ≫ (X.residueFieldCongr hy').hom
            ≫ X.descResidueField (Scheme.stalkClosedPointTo P.hom))
          ≫ Y.fromSpecResidueField y) ≫ f = P.hom := by
      rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f y,
        ← Spec.map_comp_assoc, IsIso.hom_inv_id_assoc, Spec.map_comp_assoc,
        Scheme.residueFieldCongr_fromSpecResidueField hy', hP]
    refine ⟨⟨Spec.map (inv (f.residueFieldMap y) ≫ (X.residueFieldCongr hy').hom
        ≫ X.descResidueField (Scheme.stalkClosedPointTo P.hom))
          ≫ Y.fromSpecResidueField y, ?_⟩, ?_⟩
    · rw [← Category.assoc, hgf]
      exact P.over_base
    · refine Subtype.ext ?_
      simp only [hgf]
theorem finite_extensionPoint_along {X Y : Scheme} (f : Y ⟶ X) [IsPreimmersion f]
    (π : X ⟶ Spec (.of k)) (n : ℕ) [Finite (ExtensionPoint (k := k) (p := p) X π n)] :
    Finite (ExtensionPoint (k := k) (p := p) Y (f ≫ π) n) :=
  Finite.of_equiv _ (extensionPointAlong k p f π n).symm
end Preimmersion
end FiniteFields.Dwork
end
end

section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
section OpenComplement
variable {X : Scheme}
def openComplementCloseds (U : X.Opens) : TopologicalSpace.Closeds X :=
  ⟨(↑U : Set X)ᶜ, U.2.isClosed_compl⟩
@[simp]
theorem coe_openComplementCloseds (U : X.Opens) :
    (openComplementCloseds U : Set X) = (↑U : Set X)ᶜ := rfl
def openComplementIdeal (U : X.Opens) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (openComplementCloseds U)
abbrev openComplement (U : X.Opens) : Scheme := (openComplementIdeal U).subscheme
abbrev openComplementι (U : X.Opens) : openComplement U ⟶ X := (openComplementIdeal U).subschemeι
instance isReduced_openComplement (U : X.Opens) : IsReduced (openComplement U) := by
  haveI hchart : ∀ V : X.affineOpens,
      _root_.IsReduced ((openComplementIdeal U).subschemeCover.X V : Type _) := by
    intro V
    show _root_.IsReduced (Γ(X, V.1) ⧸ (openComplementIdeal U).ideal V)
    rw [← Ideal.isRadical_iff_quotient_reduced]
    show ((openComplementIdeal U).ideal V).IsRadical
    rw [openComplementIdeal, Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  haveI : ∀ i, IsReduced ((openComplementIdeal U).subschemeCover.openCover.X i) := by
    intro V
    show IsReduced (Spec ((openComplementIdeal U).subschemeCover.X V))
    have := hchart V
    exact inferInstance
  exact IsReduced.of_openCover _ (openComplementIdeal U).subschemeCover.openCover
section Comparison
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable (π : X ⟶ Spec (.of k))
instance finite_extensionPoint_openComplement (U : X.Opens) (n : ℕ)
    [Finite (ExtensionPoint (k := k) (p := p) X π n)] :
    Finite (ExtensionPoint (k := k) (p := p) (openComplement U) (openComplementι U ≫ π) n) :=
  finite_extensionPoint_along k p (openComplementι U) π n
instance finite_extensionPoint_opens (U : X.Opens) (n : ℕ)
    [Finite (ExtensionPoint (k := k) (p := p) X π n)] :
    Finite (ExtensionPoint (k := k) (p := p) U.toScheme (U.ι ≫ π) n) :=
  finite_extensionPoint_along k p U.ι π n
end Comparison
end OpenComplement
end FiniteFields.Dwork
end
end

section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
structure FiniteAffineIntersectionCover (X : Scheme) where
  I₀ : Type
  fintypeI₀ : Fintype I₀
  decEqI₀ : DecidableEq I₀
  chart : I₀ → X.Opens
  covers : ∀ x : X, ∃ i, x ∈ chart i
  isAffineOpen_inf : ∀ S : Finset I₀, S.Nonempty → IsAffineOpen (S.inf chart)
namespace FiniteAffineIntersectionCover
variable {X : Scheme} (𝒞 : FiniteAffineIntersectionCover X)
attribute [instance] fintypeI₀ decEqI₀
def coverInter (S : Finset 𝒞.I₀) : X.Opens := S.inf 𝒞.chart
end FiniteAffineIntersectionCover
end FiniteFields.Dwork
end
end

section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
section Charts
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {X : Scheme} (π : X ⟶ Spec (.of k))
def extensionPoint_mem_affineCover (U : X.Opens) (n : ℕ) :
    ExtensionPoint (k := k) (p := p) U.toScheme (U.ι ≫ π) n
      ≃ {P : ExtensionPoint (k := k) (p := p) X π n // extensionPointBase k p P ∈ U} :=
  (extensionPointAlong k p U.ι π n).trans
    (Equiv.subtypeEquivRight fun P ↦ by simp [Scheme.Opens.range_ι])
end Charts
end FiniteFields.Dwork
end
end

section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
section Construction
theorem isAffineOpen_finsetInf {X : Scheme} [X.IsSeparated] {ι : Type*} (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) {S : Finset ι} (hS : S.Nonempty) :
    IsAffineOpen (S.inf U) := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton i => rw [Finset.inf_singleton]; exact hU i
  | cons i s _ _ ih => rw [Finset.inf_cons]; exact (hU i).inf ih
noncomputable def finiteAffineIntersectionCoverOfSeparatedFiniteType {k : Type} [Field k]
    {X : Scheme} (π : X ⟶ Spec (.of k)) [QuasiCompact π] [IsSeparated π] :
    FiniteAffineIntersectionCover X :=
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  letI : X.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from π]
    infer_instance⟩
  { I₀ := X.affineCover.finiteSubcover.I₀
    fintypeI₀ := inferInstance
    decEqI₀ := Classical.decEq _
    chart := fun i ↦ (X.affineCover.finiteSubcover.f i).opensRange
    covers := fun x ↦ X.affineCover.finiteSubcover.isOpenCover_opensRange.exists_mem x
    isAffineOpen_inf := fun S hS ↦
      isAffineOpen_finsetInf _ (fun i ↦ isAffineOpen_opensRange _) hS }
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
end Construction
end FiniteFields.Dwork
end
end

section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
abbrev reduction (X : Scheme) : Scheme := X.nilradical.subscheme
abbrev reductionι (X : Scheme) : reduction X ⟶ X := X.nilradical.subschemeι
@[simp]
theorem range_reductionι (X : Scheme) : Set.range (reductionι X).base = Set.univ := by
  simp
instance isReduced_reduction (X : Scheme) : IsReduced (reduction X) := by
  haveI hchart : ∀ U : X.affineOpens,
      _root_.IsReduced (X.nilradical.subschemeCover.X U : Type _) := by
    intro U
    show _root_.IsReduced (Γ(X, U.1) ⧸ X.nilradical.ideal U)
    rw [← Ideal.isRadical_iff_quotient_reduced]
    show (Ideal.radical _).IsRadical
    exact Ideal.radical_isRadical _
  haveI : ∀ i, IsReduced (X.nilradical.subschemeCover.openCover.X i) := by
    intro U
    show IsReduced (Spec (X.nilradical.subschemeCover.X U))
    have := hchart U
    exact inferInstance
  exact IsReduced.of_openCover _ X.nilradical.subschemeCover.openCover
section Reduction
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {X : Scheme} (π : X ⟶ Spec (.of k))
def extensionPointReductionEquiv (n : ℕ) :
    ExtensionPoint (k := k) (p := p) (reduction X) (reductionι X ≫ π) n
      ≃ ExtensionPoint (k := k) (p := p) X π n :=
  (extensionPointAlong k p (reductionι X) π n).trans
    (Equiv.subtypeUnivEquiv fun _ ↦ by rw [range_reductionι]; trivial)
end Reduction
section General
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {X : Scheme} (π : X ⟶ Spec (.of k))
def separatedFiniteTypeZetaSeries (hπ : Schemes.FiniteType π) : PowerSeries ℚ :=
  zetaSeriesOf (fun n ↦ pointCount_of_finiteType k p X π hπ n)
end General
end FiniteFields.Dwork
end
end


