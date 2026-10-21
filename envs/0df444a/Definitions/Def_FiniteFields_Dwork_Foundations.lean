-- Prove2me | Definitions.Def_FiniteFields_Dwork_Foundations
-- name    : FiniteFields_Dwork_Foundations
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T01:25:32.697309+00:00
-- url     : https://prove2.me/theorems/4fd32b5e-9eb3-402f-a283-8707e1f01a09
-- title:
--   Foundations for Dwork's proof: point counts, zeta series, Witt coefficients and the overconvergent Tate algebra
-- statement:
--   This file introduces the arithmetic, algebraic and analytic objects on which the whole formalization of Dwork's rationality proof is built. Throughout, $k$ is a finite field of characteristic $p$ with $q=\#k$ elements, and $\mathbb F_{q^{s}}$ denotes the extension of $k$ of degree $s\ge 1$.
--
--   1. **Points and point counts.** For a scheme $X$ with structure morphism $\pi : X\to\operatorname{Spec}k$, an $\mathbb F_{q^s}$-point is a morphism $\operatorname{Spec}\mathbb F_{q^s}\to X$ over $\operatorname{Spec}k$, and
--   $$N_s(X)=\#\{P:\operatorname{Spec}\mathbb F_{q^s}\to X \ \text{ over } \operatorname{Spec}k\}.$$
--   This set is finite when $\pi$ is of finite type (locally of finite type and quasi-compact). The file also introduces affine space $\mathbb A^d_k$, whose $\mathbb F_{q^s}$-points are identified with $\mathbb F_{q^s}^d$, the arithmetic Frobenius $x\mapsto x^q$ of $\mathbb F_{q^s}$ over $k$, and the affine hypersurface $V(f)=\operatorname{Spec}k[x_1,\dots,x_d]/(f)$ of a polynomial $f$, whose $\mathbb F_{q^s}$-points are identified with the solutions $x\in\mathbb F_{q^s}^d$ of $f(x)=0$.
--   2. **Zeta series.** For a counting sequence $(N_s)_{s\ge1}$ the formal zeta series is
--   $$Z(t)=\exp\Big(\sum_{s\ge1}\frac{N_s}{s}\,t^s\Big)\in\mathbb Q[[t]],$$
--   and a series $Z$ is called a zeta series of $(N_s)$ when $Z(0)=1$ and $Z'(t)=\big(\sum_{s\ge0}N_{s+1}t^{s}\big)Z(t)$. The zeta series $Z(V(f);t)$ of an affine hypersurface is this series for $N_s=N_s(V(f))$. For the Euler product, $\nu_e$ is the number of solutions over $\mathbb F_{q^e}$ whose Frobenius orbit has exact length $e$, divided by $e$, and the partial products $\prod_{e=1}^{M}(1-t^e)^{-\nu_e}$ are formed in $\mathbb Q[[t]]$ and in $\mathbb Z[[t]]$.
--   3. **Rationality and Hankel determinants.** Over a field $K$, a series $F=\sum_n a_nt^n$ is *rational* if $QF=P$ for polynomials $P,Q$ with $Q\neq0$ and $Q(0)\neq0$. Its Hankel minors are $H_r^{(n)}(F)=\det\big(a_{n+i+j}\big)_{0\le i,j<r}$. The file defines an eventual linear recurrence of the coefficients, *Hankel rank $r$ from index $N$ on* ($H_r^{(n)}\neq0$ and $H_{r+1}^{(n)}=0$ for all $n\ge N$), and eventual vanishing of the minors of some fixed size $r>0$.
--   4. **Unramified coefficients.** The ring $W(k)$ of $p$-typical Witt vectors, the residue map $W(k)\to k$, the Teichmüller lift $a\mapsto\hat a$, and the Witt Frobenius $\sigma$, an automorphism lifting $x\mapsto x^p$. The coefficient field $K_0$ is the completion of $\operatorname{Frac}W(k)$ for the discrete valuation of the maximal ideal of $W(k)$, normalized by $v(p)=1$. It is a complete nonarchimedean normed field of characteristic $0$, and $\sigma$ extends to a continuous automorphism of $K_0$.
--   5. **Monomials and weights.** Exponent vectors $u\in\mathbb N^d$, positive weights $w\in\mathbb Z_{>0}^d$, the weight $|u|_w=\sum_i w_iu_i$, and the finite cutoffs $\{u : |u|_w\le N\}$.
--   6. **Tate algebra and exponent division.** For a nonarchimedean normed field $K$, the Banach space $c_0(\mathbb N^d,K)$ of coefficient families tending to $0$, and the Tate algebra
--   $$K\langle x_1,\dots,x_d\rangle=\Big\{g=\sum_{u\in\mathbb N^d}a_u x^u \ :\ a_u\to0\Big\},\qquad \|g\|=\sup_u|a_u|,$$
--   with the Cauchy product. It is a normed commutative $K$-algebra with ultrametric norm, and it is complete when $K$ is. Dwork's exponent-division operator $\psi_p$, given by $(\psi_p g)_u=a_{pu}$, is a continuous $K$-linear endomorphism of norm at most $1$. The file also defines the exponent dilation $u\mapsto pu$.
--   7. **The ramified field.** $L=K_0(\zeta)$ is the $p$-th cyclotomic extension of $K_0$, with the spectral norm, so $L$ is complete and ultrametric. Here $\zeta$ is its canonical primitive $p$-th root of unity, and $\lambda=\zeta-1\neq0$.
--
--   The file also contains the structural lemmas these definitions need, such as uniqueness for linear formal differential equations, finiteness of point sets of finite-type schemes, valuation and completion facts for $K_0$, and the ring axioms of the Tate algebra.
--
--   These objects are the setting of Dwork's Introduction and of §§1–2: the zeta function, the unramified field with its Frobenius, the element $\lambda$, and the space of power series on which the operator $\psi$ acts. They also include the algebraic Hankel-determinant language of the rationality criterion in §4.
--
--   **Formalization Note** Extensions are indexed from $0$: the Lean index $n$ stands for the extension of degree $n+1$, so the coefficient of $t^s$ in the zeta series uses the count at index $s-1$. In the carrier $c_0(\mathbb N^d,K)$ the weight $w$ is only a type parameter and does not change the norm. The Tate algebra is a one-field wrapper around this carrier that adds the convolution product. The valuation on $K_0$ is written multiplicatively in Lean, as $v(p)=\exp(-1)$, which is the additive normalization $v(p)=1$.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, Introduction (the zeta function $\zeta(V;t)=\exp(\sum_{s\ge1}N_st^s/s)$ and integrality of its coefficients); §1 (unramified field $L$, Frobenius $\sigma$, $1+\lambda$ a primitive $p$-th root of unity); §2 (power series spaces and the operator $\psi$); §4 (Hankel determinants, criterion (27)). Lean: ported from the `finite_fields` project (commit e8b5bf14), modules `WeilConjectures/Schemes/RationalPoints.lean`, `WeilConjectures/FiniteField/Extension.lean`, `WeilConjectures/Zeta/CountingSeries.lean`, `WeilConjectures/Dwork/AffineHypersurfaceZeta/SchemeGeometry.lean`, `WeilConjectures/Dwork/AffineHypersurfaceZeta/EulerIntegrality.lean`, `WeilConjectures/Dwork/HankelRationality/Basic.lean`, `WeilConjectures/Dwork/Coefficients.lean`, `WeilConjectures/Dwork/CoefficientField.lean`, `WeilConjectures/Dwork/MonomialWeight.lean`, `WeilConjectures/Dwork/OverconvergentSeries.lean`, `WeilConjectures/Dwork/OverconvergentTateAlgebra.lean`, `WeilConjectures/Dwork/ExponentProjection.lean`, `WeilConjectures/Dwork/CyclotomicExtension.lean`.

import Mathlib

section
namespace PowerSeries
variable {R : Type*} [CommRing R] [IsAddTorsionFree R]
theorem coeff_eq_of_derivative_eq_mul {N : ℕ} {f g a b : R⟦X⟧}
    (hf : derivative R f = f * a) (hg : derivative R g = g * b)
    (h0 : constantCoeff f = constantCoeff g)
    (hab : ∀ j, j + 1 < N → coeff j a = coeff j b) :
    ∀ m, m < N → coeff m f = coeff m g := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    cases m with
    | zero => simpa only [coeff_zero_eq_constantCoeff] using h0
    | succ n =>
      have e1 := congrArg (coeff n) hf
      have e2 := congrArg (coeff n) hg
      rw [coeff_derivative, coeff_mul] at e1 e2
      have equ : coeff (n + 1) f * (n + 1) = coeff (n + 1) g * (n + 1) := by
        rw [e1, e2]
        refine Finset.sum_congr rfl ?_
        rintro ⟨i, j⟩ hij
        have hsum : i + j = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
        rw [ih i (by omega) (by omega), hab j (by omega)]
      rw [← Nat.cast_succ, mul_comm, ← nsmul_eq_mul,
        mul_comm, ← nsmul_eq_mul] at equ
      exact (smul_right_inj (Nat.succ_ne_zero n)).mp equ
theorem eq_of_derivative_eq_mul {f g a : R⟦X⟧}
    (hf : derivative R f = f * a) (hg : derivative R g = g * a)
    (h0 : constantCoeff f = constantCoeff g) : f = g := by
  ext m
  exact coeff_eq_of_derivative_eq_mul (N := m + 1) hf hg h0
    (fun _ _ => rfl) m (Nat.lt_succ_self m)
end PowerSeries
end

section
noncomputable section
namespace FiniteFields.Schemes
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
variable {X Y Z S : Scheme.{u}}
abbrev FiniteType (f : X ⟶ Y) : Prop := LocallyOfFiniteType f ∧ QuasiCompact f
end FiniteFields.Schemes
end
end

section
noncomputable section
namespace FiniteFields
variable (k : Type*) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
abbrev Extension (n : ℕ) : Type :=
  FiniteField.Extension k p (n + 1)
instance (n : ℕ) : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
abbrev AffinePoints (d n : ℕ) : Type :=
  Fin d → Extension k p n
end FiniteFields
end
end

section
noncomputable section
namespace FiniteFields
open CategoryTheory AlgebraicGeometry
variable (k : Type) [Field k]
structure RationalPoint
    (X : Scheme) (pi : X ⟶ Spec (.of k))
    (K : Type) [Field K] [Algebra k K] where
  hom : Spec (.of K) ⟶ X
  over_base : hom ≫ pi = Spec.map (CommRingCat.ofHom (algebraMap k K))
variable [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
abbrev ExtensionPoint
    (X : Scheme) (pi : X ⟶ Spec (.of k)) (n : ℕ) :=
  RationalPoint k X pi (Extension k p n)
def pointCount
    (X : Scheme) (pi : X ⟶ Spec (.of k)) (n : ℕ)
    [Finite (ExtensionPoint (k := k) (p := p) X pi n)] : ℕ :=
  Nat.card (ExtensionPoint (k := k) (p := p) X pi n)
end FiniteFields
end
end

section
noncomputable section
namespace FiniteFields
open CategoryTheory AlgebraicGeometry
 theorem finite_algHom_of_finiteType
    (R A B : Type) [CommSemiring R] [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra R B] [Algebra.FiniteType R A] [Finite B] :
    Finite (A →ₐ[R] B) := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R A).out
  let evaluation : (A →ₐ[R] B) → (s → B) := fun f x ↦ f x
  apply Finite.of_injective evaluation
  intro f g h
  apply AlgHom.ext_of_adjoin_eq_top hs
  intro x hx
  exact congr_fun h ⟨x, hx⟩
 theorem finite_rationalPoint_spec
    (k K R : Type) [Field k] [Field K] [CommRing R] [Finite K] [Algebra k K]
    (f : CommRingCat.of k ⟶ CommRingCat.of R) (hf : f.hom.FiniteType) :
    Finite (RationalPoint k (Spec (.of R)) (Spec.map f) K) := by
  algebraize [f.hom]
  haveI : Algebra.FiniteType k R := RingHom.finiteType_algebraMap.mp hf
  let toAlgHom : RationalPoint k (Spec (.of R)) (Spec.map f) K → (R →ₐ[k] K) :=
    fun x ↦
      { (Spec.preimage x.hom).hom with
        commutes' := by
          have h := congrArg Spec.preimage x.over_base
          have h' : (f ≫ Spec.preimage x.hom).hom =
              (CommRingCat.ofHom (algebraMap k K)).hom := by
            exact congrArg CommRingCat.Hom.hom <| by
              simpa only [Spec.preimage_comp, Spec.preimage_map] using h
          intro r
          exact DFunLike.congr_fun h' r }
  have : Finite (R →ₐ[k] K) := finite_algHom_of_finiteType k R K
  apply Finite.of_injective toAlgHom
  intro x y h
  cases x with
  | mk x hx =>
    cases y with
    | mk y hy =>
      congr 1
      apply Spec.homEquiv.injective
      apply CommRingCat.hom_ext
      change (Spec.preimage x).hom = (Spec.preimage y).hom
      exact congrArg AlgHom.toRingHom h
 theorem finite_rationalPoint_of_isAffine
    (k K : Type) [Field k] [Field K] [Finite K] [Algebra k K]
    (X : Scheme) [IsAffine X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    Finite (RationalPoint k X f K) := by
  let g : Spec Γ(X, ⊤) ⟶ Spec (.of k) := X.isoSpec.inv ≫ f
  haveI : LocallyOfFiniteType g := inferInstance
  have hfinite : Finite (RationalPoint k (Spec Γ(X, ⊤)) g K) := by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective g
    rw [← hφ]
    apply finite_rationalPoint_spec k K Γ(X, ⊤) φ
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rw [hφ]
    infer_instance
  let toSpecPoint : RationalPoint k X f K →
      RationalPoint k (Spec Γ(X, ⊤)) g K := fun x ↦
    { hom := x.hom ≫ X.isoSpec.hom
      over_base := by simp only [g, Category.assoc, Iso.hom_inv_id_assoc, x.over_base] }
  apply Finite.of_injective toSpecPoint
  intro x y h
  cases x with
  | mk x hx =>
    cases y with
    | mk y hy =>
      congr 1
      exact (cancel_mono X.isoSpec.hom).mp (congrArg RationalPoint.hom h)
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
theorem finite_extensionPoint_of_finiteType
    (X : Scheme) (f : X ⟶ Spec (.of k)) (hf : Schemes.FiniteType f) (n : ℕ) :
    Finite (ExtensionPoint (k := k) (p := p) X f n) := by
  let K := Extension k p n
  letI : LocallyOfFiniteType f := hf.1
  letI : QuasiCompact f := hf.2
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let Ucover : X.OpenCover := X.affineCover.finiteSubcover
  let chartIndex (x : RationalPoint k X f K) : Ucover.I₀ :=
    Ucover.idx (x.hom (IsLocalRing.closedPoint (CommRingCat.of K)))
  have range_subset (x : RationalPoint k X f K) :
      Set.range x.hom ⊆ Set.range (Ucover.f (chartIndex x)) := by
    rintro _ ⟨y, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint y).map x.hom.continuous).mem_open
      (Ucover.f _).opensRange.2 (by
        simpa only [chartIndex] using
          Ucover.covers (x.hom (IsLocalRing.closedPoint (CommRingCat.of K))))
  let LocalPoint (i : Ucover.I₀) := RationalPoint k (Ucover.X i) (Ucover.f i ≫ f) K
  letI localPointFinite (i : Ucover.I₀) : Finite (LocalPoint i) := by
    haveI : LocallyOfFiniteType (Ucover.f i ≫ f) := inferInstance
    exact finite_rationalPoint_of_isAffine k K (Ucover.X i) (Ucover.f i ≫ f)
  let encode (x : RationalPoint k X f K) : Σ i, LocalPoint i :=
    ⟨chartIndex x,
      { hom := IsOpenImmersion.lift (Ucover.f (chartIndex x)) x.hom (range_subset x)
        over_base := by
          simpa only [IsOpenImmersion.lift_fac_assoc] using x.over_base }⟩
  let decode : (Σ i, LocalPoint i) → (Spec (.of K) ⟶ X) :=
    fun x ↦ x.2.hom ≫ Ucover.f x.1
  have decode_encode (x : RationalPoint k X f K) : decode (encode x) = x.hom := by
    exact IsOpenImmersion.lift_fac _ _ _
  apply Finite.of_injective encode
  intro x y h
  cases x with
  | mk x hx =>
    cases y with
    | mk y hy =>
      congr 1
      simpa only [decode_encode] using congrArg decode h
instance extensionPointFinite
    (X : Scheme) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] (n : ℕ) :
    Finite (ExtensionPoint (k := k) (p := p) X f n) :=
  finite_extensionPoint_of_finiteType k p X f ⟨inferInstance, inferInstance⟩ n
def pointCount_of_finiteType
    (X : Scheme) (f : X ⟶ Spec (.of k)) (hf : Schemes.FiniteType f) (n : ℕ) : ℕ := by
  letI : LocallyOfFiniteType f := hf.1
  letI : QuasiCompact f := hf.2
  exact pointCount (k := k) (p := p) X f n
end FiniteFields
end
end

section
noncomputable section
namespace FiniteFields
open CategoryTheory AlgebraicGeometry
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
abbrev AffineScheme (d : ℕ) : Scheme :=
  AlgebraicGeometry.AffineSpace (Fin d) (Spec (.of k))
abbrev AffineExtensionPoint (d n : ℕ) :=
  ExtensionPoint (k := k) (p := p) (AffineScheme k d)
    (AffineScheme k d ↘ Spec (.of k)) n
def affineExtensionPointEquiv (d n : ℕ) :
    AffineExtensionPoint k p d n ≃ AffinePoints k p d n := by
  let K := Extension k p n
  letI : (Spec (.of K)).Over (Spec (.of k)) :=
    ⟨Spec.map (CommRingCat.ofHom (algebraMap k K))⟩
  let rationalPointEquivOver :
      AffineExtensionPoint k p d n ≃
        { f : Spec (.of K) ⟶ AffineScheme k d // f.IsOver (Spec (.of k)) } :=
    { toFun := fun x ↦ ⟨x.hom, ⟨x.over_base⟩⟩
      invFun := fun f ↦ ⟨f.1, f.2.1⟩
      left_inv := fun x ↦ by cases x; rfl
      right_inv := fun f ↦ by cases f; rfl }
  let sectionsEquiv :
      (Fin d → Γ(Spec (.of K), ⊤)) ≃ (Fin d → K) :=
    Equiv.piCongrRight fun _ ↦
      (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toEquiv
  exact rationalPointEquivOver.trans
    ((AlgebraicGeometry.AffineSpace.homOverEquiv
      (S := Spec (.of k)) (X := Spec (.of K))).trans sectionsEquiv)
instance finite_affineExtensionPoint (d n : ℕ) :
    Finite (AffineExtensionPoint k p d n) :=
  Finite.of_equiv (AffinePoints k p d n)
    (affineExtensionPointEquiv k p d n).symm
end FiniteFields
end
end

section
noncomputable section
namespace FiniteFields
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
noncomputable def arithmeticFrobenius (n : ℕ) :
    Extension k p n ≃ₐ[k] Extension k p n :=
  FiniteField.Extension.frob k p (n + 1)
@[simp]
theorem arithmeticFrobenius_apply (n : ℕ) (x : Extension k p n) :
    arithmeticFrobenius k p n x = x ^ Nat.card k :=
  FiniteField.Extension.frob_apply k p (n + 1)
end FiniteFields
end
end

section
noncomputable section
namespace FiniteFields
open PowerSeries
def countingSeries (N : ℕ → ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n ↦ (N n : ℚ)
def IsZetaSeries (N : ℕ → ℕ) (Z : ℚ⟦X⟧) : Prop :=
  PowerSeries.constantCoeff Z = 1 ∧
    d⁄dX ℚ Z = countingSeries N * Z
end FiniteFields
end
end

section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ}
abbrev AffineHypersurfaceRing (f : MvPolynomial (Fin d) k) : Type :=
  MvPolynomial (Fin d) k ⧸ Ideal.span {f}
def affineHypersurfaceScheme (f : MvPolynomial (Fin d) k) : Scheme :=
  Spec (.of (AffineHypersurfaceRing k f))
def affineHypersurfaceHom (f : MvPolynomial (Fin d) k) :
    affineHypersurfaceScheme k f ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (AffineHypersurfaceRing k f)))
def hypersurfaceAlgHomEquiv (f : MvPolynomial (Fin d) k)
    (K : Type) [CommRing K] [Algebra k K] :
    (AffineHypersurfaceRing k f →ₐ[k] K)
      ≃ {x : Fin d → K // MvPolynomial.aeval x f = 0} where
  toFun φ :=
    ⟨fun i => φ (Ideal.Quotient.mk _ (MvPolynomial.X i)), by
      have hcomp : (MvPolynomial.aeval fun i => φ (Ideal.Quotient.mk _ (MvPolynomial.X i)))
          = φ.comp (Ideal.Quotient.mkₐ k (Ideal.span {f})) := by
        apply MvPolynomial.algHom_ext
        intro i
        simp
      have hf := DFunLike.congr_fun hcomp f
      rw [hf]
      show φ (Ideal.Quotient.mk _ f) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f), map_zero]⟩
  invFun x :=
    Ideal.Quotient.liftₐ _ (MvPolynomial.aeval x.1) (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, x.2, mul_zero])
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
def specRationalPointAlgHomEquiv (A : Type) [CommRing A] [Algebra k A]
    (K : Type) [Field K] [Algebra k K] :
    RationalPoint k (Spec (.of A))
        (Spec.map (CommRingCat.ofHom (algebraMap k A))) K
      ≃ (A →ₐ[k] K) where
  toFun P :=
    { toRingHom := (Spec.preimage P.hom).hom
      commutes' := fun a => by
        have h : CommRingCat.ofHom (algebraMap k A) ≫ Spec.preimage P.hom
            = CommRingCat.ofHom (algebraMap k K) := by
          apply Spec.map_injective
          rw [Spec.map_comp, Spec.map_preimage]
          exact P.over_base
        exact congrArg (fun g : CommRingCat.of k ⟶ CommRingCat.of K => g.hom a) h }
  invFun ψ :=
    { hom := Spec.map (CommRingCat.ofHom ψ.toRingHom)
      over_base := by
        rw [← Spec.map_comp]
        congr 1
        ext a
        exact ψ.commutes a }
  left_inv P := by
    cases P with
    | mk hom over_base =>
        have hmap : Spec.map (CommRingCat.ofHom ((Spec.preimage hom).hom)) = hom :=
          Spec.map_preimage hom
        simp only [hmap]
  right_inv ψ := by
    ext a
    show (Spec.preimage (Spec.map (CommRingCat.ofHom ψ.toRingHom))).hom a = ψ a
    rw [Spec.preimage_map]
    rfl
def affineHypersurfaceExtensionPointEquiv (f : MvPolynomial (Fin d) k) (n : ℕ) :
    ExtensionPoint (k := k) (p := p) (affineHypersurfaceScheme k f)
        (affineHypersurfaceHom k f) n
      ≃ {x : Fin d → Extension k p n // MvPolynomial.aeval x f = 0} :=
  (specRationalPointAlgHomEquiv k (AffineHypersurfaceRing k f) (Extension k p n)).trans
    (hypersurfaceAlgHomEquiv k f (Extension k p n))
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
abbrev AffineHypersurfaceTuples (f : MvPolynomial (Fin d) k) (n : ℕ) : Type :=
  {x : Fin d → Extension k p n // MvPolynomial.aeval x f = 0}
instance finite_affineHypersurfaceExtensionPoint (f : MvPolynomial (Fin d) k) (n : ℕ) :
    Finite (ExtensionPoint (k := k) (p := p) (affineHypersurfaceScheme k f)
      (affineHypersurfaceHom k f) n) :=
  Finite.of_equiv _ (affineHypersurfaceExtensionPointEquiv k p f n).symm
def affineHypersurfacePointCount (f : MvPolynomial (Fin d) k) (n : ℕ) : ℕ :=
  pointCount (k := k) (p := p) (affineHypersurfaceScheme k f) (affineHypersurfaceHom k f) n
def zetaLog (N : ℕ → ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (N (n - 1) : ℚ) / n
def zetaSeriesOf (N : ℕ → ℕ) : ℚ⟦X⟧ :=
  (PowerSeries.exp ℚ).subst (zetaLog N)
def affineHypersurfaceZetaSeries (f : MvPolynomial (Fin d) k) : ℚ⟦X⟧ :=
  zetaSeriesOf (affineHypersurfacePointCount k p f)
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
noncomputable def towerHom {a b : ℕ} (h : (a + 1) ∣ (b + 1)) :
    Extension k p a →ₐ[k] Extension k p b :=
  (FiniteField.nonempty_algHom_of_finrank_dvd (F := k)
    (K := Extension k p a) (L := Extension k p b) (by
      rw [FiniteField.finrank_extension, FiniteField.finrank_extension]
      exact h)).some
theorem towerHom_injective {a b : ℕ} (h : (a + 1) ∣ (b + 1)) :
    Function.Injective (towerHom k p h) :=
  (towerHom k p h).toRingHom.injective
theorem pow_natCard_pow_self (a : ℕ) (y : Extension k p a) :
    y ^ (Nat.card k ^ (a + 1)) = y := by
  letI := Fintype.ofFinite (Extension k p a)
  have hcard : Fintype.card (Extension k p a) = Nat.card k ^ (a + 1) := by
    rw [Fintype.card_eq_nat_card]
    exact FiniteField.natCard_extension k p (a + 1)
  rw [← hcard]
  exact FiniteField.pow_card y
omit [Finite k] in
theorem card_fixed_le (b Q : ℕ) (hQ : 1 < Q) :
    Nat.card {x : Extension k p b // x ^ Q = x} ≤ Q := by
  classical
  letI := Fintype.ofFinite (Extension k p b)
  have hne : (Polynomial.X ^ Q - Polynomial.X : Polynomial (Extension k p b)) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero _ hQ
  have hsub : (Finset.univ.filter (fun x : Extension k p b => x ^ Q = x)).val
      ⊆ (Polynomial.X ^ Q - Polynomial.X : Polynomial (Extension k p b)).roots := by
    intro x hx
    have hx' : x ^ Q = x := (Finset.mem_filter.mp (Finset.mem_val.mp hx)).2
    rw [Polynomial.mem_roots hne]
    simp [Polynomial.IsRoot, hx']
  have hcard : Nat.card {x : Extension k p b // x ^ Q = x}
      = (Finset.univ.filter (fun x : Extension k p b => x ^ Q = x)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]
  calc (Finset.univ.filter (fun x : Extension k p b => x ^ Q = x)).card
      ≤ (Polynomial.X ^ Q - Polynomial.X : Polynomial (Extension k p b)).natDegree :=
        Polynomial.card_le_degree_of_subset_roots hsub
    _ = Q := FiniteField.X_pow_card_sub_X_natDegree_eq _ hQ
theorem range_towerHom {a b : ℕ} (h : (a + 1) ∣ (b + 1)) :
    Set.range (towerHom k p h) = {x : Extension k p b | x ^ (Nat.card k ^ (a + 1)) = x} := by
  have hsub : Set.range (towerHom k p h) ⊆ {x : Extension k p b | x ^ (Nat.card k ^ (a + 1)) = x} := by
    rintro _ ⟨y, rfl⟩
    show (towerHom k p h y) ^ (Nat.card k ^ (a + 1)) = towerHom k p h y
    rw [← map_pow, pow_natCard_pow_self]
  have hrange : (Set.range (towerHom k p h)).ncard = Nat.card k ^ (a + 1) := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective (towerHom_injective k p h)]
    exact FiniteField.natCard_extension k p (a + 1)
  have hfix : {x : Extension k p b | x ^ (Nat.card k ^ (a + 1)) = x}.ncard
      ≤ Nat.card k ^ (a + 1) := by
    have hQ : 1 < Nat.card k ^ (a + 1) := by
      have h1 : 1 < Nat.card k := Finite.one_lt_card
      exact Nat.one_lt_pow (Nat.succ_ne_zero a) h1
    calc {x : Extension k p b | x ^ (Nat.card k ^ (a + 1)) = x}.ncard
        = Nat.card {x : Extension k p b // x ^ (Nat.card k ^ (a + 1)) = x} := rfl
      _ ≤ Nat.card k ^ (a + 1) := card_fixed_le k p b _ hQ
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [hrange]; exact hfix) (Set.toFinite _)
section Orbits
variable {α : Type*} [DecidableEq α] (φ : α → α) {e : ℕ}
end Orbits
omit [Finite k] in
 theorem aeval_comp {A B : Type*} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (σ : A →ₐ[k] B) (y : Fin d → A) (g : MvPolynomial (Fin d) k) :
    MvPolynomial.aeval (fun i => σ (y i)) g = σ (MvPolynomial.aeval y g) :=
  (MvPolynomial.comp_aeval_apply (f := y) σ g).symm
variable (f : MvPolynomial (Fin d) k)
def solutionFrobenius (n : ℕ) :
    AffineHypersurfaceTuples k p f n → AffineHypersurfaceTuples k p f n :=
  fun x => ⟨fun i => (arithmeticFrobenius k p n).toAlgHom (x.1 i), by
    rw [aeval_comp k (arithmeticFrobenius k p n).toAlgHom, x.2, map_zero]⟩
theorem solutionFrobenius_iterate_coord (n j : ℕ) (x : AffineHypersurfaceTuples k p f n)
    (i : Fin d) :
    ((solutionFrobenius k p f n)^[j] x).1 i = (x.1 i) ^ (Nat.card k ^ j) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply, ih]
      show ((arithmeticFrobenius k p n).toAlgHom (x.1 i)) ^ (Nat.card k ^ j) = _
      show ((arithmeticFrobenius k p n) (x.1 i)) ^ (Nat.card k ^ j) = _
      rw [arithmeticFrobenius_apply, ← pow_mul, ← pow_succ']
 def towerSolution {a b : ℕ} (h : (a + 1) ∣ (b + 1)) :
    AffineHypersurfaceTuples k p f a → AffineHypersurfaceTuples k p f b :=
  fun y => ⟨fun i => towerHom k p h (y.1 i), by
    rw [aeval_comp k (towerHom k p h), y.2, map_zero]⟩
 theorem towerSolution_injective {a b : ℕ} (h : (a + 1) ∣ (b + 1)) :
    Function.Injective (towerSolution k p f h) := by
  intro y z hyz
  apply Subtype.ext
  funext i
  exact towerHom_injective k p h (congrFun (congrArg Subtype.val hyz) i)
def fixedSolutionEquiv {a b : ℕ} (h : (a + 1) ∣ (b + 1)) :
    AffineHypersurfaceTuples k p f a ≃
      {x : AffineHypersurfaceTuples k p f b //
        (solutionFrobenius k p f b)^[a + 1] x = x} := by
  refine Equiv.ofBijective
    (fun y => ⟨towerSolution k p f h y, ?_⟩) ⟨?_, ?_⟩
  · apply Subtype.ext
    funext i
    rw [solutionFrobenius_iterate_coord]
    show (towerHom k p h (y.1 i)) ^ (Nat.card k ^ (a + 1)) = towerHom k p h (y.1 i)
    rw [← map_pow, pow_natCard_pow_self]
  · intro y z hyz
    exact towerSolution_injective k p f h (congrArg Subtype.val hyz)
  · rintro ⟨x, hx⟩
    have hcoord : ∀ i, ∃ z, towerHom k p h z = x.1 i := by
      intro i
      have hfix : (x.1 i) ^ (Nat.card k ^ (a + 1)) = x.1 i := by
        have := congrFun (congrArg Subtype.val hx) i
        rwa [solutionFrobenius_iterate_coord] at this
      exact (Set.ext_iff.mp (range_towerHom k p h) (x.1 i)).mpr hfix
    choose z hz using hcoord
    have hz0 : MvPolynomial.aeval z f = 0 := by
      apply towerHom_injective k p h
      rw [map_zero, ← aeval_comp k (towerHom k p h)]
      simp only [hz]
      exact x.2
    refine ⟨⟨z, hz0⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact hz i
noncomputable instance instFintypeTuples (n : ℕ) :
    Fintype (AffineHypersurfaceTuples k p f n) := Fintype.ofFinite _
open scoped Classical in
noncomputable def exactPeriodSolutions (n e : ℕ) : Finset (AffineHypersurfaceTuples k p f n) :=
  Finset.univ.filter fun x => Function.minimalPeriod (solutionFrobenius k p f n) x = e
noncomputable def orbitCount (e : ℕ) : ℕ :=
  (exactPeriodSolutions k p f (e - 1) e).card / e
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
variable (f : MvPolynomial (Fin d) k)
def geomFactor (R : Type*) [CommRing R] (e : ℕ) : PowerSeries R :=
  PowerSeries.mk fun j => if e ∣ j then 1 else 0
noncomputable def eulerPartialQ (M : ℕ) : ℚ⟦X⟧ :=
  ∏ e ∈ Finset.Icc 1 M, (geomFactor ℚ e) ^ (orbitCount k p f e)
noncomputable def eulerLogDeriv (M : ℕ) : ℚ⟦X⟧ :=
  ∑ e ∈ Finset.Icc 1 M,
    (orbitCount k p f e : ℚ⟦X⟧) * (e : ℚ⟦X⟧) * PowerSeries.X ^ (e - 1) * geomFactor ℚ e
noncomputable def eulerPartialZ (M : ℕ) : PowerSeries ℤ :=
  ∏ e ∈ Finset.Icc 1 M, (geomFactor ℤ e) ^ (orbitCount k p f e)
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries Finset
open scoped Polynomial
namespace FiniteFields.Dwork
variable {K : Type*} [Field K]
def IsRationalPowerSeries (F : K⟦X⟧) : Prop :=
  ∃ P Q : K[X], Q ≠ 0 ∧ Q.eval 0 ≠ 0 ∧ (Q : K⟦X⟧) * F = (P : K⟦X⟧)
def CoefficientRecurrence (F : K⟦X⟧) : Prop :=
  ∃ (r N : ℕ) (c : ℕ → K),
    ∀ n, N ≤ n → coeff (n + r) F = ∑ i ∈ range r, c i * coeff (n + i) F
def hankelMinor (F : K⟦X⟧) (r n : ℕ) : K :=
  (Matrix.of fun i j : Fin r => coeff (n + (i : ℕ) + (j : ℕ)) F).det
def HankelRank (F : K⟦X⟧) (r N : ℕ) : Prop :=
  (∀ n, N ≤ n → hankelMinor F r n ≠ 0) ∧ (∀ n, N ≤ n → hankelMinor F (r + 1) n = 0)
def HankelEventuallyZero (F : K⟦X⟧) : Prop :=
  ∃ r N : ℕ, HankelRank F r N
def FixedSizeHankelEventuallyZero (F : K⟦X⟧) : Prop :=
  ∃ r N : ℕ, 0 < r ∧ ∀ n, N ≤ n → hankelMinor F r n = 0
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries Finset
open scoped Polynomial
namespace FiniteFields.Dwork
variable {K : Type*} [Field K]
 def recurrenceDenominator (r : ℕ) (c : ℕ → K) : K[X] :=
  1 - ∑ i ∈ range r, Polynomial.C (c i) * Polynomial.X ^ (r - i)
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries Finset
open scoped Polynomial
namespace FiniteFields.Dwork
variable {K : Type*} [Field K]
 def hankelMatrix (F : K⟦X⟧) (m n : ℕ) : Matrix (Fin m) (Fin m) K :=
  Matrix.of fun i j => coeff (n + (i : ℕ) + (j : ℕ)) F
end FiniteFields.Dwork
end
end

section
noncomputable section
namespace FiniteFields.Dwork
abbrev CoefficientRing (k : Type*) (p : ℕ) := WittVector p k
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k]
def residueMap : CoefficientRing k p →+* k :=
  WittVector.constantCoeff
def teichmullerLift : k →* CoefficientRing k p :=
  WittVector.teichmuller p
def frobeniusLift : CoefficientRing k p →+* CoefficientRing k p :=
  WittVector.frobenius
@[simp]
theorem residueMap_apply (x : CoefficientRing k p) : residueMap k p x = x.coeff 0 :=
  rfl
variable [CharP k p]
variable [Finite k]
def frobeniusLiftEquiv : CoefficientRing k p ≃+* CoefficientRing k p :=
  WittVector.frobeniusEquiv p k
@[simp]
theorem frobeniusLiftEquiv_apply (x : CoefficientRing k p) :
    frobeniusLiftEquiv k p x = frobeniusLift k p x :=
  rfl
end FiniteFields.Dwork
end
end

section
noncomputable section
open scoped WithZero
namespace FiniteFields.Dwork
abbrev CoefficientFractionField (k : Type*) (p : ℕ) [Fact p.Prime] [CommRing k] :=
  FractionRing (CoefficientRing k p)
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
instance coefficientRingCharZero : CharZero (CoefficientRing k p) := by
  rw [CharZero.charZero_iff_forall_prime_ne_zero]
  intro q hq hqzero
  have hqk : (q : k) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (residueMap k p) hqzero
  have hpq : p ∣ q := (CharP.cast_eq_zero_iff k p q).mp hqk
  have hp_eq_q : p = q :=
    (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) hq).mp hpq
  exact WittVector.p_nonzero p k (by simpa only [hp_eq_q] using hqzero)
instance coefficientFractionFieldCharZero :
    CharZero (CoefficientFractionField k p) :=
  charZero_of_injective_ringHom
    (IsFractionRing.injective (CoefficientRing k p) (CoefficientFractionField k p))
def coefficientValuation : Valuation (CoefficientFractionField k p) ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal (CoefficientRing k p)).valuation
    (CoefficientFractionField k p)
theorem coefficientValuation_p :
    coefficientValuation k p
        (algebraMap (CoefficientRing k p) (CoefficientFractionField k p) p) =
      WithZero.exp (-1 : ℤ) := by
  rw [coefficientValuation, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact (IsDiscreteValuationRing.maximalIdeal (CoefficientRing k p)).intValuation_singleton
    (WittVector.p_nonzero p k)
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp (WittVector.irreducible p))
theorem coefficientValuation_surjective : Function.Surjective (coefficientValuation k p) := by
  intro γ
  rcases γ with _ | z
  · exact ⟨0, (coefficientValuation k p).map_zero⟩
  · refine ⟨(p : CoefficientFractionField k p) ^ (-z.toAdd), ?_⟩
    rw [map_zpow₀, show (p : CoefficientFractionField k p) =
      algebraMap (CoefficientRing k p) (CoefficientFractionField k p) p by simp,
      coefficientValuation_p, ← WithZero.exp_zsmul]
    rw [show (-z.toAdd) • (-1 : ℤ) = z.toAdd by simp]
    exact congrArg Option.some (ofAdd_toAdd z)
theorem coefficientAddVal_frobenius (a : CoefficientRing k p) :
    IsDiscreteValuationRing.addVal (CoefficientRing k p) (frobeniusLiftEquiv k p a) =
      IsDiscreteValuationRing.addVal (CoefficientRing k p) a := by
  by_cases ha : a = 0
  · simp [ha]
  · obtain ⟨n, u, rfl⟩ := WittVector.exists_eq_pow_p_mul' (p := p) a ha
    have hu : IsUnit (frobeniusLiftEquiv k p (u : CoefficientRing k p)) :=
      IsUnit.map (frobeniusLiftEquiv k p).toRingHom u.isUnit
    rw [frobeniusLiftEquiv_apply] at hu
    have hz := IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hu
    simp [map_mul, map_pow, hz]
theorem coefficientIntValuation_frobenius (a : CoefficientRing k p) :
    (IsDiscreteValuationRing.maximalIdeal (CoefficientRing k p)).intValuation
        (frobeniusLiftEquiv k p a) =
      (IsDiscreteValuationRing.maximalIdeal (CoefficientRing k p)).intValuation a := by
  simp only [IsDiscreteValuationRing.intValuation_maximalIdeal,
    coefficientAddVal_frobenius]
theorem coefficientValuation_frobenius (x : CoefficientFractionField k p) :
    coefficientValuation k p (WittVector.FractionRing.frobenius p k x) =
      coefficientValuation k p x := by
  obtain ⟨a, b, _hb, hx⟩ := IsFractionRing.div_surjective (CoefficientRing k p) x
  rw [← hx, map_div₀]
  have hf (c : CoefficientRing k p) :
      WittVector.FractionRing.frobenius p k
          (algebraMap (CoefficientRing k p) (CoefficientFractionField k p) c) =
        algebraMap (CoefficientRing k p) (CoefficientFractionField k p)
          (frobeniusLiftEquiv k p c) :=
    IsFractionRing.ringEquivOfRingEquiv_algebraMap (frobeniusLiftEquiv k p) c
  rw [hf a, hf b, Valuation.map_div, Valuation.map_div]
  simp only [coefficientValuation,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    coefficientIntValuation_frobenius]
def coefficientValuedFrobenius :
    WithVal (coefficientValuation k p) ≃+* WithVal (coefficientValuation k p) :=
  WithVal.congr (coefficientValuation k p) (coefficientValuation k p)
    (WittVector.FractionRing.frobenius p k)
 theorem coefficientValuedFrobenius_value
    (x : WithVal (coefficientValuation k p)) :
    Valued.v (coefficientValuedFrobenius k p x) = Valued.v x := by
  change coefficientValuation k p
      (WittVector.FractionRing.frobenius p k x.ofVal) = coefficientValuation k p x.ofVal
  exact coefficientValuation_frobenius k p x.ofVal
theorem coefficientValuedFrobenius_uniformContinuous :
    UniformContinuous (coefficientValuedFrobenius k p) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  use γ
  intro x hx
  have hr : Valued.v.restrict (coefficientValuedFrobenius k p x) =
      Valued.v.restrict x :=
    (Valuation.restrict_inj
      (Valued.v : Valuation (WithVal (coefficientValuation k p)) _)).mpr
        (coefficientValuedFrobenius_value k p x)
  change Valued.v.restrict (coefficientValuedFrobenius k p x) < γ.1
  rw [hr]
  exact hx
theorem coefficientValuedFrobenius_symm_uniformContinuous :
    UniformContinuous (coefficientValuedFrobenius k p).symm := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  use γ
  intro x hx
  have hv : Valued.v ((coefficientValuedFrobenius k p).symm x) = Valued.v x := by
    have h := coefficientValuedFrobenius_value k p
      ((coefficientValuedFrobenius k p).symm x)
    simpa using h.symm
  have hr : Valued.v.restrict ((coefficientValuedFrobenius k p).symm x) =
      Valued.v.restrict x :=
    (Valuation.restrict_inj
      (Valued.v : Valuation (WithVal (coefficientValuation k p)) _)).mpr hv
  change Valued.v.restrict ((coefficientValuedFrobenius k p).symm x) < γ.1
  rw [hr]
  exact hx
abbrev CoefficientField := (coefficientValuation k p).Completion
noncomputable instance coefficientFieldCharZero : CharZero (CoefficientField k p) := by
  letI : CharZero (WithVal (coefficientValuation k p)) :=
    (RingHom.charZero_iff
      (WithVal.equiv (coefficientValuation k p)).toRingHom.injective).mpr inferInstance
  exact charZero_of_injective_ringHom
    (UniformSpace.Completion.coeRingHom :
      WithVal (coefficientValuation k p) →+* CoefficientField k p).injective
 theorem valuedCoefficientValuation_surjective :
    Function.Surjective
      (Valued.v : WithVal (coefficientValuation k p) → ℤᵐ⁰) := by
  intro γ
  obtain ⟨x, hx⟩ := coefficientValuation_surjective k p γ
  exact ⟨WithVal.toVal (coefficientValuation k p) x, hx⟩
theorem coefficientFieldValuation_surjective :
    Function.Surjective (Valued.v : CoefficientField k p → ℤᵐ⁰) :=
  Valued.valuedCompletion_surjective_iff.mpr
    (valuedCoefficientValuation_surjective k p)
 theorem valueGroup_eq_top_of_surjective
    {R : Type*} [Ring R] {v : Valuation R ℤᵐ⁰} (h : Function.Surjective v) :
    MonoidWithZeroHom.valueGroup (.ofClass v) = ⊤ := by
  apply top_unique
  intro y _hy
  rw [MonoidWithZeroHom.mem_valueGroup_iff_of_comm]
  obtain ⟨x, hx⟩ := h (y : ℤᵐ⁰)
  exact ⟨1, by simp, x, by simp [hx]⟩
noncomputable instance coefficientFieldIsRankOneDiscrete :
    Valuation.IsRankOneDiscrete
      (Valued.v : Valuation (CoefficientField k p) ℤᵐ⁰) := by
  let base : Valuation (CoefficientFractionField k p) ℤᵐ⁰ := coefficientValuation k p
  let completed : Valuation (CoefficientField k p) ℤᵐ⁰ := Valued.v
  letI : Valuation.IsRankOneDiscrete base :=
    IsDiscreteValuationRing.isRankOneDiscrete
      (CoefficientRing k p) (CoefficientFractionField k p)
  refine { exists_generator_lt_one' :=
    ⟨Valuation.IsRankOneDiscrete.generator base, ?_,
      Valuation.IsRankOneDiscrete.generator_lt_one base⟩ }
  rw [Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup]
  rw [valueGroup_eq_top_of_surjective (coefficientValuation_surjective k p)]
  exact (valueGroup_eq_top_of_surjective
    (coefficientFieldValuation_surjective k p)).symm
noncomputable instance coefficientFieldRankOne :
    Valuation.RankOne (Valued.v : Valuation (CoefficientField k p) ℤᵐ⁰) :=
  Valuation.IsRankOneDiscrete.rankOne (e := p)
    (Valued.v : Valuation (CoefficientField k p) ℤᵐ⁰) (by
      exact_mod_cast (Fact.out : p.Prime).two_le)
noncomputable instance coefficientFieldNormedField : NormedField (CoefficientField k p) :=
  Valued.toNormedField (CoefficientField k p) ℤᵐ⁰
noncomputable instance coefficientFieldNontriviallyNormedField :
    NontriviallyNormedField (CoefficientField k p) :=
  Valued.toNontriviallyNormedField (CoefficientField k p) ℤᵐ⁰
theorem coefficientField_norm_p_lt_one : ‖(p : CoefficientField k p)‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff]
  rw [show (p : CoefficientField k p) =
      ((p : WithVal (coefficientValuation k p)) : CoefficientField k p) by
        exact (map_natCast
          (UniformSpace.Completion.coeRingHom :
            WithVal (coefficientValuation k p) →+* CoefficientField k p) p).symm]
  rw [Valued.valuedCompletion_apply]
  change coefficientValuation k p (p : CoefficientFractionField k p) < 1
  rw [show (p : CoefficientFractionField k p) =
      algebraMap (CoefficientRing k p) (CoefficientFractionField k p) p by simp,
    coefficientValuation_p, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num
def coefficientRingAlgebraMap : CoefficientRing k p →+* CoefficientField k p :=
  UniformSpace.Completion.coeRingHom.comp
    ((WithVal.equiv (coefficientValuation k p)).symm.toRingHom.comp
      (algebraMap (CoefficientRing k p) (CoefficientFractionField k p)))
abbrev ValuedCoefficientRing :=
  (RingHom.range
    ((WithVal.equiv (coefficientValuation k p)).symm.toRingHom.comp
      (algebraMap (CoefficientRing k p) (CoefficientFractionField k p))))
def coefficientRingEquivValued :
    CoefficientRing k p ≃+* ValuedCoefficientRing k p := by
  let f : CoefficientRing k p →+* WithVal (coefficientValuation k p) :=
    (WithVal.equiv (coefficientValuation k p)).symm.toRingHom.comp
      (algebraMap (CoefficientRing k p) (CoefficientFractionField k p))
  refine RingEquiv.ofBijective f.rangeRestrict ⟨?_, f.rangeRestrict_surjective⟩
  intro x y hxy
  apply IsFractionRing.injective (CoefficientRing k p) (CoefficientFractionField k p)
  apply WithVal.toVal_injective (coefficientValuation k p)
  exact congrArg Subtype.val hxy
def coefficientRingToField : ValuedCoefficientRing k p →+* CoefficientField k p :=
  UniformSpace.Completion.coeRingHom.comp (Subring.subtype _)
theorem coefficientRingToField_injective : Function.Injective (coefficientRingToField k p) :=
  fun _ _ hxy ↦ Subtype.ext
    (UniformSpace.Completion.coe_injective (WithVal (coefficientValuation k p)) hxy)
@[simp]
theorem coefficientRingToField_equiv_apply (x : CoefficientRing k p) :
    coefficientRingToField k p (coefficientRingEquivValued k p x) =
      coefficientRingAlgebraMap k p x :=
  rfl
theorem coefficientRingAlgebraMap_injective : Function.Injective (coefficientRingAlgebraMap k p) := by
  intro x y hxy
  apply (coefficientRingEquivValued k p).injective
  apply coefficientRingToField_injective k p
  simpa only [coefficientRingToField_equiv_apply] using hxy
def coefficientFieldFrobenius : CoefficientField k p ≃+* CoefficientField k p :=
  UniformSpace.Completion.mapRingEquiv (coefficientValuedFrobenius k p)
    (coefficientValuedFrobenius_uniformContinuous k p).continuous
    (coefficientValuedFrobenius_symm_uniformContinuous k p).continuous
theorem coefficientFieldFrobenius_continuous :
    Continuous (coefficientFieldFrobenius k p) :=
  UniformSpace.Completion.continuous_map
@[simp]
theorem coefficientFieldFrobenius_coe
    (x : WithVal (coefficientValuation k p)) :
    coefficientFieldFrobenius k p (x : CoefficientField k p) =
      (coefficientValuedFrobenius k p x : CoefficientField k p) := by
  exact UniformSpace.Completion.map_coe
    (coefficientValuedFrobenius_uniformContinuous k p) x
end FiniteFields.Dwork
end
end

section
namespace FiniteFields.Dwork
noncomputable section
abbrev MonomialIndex (d : ℕ) := Fin d →₀ ℕ
abbrev PositiveMonomialWeight (d : ℕ) := Fin d → ℕ+
def monomialWeight {d : ℕ} (w : PositiveMonomialWeight d) : MonomialIndex d →+ ℕ :=
  Finsupp.weight fun i ↦ (w i : ℕ)
def totalDegreeWeight (d : ℕ) : PositiveMonomialWeight d :=
  fun _ ↦ 1
def MonomialCutoff {d : ℕ} (w : PositiveMonomialWeight d) (bound : ℕ) :
    Set (MonomialIndex d) :=
  {u | monomialWeight w u ≤ bound}
@[simp]
theorem monomialWeight_zero {d : ℕ} (w : PositiveMonomialWeight d) :
    monomialWeight w 0 = 0 :=
  map_zero (monomialWeight w)
@[simp]
theorem monomialWeight_add {d : ℕ} (w : PositiveMonomialWeight d)
    (u v : MonomialIndex d) :
    monomialWeight w (u + v) = monomialWeight w u + monomialWeight w v :=
  map_add (monomialWeight w) u v
theorem finite_monomialCutoff {d : ℕ} (w : PositiveMonomialWeight d) (bound : ℕ) :
    (MonomialCutoff w bound).Finite := by
  exact Finsupp.finite_of_nat_weight_le (fun i ↦ (w i : ℕ)) (fun i ↦ (w i).ne_zero) bound
end
end FiniteFields.Dwork
end

section
noncomputable section
open Filter Set Topology
open scoped ZeroAtInfty
namespace FiniteFields.Dwork
abbrev DiscreteMonomialIndex (d : ℕ) := WithDiscreteTopology (MonomialIndex d)
abbrev OverconvergentSeries (K : Type*) [NormedAddCommGroup K] (d : ℕ)
    (_w : PositiveMonomialWeight d) :=
  ZeroAtInftyContinuousMap (DiscreteMonomialIndex d) K
variable {K : Type*} [NormedField K]
variable {d : ℕ} (w : PositiveMonomialWeight d)
 def discreteMonomial (u : MonomialIndex d) : DiscreteMonomialIndex d :=
  WithTopology.toTopology ⊥ u
@[simp]
 theorem discreteMonomial_ofTopology (u : DiscreteMonomialIndex d) :
    discreteMonomial u.ofTopology = u :=
  rfl
def seriesCoefficient (u : MonomialIndex d) :
    OverconvergentSeries K d w →L[K] K where
  toFun f := f (discreteMonomial u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (BoundedContinuousFunction.evalCLM K (discreteMonomial u)).continuous.comp
    ZeroAtInftyContinuousMap.isometry_toBCF.continuous
@[simp]
theorem seriesCoefficient_apply (f : OverconvergentSeries K d w) (u : MonomialIndex d) :
    seriesCoefficient w u f = f (discreteMonomial u) :=
  rfl
def weightedCoefficient (π : K) (u : MonomialIndex d) :
    OverconvergentSeries K d w →L[K] K :=
  (π ^ monomialWeight w u) • seriesCoefficient w u
@[simp]
theorem weightedCoefficient_apply (π : K) (f : OverconvergentSeries K d w)
    (u : MonomialIndex d) :
    weightedCoefficient w π u f = π ^ monomialWeight w u * f (discreteMonomial u) := by
  rfl
 def finsuppSeries (π : K) (a : MonomialIndex d →₀ K) :
    OverconvergentSeries K d w where
  toFun u := a u.ofTopology / π ^ monomialWeight w u.ofTopology
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [Filter.cocompact_eq_cofinite]
    refine tendsto_const_nhds.congr' ?_
    let e : MonomialIndex d ↪ DiscreteMonomialIndex d :=
      ⟨discreteMonomial, WithTopology.toTopology_injective ⊥⟩
    filter_upwards [(a.support.map e).eventually_cofinite_notMem] with u hu
    have hsupport : u.ofTopology ∉ a.support := by
      intro hmem
      exact hu (Finset.mem_map.mpr ⟨u.ofTopology, hmem, rfl⟩)
    simp [Finsupp.notMem_support_iff.mp hsupport]
def finsuppToOverconvergentSeries (π : K) :
    (MonomialIndex d →₀ K) →ₗ[K] OverconvergentSeries K d w where
  toFun := finsuppSeries w π
  map_add' a b := by
    ext u
    simp [finsuppSeries, add_div]
  map_smul' c a := by
    ext u
    simp [finsuppSeries, div_eq_mul_inv, mul_assoc]
@[simp]
theorem finsuppToOverconvergentSeries_apply (π : K) (a : MonomialIndex d →₀ K)
    (u : MonomialIndex d) :
    finsuppToOverconvergentSeries w π a (discreteMonomial u) =
      a u / π ^ monomialWeight w u :=
  rfl
@[simp]
theorem weightedCoefficient_finsuppToOverconvergentSeries (π : K) (hπ : π ≠ 0)
    (a : MonomialIndex d →₀ K) (u : MonomialIndex d) :
    weightedCoefficient w π u (finsuppToOverconvergentSeries w π a) = a u := by
  rw [weightedCoefficient_apply, finsuppToOverconvergentSeries_apply,
    mul_div_cancel₀ _ (pow_ne_zero _ hπ)]
theorem overconvergentSeries_norm_add_le_max
    (hK : IsNonarchimedean ((‖·‖) : K → ℝ))
    (f g : OverconvergentSeries K d w) :
    ‖f + g‖ ≤ max ‖f‖ ‖g‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  have hmax : 0 ≤ max ‖f.toBCF‖ ‖g.toBCF‖ :=
    (norm_nonneg _).trans (le_max_left _ _)
  refine (BoundedContinuousFunction.norm_le hmax).2 ?_
  intro u
  exact (hK (f u) (g u)).trans (max_le_max
    (BoundedContinuousFunction.norm_coe_le_norm f.toBCF u)
    (BoundedContinuousFunction.norm_coe_le_norm g.toBCF u))
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Set Topology
open scoped ZeroAtInfty
namespace FiniteFields.Dwork
variable {K : Type*} [NormedField K]
variable {d : ℕ} (w : PositiveMonomialWeight d)
 def toDiscreteMonomial (u : MonomialIndex d) : DiscreteMonomialIndex d :=
  WithTopology.toTopology ⊥ u
@[simp]
 theorem toDiscreteMonomial_ofTopology (u : DiscreteMonomialIndex d) :
    toDiscreteMonomial u.ofTopology = u :=
  rfl
 theorem toDiscreteMonomial_injective :
    Function.Injective (toDiscreteMonomial : MonomialIndex d → DiscreteMonomialIndex d) :=
  WithTopology.toTopology_injective ⊥
@[simp]
 theorem weightedCoefficient_apply_toDiscrete (π : K)
    (f : OverconvergentSeries K d w) (u : MonomialIndex d) :
    weightedCoefficient w π u f = π ^ monomialWeight w u * f (toDiscreteMonomial u) :=
  weightedCoefficient_apply w π f u
@[simp]
 theorem finsuppToOverconvergentSeries_apply_toDiscrete (π : K)
    (a : MonomialIndex d →₀ K) (u : MonomialIndex d) :
    finsuppToOverconvergentSeries w π a (toDiscreteMonomial u) =
      a u / π ^ monomialWeight w u :=
  finsuppToOverconvergentSeries_apply w π a u
 def normalizedPowerSeries (f : OverconvergentSeries K d w) :
    MvPowerSeries (Fin d) K :=
  fun u ↦ f (toDiscreteMonomial u)
 theorem normalizedPowerSeries_injective :
    Function.Injective (normalizedPowerSeries w :
      OverconvergentSeries K d w → MvPowerSeries (Fin d) K) := by
  intro f g h
  ext u
  have hu := congrFun h u.ofTopology
  simpa [normalizedPowerSeries] using hu
 def convolutionCoordinate (f g : OverconvergentSeries K d w)
    (u : MonomialIndex d) : K :=
  ∑ uv ∈ Finset.HasAntidiagonal.antidiagonal u,
    f (toDiscreteMonomial uv.1) * g (toDiscreteMonomial uv.2)
def seriesConvolution (π : K) (f g : OverconvergentSeries K d w)
    (u : MonomialIndex d) : K :=
  ∑ uv ∈ Finset.HasAntidiagonal.antidiagonal u,
    weightedCoefficient w π uv.1 f * weightedCoefficient w π uv.2 g
 theorem convolutionCoordinate_zeroAtInfty [IsUltrametricDist K]
    (f g : OverconvergentSeries K d w) :
    Tendsto (fun u : DiscreteMonomialIndex d ↦
      convolutionCoordinate w f g u.ofTopology) (cocompact _) (𝓝 0) := by
  rw [Filter.cocompact_eq_cofinite, Metric.tendsto_nhds]
  intro ε hε
  let M : ℝ := max ‖f‖ ‖g‖
  let δ : ℝ := (ε / 2) / (M + 1)
  have hM : 0 ≤ M := (norm_nonneg f).trans (le_max_left _ _)
  have hM1 : 0 < M + 1 := by positivity
  have hδ : 0 < δ := div_pos (half_pos hε) hM1
  have hfsmall :
      ∀ᶠ u : DiscreteMonomialIndex d in cofinite, ‖f u‖ < δ := by
    have hf := Metric.tendsto_nhds.mp (zero_at_infty f) δ hδ
    rw [Filter.cocompact_eq_cofinite] at hf
    simpa only [dist_zero_right] using hf
  have hgsmall :
      ∀ᶠ u : DiscreteMonomialIndex d in cofinite, ‖g u‖ < δ := by
    have hg := Metric.tendsto_nhds.mp (zero_at_infty g) δ hδ
    rw [Filter.cocompact_eq_cofinite] at hg
    simpa only [dist_zero_right] using hg
  let A : Set (MonomialIndex d) :=
    {u | ¬‖f (toDiscreteMonomial u)‖ < δ}
  let B : Set (MonomialIndex d) :=
    {u | ¬‖g (toDiscreteMonomial u)‖ < δ}
  have hA : A.Finite := by
    have hfinite : {u : DiscreteMonomialIndex d | ¬‖f u‖ < δ}.Finite :=
      Filter.eventually_cofinite.mp hfsmall
    exact hfinite.preimage (toDiscreteMonomial_injective (d := d)).injOn
  have hB : B.Finite := by
    have hfinite : {u : DiscreteMonomialIndex d | ¬‖g u‖ < δ}.Finite :=
      Filter.eventually_cofinite.mp hgsmall
    exact hfinite.preimage (toDiscreteMonomial_injective (d := d)).injOn
  let E : Set (MonomialIndex d) := Set.image2 (· + ·) A B
  have hE : E.Finite := hA.image2 (· + ·) hB
  let ED : Set (DiscreteMonomialIndex d) := toDiscreteMonomial '' E
  have hED : ED.Finite := hE.image _
  filter_upwards [hED.eventually_cofinite_notMem] with u huD
  have hu : u.ofTopology ∉ E := by
    intro hmem
    exact huD ⟨u.ofTopology, hmem, rfl⟩
  rw [dist_zero_right]
  refine lt_of_le_of_lt
    (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (half_pos hε).le ?_)
    (half_lt_self hε)
  intro uv huv
  have huv_add : uv.1 + uv.2 = u.ofTopology := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  have hsmall : ‖f (toDiscreteMonomial uv.1)‖ < δ ∨
      ‖g (toDiscreteMonomial uv.2)‖ < δ := by
    by_contra h
    rw [not_or, not_lt, not_lt] at h
    apply hu
    exact ⟨uv.1, by simpa [A] using h.1, uv.2, by simpa [B] using h.2, huv_add⟩
  rw [norm_mul]
  rcases hsmall with hf | hg
  · exact le_of_lt <| calc
      ‖f (toDiscreteMonomial uv.1)‖ * ‖g (toDiscreteMonomial uv.2)‖
          ≤ ‖f (toDiscreteMonomial uv.1)‖ * (M + 1) := by
            gcongr
            exact (BoundedContinuousFunction.norm_coe_le_norm g.toBCF _).trans
              ((le_max_right ‖f‖ ‖g‖).trans (le_add_of_nonneg_right zero_le_one))
      _ < δ * (M + 1) := mul_lt_mul_of_pos_right hf hM1
      _ = ε / 2 := div_mul_cancel₀ _ hM1.ne'
  · exact le_of_lt <| calc
      ‖f (toDiscreteMonomial uv.1)‖ * ‖g (toDiscreteMonomial uv.2)‖
          ≤ (M + 1) * ‖g (toDiscreteMonomial uv.2)‖ := by
            gcongr
            exact (BoundedContinuousFunction.norm_coe_le_norm f.toBCF _).trans
              ((le_max_left ‖f‖ ‖g‖).trans (le_add_of_nonneg_right zero_le_one))
      _ < (M + 1) * δ := mul_lt_mul_of_pos_left hg hM1
      _ = ε / 2 := by rw [mul_comm, div_mul_cancel₀ _ hM1.ne']
def overconvergentSeriesMul [IsUltrametricDist K]
    (f g : OverconvergentSeries K d w) : OverconvergentSeries K d w where
  toFun u := convolutionCoordinate w f g u.ofTopology
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := convolutionCoordinate_zeroAtInfty w f g
@[simp]
theorem overconvergentSeriesMul_apply [IsUltrametricDist K]
    (f g : OverconvergentSeries K d w) (u : MonomialIndex d) :
    overconvergentSeriesMul w f g (toDiscreteMonomial u) =
      ∑ uv ∈ Finset.HasAntidiagonal.antidiagonal u,
        f (toDiscreteMonomial uv.1) * g (toDiscreteMonomial uv.2) :=
  rfl
 theorem normalizedPowerSeries_mul [IsUltrametricDist K]
    (f g : OverconvergentSeries K d w) :
    normalizedPowerSeries w (overconvergentSeriesMul w f g) =
      normalizedPowerSeries w f * normalizedPowerSeries w g := by
  ext u
  rw [MvPowerSeries.coeff_mul]
  rfl
 theorem normalizedPowerSeries_add (f g : OverconvergentSeries K d w) :
    normalizedPowerSeries w (f + g) = normalizedPowerSeries w f + normalizedPowerSeries w g :=
  rfl
 theorem normalizedPowerSeries_smul (c : K) (f : OverconvergentSeries K d w) :
    normalizedPowerSeries w (c • f) = c • normalizedPowerSeries w f :=
  rfl
theorem seriesConvolution_weightedCoefficient [IsUltrametricDist K]
    (π : K) (f g : OverconvergentSeries K d w) (u : MonomialIndex d) :
    weightedCoefficient w π u (overconvergentSeriesMul w f g) =
      seriesConvolution w π f g u := by
  rw [weightedCoefficient_apply_toDiscrete, overconvergentSeriesMul_apply]
  simp only [seriesConvolution, weightedCoefficient_apply_toDiscrete, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro uv huv
  have huv_add : uv.1 + uv.2 = u := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  rw [← huv_add, monomialWeight_add, pow_add]
  ring
theorem overconvergentSeriesMul_assoc [IsUltrametricDist K]
    (f g h : OverconvergentSeries K d w) :
    overconvergentSeriesMul w (overconvergentSeriesMul w f g) h =
      overconvergentSeriesMul w f (overconvergentSeriesMul w g h) := by
  apply normalizedPowerSeries_injective w
  simp only [normalizedPowerSeries_mul, mul_assoc]
theorem overconvergentSeriesMul_comm [IsUltrametricDist K]
    (f g : OverconvergentSeries K d w) :
    overconvergentSeriesMul w f g = overconvergentSeriesMul w g f := by
  apply normalizedPowerSeries_injective w
  simp only [normalizedPowerSeries_mul, mul_comm]
def overconvergentSeriesOne : OverconvergentSeries K d w :=
  finsuppToOverconvergentSeries w 1 (Finsupp.single 0 1)
 theorem normalizedPowerSeries_one :
    normalizedPowerSeries w (overconvergentSeriesOne w : OverconvergentSeries K d w) = 1 := by
  ext u
  rw [MvPowerSeries.coeff_one]
  change (finsuppToOverconvergentSeries w 1 (Finsupp.single 0 1))
    (toDiscreteMonomial u) = _
  rw [finsuppToOverconvergentSeries_apply_toDiscrete]
  change Finsupp.single 0 1 u / 1 ^ monomialWeight w u = if u = 0 then 1 else 0
  simp [Finsupp.single_apply, eq_comm]
@[simp]
theorem overconvergentSeriesOne_mul [IsUltrametricDist K]
    (f : OverconvergentSeries K d w) :
    overconvergentSeriesMul w (overconvergentSeriesOne w) f = f := by
  apply normalizedPowerSeries_injective w
  rw [normalizedPowerSeries_mul, normalizedPowerSeries_one, one_mul]
@[simp]
theorem overconvergentSeriesMul_one [IsUltrametricDist K]
    (f : OverconvergentSeries K d w) :
    overconvergentSeriesMul w f (overconvergentSeriesOne w) = f := by
  rw [overconvergentSeriesMul_comm, overconvergentSeriesOne_mul]
theorem overconvergentSeriesMul_add_left [IsUltrametricDist K]
    (f g h : OverconvergentSeries K d w) :
    overconvergentSeriesMul w (f + g) h =
      overconvergentSeriesMul w f h + overconvergentSeriesMul w g h := by
  apply normalizedPowerSeries_injective w
  rw [normalizedPowerSeries_mul, normalizedPowerSeries_add, normalizedPowerSeries_add,
    normalizedPowerSeries_mul, normalizedPowerSeries_mul, add_mul]
theorem overconvergentSeriesMul_smul_left [IsUltrametricDist K]
    (c : K) (f g : OverconvergentSeries K d w) :
    overconvergentSeriesMul w (c • f) g = c • overconvergentSeriesMul w f g := by
  apply normalizedPowerSeries_injective w
  rw [normalizedPowerSeries_mul, normalizedPowerSeries_smul, normalizedPowerSeries_smul,
    normalizedPowerSeries_mul]
  exact (smul_mul_assoc c (normalizedPowerSeries w f) (normalizedPowerSeries w g))
theorem overconvergentSeriesMul_add_right [IsUltrametricDist K]
    (f g h : OverconvergentSeries K d w) :
    overconvergentSeriesMul w f (g + h) =
      overconvergentSeriesMul w f g + overconvergentSeriesMul w f h := by
  simpa only [overconvergentSeriesMul_comm w f] using
    overconvergentSeriesMul_add_left w g h f
theorem overconvergentSeriesMul_smul_right [IsUltrametricDist K]
    (c : K) (f g : OverconvergentSeries K d w) :
    overconvergentSeriesMul w f (c • g) = c • overconvergentSeriesMul w f g := by
  simpa only [overconvergentSeriesMul_comm w f] using
    overconvergentSeriesMul_smul_left w c g f
 theorem norm_convolutionCoordinate_le [IsUltrametricDist K]
    (f g : OverconvergentSeries K d w) (u : MonomialIndex d) :
    ‖convolutionCoordinate w f g u‖ ≤ ‖f‖ * ‖g‖ := by
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
  intro uv huv
  rw [norm_mul]
  exact mul_le_mul
    (BoundedContinuousFunction.norm_coe_le_norm f.toBCF _)
    (BoundedContinuousFunction.norm_coe_le_norm g.toBCF _)
    (norm_nonneg _) (norm_nonneg _)
theorem overconvergentSeriesNorm_mul_le [IsUltrametricDist K]
    (f g : OverconvergentSeries K d w) :
    ‖overconvergentSeriesMul w f g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 ?_
  intro u
  exact norm_convolutionCoordinate_le w f g u.ofTopology
 theorem eq_of_weightedCoefficient_eq (π : K) (hπ : π ≠ 0)
    {f g : OverconvergentSeries K d w}
    (h : ∀ u, weightedCoefficient w π u f = weightedCoefficient w π u g) : f = g := by
  ext u
  have hu := h u.ofTopology
  change π ^ monomialWeight w u.ofTopology * f u =
    π ^ monomialWeight w u.ofTopology * g u at hu
  exact (mul_left_cancel₀ (pow_ne_zero _ hπ) hu)
def finsuppCauchyProduct (a b : MonomialIndex d →₀ K) : MonomialIndex d →₀ K :=
  ((AddMonoidAlgebra.ofCoeff a : AddMonoidAlgebra K (MonomialIndex d)) *
    AddMonoidAlgebra.ofCoeff b).coeff
@[simp]
theorem finsuppCauchyProduct_apply (a b : MonomialIndex d →₀ K) (u : MonomialIndex d) :
    finsuppCauchyProduct a b u =
      ∑ uv ∈ Finset.HasAntidiagonal.antidiagonal u, a uv.1 * b uv.2 := by
  exact AddMonoidAlgebra.coeff_mul_antidiag _ _ u (Finset.HasAntidiagonal.antidiagonal u)
    (fun {_} ↦ Finset.HasAntidiagonal.mem_antidiagonal)
theorem overconvergentSeriesMul_finsupp [IsUltrametricDist K]
    (π : K) (hπ : π ≠ 0) (a b : MonomialIndex d →₀ K) :
    overconvergentSeriesMul w
        (finsuppToOverconvergentSeries w π a)
        (finsuppToOverconvergentSeries w π b) =
      finsuppToOverconvergentSeries w π (finsuppCauchyProduct a b) := by
  apply eq_of_weightedCoefficient_eq w π hπ
  intro u
  rw [seriesConvolution_weightedCoefficient]
  simp only [seriesConvolution,
    weightedCoefficient_finsuppToOverconvergentSeries w π hπ]
  change (∑ uv ∈ Finset.HasAntidiagonal.antidiagonal u, a uv.1 * b uv.2) =
    finsuppCauchyProduct a b u
  exact (finsuppCauchyProduct_apply a b u).symm
def monomialFrobenius (q : ℕ) (u : MonomialIndex d) : MonomialIndex d :=
  q • u
@[simp]
theorem monomialFrobenius_zero (q : ℕ) :
    monomialFrobenius (d := d) q 0 = 0 := by
  simp [monomialFrobenius]
@[simp]
theorem monomialFrobenius_add (q : ℕ) (u v : MonomialIndex d) :
    monomialFrobenius q (u + v) = monomialFrobenius q u + monomialFrobenius q v := by
  simp [monomialFrobenius]
theorem monomialFrobenius_injective (q : ℕ) (hq : q ≠ 0) :
    Function.Injective (monomialFrobenius (d := d) q) := by
  intro u v huv
  ext i
  have hi := DFunLike.congr_fun huv i
  change q * u i = q * v i at hi
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq) hi
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Set Topology
namespace FiniteFields.Dwork
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
variable {d : ℕ} (w : PositiveMonomialWeight d)
structure OverconvergentTateAlgebra (K : Type*) [NormedField K] [IsUltrametricDist K]
    (d : ℕ) (w : PositiveMonomialWeight d) where
  toSeries : OverconvergentSeries K d w
namespace OverconvergentTateAlgebra
variable {w}
@[ext]
theorem ext {f g : OverconvergentTateAlgebra K d w} (h : f.toSeries = g.toSeries) : f = g := by
  cases f
  cases g
  cases h
  rfl
def carrierEquiv : OverconvergentTateAlgebra K d w ≃ OverconvergentSeries K d w where
  toFun := toSeries
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
instance : AddCommGroup (OverconvergentTateAlgebra K d w) := carrierEquiv.addCommGroup
instance : Module K (OverconvergentTateAlgebra K d w) := carrierEquiv.module K
instance : NormedAddCommGroup (OverconvergentTateAlgebra K d w) :=
  carrierEquiv.normedAddCommGroup
instance : NormedSpace K (OverconvergentTateAlgebra K d w) :=
  carrierEquiv.normedSpace K
@[simp]
theorem toSeries_zero : (0 : OverconvergentTateAlgebra K d w).toSeries = 0 := rfl
@[simp]
theorem toSeries_add (f g : OverconvergentTateAlgebra K d w) :
    (f + g).toSeries = f.toSeries + g.toSeries := rfl
@[simp]
theorem toSeries_neg (f : OverconvergentTateAlgebra K d w) :
    (-f).toSeries = -f.toSeries := rfl
@[simp]
theorem toSeries_sub (f g : OverconvergentTateAlgebra K d w) :
    (f - g).toSeries = f.toSeries - g.toSeries := rfl
@[simp]
theorem toSeries_smul (c : K) (f : OverconvergentTateAlgebra K d w) :
    (c • f).toSeries = c • f.toSeries := rfl
@[simp]
theorem norm_toSeries (f : OverconvergentTateAlgebra K d w) :
    ‖f.toSeries‖ = ‖f‖ := rfl
end OverconvergentTateAlgebra
def overconvergentTateAlgebraEquivSeries :
    OverconvergentTateAlgebra K d w ≃ₗᵢ[K] OverconvergentSeries K d w where
  toLinearEquiv := (OverconvergentTateAlgebra.carrierEquiv (K := K) (d := d) (w := w)).linearEquiv K
  norm_map' _ := rfl
namespace OverconvergentTateAlgebra
variable {w}
instance [CompleteSpace K] : CompleteSpace (OverconvergentTateAlgebra K d w) :=
  (overconvergentTateAlgebraEquivSeries (K := K) (d := d) w).toIsometryEquiv.completeSpace
instance : Mul (OverconvergentTateAlgebra K d w) where
  mul f g := ⟨overconvergentSeriesMul w f.toSeries g.toSeries⟩
instance : One (OverconvergentTateAlgebra K d w) where
  one := ⟨overconvergentSeriesOne w⟩
@[simp]
theorem toSeries_mul (f g : OverconvergentTateAlgebra K d w) :
    (f * g).toSeries = overconvergentSeriesMul w f.toSeries g.toSeries := rfl
@[simp]
theorem toSeries_one : (1 : OverconvergentTateAlgebra K d w).toSeries =
    overconvergentSeriesOne w := rfl
instance : CommRing (OverconvergentTateAlgebra K d w) where
  mul_assoc f g h := ext (overconvergentSeriesMul_assoc w f.toSeries g.toSeries h.toSeries)
  one_mul f := ext (overconvergentSeriesOne_mul w f.toSeries)
  mul_one f := ext (overconvergentSeriesMul_one w f.toSeries)
  zero_mul f := ext <| by
    simpa using overconvergentSeriesMul_smul_left w (0 : K) 0 f.toSeries
  mul_zero f := ext <| by
    simpa using overconvergentSeriesMul_smul_right w (0 : K) f.toSeries 0
  left_distrib f g h := ext (overconvergentSeriesMul_add_right w f.toSeries g.toSeries h.toSeries)
  right_distrib f g h := ext (overconvergentSeriesMul_add_left w f.toSeries g.toSeries h.toSeries)
  mul_comm f g := ext (overconvergentSeriesMul_comm w f.toSeries g.toSeries)
instance : NormedCommRing (OverconvergentTateAlgebra K d w) where
  dist_eq f g := by rw [dist_eq_norm, norm_neg_add]
  norm_mul_le f g := overconvergentSeriesNorm_mul_le w f.toSeries g.toSeries
instance : Algebra K (OverconvergentTateAlgebra K d w) :=
  Algebra.ofModule
    (fun c f g ↦ ext (overconvergentSeriesMul_smul_left w c f.toSeries g.toSeries))
    (fun c f g ↦ ext (overconvergentSeriesMul_smul_right w c f.toSeries g.toSeries))
instance : NormedAlgebra K (OverconvergentTateAlgebra K d w) where
  norm_smul_le c f := norm_smul_le c f
instance : IsUltrametricDist (OverconvergentTateAlgebra K d w) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun f g ↦ by
    exact overconvergentSeries_norm_add_le_max w
      IsUltrametricDist.isNonarchimedean_norm f.toSeries g.toSeries
end OverconvergentTateAlgebra
section Coefficients
def overconvergentTateAlgebraCoefficient (u : MonomialIndex d) :
    OverconvergentTateAlgebra K d w →L[K] K where
  toFun f := seriesCoefficient w u f.toSeries
  map_add' _ _ := map_add (seriesCoefficient w u) _ _
  map_smul' _ _ := map_smul (seriesCoefficient w u) _ _
  cont := (seriesCoefficient w u).continuous.comp
    (overconvergentTateAlgebraEquivSeries (K := K) (d := d) w).continuous
@[simp]
theorem overconvergentTateAlgebraCoefficient_apply
    (u : MonomialIndex d) (f : OverconvergentTateAlgebra K d w) :
    overconvergentTateAlgebraCoefficient w u f = seriesCoefficient w u f.toSeries := rfl
def finsuppToOverconvergentTateAlgebra (π : K) :
    (MonomialIndex d →₀ K) →ₗ[K] OverconvergentTateAlgebra K d w :=
  (overconvergentTateAlgebraEquivSeries (K := K) (d := d) w).symm.toLinearMap.comp
    (finsuppToOverconvergentSeries w π)
@[simp]
theorem finsuppToOverconvergentTateAlgebra_toSeries (π : K) (a : MonomialIndex d →₀ K) :
    (finsuppToOverconvergentTateAlgebra w π a).toSeries =
      finsuppToOverconvergentSeries w π a := rfl
omit [IsUltrametricDist K] in
theorem finsuppCauchyProduct_single (u v : MonomialIndex d) (a b : K) :
    finsuppCauchyProduct (Finsupp.single u a) (Finsupp.single v b) =
      Finsupp.single (u + v) (a * b) := by
  exact congrArg AddMonoidAlgebra.coeff (AddMonoidAlgebra.single_mul_single u v a b)
theorem finsuppToOverconvergentTateAlgebra_mul (π : K) (hπ : π ≠ 0)
    (a b : MonomialIndex d →₀ K) :
    finsuppToOverconvergentTateAlgebra w π (finsuppCauchyProduct a b) =
      finsuppToOverconvergentTateAlgebra w π a *
        finsuppToOverconvergentTateAlgebra w π b := by
  apply OverconvergentTateAlgebra.ext
  exact (overconvergentSeriesMul_finsupp w π hπ a b).symm
end Coefficients
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable {K : Type*} [NormedField K]
variable {d : ℕ} (w : PositiveMonomialWeight d)
variable (p : ℕ) [Fact p.Prime]
 theorem exponentDilation_injective :
    Function.Injective (fun u : DiscreteMonomialIndex d ↦
      WithTopology.toTopology ⊥ (monomialFrobenius p u.ofTopology)) := by
  intro u v huv
  apply WithTopology.ofTopology_injective
  exact monomialFrobenius_injective p (Fact.out : p.Prime).ne_zero <|
    congrArg WithTopology.ofTopology huv
def monomialDivisionCocompactMap :
    CocompactMap (DiscreteMonomialIndex d) (DiscreteMonomialIndex d) where
  toFun u := WithTopology.toTopology ⊥ (monomialFrobenius p u.ofTopology)
  continuous_toFun := continuous_of_discreteTopology
  cocompact_tendsto' := by
    simpa only [Filter.cocompact_eq_cofinite] using
      (exponentDilation_injective (d := d) p).tendsto_cofinite
set_option linter.unusedSectionVars false in
@[simp]
theorem monomialDivisionCocompactMap_apply (u : MonomialIndex d) :
    monomialDivisionCocompactMap (d := d) p (WithTopology.toTopology ⊥ u) =
      WithTopology.toTopology ⊥ (monomialFrobenius p u) :=
  rfl
set_option linter.unusedSectionVars false in
 theorem exponentDivisionSeries_norm_bound (f : OverconvergentSeries K d w) :
    ‖f.comp (monomialDivisionCocompactMap (d := d) p)‖ ≤ ‖f‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 ?_
  intro u
  exact BoundedContinuousFunction.norm_coe_le_norm f.toBCF _
def exponentDivisionSeries :
    OverconvergentSeries K d w →L[K] OverconvergentSeries K d w :=
  (ZeroAtInftyContinuousMap.compLinearMap
    (R := K) (monomialDivisionCocompactMap (d := d) p)).mkContinuous 1 (by
      intro f
      change ‖f.comp (monomialDivisionCocompactMap (d := d) p)‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using exponentDivisionSeries_norm_bound w p f)
set_option linter.unusedSectionVars false in
@[simp]
theorem exponentDivisionSeries_apply (f : OverconvergentSeries K d w)
    (u : MonomialIndex d) :
    seriesCoefficient w u (exponentDivisionSeries w p f) =
      seriesCoefficient w (monomialFrobenius p u) f :=
  rfl
variable [IsUltrametricDist K]
def exponentDivision :
    OverconvergentTateAlgebra K d w →L[K] OverconvergentTateAlgebra K d w where
  toFun f := ⟨exponentDivisionSeries w p f.toSeries⟩
  map_add' _ _ := OverconvergentTateAlgebra.ext <| map_add (exponentDivisionSeries w p) _ _
  map_smul' _ _ := OverconvergentTateAlgebra.ext <| map_smul (exponentDivisionSeries w p) _ _
  cont := (overconvergentTateAlgebraEquivSeries
      (K := K) (d := d) w).symm.continuous.comp
    ((exponentDivisionSeries w p).continuous.comp
      (overconvergentTateAlgebraEquivSeries (K := K) (d := d) w).continuous)
set_option linter.unusedSectionVars false in
@[simp]
theorem exponentDivision_toSeries (f : OverconvergentTateAlgebra K d w) :
    (exponentDivision w p f).toSeries = exponentDivisionSeries w p f.toSeries :=
  rfl
set_option linter.unusedSectionVars false in
@[simp]
theorem exponentDivision_coefficient (f : OverconvergentTateAlgebra K d w)
    (u : MonomialIndex d) :
    overconvergentTateAlgebraCoefficient w u (exponentDivision w p f) =
      overconvergentTateAlgebraCoefficient w (monomialFrobenius p u) f := by
  exact exponentDivisionSeries_apply w p f.toSeries u
section CoefficientFrobenius
variable (k : Type*) [Field k] [CharP k p] [Finite k]
end CoefficientFrobenius
end FiniteFields.Dwork
end
end

section
noncomputable section
open Polynomial
open scoped NNReal Valued
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
def DworkCyclotomicPolynomial : (CoefficientField k p)[X] :=
  cyclotomic p (CoefficientField k p)
abbrev DworkCyclotomicField := CyclotomicField p (CoefficientField k p)
noncomputable instance dworkCyclotomicFieldFiniteDimensional :
    FiniteDimensional (CoefficientField k p) (DworkCyclotomicField k p) :=
  IsCyclotomicExtension.finiteDimensional
    (S := ({p} : Set ℕ)) (CoefficientField k p) (DworkCyclotomicField k p)
noncomputable instance dworkCyclotomicFieldNormedField :
    NormedField (DworkCyclotomicField k p) :=
  spectralNorm.normedField (CoefficientField k p) (DworkCyclotomicField k p)
noncomputable instance dworkCyclotomicFieldNormedAlgebra :
    NormedAlgebra (CoefficientField k p) (DworkCyclotomicField k p) :=
  spectralNorm.normedAlgebra (CoefficientField k p) (DworkCyclotomicField k p)
theorem dworkCyclotomicField_norm_algebraMap (x : CoefficientField k p) :
    ‖algebraMap (CoefficientField k p) (DworkCyclotomicField k p) x‖ = ‖x‖ := by
  change spectralNorm (CoefficientField k p) (DworkCyclotomicField k p)
    (algebraMap (CoefficientField k p) (DworkCyclotomicField k p) x) = ‖x‖
  exact spectralNorm_extends x
noncomputable instance dworkCyclotomicFieldComplete :
    CompleteSpace (DworkCyclotomicField k p) :=
  spectralNorm.completeSpace (CoefficientField k p) (DworkCyclotomicField k p)
noncomputable instance dworkCyclotomicFieldUltrametric :
    IsUltrametricDist (DworkCyclotomicField k p) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm
      (K := CoefficientField k p) (L := DworkCyclotomicField k p))
def dworkPrimitiveRoot : DworkCyclotomicField k p :=
  IsCyclotomicExtension.zeta p (CoefficientField k p) (DworkCyclotomicField k p)
theorem dworkPrimitiveRoot_isPrimitiveRoot :
    IsPrimitiveRoot (dworkPrimitiveRoot k p) p :=
  IsCyclotomicExtension.zeta_spec p (CoefficientField k p) (DworkCyclotomicField k p)
def dworkRamificationParameter : DworkCyclotomicField k p :=
  dworkPrimitiveRoot k p - 1
theorem dworkRamificationParameter_ne_zero : dworkRamificationParameter k p ≠ 0 := by
  exact sub_ne_zero.mpr
    ((dworkPrimitiveRoot_isPrimitiveRoot k p).ne_one
      (Fact.out : Nat.Prime p).one_lt)
 lemma norm_lt_one_of_monic_root
    {K : Type*} [NormedField K] [IsUltrametricDist K]
    {f : K[X]} (hf : f.Monic) {x : K} (hroot : f.IsRoot x)
    (hdeg : 0 < f.natDegree)
    (hcoeff : ∀ i < f.natDegree, ‖f.coeff i‖ < 1) :
    ‖x‖ < 1 := by
  by_contra hx
  have h_one_le : 1 ≤ ‖x‖ := le_of_not_gt hx
  have hx0 : x ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at h_one_le
    exact (not_le_of_gt zero_lt_one) h_one_le
  have heval := hroot
  rw [IsRoot.def, eval_eq_sum_range, Finset.range_add_one,
    Finset.sum_insert (by simp)] at heval
  rw [hf.coeff_natDegree, one_mul, add_eq_zero_iff_eq_neg] at heval
  have hnorm_eq : ‖x‖ ^ f.natDegree =
      ‖∑ i ∈ Finset.range f.natDegree, f.coeff i * x ^ i‖ := by
    rw [← norm_pow, heval, norm_neg]
  let hrange : (Finset.range f.natDegree).Nonempty :=
    ⟨0, Finset.mem_range.mpr hdeg⟩
  obtain ⟨i, hi, hisup⟩ :=
    Finset.exists_mem_eq_sup' hrange (fun i => ‖f.coeff i * x ^ i‖)
  have hsum := hrange.norm_sum_le_sup'_norm (fun i => f.coeff i * x ^ i)
  rw [hisup] at hsum
  have hi_lt : i < f.natDegree := Finset.mem_range.mp hi
  have hpow_le : ‖x‖ ^ i ≤ ‖x‖ ^ f.natDegree :=
    pow_le_pow_right₀ h_one_le hi_lt.le
  have hterm_lt : ‖f.coeff i * x ^ i‖ < ‖x‖ ^ f.natDegree := by
    rw [norm_mul, norm_pow]
    calc
      ‖f.coeff i‖ * ‖x‖ ^ i < 1 * ‖x‖ ^ i := by
        exact mul_lt_mul_of_pos_right (hcoeff i hi_lt)
          (pow_pos (norm_pos_iff.mpr hx0) i)
      _ ≤ ‖x‖ ^ f.natDegree := by simpa using hpow_le
  have := hsum.trans_lt hterm_lt
  rw [← hnorm_eq] at this
  exact (lt_irrefl _ this)
 def shiftedDworkCyclotomicPolynomial : (DworkCyclotomicField k p)[X] :=
  (cyclotomic p (DworkCyclotomicField k p)).comp (X + 1)
 theorem shiftedDworkCyclotomicPolynomial_monic :
    (shiftedDworkCyclotomicPolynomial k p).Monic := by
  apply (cyclotomic.monic p (DworkCyclotomicField k p)).comp
  · simpa using (monic_X_add_C (1 : DworkCyclotomicField k p))
  · intro h
    rw [show (X + 1 : (DworkCyclotomicField k p)[X]) = X + C 1 by simp,
      natDegree_X_add_C] at h
    exact one_ne_zero h
 theorem shiftedDworkCyclotomicPolynomial_natDegree :
    (shiftedDworkCyclotomicPolynomial k p).natDegree = p - 1 := by
  rw [shiftedDworkCyclotomicPolynomial, natDegree_comp,
    natDegree_cyclotomic, Nat.totient_prime (Fact.out : Nat.Prime p),
    show (X + 1 : (DworkCyclotomicField k p)[X]) = X + C 1 by simp,
    natDegree_X_add_C, mul_one]
 theorem shiftedDworkCyclotomicPolynomial_isRoot :
    (shiftedDworkCyclotomicPolynomial k p).IsRoot (dworkRamificationParameter k p) := by
  rw [IsRoot.def, shiftedDworkCyclotomicPolynomial, eval_comp, eval_add, eval_X, eval_one,
    dworkRamificationParameter, sub_add_cancel]
  exact (dworkPrimitiveRoot_isPrimitiveRoot k p).isRoot_cyclotomic
    (Fact.out : Nat.Prime p).pos
 theorem shiftedDworkCyclotomicPolynomial_coeff_norm_lt_one
    {i : ℕ} (hi : i < (shiftedDworkCyclotomicPolynomial k p).natDegree) :
    ‖(shiftedDworkCyclotomicPolynomial k p).coeff i‖ < 1 := by
  rw [shiftedDworkCyclotomicPolynomial_natDegree] at hi
  have hip : i < p := lt_of_lt_of_le hi (Nat.sub_le p 1)
  have hcoeff : (shiftedDworkCyclotomicPolynomial k p).coeff i =
      (p.choose (i + 1) : DworkCyclotomicField k p) := by
    rw [shiftedDworkCyclotomicPolynomial, cyclotomic_prime,
      geom_sum_X_comp_X_add_one_eq_sum, finsetSum_coeff]
    simp [hip]
  rw [hcoeff]
  obtain ⟨a, ha⟩ := (Fact.out : Nat.Prime p).dvd_choose_self i.succ_ne_zero (by omega)
  rw [ha, Nat.cast_mul, norm_mul]
  have hpNorm : ‖(p : DworkCyclotomicField k p)‖ < 1 := by
    rw [show (p : DworkCyclotomicField k p) =
      algebraMap (CoefficientField k p) (DworkCyclotomicField k p)
        (p : CoefficientField k p) by simp]
    change spectralNorm (CoefficientField k p) (DworkCyclotomicField k p)
      (algebraMap (CoefficientField k p) (DworkCyclotomicField k p)
        (p : CoefficientField k p)) < 1
    rw [spectralNorm_extends]
    exact coefficientField_norm_p_lt_one k p
  exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _)
    hpNorm (IsUltrametricDist.norm_natCast_le_one (DworkCyclotomicField k p) a)
theorem dworkRamificationParameter_norm_lt_one :
    ‖dworkRamificationParameter k p‖ < 1 := by
  apply norm_lt_one_of_monic_root (shiftedDworkCyclotomicPolynomial_monic k p)
    (shiftedDworkCyclotomicPolynomial_isRoot k p)
  · rw [shiftedDworkCyclotomicPolynomial_natDegree]
    exact Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
  · exact fun i hi => shiftedDworkCyclotomicPolynomial_coeff_norm_lt_one k p hi
end FiniteFields.Dwork
end
end


