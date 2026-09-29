-- Prove2me | Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
-- name    : WeierstrassCurve_ProjModel_GroupLawVocabulary
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/b53fe438-9308-5bea-8e29-6c507f56c845
-- title:
--   Group-law vocabulary for the projective Weierstrass model
-- statement:
--   Let $R$ be a commutative ring and $W$ a Weierstrass curve over $R$, with homogeneous cubic $F_W$ = `W.toProjective.polynomial` in $R[X_0,X_1,X_2]$. Writing $\mathcal{B}$ for the graded quotient $R[X_0,X_1,X_2]/(F_W)$ with the grading induced from the homogeneous submodules (`ProjModelRingCR`, `projModelGradingCR`), the module sets up the algebra in which a group law on $\mathrm{Proj}\,\mathcal{B}$ is expressed. In the six-variable ring $P_6=R[X_{\mathrm{inl}\,0},\dots,X_{\mathrm{inr}\,2}]$ the two renamings `kw_lrAdd_WP₁`, `kw_lrAdd_WP₂` of $F_W$ along `Sum.inl`, `Sum.inr` are homogeneous of degree $3$, so the ideal they span is homogeneous; `kw_lrComul_biIdeal` packages it, `KwLRBiRing` is the quotient $\mathcal{B}^2=P_6/(F_1,F_2)$ and `kw_lrComul_biGrading` its induced grading. One group of results shows that the quadruple-degree forms supplied by the addition-formulas module satisfy the cubic modulo that ideal: `kw_lrSym_onCurve_mem_span` asserts that substituting the triple `kw_lrSym_X/Y/Z` into $F_W$ lands in $(F_1,F_2)$. It is deduced from the identities $F(\lambda x,\lambda y,\lambda z)=\lambda^3F(x,y,z)$ and an explicit factorisation of $F(x,y,z)-F(x',y',z')$, from the corresponding statement for the `kw_lrAdd` triple, and from the minor relations, by passing to the universal curve $\langle X_0,\dots,X_4\rangle$ over $\mathbb{Z}[X_0,\dots,X_4]$, where the quotient by $(F_1,F_2)$ is shown to be a domain and `kw_lrAdd_Z` is shown non-zero in it. Consequently the substitutions descend to graded algebra maps $\mathcal{B}\to\mathcal{B}^2$ (`kw_lrAdd_comulHom`, `kw_lrSym_comulHom`), multiplying degrees by $4$, and $\mathcal{B}^2\to\mathcal{B}\otimes_R\mathcal{B}$ (`kw_lrComul_biToTensor`). On charts, `kw_lrChart_gen` is the fraction $X_m/X_i$ in the homogeneous localisation away from $X_i$, `kw_lrChart_dehom` the resulting dehomogenisation killing $F_W$, and `kw_lrChart_away`, `kw_lrChart_ev'`, `kw_lrChart_toTensor`, `kw_lrChart_tensor` (with `kw_lrSymChart` analogues) the induced maps between charts, away-localisations of $\mathcal{B}^2$ and tensor products of two charts. A further block identifies the degree-zero part of the graded quotient with $R$ — the defining ideal lies in the kernel of `constantCoeff`, so $R\to(\mathcal{B})_0$ is bijective — whence `projModelSpecDegreeZeroIsoCR` and the instance `isProper_projModelStrCR`: the structure morphism $\mathrm{Proj}\to\operatorname{Spec} R$ of the projective model is proper. Auxiliary lemmas record finite-typeness of a polynomial ring, and of a graded quotient, over its degree-zero subalgebra.
--
--   **Relation to Mathlib.** Mathlib supplies `WeierstrassCurve.Projective` with its homogeneous cubic, `Proj` of a graded algebra, `HomogeneousLocalization.Away` and `IsProper`; the homogeneous coordinate ring of the projective model as a graded quotient, the two-copy ring $P_6/(F_1,F_2)$, the comultiplication and chart comparison maps built from the addition formulas, and the properness of the model's structure morphism are the project's own. Mathlib's group law for Weierstrass curves is defined on point sets (affine, projective, Jacobian), not as a morphism of schemes on `Proj`.
--
--   **Where it is used.** These definitions support the construction of the relative group law on the projective model of a Weierstrass curve over a base ring, and hence of its torsion subschemes and of the Galois action on points with values in a field over $R$; that structure is what makes the mod-$\ell$ representation attached to the Frey curve available.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_ProjModel_GroupLawVocabulary.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false

section MEGA_KwLRSymOnCurveScaled_lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6400000

noncomputable section

open MvPolynomial WeierstrassCurve

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

local notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R
local notation "WP₁" => kw_lrAdd_WP₁ W
local notation "WP₂" => kw_lrAdd_WP₂ W

section Abstract

variable {S : Type u} [CommRing S] [Algebra R S]

theorem kw_lrSymOC_aeval_scale (l x y z : S) :
    aeval ![l*x, l*y, l*z] W.toProjective.polynomial
      = l^3 * aeval ![x, y, z] W.toProjective.polynomial := by
  simp only [WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem kw_lrSymOC_aeval_diff (x x' y y' z z' : S) :
    aeval ![x, y, z] W.toProjective.polynomial
        - aeval ![x', y', z'] W.toProjective.polynomial
      = (x - x') * (- (x^2 + x*x' + x'^2) - algebraMap R S W.a₂ * (x+x') * z
          + algebraMap R S W.a₁ * y * z - algebraMap R S W.a₄ * z^2)
        + (y - y') * ((y+y') * z + algebraMap R S W.a₁ * x' * z
          + algebraMap R S W.a₃ * z^2)
        + (z - z') * (y'^2 + algebraMap R S W.a₁ * x' * y'
          + algebraMap R S W.a₃ * y' * (z+z') - algebraMap R S W.a₂ * x'^2
          - algebraMap R S W.a₄ * x' * (z+z')
          - algebraMap R S W.a₆ * (z^2 + z*z' + z'^2)) := by
  simp only [WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

end Abstract

theorem kw_lrSymOC_scaled_mem_span_of (l m : P₆)
    (hX : l * kw_lrSym_X W - m * kw_lrAdd_X W ∈ Ideal.span {WP₁, WP₂})
    (hY : l * kw_lrSym_Y W - m * kw_lrAdd_Y W ∈ Ideal.span {WP₁, WP₂})
    (hZ : l * kw_lrSym_Z W - m * kw_lrAdd_Z W ∈ Ideal.span {WP₁, WP₂}) :
    l^3 * aeval ![kw_lrSym_X W, kw_lrSym_Y W, kw_lrSym_Z W]
          W.toProjective.polynomial
      ∈ Ideal.span {WP₁, WP₂} := by
  have hdiff : l^3 * aeval ![kw_lrSym_X W, kw_lrSym_Y W, kw_lrSym_Z W]
        W.toProjective.polynomial
      - m^3 * aeval ![kw_lrAdd_X W, kw_lrAdd_Y W, kw_lrAdd_Z W]
        W.toProjective.polynomial ∈ Ideal.span {WP₁, WP₂} := by
    rw [← kw_lrSymOC_aeval_scale W l, ← kw_lrSymOC_aeval_scale W m,
        kw_lrSymOC_aeval_diff W
          (l * kw_lrSym_X W) (m * kw_lrAdd_X W)
          (l * kw_lrSym_Y W) (m * kw_lrAdd_Y W)
          (l * kw_lrSym_Z W) (m * kw_lrAdd_Z W)]
    exact add_mem (add_mem (Ideal.mul_mem_right _ _ hX) (Ideal.mul_mem_right _ _ hY))
      (Ideal.mul_mem_right _ _ hZ)
  have hAdd : m^3 * aeval ![kw_lrAdd_X W, kw_lrAdd_Y W, kw_lrAdd_Z W]
        W.toProjective.polynomial ∈ Ideal.span {WP₁, WP₂} :=
    Ideal.mul_mem_left _ _ (kw_lrAdd_onCurve_mem_span W)
  have := add_mem hdiff hAdd
  simpa using this

theorem kw_lrSymOC_scaled_mem_span_Z :
    (kw_lrAdd_Z W)^3 * aeval ![kw_lrSym_X W, kw_lrSym_Y W, kw_lrSym_Z W]
          W.toProjective.polynomial
      ∈ Ideal.span {WP₁, WP₂} := by
  refine kw_lrSymOC_scaled_mem_span_of W (kw_lrAdd_Z W) (kw_lrSym_Z W) ?_ ?_ ?_
  · have := kw_lrSym_minor_XZ_mem_span W
    rwa [show kw_lrSym_X W * kw_lrAdd_Z W - kw_lrSym_Z W * kw_lrAdd_X W
        = kw_lrAdd_Z W * kw_lrSym_X W - kw_lrSym_Z W * kw_lrAdd_X W from by ring] at this
  · have := kw_lrSym_minor_YZ_mem_span W
    rwa [show kw_lrSym_Y W * kw_lrAdd_Z W - kw_lrSym_Z W * kw_lrAdd_Y W
        = kw_lrAdd_Z W * kw_lrSym_Y W - kw_lrSym_Z W * kw_lrAdd_Y W from by ring] at this
  · rw [mul_comm, sub_self]; exact Ideal.zero_mem _

end WeierstrassProjModel

end

end MEGA_KwLRSymOnCurveScaled_lean

section MEGA_KwLRSymOnCurve_lean
set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSimpArgs false

noncomputable section

open MvPolynomial WeierstrassCurve ProjWeierstrassCubicPrime

namespace WeierstrassProjModel

universe u v

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Map

variable {S : Type v} [CommRing S] (f : R →+* S)

theorem kw_lrSymOC_map_WP₁ :
    MvPolynomial.map f (kw_lrAdd_WP₁ W) = kw_lrAdd_WP₁ (W.map f) := by
  simp only [kw_lrAdd_WP₁, MvPolynomial.map_rename,
    WeierstrassCurve.Projective.map_polynomial, WeierstrassCurve.Projective.map,
    WeierstrassCurve.toProjective]

theorem kw_lrSymOC_map_WP₂ :
    MvPolynomial.map f (kw_lrAdd_WP₂ W) = kw_lrAdd_WP₂ (W.map f) := by
  simp only [kw_lrAdd_WP₂, MvPolynomial.map_rename,
    WeierstrassCurve.Projective.map_polynomial, WeierstrassCurve.Projective.map,
    WeierstrassCurve.toProjective]

theorem kw_lrSymOC_map_lrSym_X :
    MvPolynomial.map f (kw_lrSym_X W) = kw_lrSym_X (W.map f) := by
  simp only [kw_lrSym_X, map_add, map_mul, map_neg, map_pow, MvPolynomial.map_C,
    MvPolynomial.map_X, map_ofNat, map_one, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_sub]

theorem kw_lrSymOC_map_lrSym_Y :
    MvPolynomial.map f (kw_lrSym_Y W) = kw_lrSym_Y (W.map f) := by
  simp only [kw_lrSym_Y, map_add, map_mul, map_neg, map_pow, MvPolynomial.map_C,
    MvPolynomial.map_X, map_ofNat, map_one, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_sub]

theorem kw_lrSymOC_map_lrSym_Z :
    MvPolynomial.map f (kw_lrSym_Z W) = kw_lrSym_Z (W.map f) := by
  simp only [kw_lrSym_Z, map_add, map_mul, map_neg, map_pow, MvPolynomial.map_C,
    MvPolynomial.map_X, map_ofNat, map_one, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_sub]

theorem kw_lrSymOC_map_W_lrSym :
    MvPolynomial.map f
        (aeval ![kw_lrSym_X W, kw_lrSym_Y W, kw_lrSym_Z W] W.toProjective.polynomial)
      = aeval ![kw_lrSym_X (W.map f), kw_lrSym_Y (W.map f), kw_lrSym_Z (W.map f)]
          (W.map f).toProjective.polynomial := by
  simp only [WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, MvPolynomial.map_C, MvPolynomial.algebraMap_eq,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    kw_lrSymOC_map_lrSym_X, kw_lrSymOC_map_lrSym_Y, kw_lrSymOC_map_lrSym_Z]

end Map

local notation "R₀" => MvPolynomial (Fin 5) ℤ

abbrev kw_lrSymOC_W₀ : WeierstrassCurve R₀ := ⟨X 0, X 1, X 2, X 3, X 4⟩

local notation "W₀" => kw_lrSymOC_W₀
local notation "P₆₀" => MvPolynomial (Fin 3 ⊕ Fin 3) R₀
local notation "WP₁₀" => kw_lrAdd_WP₁ W₀
local notation "WP₂₀" => kw_lrAdd_WP₂ W₀

theorem kw_lrSymOC_W₀_map :
    WeierstrassCurve.map kw_lrSymOC_W₀
        (MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]) = W := by
  ext <;> simp only [WeierstrassCurve.map, kw_lrSymOC_W₀, MvPolynomial.eval₂Hom_X'] <;> rfl

section EngineHelpers

variable {F : Type*} [CommRing F]

theorem kw_lrSymOC_finSuccEquiv_map {S : Type*} [CommRing S] (f : F →+* S)
    (p : MvPolynomial (Fin 3) F) :
    finSuccEquiv S 2 (MvPolynomial.map f p)
      = Polynomial.map (MvPolynomial.map f) (finSuccEquiv F 2 p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply, MvPolynomial.eval₂_C]
  | add p q hp hq => simp [hp, hq, map_add, Polynomial.map_add]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.map_X, hp, Polynomial.map_mul]
    congr 1
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [finSuccEquiv_apply]
    · simp [finSuccEquiv_apply]

theorem kw_lrSymOC_wCubic_map (V : WeierstrassCurve.Projective F)
    {S : Type*} [CommRing S] (f : F →+* S) :
    (wCubic (V.map f)).toPoly
      = Polynomial.map (MvPolynomial.map f) (wCubic V).toPoly := by
  simp only [wCubic, Cubic.toPoly, WeierstrassCurve.Projective.map, WeierstrassCurve.map,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_one, MvPolynomial.map_C,
    MvPolynomial.map_X, map_mul, map_sub, map_one, map_pow]

end EngineHelpers

section Engine

variable {F : Type*} [CommRing F] [IsDomain F] (V : WeierstrassCurve.Projective F)

theorem kw_lrSymOC_isDomain_quot_span_poly :
    IsDomain (MvPolynomial (Fin 3) F ⧸ Ideal.span {V.polynomial}) := by
  have hθ : Function.Injective (algebraMap F (FractionRing F)) :=
    IsFractionRing.injective F (FractionRing F)
  have hθ'' : Function.Injective
      (MvPolynomial.map (σ := Fin 2) (algebraMap F (FractionRing F))) :=
    MvPolynomial.map_injective _ hθ

  have hD : IsDomain (MvPolynomial (Fin 3) (FractionRing F)
      ⧸ Ideal.span {(V.map (algebraMap F (FractionRing F))).polynomial}) :=
    isDomain_quotient_span_polynomial (V.map (algebraMap F (FractionRing F)))

  have hcomap : (Ideal.span {(V.map (algebraMap F (FractionRing F))).polynomial}).comap
      (MvPolynomial.map (algebraMap F (FractionRing F)) :
        MvPolynomial (Fin 3) F →+* MvPolynomial (Fin 3) (FractionRing F))
      ≤ Ideal.span {V.polynomial} := by
    intro p hp
    simp only [Ideal.mem_comap, Ideal.mem_span_singleton] at hp ⊢

    have hp' : finSuccEquiv (FractionRing F) 2 (V.map (algebraMap F (FractionRing F))).polynomial
        ∣ finSuccEquiv (FractionRing F) 2 (MvPolynomial.map (algebraMap F (FractionRing F)) p) :=
      map_dvd (finSuccEquiv (FractionRing F) 2) hp
    rw [kw_lrSymOC_finSuccEquiv_map (algebraMap F (FractionRing F)) p,
        finSuccEquiv_polynomial (V.map (algebraMap F (FractionRing F))),
        kw_lrSymOC_wCubic_map V (algebraMap F (FractionRing F))] at hp'
    have hdvd : (wCubic V).toPoly ∣ finSuccEquiv F 2 p :=
      (Polynomial.map_dvd_map _ hθ'' (wCubic_toPoly_monic V)).mp (neg_dvd.mp hp')

    have hdvd' : finSuccEquiv F 2 V.polynomial ∣ finSuccEquiv F 2 p := by
      rw [finSuccEquiv_polynomial V]; exact hdvd.neg_left
    have := map_dvd (finSuccEquiv F 2).symm hdvd'
    simpa only [AlgEquiv.symm_apply_apply] using this

  have hH : Ideal.span {V.polynomial}
      ≤ (Ideal.span {(V.map (algebraMap F (FractionRing F))).polynomial}).comap
        (MvPolynomial.map (algebraMap F (FractionRing F))) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap,
      WeierstrassCurve.Projective.map_polynomial]
    exact Ideal.subset_span (Set.mem_singleton _)
  exact (Ideal.quotientMap_injective' hcomap :
    Function.Injective (Ideal.quotientMap _ _ hH)).isDomain _

end Engine

abbrev kw_lrSymOC_ℬ₀ :=
  MvPolynomial (Fin 3) R₀ ⧸ Ideal.span {kw_lrSymOC_W₀.toProjective.polynomial}

local notation "ℬ₀" => kw_lrSymOC_ℬ₀

instance kw_lrSymOC_isDomain_ℬ₀ : IsDomain ℬ₀ :=
  kw_lrSymOC_isDomain_quot_span_poly kw_lrSymOC_W₀.toProjective

theorem kw_lrSymOC_isDomain_quotSpanPair :
    IsDomain (P₆₀ ⧸ Ideal.span {WP₁₀, WP₂₀}) := by
  classical
  let A := MvPolynomial (Fin 3) R₀
  let π : A →+* ℬ₀ := Ideal.Quotient.mk _
  let πC : R₀ →+* ℬ₀ := π.comp C
  let Wℬ : WeierstrassCurve ℬ₀ := kw_lrSymOC_W₀.map πC

  haveI hD : IsDomain
      (MvPolynomial (Fin 3) ℬ₀ ⧸ Ideal.span {Wℬ.toProjective.polynomial}) :=
    kw_lrSymOC_isDomain_quot_span_poly Wℬ.toProjective

  let e : P₆₀ ≃+* MvPolynomial (Fin 3) A :=
    (sumAlgEquiv R₀ (Fin 3) (Fin 3) : P₆₀ ≃ₐ[R₀] _).toRingEquiv
  let mπ : MvPolynomial (Fin 3) A →+* MvPolynomial (Fin 3) ℬ₀ := MvPolynomial.map π
  let ψ : P₆₀ →+* (MvPolynomial (Fin 3) ℬ₀ ⧸ Ideal.span {Wℬ.toProjective.polynomial}) :=
    (Ideal.Quotient.mk _).comp (mπ.comp (e : P₆₀ →+* _))
  have hsurj : Function.Surjective ψ :=
    (Ideal.Quotient.mk_surjective).comp
      ((MvPolynomial.map_surjective π Ideal.Quotient.mk_surjective).comp e.surjective)

  have heWP₁ : e WP₁₀
      = MvPolynomial.map (C : R₀ →+* A) kw_lrSymOC_W₀.toProjective.polynomial := by
    have h := DFunLike.congr_fun (sumAlgEquiv_comp_rename_inl R₀ (Fin 3) (Fin 3))
      kw_lrSymOC_W₀.toProjective.polynomial
    simpa [kw_lrAdd_WP₁, e] using h
  have heWP₂ : e WP₂₀ = C kw_lrSymOC_W₀.toProjective.polynomial := by
    have h := DFunLike.congr_fun (sumAlgEquiv_comp_rename_inr R₀ (Fin 3) (Fin 3))
      kw_lrSymOC_W₀.toProjective.polynomial
    simpa [kw_lrAdd_WP₂, e] using h

  have hker : RingHom.ker ψ = Ideal.span {WP₁₀, WP₂₀} := by

    have hkermπ : RingHom.ker mπ
        = Ideal.span {(C kw_lrSymOC_W₀.toProjective.polynomial :
            MvPolynomial (Fin 3) A)} := by
      rw [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_span, Set.image_singleton]
    have hmap : mπ (e WP₁₀) = Wℬ.toProjective.polynomial := by
      rw [heWP₁]
      show (MvPolynomial.map π) ((MvPolynomial.map C) _) = _
      rw [MvPolynomial.map_map, ← WeierstrassCurve.Projective.map_polynomial]
    have hcomap :
        (Ideal.span {Wℬ.toProjective.polynomial}).comap mπ
          = Ideal.span {e WP₁₀, e WP₂₀} := by
      have hmapspan :
          (Ideal.span {e WP₁₀}).map mπ = Ideal.span {Wℬ.toProjective.polynomial} := by
        rw [Ideal.map_span, Set.image_singleton, hmap]
      rw [← hmapspan, Ideal.comap_map_of_surjective mπ
          (MvPolynomial.map_surjective π Ideal.Quotient.mk_surjective),
        ← RingHom.ker_eq_comap_bot, hkermπ, ← heWP₂, ← Ideal.span_union,
        Set.union_singleton, Set.pair_comm]

    have h₁ : RingHom.ker ψ
        = ((Ideal.span {Wℬ.toProjective.polynomial}).comap mπ).comap
            (e : P₆₀ →+* _) := by
      ext x; simp only [RingHom.mem_ker, Ideal.mem_comap]
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [h₁, hcomap, Ideal.comap_coe, ← Ideal.map_symm, Ideal.map_span, Set.image_pair,
      RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]

  have heq : P₆₀ ⧸ Ideal.span {WP₁₀, WP₂₀}
      ≃+* (MvPolynomial (Fin 3) ℬ₀ ⧸ Ideal.span {Wℬ.toProjective.polynomial}) :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  exact heq.injective.isDomain _

theorem kw_lrSymOC_lrAddZ_notMem_span :
    kw_lrAdd_Z W₀ ∉ Ideal.span {WP₁₀, WP₂₀} := by

  let ev₀ : R₀ →+* ℤ := MvPolynomial.eval (0 : Fin 5 → ℤ)
  let ev : P₆₀ →+* ℤ :=
    MvPolynomial.eval₂Hom ev₀ (Sum.elim ![0, 0, 1] ![1, 1, 1])

  have hevXl : ∀ i, ev (X (Sum.inl i)) = ![(0:ℤ), 0, 1] i := fun i => by
    simp [ev, Sum.elim_inl]
  have hevXr : ∀ i, ev (X (Sum.inr i)) = ![(1:ℤ), 1, 1] i := fun i => by
    simp [ev, Sum.elim_inr]
  have hevCX : ∀ j : Fin 5, ev (C (X j)) = 0 := fun j => by
    simp [ev, ev₀]
  have hevC : ∀ n : ℤ, ev (C ((n : R₀))) = n := fun n => by
    simp [ev, ev₀]
  intro hmem
  have hWP₁ : ev WP₁₀ = 0 := by
    show ev (rename Sum.inl kw_lrSymOC_W₀.toProjective.polynomial) = 0
    simp only [WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
      kw_lrSymOC_W₀, map_add, map_sub, map_mul, map_pow, rename_C, rename_X]
    simp only [hevXl, hevCX, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  have hWP₂ : ev WP₂₀ = 0 := by
    show ev (rename Sum.inr kw_lrSymOC_W₀.toProjective.polynomial) = 0
    simp only [WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
      kw_lrSymOC_W₀, map_add, map_sub, map_mul, map_pow, rename_C, rename_X]
    simp only [hevXr, hevCX, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  have hZ : ev (kw_lrAdd_Z W₀) = 1 := by
    simp only [kw_lrAdd_Z, kw_lrAdd_starZ, kw_lrAdd_c₁₂, kw_lrAdd_c₂₁,
      kw_lrSymOC_W₀, map_add, map_sub, map_mul, map_neg, map_pow,
      hevXl, hevXr, hevCX, C_mul, hevC,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  have hker : Ideal.span {WP₁₀, WP₂₀} ≤ RingHom.ker ev := by
    rw [Ideal.span_le]
    intro x hx
    rcases (Set.mem_insert_iff.mp hx) with rfl | hx'
    · exact hWP₁
    · rw [Set.mem_singleton_iff.mp hx']; exact hWP₂
  have habs : ev (kw_lrAdd_Z W₀) = 0 := hker hmem
  rw [hZ] at habs
  exact one_ne_zero habs

theorem kw_lrSymOC_univ_mem_span :
    aeval ![kw_lrSym_X W₀, kw_lrSym_Y W₀, kw_lrSym_Z W₀]
        kw_lrSymOC_W₀.toProjective.polynomial
      ∈ Ideal.span {WP₁₀, WP₂₀} := by
  haveI := kw_lrSymOC_isDomain_quotSpanPair
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hscaled := kw_lrSymOC_scaled_mem_span_Z W₀
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow] at hscaled
  have hZne : (Ideal.Quotient.mk (Ideal.span {WP₁₀, WP₂₀})) (kw_lrAdd_Z W₀) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact kw_lrSymOC_lrAddZ_notMem_span
  exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero 3 hZne)

theorem kw_lrSym_onCurve_mem_span :
    aeval ![kw_lrSym_X W, kw_lrSym_Y W, kw_lrSym_Z W]
        W.toProjective.polynomial
      ∈ Ideal.span {kw_lrAdd_WP₁ W, kw_lrAdd_WP₂ W} := by
  let φ : R₀ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
  have hW : kw_lrSymOC_W₀.map φ = W := kw_lrSymOC_W₀_map W

  have hmem := Ideal.mem_map_of_mem
    (MvPolynomial.map φ : P₆₀ →+* MvPolynomial (Fin 3 ⊕ Fin 3) R)
    kw_lrSymOC_univ_mem_span
  rw [Ideal.map_span, Set.image_pair, kw_lrSymOC_map_WP₁, kw_lrSymOC_map_WP₂,
    hW] at hmem
  have hrw := kw_lrSymOC_map_W_lrSym kw_lrSymOC_W₀ φ
  rw [hW] at hrw
  rw [← hrw]
  exact hmem

end WeierstrassProjModel

end

end MEGA_KwLRSymOnCurve_lean

section MEGA_KwLRAddQuotientGradedHom_lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

open MvPolynomial WeierstrassCurve HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime
open scoped TensorProduct

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

local notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R
local notation "WP₁" => kw_lrAdd_WP₁ W
local notation "WP₂" => kw_lrAdd_WP₂ W
local notation "ℬ" => ProjModelRingCR W.toProjective

def kw_lrAdd_vec : Fin 3 → P₆ := ![kw_lrAdd_X W, kw_lrAdd_Y W, kw_lrAdd_Z W]

theorem kw_lrAdd_vec_isHomogeneous (k : Fin 3) : (kw_lrAdd_vec W k).IsHomogeneous 4 := by
  fin_cases k
  · exact kw_lrAdd_X_isHomogeneous W
  · exact kw_lrAdd_Y_isHomogeneous W
  · exact kw_lrAdd_Z_isHomogeneous W

theorem kw_lrComul_WP₁_isHomogeneous : (WP₁).IsHomogeneous 3 :=
  (isHomogeneous_polynomial W.toProjective).rename_isHomogeneous

theorem kw_lrComul_WP₂_isHomogeneous : (WP₂).IsHomogeneous 3 :=
  (isHomogeneous_polynomial W.toProjective).rename_isHomogeneous

theorem kw_lrComul_biSpan_isHomogeneous :
    (Ideal.span {WP₁, WP₂}).IsHomogeneous (homogeneousSubmodule (Fin 3 ⊕ Fin 3) R) := by
  refine Ideal.homogeneous_span _ _ ?_
  rintro p (rfl | hp)
  · exact ⟨3, (mem_homogeneousSubmodule _ _).mpr (kw_lrComul_WP₁_isHomogeneous W)⟩
  · rw [Set.mem_singleton_iff] at hp; subst hp
    exact ⟨3, (mem_homogeneousSubmodule _ _).mpr (kw_lrComul_WP₂_isHomogeneous W)⟩

def kw_lrComul_biIdeal : HomogeneousIdeal (homogeneousSubmodule (Fin 3 ⊕ Fin 3) R) :=
  ⟨Ideal.span {WP₁, WP₂}, kw_lrComul_biSpan_isHomogeneous W⟩

abbrev KwLRBiRing : Type u := P₆ ⧸ (kw_lrComul_biIdeal W).toIdeal

local notation "ℬ²" => KwLRBiRing W

abbrev kw_lrComul_biGrading : ℕ → Submodule R (ℬ²) :=
  quotGradingSubmodule (homogeneousSubmodule (Fin 3 ⊕ Fin 3) R) (kw_lrComul_biIdeal W).toIdeal

def kw_lrAdd_substHom : MvPolynomial (Fin 3) R →ₐ[R] P₆ := aeval (kw_lrAdd_vec W)

@[simp]
theorem kw_lrAdd_substHom_X (k : Fin 3) :
    kw_lrAdd_substHom W (X k) = kw_lrAdd_vec W k := aeval_X _ _

theorem kw_lrAdd_substHom_isHomogeneous {p : MvPolynomial (Fin 3) R} {n : ℕ}
    (hp : p.IsHomogeneous n) : (kw_lrAdd_substHom W p).IsHomogeneous (4 * n) :=
  hp.aeval (kw_lrAdd_vec W) (kw_lrAdd_vec_isHomogeneous W)

theorem kw_lrAdd_substHom_polynomial_mem :
    kw_lrAdd_substHom W W.toProjective.polynomial ∈ (kw_lrComul_biIdeal W).toIdeal := by
  exact kw_lrAdd_onCurve_mem_span W

noncomputable def kw_lrAdd_comulHom : (ℬ) →ₐ[R] (ℬ²) :=
  Ideal.Quotient.liftₐ (projModelHomogeneousIdealCR W.toProjective).toIdeal
    ((Ideal.Quotient.mkₐ R (kw_lrComul_biIdeal W).toIdeal).comp (kw_lrAdd_substHom W))
    (fun a ha => by
      refine (Ideal.Quotient.eq_zero_iff_mem).mpr ?_
      have hle : Ideal.span {W.toProjective.polynomial}
          ≤ (kw_lrComul_biIdeal W).toIdeal.comap (kw_lrAdd_substHom W).toRingHom :=
        Ideal.span_le.mpr
          (Set.singleton_subset_iff.mpr (kw_lrAdd_substHom_polynomial_mem W))
      exact hle ha)

theorem kw_lrAdd_comulHom_mk (a : MvPolynomial (Fin 3) R) :
    kw_lrAdd_comulHom W
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal a)
      = Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrAdd_substHom W a) := by
  rfl

theorem kw_lrAdd_comulHom_mk_X (k : Fin 3) :
    kw_lrAdd_comulHom W
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X k))
      = Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrAdd_vec W k) := by
  rw [kw_lrAdd_comulHom_mk, kw_lrAdd_substHom_X]

theorem kw_lrAdd_comulHom_graded {n : ℕ} {x : ℬ}
    (hx : x ∈ projModelGradingCR W.toProjective n) :
    kw_lrAdd_comulHom W x ∈ kw_lrComul_biGrading W (4 * n) := by
  obtain ⟨a, ha, rfl⟩ := (mem_quotGradingSubmodule_iff _ _).mp hx
  show Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrAdd_substHom W a)
    ∈ kw_lrComul_biGrading W (4 * n)
  exact mk_mem_quotGradingSubmodule _ _
    ((mem_homogeneousSubmodule _ _).mpr
      (kw_lrAdd_substHom_isHomogeneous W ((mem_homogeneousSubmodule _ _).mp ha)))

section TensorBridge

open Algebra.TensorProduct

noncomputable def kw_lrComul_incL : (ℬ) →ₐ[R] (ℬ) ⊗[R] (ℬ) :=
  Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := ℬ) (B := ℬ)

noncomputable def kw_lrComul_incR : (ℬ) →ₐ[R] (ℬ) ⊗[R] (ℬ) :=
  Algebra.TensorProduct.includeRight (R := R) (A := ℬ) (B := ℬ)

noncomputable def kw_lrComul_tensorProj : P₆ →ₐ[R] (ℬ) ⊗[R] (ℬ) :=
  aeval (Sum.elim
    (fun i => kw_lrComul_incL W
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X i)))
    (fun i => kw_lrComul_incR W
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X i))))

theorem kw_lrComul_tensorProj_rename_inl :
    (kw_lrComul_tensorProj W).comp (rename Sum.inl)
      = (kw_lrComul_incL W).comp
          (Ideal.Quotient.mkₐ R (projModelHomogeneousIdealCR W.toProjective).toIdeal) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp only [AlgHom.comp_apply, kw_lrComul_tensorProj, rename_X, aeval_X, Sum.elim_inl,
    Ideal.Quotient.mkₐ_eq_mk]

theorem kw_lrComul_tensorProj_rename_inr :
    (kw_lrComul_tensorProj W).comp (rename Sum.inr)
      = (kw_lrComul_incR W).comp
          (Ideal.Quotient.mkₐ R (projModelHomogeneousIdealCR W.toProjective).toIdeal) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp only [AlgHom.comp_apply, kw_lrComul_tensorProj, rename_X, aeval_X, Sum.elim_inr,
    Ideal.Quotient.mkₐ_eq_mk]

theorem kw_lrComul_mk_polynomial_eq_zero :
    Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
      W.toProjective.polynomial = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

theorem kw_lrComul_tensorProj_WP₁ : kw_lrComul_tensorProj W WP₁ = 0 := by
  have h := DFunLike.congr_fun (kw_lrComul_tensorProj_rename_inl W) W.toProjective.polynomial
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h
  show kw_lrComul_tensorProj W (rename Sum.inl W.toProjective.polynomial) = 0
  rw [h, kw_lrComul_mk_polynomial_eq_zero, map_zero]

theorem kw_lrComul_tensorProj_WP₂ : kw_lrComul_tensorProj W WP₂ = 0 := by
  have h := DFunLike.congr_fun (kw_lrComul_tensorProj_rename_inr W) W.toProjective.polynomial
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h
  show kw_lrComul_tensorProj W (rename Sum.inr W.toProjective.polynomial) = 0
  rw [h, kw_lrComul_mk_polynomial_eq_zero, map_zero]

noncomputable def kw_lrComul_biToTensor : (ℬ²) →ₐ[R] (ℬ) ⊗[R] (ℬ) :=
  Ideal.Quotient.liftₐ (kw_lrComul_biIdeal W).toIdeal (kw_lrComul_tensorProj W)
    (fun a ha => by
      have hle : Ideal.span {WP₁, WP₂} ≤ RingHom.ker (kw_lrComul_tensorProj W).toRingHom :=
        Ideal.span_le.mpr (by
          rintro p (rfl | hp)
          · exact kw_lrComul_tensorProj_WP₁ W
          · rw [Set.mem_singleton_iff] at hp; subst hp; exact kw_lrComul_tensorProj_WP₂ W)
      exact hle ha)

end TensorBridge

end WeierstrassProjModel

end

end MEGA_KwLRAddQuotientGradedHom_lean

section MEGA_KwLRSymQuotientGradedHom_lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

open MvPolynomial WeierstrassCurve HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime
open scoped TensorProduct

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

local notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R
local notation "ℬ" => ProjModelRingCR W.toProjective
local notation "ℬ²" => KwLRBiRing W

def kw_lrSym_vec : Fin 3 → P₆ := ![kw_lrSym_X W, kw_lrSym_Y W, kw_lrSym_Z W]

theorem kw_lrSym_vec_isHomogeneous (k : Fin 3) : (kw_lrSym_vec W k).IsHomogeneous 4 := by
  fin_cases k
  · exact kw_lrSym_X_isHomogeneous W
  · exact kw_lrSym_Y_isHomogeneous W
  · exact kw_lrSym_Z_isHomogeneous W

def kw_lrSym_substHom : MvPolynomial (Fin 3) R →ₐ[R] P₆ := aeval (kw_lrSym_vec W)

@[simp]
theorem kw_lrSym_substHom_X (k : Fin 3) :
    kw_lrSym_substHom W (X k) = kw_lrSym_vec W k := aeval_X _ _

theorem kw_lrSym_substHom_isHomogeneous {p : MvPolynomial (Fin 3) R} {n : ℕ}
    (hp : p.IsHomogeneous n) : (kw_lrSym_substHom W p).IsHomogeneous (4 * n) :=
  hp.aeval (kw_lrSym_vec W) (kw_lrSym_vec_isHomogeneous W)

theorem kw_lrSym_substHom_polynomial_mem :
    kw_lrSym_substHom W W.toProjective.polynomial ∈ (kw_lrComul_biIdeal W).toIdeal := by
  exact kw_lrSym_onCurve_mem_span W

noncomputable def kw_lrSym_comulHom : (ℬ) →ₐ[R] (ℬ²) :=
  Ideal.Quotient.liftₐ (projModelHomogeneousIdealCR W.toProjective).toIdeal
    ((Ideal.Quotient.mkₐ R (kw_lrComul_biIdeal W).toIdeal).comp (kw_lrSym_substHom W))
    (fun a ha => by
      refine (Ideal.Quotient.eq_zero_iff_mem).mpr ?_
      have hle : Ideal.span {W.toProjective.polynomial}
          ≤ (kw_lrComul_biIdeal W).toIdeal.comap (kw_lrSym_substHom W).toRingHom :=
        Ideal.span_le.mpr
          (Set.singleton_subset_iff.mpr (kw_lrSym_substHom_polynomial_mem W))
      exact hle ha)

theorem kw_lrSym_comulHom_mk (a : MvPolynomial (Fin 3) R) :
    kw_lrSym_comulHom W
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal a)
      = Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrSym_substHom W a) := by
  rfl

theorem kw_lrSym_comulHom_mk_X (k : Fin 3) :
    kw_lrSym_comulHom W
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X k))
      = Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrSym_vec W k) := by
  rw [kw_lrSym_comulHom_mk, kw_lrSym_substHom_X]

theorem kw_lrSym_comulHom_graded {n : ℕ} {x : ℬ}
    (hx : x ∈ projModelGradingCR W.toProjective n) :
    kw_lrSym_comulHom W x ∈ kw_lrComul_biGrading W (4 * n) := by
  obtain ⟨a, ha, rfl⟩ := (mem_quotGradingSubmodule_iff _ _).mp hx
  show Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrSym_substHom W a)
    ∈ kw_lrComul_biGrading W (4 * n)
  exact mk_mem_quotGradingSubmodule _ _
    ((mem_homogeneousSubmodule _ _).mpr
      (kw_lrSym_substHom_isHomogeneous W ((mem_homogeneousSubmodule _ _).mp ha)))

end WeierstrassProjModel

end

end MEGA_KwLRSymQuotientGradedHom_lean

section MEGA_KwLRChartHomAway_lean
set_option autoImplicit false

noncomputable section

open MvPolynomial WeierstrassCurve HomogeneousLocalization HomogeneousIdealQuotientGrading

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "ℬ" => ProjModelRingCR W.toProjective
set_option quotPrecheck false in
local notation "ℬ²" => KwLRBiRing W
set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
set_option quotPrecheck false in
local notation "mk₆" => Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal

instance kw_lrChart_biGrading_gradedAlgebra :
    GradedAlgebra (kw_lrComul_biGrading W) := inferInstance

theorem kw_lrChart_mkX_mem_one (k : Fin 3) :
    mk₃ (X k : MvPolynomial (Fin 3) R) ∈ projModelGradingCR W.toProjective 1 :=
  mk_mem_quotGradingSubmodule _ _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R k))

theorem kw_lrChart_mkAdd_mem_four (k : Fin 3) :
    mk₆ (kw_lrAdd_vec W k) ∈ kw_lrComul_biGrading W 4 :=
  mk_mem_quotGradingSubmodule _ _
    ((mem_homogeneousSubmodule _ _).mpr (kw_lrAdd_vec_isHomogeneous W k))

set_option quotPrecheck false in

local notation "𝒜" k => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X k : MvPolynomial (Fin 3) R))

set_option quotPrecheck false in

local notation "𝒜²" k => HomogeneousLocalization.Away (kw_lrComul_biGrading W)
  (Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrAdd_vec W k))

theorem kw_lrChart_comulHom_mkX_pow (k : Fin 3) (n : ℕ) :
    kw_lrAdd_comulHom W (mk₃ (X k : MvPolynomial (Fin 3) R) ^ n)
      = mk₆ (kw_lrAdd_vec W k) ^ n := by
  rw [map_pow, kw_lrAdd_comulHom_mk_X]

theorem kw_lrChart_powers_comap_le (k : Fin 3) :
    Submonoid.powers (mk₃ (X k : MvPolynomial (Fin 3) R))
      ≤ (Submonoid.powers (mk₆ (kw_lrAdd_vec W k))).comap
          (kw_lrAdd_comulHom W).toRingHom := by
  rintro a ⟨n, rfl⟩
  exact ⟨n, (kw_lrChart_comulHom_mkX_pow W k n).symm⟩

noncomputable def kw_lrChart_locMap (k : Fin 3) :
    Localization.Away (mk₃ (X k : MvPolynomial (Fin 3) R))
      →+* Localization.Away (mk₆ (kw_lrAdd_vec W k)) :=
  IsLocalization.map _ (kw_lrAdd_comulHom W).toRingHom (kw_lrChart_powers_comap_le W k)

noncomputable def kw_lrChart_aux (k : Fin 3) :
    (𝒜 k) →+* Localization.Away (mk₆ (kw_lrAdd_vec W k)) :=
  (kw_lrChart_locMap W k).comp
    (algebraMap (𝒜 k) (Localization.Away (mk₃ (X k : MvPolynomial (Fin 3) R))))

theorem kw_lrChart_aux_mk (k : Fin 3) (n : ℕ) (a : ℬ)
    (ha : a ∈ projModelGradingCR W.toProjective (n • 1)) :
    kw_lrChart_aux W k
        (HomogeneousLocalization.Away.mk (projModelGradingCR W.toProjective)
          (kw_lrChart_mkX_mem_one W k) n a ha)
      = Localization.mk (kw_lrAdd_comulHom W a)
          (⟨mk₆ (kw_lrAdd_vec W k) ^ n, n, rfl⟩
            : Submonoid.powers (mk₆ (kw_lrAdd_vec W k))) := by
  show kw_lrChart_locMap W k
      (HomogeneousLocalization.Away.mk _ (kw_lrChart_mkX_mem_one W k) n a ha).val = _
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', kw_lrChart_locMap,
    IsLocalization.map_mk', ← Localization.mk_eq_mk']
  congr 1
  exact Subtype.ext (kw_lrChart_comulHom_mkX_pow W k n)

noncomputable def kw_lrChart_witness (k : Fin 3) (n : ℕ) (a : ℬ)
    (ha : a ∈ projModelGradingCR W.toProjective (n • 1)) : (𝒜² k) :=
  HomogeneousLocalization.Away.mk (kw_lrComul_biGrading W)
    (kw_lrChart_mkAdd_mem_four W k) n (kw_lrAdd_comulHom W a)
    (by
      have ha' : a ∈ projModelGradingCR W.toProjective n := by simpa using ha
      have h4n : kw_lrAdd_comulHom W a ∈ kw_lrComul_biGrading W (4 * n) :=
        kw_lrAdd_comulHom_graded W ha'
      simpa [smul_eq_mul, Nat.mul_comm] using h4n)

theorem kw_lrChart_witness_val (k : Fin 3) (n : ℕ) (a : ℬ)
    (ha : a ∈ projModelGradingCR W.toProjective (n • 1)) :
    (kw_lrChart_witness W k n a ha).val
      = kw_lrChart_aux W k
          (HomogeneousLocalization.Away.mk (projModelGradingCR W.toProjective)
            (kw_lrChart_mkX_mem_one W k) n a ha) := by
  rw [kw_lrChart_aux_mk]; rfl

theorem kw_lrChart_aux_range_subset (k : Fin 3) :
    Set.range (kw_lrChart_aux W k)
      ⊆ Set.range (algebraMap (𝒜² k) (Localization.Away (mk₆ (kw_lrAdd_vec W k)))) := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (projModelGradingCR W.toProjective) (kw_lrChart_mkX_mem_one W k) z
  exact ⟨kw_lrChart_witness W k n a ha,
    (HomogeneousLocalization.algebraMap_apply _).trans (kw_lrChart_witness_val W k n a ha)⟩

theorem kw_lrChart_aux_range_le (k : Fin 3) :
    (kw_lrChart_aux W k).range
      ≤ (algebraMap (𝒜² k) (Localization.Away (mk₆ (kw_lrAdd_vec W k)))).range := by
  rintro _ ⟨z, rfl⟩
  exact kw_lrChart_aux_range_subset W k ⟨z, rfl⟩

noncomputable def kw_lrChart_away (k : Fin 3) : (𝒜 k) →+* (𝒜² k) := by
  let e := RingEquiv.ofLeftInverse
    (f := algebraMap (𝒜² k) (Localization.Away (mk₆ (kw_lrAdd_vec W k))))
    (h := (HomogeneousLocalization.val_injective _).hasLeftInverse.choose_spec)
  exact RingHom.comp (e.symm.toRingHom.comp (Subring.inclusion (kw_lrChart_aux_range_le W k)))
    (kw_lrChart_aux W k).rangeRestrict

end WeierstrassProjModel

end

end MEGA_KwLRChartHomAway_lean

section MEGA_KwProjPullbackAwayCoverCR_lean
set_option autoImplicit false

noncomputable section

open MvPolynomial HomogeneousLocalization

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (R : Type u) [CommRing R]

section ChartStructureMap

variable (V : WeierstrassCurve.Projective R)

set_option quotPrecheck false in

local notation "𝒜" i =>
  HomogeneousLocalization.Away (projModelGradingCR V)
    (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))

@[reducible] noncomputable def kw_pbac_awayAlgebra (i : Fin 3) : Algebra R (𝒜 i) :=
  ((fromZeroRingHom (projModelGradingCR V) _).comp
    (algebraMap R ((projModelGradingCR V) 0))).toAlgebra

end ChartStructureMap

end WeierstrassProjModel

end
end MEGA_KwProjPullbackAwayCoverCR_lean

section MEGA_A1_Properness_lean

set_option autoImplicit false

namespace WeierstrassProjModel

open HomogeneousIdealQuotientGrading

section FiniteTypeEngine

variable {ι A σ τ : Type*}
variable [CommRing A] [AddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜]
variable (I : Ideal A)
variable [SetLike τ (A ⧸ I)] [AddSubmonoidClass τ (A ⧸ I)] (ℬ : ι → τ) [SetLike.GradedMonoid ℬ]

theorem finiteType_gradeZero_quotient_of_mk_mem
    (hmem0 : ∀ a : A, a ∈ 𝒜 0 → Ideal.Quotient.mk I a ∈ ℬ 0)
    (hFT : Algebra.FiniteType (𝒜 0) A) :
    Algebra.FiniteType (ℬ 0) (A ⧸ I) := by
  classical
  obtain ⟨s, hs⟩ := hFT.out
  refine ⟨⟨s.image (Ideal.Quotient.mk I), ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ha : a ∈ Algebra.adjoin (𝒜 0) (s : Set A) := hs.ge Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
      exact Algebra.subset_adjoin (by
        simpa using Finset.mem_image_of_mem (Ideal.Quotient.mk I) hy)
  | algebraMap r =>
      have hr : Ideal.Quotient.mk I (algebraMap (𝒜 0) A r) ∈ ℬ 0 := hmem0 _ r.2
      exact Subalgebra.algebraMap_mem _ (⟨_, hr⟩ : ℬ 0)
  | add x y hx hy ihx ihy =>
      rw [map_add]; exact add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
      rw [map_mul]; exact mul_mem ihx ihy

end FiniteTypeEngine

section BaseUpgrade

variable {ι R A : Type*}
variable [CommRing R] [CommRing A] [Algebra R A] [AddMonoid ι]
variable (𝒜 : ι → Submodule R A) [SetLike.GradedMonoid 𝒜]

theorem isScalarTower_gradeZero : IsScalarTower R (𝒜 0) A :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem finiteType_gradeZero_of_finiteType_base (hFT : Algebra.FiniteType R A) :
    Algebra.FiniteType (𝒜 0) A := by
  haveI : IsScalarTower R (𝒜 0) A := isScalarTower_gradeZero 𝒜
  haveI := hFT
  exact Algebra.FiniteType.of_restrictScalars_finiteType R (𝒜 0) A

end BaseUpgrade

section QuotGradingSubmoduleDegreeZero

variable {ι R A : Type*}
variable [CommRing R] [CommRing A] [Algebra R A] [AddMonoid ι]
variable (𝒜 : ι → Submodule R A) [SetLike.GradedMonoid 𝒜]
variable (I : Ideal A)

theorem quotGradingSubmodule_degreeZero_finiteType (hFT : Algebra.FiniteType (𝒜 0) A) :
    Algebra.FiniteType ((quotGradingSubmodule 𝒜 I) 0) (A ⧸ I) :=
  finiteType_gradeZero_quotient_of_mk_mem 𝒜 I (quotGradingSubmodule 𝒜 I)
    (fun _ ha => mk_mem_quotGradingSubmodule 𝒜 I ha) hFT

instance quotGradingSubmoduleDegreeZeroFiniteType [Algebra.FiniteType (𝒜 0) A] :
    Algebra.FiniteType ((quotGradingSubmodule 𝒜 I) 0) (A ⧸ I) :=
  quotGradingSubmodule_degreeZero_finiteType 𝒜 I ‹_›

end QuotGradingSubmoduleDegreeZero

section MvPolynomialVenue

open MvPolynomial

instance homogeneousSubmoduleDegreeZeroFiniteType (σs R : Type*) [Finite σs] [CommRing R] :
    Algebra.FiniteType ((homogeneousSubmodule σs R) 0) (MvPolynomial σs R) :=
  finiteType_gradeZero_of_finiteType_base (homogeneousSubmodule σs R) inferInstance

end MvPolynomialVenue

section DegreeZeroEngine

variable {ι R A : Type*}
variable [CommRing R] [CommRing A] [Algebra R A] [AddMonoid ι]
variable (𝒜 : ι → Submodule R A) [SetLike.GradedMonoid 𝒜]
variable (I : Ideal A)

end DegreeZeroEngine

section PolynomialDegreeZero

open MvPolynomial

theorem mem_homogeneousSubmodule_zero_iff_exists_C {σ R : Type*} [CommSemiring R]
    {p : MvPolynomial σ R} :
    p ∈ homogeneousSubmodule σ R 0 ↔ ∃ r : R, C r = p := by
  constructor
  · intro hp
    rw [homogeneousSubmodule_zero] at hp
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hp
    exact ⟨r, by rwa [← algebraMap_eq]⟩
  · rintro ⟨r, rfl⟩
    exact (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ _)

variable (σ R : Type*) [CommSemiring R]

end PolynomialDegreeZero

section ConstantCoeffKernel

open MvPolynomial

variable {σ R : Type*} [CommSemiring R]

theorem constantCoeff_eq_zero_of_isHomogeneous_of_ne_zero {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) (hn : n ≠ 0) :
    constantCoeff p = 0 :=
  hp.coeff_eq_zero (by simpa using hn.symm)

theorem span_le_ker_constantCoeff_of_forall_constantCoeff_eq_zero
    {S : Set (MvPolynomial σ R)} (h : ∀ p ∈ S, constantCoeff p = 0) :
    Ideal.span S ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R) :=
  Ideal.span_le.mpr fun p hp => RingHom.mem_ker.mpr (h p hp)

theorem span_le_ker_constantCoeff_of_forall_isHomogeneous_pos
    {S : Set (MvPolynomial σ R)} (h : ∀ p ∈ S, ∃ n : ℕ, n ≠ 0 ∧ p.IsHomogeneous n) :
    Ideal.span S ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R) :=
  span_le_ker_constantCoeff_of_forall_constantCoeff_eq_zero fun p hp => by
    obtain ⟨n, hn, hhom⟩ := h p hp
    exact constantCoeff_eq_zero_of_isHomogeneous_of_ne_zero hhom hn

end ConstantCoeffKernel

section DegreeZeroIdentification

open MvPolynomial

variable {σ R : Type*} [CommRing R]
variable (I : Ideal (MvPolynomial σ R))

lemma quotGradingSubmodule_degreeZero_algebraMap_coe (r : R) :
    ((algebraMap R ((quotGradingSubmodule (homogeneousSubmodule σ R) I) 0) r :
        (quotGradingSubmodule (homogeneousSubmodule σ R) I) 0) : MvPolynomial σ R ⧸ I)
      = Ideal.Quotient.mk I (C r) := rfl

theorem quotGradingSubmodule_degreeZero_algebraMap_surjective :
    Function.Surjective
      (algebraMap R ((quotGradingSubmodule (homogeneousSubmodule σ R) I) 0)) := by
  rintro ⟨b, hb⟩
  obtain ⟨p, hp, rfl⟩ := (mem_quotGradingSubmodule_iff (homogeneousSubmodule σ R) I).mp hb
  obtain ⟨r, rfl⟩ := mem_homogeneousSubmodule_zero_iff_exists_C.mp hp
  exact ⟨r, Subtype.ext rfl⟩

theorem quotGradingSubmodule_degreeZero_algebraMap_injective
    (hI : I ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R)) :
    Function.Injective
      (algebraMap R ((quotGradingSubmodule (homogeneousSubmodule σ R) I) 0)) := by
  intro r s hrs
  have hval : Ideal.Quotient.mk I (C r) = Ideal.Quotient.mk I (C s) :=
    congrArg Subtype.val hrs
  have hsub : (C r - C s : MvPolynomial σ R) ∈ I := Ideal.Quotient.eq.mp hval
  rw [← map_sub] at hsub
  have h0 : constantCoeff (C (r - s) : MvPolynomial σ R) = 0 := RingHom.mem_ker.mp (hI hsub)
  rw [constantCoeff_C] at h0
  exact sub_eq_zero.mp h0

theorem quotGradingSubmodule_degreeZero_algebraMap_bijective
    (hI : I ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R)) :
    Function.Bijective
      (algebraMap R ((quotGradingSubmodule (homogeneousSubmodule σ R) I) 0)) :=
  ⟨quotGradingSubmodule_degreeZero_algebraMap_injective I hI,
   quotGradingSubmodule_degreeZero_algebraMap_surjective I⟩

end DegreeZeroIdentification

end WeierstrassProjModel

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type*} [CommRing R]

theorem projModelIdeal_le_ker_constantCoeffCR (V : WeierstrassCurve.Projective R) :
    (projModelHomogeneousIdealCR V).toIdeal
      ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin 3) R →+* R) :=
  span_le_ker_constantCoeff_of_forall_isHomogeneous_pos fun p hp => by
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact ⟨3, by decide, isHomogeneous_polynomial V⟩

theorem projModel_degreeZero_algebraMap_bijectiveCR (V : WeierstrassCurve.Projective R) :
    Function.Bijective (algebraMap R ((projModelGradingCR V) 0)) :=
  quotGradingSubmodule_degreeZero_algebraMap_bijective (projModelHomogeneousIdealCR V).toIdeal
    (projModelIdeal_le_ker_constantCoeffCR V)

def projModelDegreeZeroRingEquivCR (V : WeierstrassCurve.Projective R) :
    R ≃+* ((projModelGradingCR V) 0) :=
  RingEquiv.ofBijective (algebraMap R ((projModelGradingCR V) 0))
    (projModel_degreeZero_algebraMap_bijectiveCR V)

def projModelSpecDegreeZeroIsoCR (V : WeierstrassCurve.Projective R) :
    Spec (CommRingCat.of ((projModelGradingCR V) 0)) ≅ Spec (CommRingCat.of R) where
  hom := Spec.map (CommRingCat.ofHom (algebraMap R ((projModelGradingCR V) 0)))
  inv := Spec.map (CommRingCat.ofHom
    ((projModelDegreeZeroRingEquivCR V).symm : ((projModelGradingCR V) 0) →+* R))
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show (algebraMap R ((projModelGradingCR V) 0)).comp
          ((projModelDegreeZeroRingEquivCR V).symm : ((projModelGradingCR V) 0) →+* R)
        = RingHom.id ((projModelGradingCR V) 0) from
        RingHom.ext fun x => (projModelDegreeZeroRingEquivCR V).apply_symm_apply x,
      CommRingCat.ofHom_id, Spec.map_id]
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show ((projModelDegreeZeroRingEquivCR V).symm : ((projModelGradingCR V) 0) →+* R).comp
          (algebraMap R ((projModelGradingCR V) 0))
        = RingHom.id R from
        RingHom.ext fun x => (projModelDegreeZeroRingEquivCR V).symm_apply_apply x,
      CommRingCat.ofHom_id, Spec.map_id]

instance projModel_isIso_spec_mapCR (V : WeierstrassCurve.Projective R) :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap R ((projModelGradingCR V) 0)))) :=
  inferInstanceAs (IsIso (projModelSpecDegreeZeroIsoCR V).hom)

instance isProper_projModelStrCR (V : WeierstrassCurve.Projective R) :
    IsProper (projModelStrCR V) := by
  show IsProper (Proj.toSpecZero (projModelGradingCR V) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R ((projModelGradingCR V) 0))))
  infer_instance

end WeierstrassProjModel

end

end MEGA_A1_Properness_lean

section MEGA_KwLRChartHomToTensor_lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

noncomputable section

open MvPolynomial WeierstrassCurve HomogeneousLocalization HomogeneousIdealQuotientGrading
open scoped TensorProduct

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "ℬ" => ProjModelRingCR W.toProjective
set_option quotPrecheck false in
local notation "ℬ²" => KwLRBiRing W
set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
set_option quotPrecheck false in
local notation "mk₆" => Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))
set_option quotPrecheck false in
local notation "𝒜²" k => HomogeneousLocalization.Away (kw_lrComul_biGrading W)
  (Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrAdd_vec W k))

noncomputable def kw_lrChart_gen (i m : Fin 3) : (𝒜 i) :=
  HomogeneousLocalization.mk
    ⟨1, ⟨mk₃ (X m : MvPolynomial (Fin 3) R), kw_lrChart_mkX_mem_one W m⟩,
        ⟨mk₃ (X i : MvPolynomial (Fin 3) R), kw_lrChart_mkX_mem_one W i⟩, ⟨1, pow_one _⟩⟩

theorem kw_lrChart_gen_val (i m : Fin 3) :
    (kw_lrChart_gen W i m).val
      = Localization.mk (mk₃ (X m : MvPolynomial (Fin 3) R))
          (⟨mk₃ (X i : MvPolynomial (Fin 3) R), 1, pow_one _⟩
            : Submonoid.powers (mk₃ (X i : MvPolynomial (Fin 3) R))) := rfl

noncomputable def kw_lrChart_dehom (i : Fin 3) :
    MvPolynomial (Fin 3) R →ₐ[R] (𝒜 i) :=
  aeval (kw_lrChart_gen W i)

theorem kw_lrChart_dehom_C_val (i : Fin 3) (r : R) :
    (kw_lrChart_dehom W i (C r)).val
      = Localization.mk (mk₃ (C r : MvPolynomial (Fin 3) R))
          (1 : Submonoid.powers (mk₃ (X i : MvPolynomial (Fin 3) R))) := by
  rw [kw_lrChart_dehom, aeval_C]
  show (fromZeroRingHom (projModelGradingCR W.toProjective) _
      (algebraMap R ((projModelGradingCR W.toProjective) 0) r)).val = _

  simp only [fromZeroRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    HomogeneousLocalization.val_mk, quotGradingSubmodule_degreeZero_algebraMap_coe]
  rfl

theorem kw_lrChart_dehom_X_val (i m : Fin 3) :
    (kw_lrChart_dehom W i (X m)).val
      = Localization.mk (mk₃ (X m : MvPolynomial (Fin 3) R))
          (⟨mk₃ (X i : MvPolynomial (Fin 3) R), 1, pow_one _⟩
            : Submonoid.powers (mk₃ (X i : MvPolynomial (Fin 3) R))) := by
  rw [kw_lrChart_dehom, aeval_X, kw_lrChart_gen_val]

theorem kw_lrChart_dehom_monomial_val (i : Fin 3) (d : Fin 3 →₀ ℕ) (c : R) (n : ℕ)
    (hn : d 0 + d 1 + d 2 = n) :
    (kw_lrChart_dehom W i (monomial d c)).val
      = Localization.mk (mk₃ (monomial d c : MvPolynomial (Fin 3) R))
          (⟨mk₃ (X i : MvPolynomial (Fin 3) R) ^ n, n, rfl⟩
            : Submonoid.powers (mk₃ (X i : MvPolynomial (Fin 3) R))) := by
  have hmon : (monomial d c : MvPolynomial (Fin 3) R)
      = C c * (X 0 ^ d 0 * X 1 ^ d 1 * X 2 ^ d 2) := by
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ fun _ => pow_zero _,
      Fin.prod_univ_three]

  rw [hmon]
  simp only [map_mul, map_pow, HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
    kw_lrChart_dehom_C_val, kw_lrChart_dehom_X_val,
    Localization.mk_pow, Localization.mk_mul, one_mul, mul_one, one_pow]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩

  have key : (mk₃ (X i : MvPolynomial (Fin 3) R)) ^ n
      = (mk₃ (X i : MvPolynomial (Fin 3) R)) ^ d 0
        * (mk₃ (X i : MvPolynomial (Fin 3) R)) ^ d 1
        * (mk₃ (X i : MvPolynomial (Fin 3) R)) ^ d 2 := by
    rw [← pow_add, ← pow_add, hn]
  push_cast [key]
  ring

set_option maxSynthPendingDepth 3 in

theorem kw_lrChart_dehom_isHomogeneous_val (i : Fin 3) (n : ℕ)
    (p : MvPolynomial (Fin 3) R) (hp : p.IsHomogeneous n) :
    (kw_lrChart_dehom W i p).val
      = Localization.mk (mk₃ p)
          (⟨mk₃ (X i : MvPolynomial (Fin 3) R) ^ n, n, rfl⟩
            : Submonoid.powers (mk₃ (X i : MvPolynomial (Fin 3) R))) := by
  conv_lhs => rw [MvPolynomial.as_sum p]
  conv_rhs => rw [MvPolynomial.as_sum p]

  haveI : AddMonoidHomClass
      ((𝒜 i) →+* Localization (Submonoid.powers (mk₃ (X i : MvPolynomial (Fin 3) R))))
      (𝒜 i) (Localization (Submonoid.powers (mk₃ (X i : MvPolynomial (Fin 3) R)))) :=
    RingHomClass.toAddMonoidHomClass
  rw [map_sum, ← HomogeneousLocalization.algebraMap_apply, map_sum, map_sum, Localization.mk_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [HomogeneousLocalization.algebraMap_apply]
  have hdeg : d.degree = n := by
    by_contra hne; exact MvPolynomial.mem_support_iff.mp hd (hp.coeff_eq_zero hne)
  exact kw_lrChart_dehom_monomial_val W i d (MvPolynomial.coeff d p) n
    (by rw [← hdeg, Finsupp.degree_eq_sum, Fin.sum_univ_three])

theorem kw_lrChart_mk_mem_of_isHomogeneous (n : ℕ) (p : MvPolynomial (Fin 3) R)
    (hp : p.IsHomogeneous n) :
    mk₃ p ∈ projModelGradingCR W.toProjective (n • 1) := by
  rw [nsmul_one, Nat.cast_id]
  exact mk_mem_quotGradingSubmodule _ _ ((mem_homogeneousSubmodule _ _).mpr hp)

theorem kw_lrChart_dehom_isHomogeneous (i : Fin 3) (n : ℕ)
    (p : MvPolynomial (Fin 3) R) (hp : p.IsHomogeneous n) :
    kw_lrChart_dehom W i p
      = HomogeneousLocalization.Away.mk (projModelGradingCR W.toProjective)
          (kw_lrChart_mkX_mem_one W i) n (mk₃ p)
          (kw_lrChart_mk_mem_of_isHomogeneous W n p hp) := by
  apply HomogeneousLocalization.val_injective
  rw [kw_lrChart_dehom_isHomogeneous_val W i n p hp, HomogeneousLocalization.Away.val_mk]

theorem kw_lrChart_dehom_polynomial (i : Fin 3) :
    kw_lrChart_dehom W i W.toProjective.polynomial = 0 := by
  rw [kw_lrChart_dehom_isHomogeneous W i 3 _
    (ProjWeierstrassCubicPrime.isHomogeneous_polynomial W.toProjective)]
  refine HomogeneousLocalization.mk_eq_zero_of_num _ ?_
  exact Subtype.ext (kw_lrComul_mk_polynomial_eq_zero W)

section TensorEv

variable (i j : Fin 3)

noncomputable def kw_lrChart_inL : (𝒜 i) →ₐ[R] (𝒜 i) ⊗[R] (𝒜 j) :=
  Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := 𝒜 i) (B := 𝒜 j)

noncomputable def kw_lrChart_inR : (𝒜 j) →ₐ[R] (𝒜 i) ⊗[R] (𝒜 j) :=
  Algebra.TensorProduct.includeRight (R := R) (A := 𝒜 i) (B := 𝒜 j)

noncomputable def kw_lrChart_ev :
    MvPolynomial (Fin 3 ⊕ Fin 3) R →ₐ[R] (𝒜 i) ⊗[R] (𝒜 j) :=
  aeval (Sum.elim (fun m => kw_lrChart_inL W i j (kw_lrChart_gen W i m))
                  (fun m => kw_lrChart_inR W i j (kw_lrChart_gen W j m)))

theorem kw_lrChart_ev_rename_inl :
    (kw_lrChart_ev W i j).comp (rename Sum.inl)
      = (kw_lrChart_inL W i j).comp (kw_lrChart_dehom W i) := by
  refine MvPolynomial.algHom_ext fun m => ?_
  simp only [AlgHom.comp_apply, kw_lrChart_ev, rename_X, aeval_X, Sum.elim_inl,
    kw_lrChart_dehom]

theorem kw_lrChart_ev_rename_inr :
    (kw_lrChart_ev W i j).comp (rename Sum.inr)
      = (kw_lrChart_inR W i j).comp (kw_lrChart_dehom W j) := by
  refine MvPolynomial.algHom_ext fun m => ?_
  simp only [AlgHom.comp_apply, kw_lrChart_ev, rename_X, aeval_X, Sum.elim_inr,
    kw_lrChart_dehom]

theorem kw_lrChart_ev_WP₁ : kw_lrChart_ev W i j (kw_lrAdd_WP₁ W) = 0 := by
  have h := DFunLike.congr_fun (kw_lrChart_ev_rename_inl W i j) W.toProjective.polynomial
  simp only [AlgHom.comp_apply] at h
  show kw_lrChart_ev W i j (rename Sum.inl W.toProjective.polynomial) = 0
  rw [h, kw_lrChart_dehom_polynomial, map_zero]

theorem kw_lrChart_ev_WP₂ : kw_lrChart_ev W i j (kw_lrAdd_WP₂ W) = 0 := by
  have h := DFunLike.congr_fun (kw_lrChart_ev_rename_inr W i j) W.toProjective.polynomial
  simp only [AlgHom.comp_apply] at h
  show kw_lrChart_ev W i j (rename Sum.inr W.toProjective.polynomial) = 0
  rw [h, kw_lrChart_dehom_polynomial, map_zero]

noncomputable def kw_lrChart_ev' : (ℬ²) →ₐ[R] (𝒜 i) ⊗[R] (𝒜 j) :=
  Ideal.Quotient.liftₐ (kw_lrComul_biIdeal W).toIdeal (kw_lrChart_ev W i j)
    (fun a ha => by
      have hle : Ideal.span {kw_lrAdd_WP₁ W, kw_lrAdd_WP₂ W}
          ≤ RingHom.ker (kw_lrChart_ev W i j).toRingHom :=
        Ideal.span_le.mpr (by
          rintro p (rfl | hp)
          · exact kw_lrChart_ev_WP₁ W i j
          · rw [Set.mem_singleton_iff] at hp; subst hp; exact kw_lrChart_ev_WP₂ W i j)
      exact hle ha)

end TensorEv

section ToTensor

variable (i j k : Fin 3)

instance kw_lrChart_tensorCommRing : CommRing ((𝒜 i) ⊗[R] (𝒜 j)) := inferInstance

noncomputable def kw_lrChart_u : (𝒜 i) ⊗[R] (𝒜 j) :=
  kw_lrChart_ev' W i j (mk₆ (kw_lrAdd_vec W k))

theorem kw_lrChart_powers_ev'_comap_le :
    Submonoid.powers (mk₆ (kw_lrAdd_vec W k))
      ≤ (Submonoid.powers (kw_lrChart_u W i j k)).comap
          (kw_lrChart_ev' W i j).toRingHom := by
  rintro a ⟨n, rfl⟩
  exact ⟨n, by rw [map_pow]; rfl⟩

noncomputable def kw_lrChart_toTensorLoc :
    Localization.Away (mk₆ (kw_lrAdd_vec W k))
      →+* Localization.Away (kw_lrChart_u W i j k) :=
  IsLocalization.map _ (kw_lrChart_ev' W i j).toRingHom
    (kw_lrChart_powers_ev'_comap_le W i j k)

noncomputable def kw_lrChart_toTensor :
    (𝒜² k) →+* Localization.Away (kw_lrChart_u W i j k) :=
  (kw_lrChart_toTensorLoc W i j k).comp
    (algebraMap (𝒜² k) (Localization.Away (mk₆ (kw_lrAdd_vec W k))))

end ToTensor

section Composite

variable (i j k : Fin 3)

noncomputable def kw_lrChart_tensor :
    (𝒜 k) →+* Localization.Away (kw_lrChart_u W i j k) :=
  (kw_lrChart_toTensor W i j k).comp (kw_lrChart_away W k)

end Composite

end WeierstrassProjModel

end

end MEGA_KwLRChartHomToTensor_lean

section MEGA_KwLRSymChartHomAway_lean
set_option autoImplicit false

noncomputable section

open MvPolynomial WeierstrassCurve HomogeneousLocalization HomogeneousIdealQuotientGrading

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "ℬ" => ProjModelRingCR W.toProjective
set_option quotPrecheck false in
local notation "ℬ²" => KwLRBiRing W
set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
set_option quotPrecheck false in
local notation "mk₆" => Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal

theorem kw_lrSymChart_mkSym_mem_four (k : Fin 3) :
    mk₆ (kw_lrSym_vec W k) ∈ kw_lrComul_biGrading W 4 :=
  mk_mem_quotGradingSubmodule _ _
    ((mem_homogeneousSubmodule _ _).mpr (kw_lrSym_vec_isHomogeneous W k))

set_option quotPrecheck false in

local notation "𝒜" k => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X k : MvPolynomial (Fin 3) R))

set_option quotPrecheck false in

local notation "𝒜²ₛ" k => HomogeneousLocalization.Away (kw_lrComul_biGrading W)
  (Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrSym_vec W k))

theorem kw_lrSymChart_comulHom_mkX_pow (k : Fin 3) (n : ℕ) :
    kw_lrSym_comulHom W (mk₃ (X k : MvPolynomial (Fin 3) R) ^ n)
      = mk₆ (kw_lrSym_vec W k) ^ n := by
  rw [map_pow, kw_lrSym_comulHom_mk_X]

theorem kw_lrSymChart_powers_comap_le (k : Fin 3) :
    Submonoid.powers (mk₃ (X k : MvPolynomial (Fin 3) R))
      ≤ (Submonoid.powers (mk₆ (kw_lrSym_vec W k))).comap
          (kw_lrSym_comulHom W).toRingHom := by
  rintro a ⟨n, rfl⟩
  exact ⟨n, (kw_lrSymChart_comulHom_mkX_pow W k n).symm⟩

noncomputable def kw_lrSymChart_locMap (k : Fin 3) :
    Localization.Away (mk₃ (X k : MvPolynomial (Fin 3) R))
      →+* Localization.Away (mk₆ (kw_lrSym_vec W k)) :=
  IsLocalization.map _ (kw_lrSym_comulHom W).toRingHom (kw_lrSymChart_powers_comap_le W k)

noncomputable def kw_lrSymChart_aux (k : Fin 3) :
    (𝒜 k) →+* Localization.Away (mk₆ (kw_lrSym_vec W k)) :=
  (kw_lrSymChart_locMap W k).comp
    (algebraMap (𝒜 k) (Localization.Away (mk₃ (X k : MvPolynomial (Fin 3) R))))

theorem kw_lrSymChart_aux_mk (k : Fin 3) (n : ℕ) (a : ℬ)
    (ha : a ∈ projModelGradingCR W.toProjective (n • 1)) :
    kw_lrSymChart_aux W k
        (HomogeneousLocalization.Away.mk (projModelGradingCR W.toProjective)
          (kw_lrChart_mkX_mem_one W k) n a ha)
      = Localization.mk (kw_lrSym_comulHom W a)
          (⟨mk₆ (kw_lrSym_vec W k) ^ n, n, rfl⟩
            : Submonoid.powers (mk₆ (kw_lrSym_vec W k))) := by
  show kw_lrSymChart_locMap W k
      (HomogeneousLocalization.Away.mk _ (kw_lrChart_mkX_mem_one W k) n a ha).val = _
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', kw_lrSymChart_locMap,
    IsLocalization.map_mk', ← Localization.mk_eq_mk']
  congr 1
  exact Subtype.ext (kw_lrSymChart_comulHom_mkX_pow W k n)

noncomputable def kw_lrSymChart_witness (k : Fin 3) (n : ℕ) (a : ℬ)
    (ha : a ∈ projModelGradingCR W.toProjective (n • 1)) : (𝒜²ₛ k) :=
  HomogeneousLocalization.Away.mk (kw_lrComul_biGrading W)
    (kw_lrSymChart_mkSym_mem_four W k) n (kw_lrSym_comulHom W a)
    (by
      have ha' : a ∈ projModelGradingCR W.toProjective n := by simpa using ha
      have h4n : kw_lrSym_comulHom W a ∈ kw_lrComul_biGrading W (4 * n) :=
        kw_lrSym_comulHom_graded W ha'
      simpa [smul_eq_mul, Nat.mul_comm] using h4n)

theorem kw_lrSymChart_witness_val (k : Fin 3) (n : ℕ) (a : ℬ)
    (ha : a ∈ projModelGradingCR W.toProjective (n • 1)) :
    (kw_lrSymChart_witness W k n a ha).val
      = kw_lrSymChart_aux W k
          (HomogeneousLocalization.Away.mk (projModelGradingCR W.toProjective)
            (kw_lrChart_mkX_mem_one W k) n a ha) := by
  rw [kw_lrSymChart_aux_mk]; rfl

theorem kw_lrSymChart_aux_range_subset (k : Fin 3) :
    Set.range (kw_lrSymChart_aux W k)
      ⊆ Set.range (algebraMap (𝒜²ₛ k) (Localization.Away (mk₆ (kw_lrSym_vec W k)))) := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (projModelGradingCR W.toProjective) (kw_lrChart_mkX_mem_one W k) z
  exact ⟨kw_lrSymChart_witness W k n a ha,
    (HomogeneousLocalization.algebraMap_apply _).trans (kw_lrSymChart_witness_val W k n a ha)⟩

theorem kw_lrSymChart_aux_range_le (k : Fin 3) :
    (kw_lrSymChart_aux W k).range
      ≤ (algebraMap (𝒜²ₛ k) (Localization.Away (mk₆ (kw_lrSym_vec W k)))).range := by
  rintro _ ⟨z, rfl⟩
  exact kw_lrSymChart_aux_range_subset W k ⟨z, rfl⟩

noncomputable def kw_lrSymChart_away (k : Fin 3) : (𝒜 k) →+* (𝒜²ₛ k) := by
  let e := RingEquiv.ofLeftInverse
    (f := algebraMap (𝒜²ₛ k) (Localization.Away (mk₆ (kw_lrSym_vec W k))))
    (h := (HomogeneousLocalization.val_injective _).hasLeftInverse.choose_spec)
  exact RingHom.comp (e.symm.toRingHom.comp
      (Subring.inclusion (kw_lrSymChart_aux_range_le W k)))
    (kw_lrSymChart_aux W k).rangeRestrict

end WeierstrassProjModel

end
end MEGA_KwLRSymChartHomAway_lean

section MEGA_KwLRSymChartHomToTensor_lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

noncomputable section

open MvPolynomial WeierstrassCurve HomogeneousLocalization HomogeneousIdealQuotientGrading
open scoped TensorProduct

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "ℬ" => ProjModelRingCR W.toProjective
set_option quotPrecheck false in
local notation "mk₆" => Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))
set_option quotPrecheck false in
local notation "𝒜²ₛ" k => HomogeneousLocalization.Away (kw_lrComul_biGrading W)
  (Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrSym_vec W k))

section ToTensor

variable (i j k : Fin 3)

noncomputable def kw_lrSymChart_u : (𝒜 i) ⊗[R] (𝒜 j) :=
  kw_lrChart_ev' W i j (mk₆ (kw_lrSym_vec W k))

theorem kw_lrSymChart_powers_ev'_comap_le :
    Submonoid.powers (mk₆ (kw_lrSym_vec W k))
      ≤ (Submonoid.powers (kw_lrSymChart_u W i j k)).comap
          (kw_lrChart_ev' W i j).toRingHom := by
  rintro a ⟨n, rfl⟩
  exact ⟨n, by rw [map_pow]; rfl⟩

noncomputable def kw_lrSymChart_toTensorLoc :
    Localization.Away (mk₆ (kw_lrSym_vec W k))
      →+* Localization.Away (kw_lrSymChart_u W i j k) :=
  IsLocalization.map _ (kw_lrChart_ev' W i j).toRingHom
    (kw_lrSymChart_powers_ev'_comap_le W i j k)

noncomputable def kw_lrSymChart_toTensor :
    (𝒜²ₛ k) →+* Localization.Away (kw_lrSymChart_u W i j k) :=
  (kw_lrSymChart_toTensorLoc W i j k).comp
    (algebraMap (𝒜²ₛ k) (Localization.Away (mk₆ (kw_lrSym_vec W k))))

end ToTensor

section Composite

variable (i j k : Fin 3)

noncomputable def kw_lrSymChart_tensor :
    (𝒜 k) →+* Localization.Away (kw_lrSymChart_u W i j k) :=
  (kw_lrSymChart_toTensor W i j k).comp (kw_lrSymChart_away W k)

end Composite

end WeierstrassProjModel

end

end MEGA_KwLRSymChartHomToTensor_lean

section MEGA_KwLRSixUCoverage_lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

noncomputable section

open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

noncomputable def kw_lrSixU (i j : Fin 3) : Fin 3 ⊕ Fin 3 → (𝒜 i) ⊗[R] (𝒜 j) :=
  Sum.elim (kw_lrChart_u W i j) (kw_lrSymChart_u W i j)

def KwLRSixUCoverage : Prop :=
  ∀ (i j : Fin 3),
    Ideal.span (Set.range (kw_lrSixU W i j)) = (⊤ : Ideal ((𝒜 i) ⊗[R] (𝒜 j)))

end WeierstrassProjModel

end
end MEGA_KwLRSixUCoverage_lean

section MEGA_KwLRPerChartGlue_lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective

noncomputable def kw_lrSixU_cover (i j : Fin 3)
    (h : Ideal.span (Set.range (kw_lrSixU W i j)) = ⊤) :
    (Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j)))).AffineOpenCover :=
  Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of ((𝒜 i) ⊗[R] (𝒜 j))) (kw_lrSixU W i j) h

section ToE

variable (i j : Fin 3)

noncomputable def kw_lrSixU_toE :
    ∀ l : Fin 3 ⊕ Fin 3,
      Spec (CommRingCat.of (Localization.Away (kw_lrSixU W i j l))) ⟶ E
  | .inl k => Spec.map (CommRingCat.ofHom (kw_lrChart_tensor W i j k))
      ≫ Proj.awayι (projModelGradingCR W.toProjective) _ (kw_lrChart_mkX_mem_one W k) one_pos
  | .inr k => Spec.map (CommRingCat.ofHom (kw_lrSymChart_tensor W i j k))
      ≫ Proj.awayι (projModelGradingCR W.toProjective) _ (kw_lrChart_mkX_mem_one W k) one_pos

end ToE

noncomputable def kw_lrSixU_locMap (i j : Fin 3) (l : Fin 3 ⊕ Fin 3) :
    Spec (CommRingCat.of (Localization.Away (kw_lrSixU W i j l)))
      ⟶ Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j))) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (kw_lrSixU W i j l))))

def KwLRPerChartCompat : Prop :=
  ∀ (i j : Fin 3) (l l' : Fin 3 ⊕ Fin 3),
    pullback.fst (kw_lrSixU_locMap W i j l) (kw_lrSixU_locMap W i j l')
        ≫ kw_lrSixU_toE W i j l
      = pullback.snd (kw_lrSixU_locMap W i j l) (kw_lrSixU_locMap W i j l')
        ≫ kw_lrSixU_toE W i j l'

noncomputable def kw_lrPerChart_toE (hcov : KwLRSixUCoverage W)
    (hcompat : KwLRPerChartCompat W) (i j : Fin 3) :
    Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j))) ⟶ E :=
  (kw_lrSixU_cover W i j (hcov i j)).openCover.glueMorphisms
    (kw_lrSixU_toE W i j) (hcompat i j)

end WeierstrassProjModel

end
end MEGA_KwLRPerChartGlue_lean

section MEGA_KwProjPullbackAwayCoverCRCover_lean
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open HomogeneousLocalization HomogeneousIdealQuotientGrading
open scoped TensorProduct

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (R : Type u) [CommRing R]

section CoverCRPort

variable (V : WeierstrassCurve.Projective R)

open MvPolynomial in

theorem kw_pbac_mk_X_mem_one_CR (i : Fin 3) :
    Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X i : MvPolynomial (Fin 3) R)
      ∈ projModelGradingCR V 1 :=
  mk_mem_quotGradingSubmodule _ _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i))

theorem kw_pbac_ambient_irrelevant_le_span_X_CR :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 3) R)).toIdeal
      ≤ Ideal.span (Set.range (X : Fin 3 → MvPolynomial (Fin 3) R)) := by
  classical
  intro p hp
  rw [HomogeneousIdeal.toIdeal_irrelevant, RingHom.mem_ker] at hp
  have hzero : (DirectSum.decompose (homogeneousSubmodule (Fin 3) R) p 0
      : MvPolynomial (Fin 3) R) = 0 := by
    rw [← GradedRing.projZeroRingHom_apply]; exact hp
  have hc0 : MvPolynomial.coeff 0 p = 0 := by
    conv_lhs => rw [← DirectSum.sum_support_decompose (homogeneousSubmodule (Fin 3) R) p]
    rw [MvPolynomial.coeff_sum]
    refine Finset.sum_eq_zero fun n _ => ?_
    by_cases h0 : n = 0
    · rw [h0, hzero, MvPolynomial.coeff_zero]
    · have hmem : ((DirectSum.decompose (homogeneousSubmodule (Fin 3) R) p n
          : MvPolynomial (Fin 3) R)).IsHomogeneous n :=
        (MvPolynomial.mem_homogeneousSubmodule _ _).mp (SetLike.coe_mem _)
      exact hmem.coeff_eq_zero (by simpa using Ne.symm h0)
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hmne : m ≠ 0 := by rintro rfl; exact (MvPolynomial.mem_support_iff.mp hm) hc0
  obtain ⟨l, hl⟩ := Finsupp.ne_iff.mp hmne
  exact ⟨l, Set.mem_univ l, by simpa using hl⟩

theorem kw_pbac_irrelevant_le_span_mk_X_CR :
    (HomogeneousIdeal.irrelevant (projModelGradingCR V)).toIdeal
      ≤ Ideal.span (Set.range fun i : Fin 3 =>
          Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
            (X i : MvPolynomial (Fin 3) R)) := by
  intro z hz
  rw [HomogeneousIdeal.toIdeal_irrelevant, RingHom.mem_ker,
    GradedRing.projZeroRingHom_apply] at hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [decompose_quotGradingSubmodule_mk_apply (homogeneousSubmodule (Fin 3) R)
      (projModelHomogeneousIdealCR V) p 0] at hz
  have hrewrite : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal p
      = Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
          (p - (DirectSum.decompose (homogeneousSubmodule (Fin 3) R) p 0
            : MvPolynomial (Fin 3) R)) := by
    rw [map_sub, hz, sub_zero]
  rw [hrewrite]
  have hirr : (p - (DirectSum.decompose (homogeneousSubmodule (Fin 3) R) p 0
        : MvPolynomial (Fin 3) R))
      ∈ (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 3) R)).toIdeal := by
    rw [HomogeneousIdeal.toIdeal_irrelevant, RingHom.mem_ker,
      GradedRing.projZeroRingHom_apply, DirectSum.decompose_sub,
      DirectSum.decompose_coe, DirectSum.sub_apply, DirectSum.of_eq_same,
      AddSubgroupClass.coe_sub, sub_self]
  have hmem := kw_pbac_ambient_irrelevant_le_span_X_CR R hirr
  have hmap : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (p - (DirectSum.decompose (homogeneousSubmodule (Fin 3) R) p 0
          : MvPolynomial (Fin 3) R))
      ∈ Ideal.map (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal)
          (Ideal.span (Set.range (X : Fin 3 → MvPolynomial (Fin 3) R))) :=
    Ideal.mem_map_of_mem _ hmem
  rwa [Ideal.map_span, ← Set.range_comp] at hmap

noncomputable def projModelAffineOpenCoverCR :
    Scheme.AffineOpenCover (projModelCR V) :=
  Proj.affineOpenCoverOfIrrelevantLESpan (projModelGradingCR V)
    (fun i : Fin 3 =>
      Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))
    (m := fun _ => 1)
    (fun i => kw_pbac_mk_X_mem_one_CR R V i) (fun _ => Nat.one_pos)
    (kw_pbac_irrelevant_le_span_mk_X_CR R V)

end CoverCRPort

section ChartStructureMap

variable (V : WeierstrassCurve.Projective R)

set_option quotPrecheck false in

local notation "𝒜" i =>
  HomogeneousLocalization.Away (projModelGradingCR V)
    (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))

attribute [local instance] kw_pbac_awayAlgebra

theorem kw_pbac_awayι_comp_projModelStrCR (i : Fin 3) :
    Proj.awayι (projModelGradingCR V) _ (kw_pbac_mk_X_mem_one_CR R V i) one_pos
        ≫ projModelStrCR V
      = Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 i))) := by
  unfold projModelStrCR
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

end ChartStructureMap

section PullbackCover

variable (V : WeierstrassCurve.Projective R)

noncomputable def kwProjPullbackOpenCoverCR :
    (pullback (projModelStrCR V) (projModelStrCR V)).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight
    (projModelAffineOpenCoverCR R V).openCover
    (projModelAffineOpenCoverCR R V).openCover
    (projModelStrCR V) (projModelStrCR V)

end PullbackCover

section ChartIso

variable (V : WeierstrassCurve.Projective R)

set_option quotPrecheck false in

local notation "𝒜" i =>
  HomogeneousLocalization.Away (projModelGradingCR V)
    (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))

attribute [local instance] kw_pbac_awayAlgebra

noncomputable def kwProjPullbackChartIsoCR (i j : Fin 3) :
    (kwProjPullbackOpenCoverCR R V).X (i, j)
      ≅ Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j))) :=
  pullback.congrHom (kw_pbac_awayι_comp_projModelStrCR R V i)
      (kw_pbac_awayι_comp_projModelStrCR R V j)
    ≪≫ pullbackSpecIso R (𝒜 i) (𝒜 j)

end ChartIso

end WeierstrassProjModel

end

end MEGA_KwProjPullbackAwayCoverCRCover_lean

section MEGA_KwLROuterGlue_lean
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective

noncomputable def kw_lrOuter_toE (hcov : KwLRSixUCoverage W)
    (hcompat : KwLRPerChartCompat W) :
    ∀ ij, (kwProjPullbackOpenCoverCR R W.toProjective).X ij ⟶ E :=
  fun ij => (kwProjPullbackChartIsoCR R W.toProjective ij.1 ij.2).hom
            ≫ kw_lrPerChart_toE W hcov hcompat ij.1 ij.2

def KwLROuterCompat : Prop :=
  ∀ (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W)
    (ij ij' : Fin 3 × Fin 3),
    pullback.fst ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
                 ((kwProjPullbackOpenCoverCR R W.toProjective).f ij')
        ≫ kw_lrOuter_toE W hcov hcompat ij
      = pullback.snd ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
                     ((kwProjPullbackOpenCoverCR R W.toProjective).f ij')
        ≫ kw_lrOuter_toE W hcov hcompat ij'

noncomputable def kw_lrAddMorphism (hcov : KwLRSixUCoverage W)
    (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W) :
    pullback (projModelStrCR W.toProjective) (projModelStrCR W.toProjective) ⟶ E :=
  (kwProjPullbackOpenCoverCR R W.toProjective).glueMorphisms
    (kw_lrOuter_toE W hcov hcompat) (houter hcov hcompat)

end WeierstrassProjModel

end
end MEGA_KwLROuterGlue_lean

section MEGA_KwLRAddNegDiagZeroNegMor_lean
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial WeierstrassCurve HomogeneousLocalization HomogeneousIdealQuotientGrading
open scoped TensorProduct

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))
set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective
set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective
set_option quotPrecheck false in
local notation "ℬ" => ProjModelRingCR W.toProjective
set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal

section NegMor

def kw_lrAddNegDiag_negSubstGen : Fin 3 → MvPolynomial (Fin 3) R :=
  ![X 0, -X 1 - C W.a₁ * X 0 - C W.a₃ * X 2, X 2]

def kw_lrAddNegDiag_negSubst : MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 3) R :=
  aeval (kw_lrAddNegDiag_negSubstGen W)

local notation "negSubst" => kw_lrAddNegDiag_negSubst W

theorem kw_lrAddNegDiag_negSubstGen_isHomogeneous (m : Fin 3) :
    (kw_lrAddNegDiag_negSubstGen W m).IsHomogeneous 1 := by
  fin_cases m
  · exact isHomogeneous_X R 0
  · refine ((((isHomogeneous_X R 1).neg).sub ?_).sub ?_)
    · exact (isHomogeneous_C _ W.a₁).mul (isHomogeneous_X R 0)
    · exact (isHomogeneous_C _ W.a₃).mul (isHomogeneous_X R 2)
  · exact isHomogeneous_X R 2

theorem kw_lrAddNegDiag_negSubst_isHomogeneous {p : MvPolynomial (Fin 3) R} {n : ℕ}
    (hp : p.IsHomogeneous n) : (negSubst p).IsHomogeneous n := by
  have key : (aeval (kw_lrAddNegDiag_negSubstGen W) p).IsHomogeneous (1 * n) :=
    hp.aeval _ (kw_lrAddNegDiag_negSubstGen_isHomogeneous W)
  simpa [kw_lrAddNegDiag_negSubst, one_mul] using key

theorem kw_lrAddNegDiag_negSubst_polynomial :
    negSubst W.toProjective.polynomial = W.toProjective.polynomial := by
  simp only [kw_lrAddNegDiag_negSubst, WeierstrassCurve.Projective.polynomial,
    WeierstrassCurve.toProjective, map_sub, map_add, map_mul, map_pow, aeval_C, aeval_X,
    kw_lrAddNegDiag_negSubstGen, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, MvPolynomial.algebraMap_eq]
  ring

theorem kw_lrAddNegDiag_negSubst_mapSpan :
    Ideal.map (negSubst : MvPolynomial (Fin 3) R →+* _)
        (Ideal.span {W.toProjective.polynomial})
      = Ideal.span {W.toProjective.polynomial} := by
  rw [Ideal.map_span, Set.image_singleton]
  exact congrArg (Ideal.span {·}) (kw_lrAddNegDiag_negSubst_polynomial W)

def kw_lrAddNegDiag_negQuotHom : ℬ →+* ℬ :=
  Ideal.Quotient.lift (projModelHomogeneousIdealCR W.toProjective).toIdeal
    ((Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal).comp
      (negSubst : MvPolynomial (Fin 3) R →+* _))
    (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr
      ((Ideal.map_le_iff_le_comap.mp (kw_lrAddNegDiag_negSubst_mapSpan W).le)
        (projModelHomogeneousIdealCR_toIdeal W.toProjective ▸ ha)))

def kw_lrAddNegDiag_negGradedHom :
    projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR W.toProjective where
  toRingHom := kw_lrAddNegDiag_negQuotHom W
  map_mem {i x} hx := by
    obtain ⟨a, ha, rfl⟩ := (mem_quotGradingSubmodule_iff _ _).mp hx
    exact mk_mem_quotGradingSubmodule _ _
      ((mem_homogeneousSubmodule _ _).mpr
        (kw_lrAddNegDiag_negSubst_isHomogeneous W
          ((mem_homogeneousSubmodule _ _).mp ha)))

local notation "negGradedHom" => kw_lrAddNegDiag_negGradedHom W

set_option linter.unnecessarySeqFocus false in

theorem kw_lrAddNegDiag_negSubst_comp_self :
    (negSubst).comp negSubst = AlgHom.id R (MvPolynomial (Fin 3) R) := by
  refine MvPolynomial.algHom_ext fun m => ?_
  fin_cases m <;>
    simp [kw_lrAddNegDiag_negSubst, kw_lrAddNegDiag_negSubstGen,
      map_sub, map_neg, map_mul] <;>
    ring

theorem kw_lrAddNegDiag_negGradedHom_comp_self :
    (negGradedHom : ℬ →+* ℬ).comp negGradedHom = RingHom.id ℬ := by
  refine Ideal.Quotient.ringHom_ext ?_
  exact RingHom.ext fun a => congrArg mk₃
    (DFunLike.congr_fun (kw_lrAddNegDiag_negSubst_comp_self W) a)

theorem kw_lrAddNegDiag_negGradedHom_map_proj (n : ℕ) (x : ℬ) :
    GradedRing.proj (projModelGradingCR W.toProjective) n (negGradedHom x)
      = negGradedHom (GradedRing.proj (projModelGradingCR W.toProjective) n x) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose (projModelGradingCR W.toProjective) x]
  conv_rhs => rw [← DirectSum.sum_support_decompose (projModelGradingCR W.toProjective) x]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hy : (↑((DirectSum.decompose (projModelGradingCR W.toProjective) x) m) : ℬ)
      ∈ projModelGradingCR W.toProjective m := SetLike.coe_mem _
  have hfy : negGradedHom
        (↑((DirectSum.decompose (projModelGradingCR W.toProjective) x) m) : ℬ)
      ∈ projModelGradingCR W.toProjective m := (negGradedHom).map_mem hy
  rcases eq_or_ne m n with h | h
  · subst h
    rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same _ hfy,
      GradedRing.proj_apply, DirectSum.decompose_of_mem_same _ hy]
  · rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne _ hfy h,
      GradedRing.proj_apply, DirectSum.decompose_of_mem_ne _ hy h, map_zero]

theorem kw_lrAddNegDiag_negGradedHom_irrelevant_le :
    HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)
      ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map
          negGradedHom := by
  intro x hx
  have heq : x = negGradedHom (negGradedHom x) :=
    (RingHom.congr_fun (kw_lrAddNegDiag_negGradedHom_comp_self W) x).symm
  rw [heq]
  refine Ideal.mem_map_of_mem _ ?_
  show negGradedHom x ∈ HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)
  rw [HomogeneousIdeal.mem_irrelevant_iff] at hx ⊢
  rw [kw_lrAddNegDiag_negGradedHom_map_proj W 0 x, hx, map_zero]

def kw_lrAddNegDiag_negMor : E ⟶ E :=
  Proj.map negGradedHom (kw_lrAddNegDiag_negGradedHom_irrelevant_le W)

local notation "negMor" => kw_lrAddNegDiag_negMor W

end NegMor

section GeneralNaturality

variable {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒢 : ℕ → σ} [GradedRing 𝒢]

end GeneralNaturality

section NegMor2

local notation "negGradedHom" => kw_lrAddNegDiag_negGradedHom W
local notation "negMor" => kw_lrAddNegDiag_negMor W
local notation "negSubst" => kw_lrAddNegDiag_negSubst W

end NegMor2

section PolyIdentity

noncomputable def kw_lrAddNegDiag_evalNeg :
    MvPolynomial (Fin 3 ⊕ Fin 3) R →ₐ[R] MvPolynomial (Fin 3) R :=
  aeval (Sum.elim (kw_lrAddNegDiag_negSubstGen W) X)

set_option quotPrecheck false in
local notation "evalNeg" => kw_lrAddNegDiag_evalNeg W

macro "simp_evalNeg" : tactic =>
  `(tactic| simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one,
    kw_lrAddNegDiag_evalNeg_C, kw_lrAddNegDiag_evalNeg_inr,
    kw_lrAddNegDiag_evalNeg_inl, kw_lrAddNegDiag_negSubstGen,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons])

end PolyIdentity

end WeierstrassProjModel

end

end MEGA_KwLRAddNegDiagZeroNegMor_lean

section MEGA_KwProjWeierstrassRelGroupLawConstruct_lean
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve

universe u

namespace WeierstrassProjModel

open WeierstrassProjModel NeronModelInfra HomogeneousIdealQuotientGrading

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R]

section ZeroSection

variable (W : WeierstrassCurve R)

open MvPolynomial in

theorem kw_mk_X1_mem_one_CR :
    Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
        (X 1 : MvPolynomial (Fin 3) R)
      ∈ projModelGradingCR W.toProjective 1 :=
  mk_mem_quotGradingSubmodule _ _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R 1))

open MvPolynomial in

def kwYEvalRingHom : ProjModelRingCR W.toProjective →+* R :=
  Ideal.Quotient.lift _ (MvPolynomial.eval ![(0 : R), 1, 0]) fun a ha => by
    refine (Ideal.span_le.mpr ?_ : Ideal.span _ ≤ RingHom.ker _)
      (projModelHomogeneousIdealCR_toIdeal W.toProjective ▸ ha)
    simp only [Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]

    exact WeierstrassCurve.Projective.equation_zero

open MvPolynomial in

theorem kwYEvalRingHom_mk_X1 :
    kwYEvalRingHom R W (Ideal.Quotient.mk _ (X 1 : MvPolynomial (Fin 3) R)) = 1 := by
  show (MvPolynomial.eval ![(0 : R), 1, 0]) (X 1) = 1
  simp

def kwYChartEval :
    HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
      (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)) →+* R :=
  (IsLocalization.Away.lift (g := kwYEvalRingHom R W)
      (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R))
      (kwYEvalRingHom_mk_X1 R W ▸ isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)))
      (Localization.Away
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X 1 : MvPolynomial (Fin 3) R))))

open MvPolynomial in

theorem kwYEvalRingHom_comp_algebraMap :
    (kwYEvalRingHom R W).comp (algebraMap R (ProjModelRingCR W.toProjective)) = RingHom.id R :=
  RingHom.ext fun r => by
    show (MvPolynomial.eval ![(0 : R), 1, 0]) (C r) = r
    exact MvPolynomial.eval_C _

theorem kwYChartEval_section :
    (kwYChartEval R W).comp
      ((HomogeneousLocalization.fromZeroRingHom (projModelGradingCR W.toProjective) _).comp
        (algebraMap R (projModelGradingCR W.toProjective 0))) = RingHom.id R := by

  refine RingHom.ext fun r => ?_
  simp only [RingHom.comp_apply, RingHom.id_apply, kwYChartEval,
    HomogeneousLocalization.algebraMap_apply]

  have hval :
      (HomogeneousLocalization.fromZeroRingHom (projModelGradingCR W.toProjective) _
          (algebraMap R (projModelGradingCR W.toProjective 0) r)).val
        = algebraMap (ProjModelRingCR W.toProjective)
            (Localization.Away
              (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)))
            (algebraMap R (ProjModelRingCR W.toProjective) r) := by

    rfl
  rw [hval, IsLocalization.Away.lift, IsLocalization.lift_eq]
  exact RingHom.congr_fun (kwYEvalRingHom_comp_algebraMap R W) r

def kwZeroSect : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) (projModelStrCR W.toProjective) :=
  ⟨Spec.map (CommRingCat.ofHom (kwYChartEval R W)) ≫
    Proj.awayι (projModelGradingCR W.toProjective) _ (kw_mk_X1_mem_one_CR R W) one_pos,
   by
    simp only [projModelStrCR, Category.assoc]
    rw [← Category.assoc (Proj.awayι ..), Proj.awayι_toSpecZero, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      kwYChartEval_section, CommRingCat.ofHom_id, Spec.map_id]⟩

end ZeroSection

section AddLawData

variable (W : WeierstrassCurve R)

local notation "E" => projModelCR W.toProjective
local notation "π" => projModelStrCR W.toProjective

end AddLawData

section Assembly

end Assembly

end WeierstrassProjModel

end
end MEGA_KwProjWeierstrassRelGroupLawConstruct_lean

section MEGA_KwLRAffinePtTorsionBridge_lean

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve

namespace WeierstrassProjModel

open WeierstrassProjModel NeronModelInfra

attribute [local instance] Classical.propDecidable

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Bridge

variable (F : Type u) [Field F] [Algebra R F]

abbrev kw_lrAptb_tF : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R F))

section Engine

end Engine

end Bridge

end WeierstrassProjModel

end

end MEGA_KwLRAffinePtTorsionBridge_lean

section MEGA_KwLRAffinePtSetEquiv_lean
set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve MvPolynomial
open HomogeneousLocalization HomogeneousIdealQuotientGrading
open scoped WeierstrassCurve.Projective

namespace WeierstrassProjModel

open WeierstrassProjModel NeronModelInfra

attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (F : Type u) [Field F] [Algebra R F]

set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (mk₃ (X i : MvPolynomial (Fin 3) R))
set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective
set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective
set_option quotPrecheck false in
local notation "coverE" => (projModelAffineOpenCoverCR R W.toProjective).openCover
set_option quotPrecheck false in
local notation "gen" => kw_lrChart_gen W
set_option quotPrecheck false in
local notation "dehom" => kw_lrChart_dehom W
set_option quotPrecheck false in
local notation "t_F" => kw_lrAptb_tF (R := R) F

set_option quotPrecheck false in
local notation "awayι₃" i => Proj.awayι (projModelGradingCR W.toProjective)
  (mk₃ (X i : MvPolynomial (Fin 3) R)) (kw_pbac_mk_X_mem_one_CR R W.toProjective i) one_pos

abbrev kw_lrApt_WF : WeierstrassCurve.Projective F := (W.baseChange F).toProjective

set_option quotPrecheck false in
local notation "W_F" => kw_lrApt_WF W F

section ChartClassification

def kw_lrApt_chartEval (i : Fin 3) (ψ : (𝒜 i) →ₐ[R] F) : Fin 3 → F :=
  fun k => ψ (gen i k)

end ChartClassification

section ChartFactorization

end ChartFactorization

section Forward

end Forward

section Nonsingular

variable {F}

end Nonsingular

section Inverse

end Inverse

section Assembly

end Assembly

end WeierstrassProjModel

end
end MEGA_KwLRAffinePtSetEquiv_lean


