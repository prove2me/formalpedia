-- Prove2me | Definitions.Def_WeierstrassCurve_ProjModel_ThirdLawCharts
-- name    : WeierstrassCurve_ProjModel_ThirdLawCharts
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/bf02f931-0e93-56ce-a998-ec86d5f3e768
-- title:
--   Chart data for the third Weierstrass addition law
-- statement:
--   Throughout, $R$ is a commutative ring and $W$ a Weierstrass curve over $R$, with projective cubic $F = W.toProjective.polynomial$ in $R[X_0,X_1,X_2]$; $P_6 = R[X_{\mathrm{inl}\,k}, X_{\mathrm{inr}\,k}]$ carries the two copies $WP_1, WP_2$ of $F$ in the left and right triples of variables. The triple $(T_X,T_Y,T_Z) = (\mathtt{kw\_lrThird\_X}, \mathtt{kw\_lrThird\_Y}, \mathtt{kw\_lrThird\_Z})$ of bihomogeneous forms of degree $4$, bidegree $(2,2)$ in each factor, is assembled into the vector `kw_lrThird_vec`, shown to be homogeneous of degree $4$ componentwise, and into the substitution algebra map `kw_lrThird_substHom` $= \operatorname{aeval}(T)$, which sends forms homogeneous of degree $n$ to forms homogeneous of degree $4n$.
--
--   The arithmetic input is that $F(T_X,T_Y,T_Z)$ lies in the ideal $(WP_1, WP_2)$. This is obtained by first proving a scaled version: if $l\,T_k - m\,A_k$ lies in $(WP_1,WP_2)$ for each of the three coordinates of the chord addition law $A = (\mathtt{kw\_lrAdd\_X}, \mathtt{kw\_lrAdd\_Y}, \mathtt{kw\_lrAdd\_Z})$, then $l^3 F(T) \in (WP_1,WP_2)$; applying this with $l = A_Z$, $m = T_Z$ using the two cross-ratio minors, and cancelling $A_Z^3$ in the quotient by $(WP_1,WP_2)$ for the universal curve over $\mathbb{Z}[a_1,\dots,a_6]$ (a domain in which $A_Z$ is nonzero), gives the universal case; base change along the ring map sending the universal coefficients to $a_1,\dots,a_6$ of $W$, for which the auxiliary lemmas `kw_lrThirdOC_map_X`, `kw_lrThirdOC_map_Y`, `kw_lrThirdOC_map_Z` and `kw_lrThirdOC_map_W` record the compatibility of $T$ and of $F(T)$ with coefficient maps $f : R \to S$, yields `kw_lrThirdCharts_onCurve_mem_span` over an arbitrary base.
--
--   Consequently $\operatorname{aeval}(T)$ descends to an $R$-algebra map $\mathtt{kw\_lrThird\_comulHom} : \mathcal{B} \to \mathcal{B}^{(2)}$ from $R[X_0,X_1,X_2]/(F)$ to $P_6/(WP_1,WP_2)$, computed on classes of polynomials and of the variables, and carrying the $n$-th graded piece into the $4n$-th piece of the bigraded quotient. The remaining definitions dehomogenise this. For each $k$, the class $\mathtt{mk}_6(T_k)$ lies in degree $4$, so the powers of $\mathtt{mk}_3(X_k)$ map into the powers of $\mathtt{mk}_6(T_k)$; localising gives `kw_lrThirdChart_locMap` and then `kw_lrThirdChart_aux`, a ring map from the degree-zero homogeneous localisation $\mathcal{A}_k$ of $\mathcal{B}$ at $X_k$ into the full localisation of $\mathcal{B}^{(2)}$ away from $T_k$. Explicit witnesses (`kw_lrThirdChart_witness`, with its value computed by `kw_lrThirdChart_witness_val`) show the image of this map lies in the image of the homogeneous localisation $\mathcal{A}^{2}_{T,k}$ of $\mathcal{B}^{(2)}$ away from $T_k$, whence `kw_lrThirdChart_away` $: \mathcal{A}_k \to \mathcal{A}^{2}_{T,k}$, defined by inverting the injective map to values. Finally, for chart indices $i,j$ and $k$, $\mathtt{kw\_lrThirdChart\_u}\,W\,i\,j\,k$ is the image of $\mathtt{mk}_6(T_k)$ under the evaluation map `kw_lrChart_ev'` into $\mathcal{A}_i \otimes_R \mathcal{A}_j$, and composing `kw_lrThirdChart_away` with the induced localisation map gives $\mathtt{kw\_lrThirdChart\_tensor} : \mathcal{A}_k \to (\mathcal{A}_i \otimes_R \mathcal{A}_j)[1/u]$. Taking $\mathrm{Spec}$ of this and following it with the open immersion $\mathtt{Proj.awayι}$ of the chart $D_+(X_k)$ yields the morphism $\mathtt{kw\_lrThird\_toE₃}\,W\,i\,j\,k$ from $\mathrm{Spec}$ of that localisation to the projective model $\mathrm{Proj}$ of $W$; the triple of the $u$'s is packaged as `kw_lrThird_u₃`.
--
--   **Relation to Mathlib.** Mathlib supplies the projective Weierstrass cubic, `Proj` of a graded ring, homogeneous localisations and `Proj.awayι`; the addition-law forms, their comultiplication on the homogeneous coordinate ring of the cubic, and the resulting chart morphisms are the project's own.
--
--   **Where it is used.** These charts provide the witnesses for covering the product of the projective model with itself by affine pieces on which a given addition law has invertible coordinates, which is how the relative group law on the projective Weierstrass model over an arbitrary base is assembled; the third law supplements the chord law on the locus where the latter degenerates, in particular along the diagonal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_ProjModel_ThirdLawCharts.lean

import Definitions.Def_WeierstrassCurve_ProjModel_ThirdAddFormulas
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false

section MEGA_KwLRThirdOnCurve_lean
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

noncomputable section

open MvPolynomial WeierstrassCurve

namespace WeierstrassProjModel

universe u v

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

local notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R
local notation "WP₁" => kw_lrAdd_WP₁ W
local notation "WP₂" => kw_lrAdd_WP₂ W

section Map

variable {S : Type v} [CommRing S] (f : R →+* S)

theorem kw_lrThirdOC_map_X :
    MvPolynomial.map f (kw_lrThird_X W) = kw_lrThird_X (W.map f) := by
  simp only [kw_lrThird_X, map_add, map_mul, map_neg, map_pow, MvPolynomial.map_C,
    MvPolynomial.map_X, map_ofNat, map_one, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_sub]

theorem kw_lrThirdOC_map_Y :
    MvPolynomial.map f (kw_lrThird_Y W) = kw_lrThird_Y (W.map f) := by
  simp only [kw_lrThird_Y, map_add, map_mul, map_neg, map_pow, MvPolynomial.map_C,
    MvPolynomial.map_X, map_ofNat, map_one, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_sub]

theorem kw_lrThirdOC_map_Z :
    MvPolynomial.map f (kw_lrThird_Z W) = kw_lrThird_Z (W.map f) := by
  simp only [kw_lrThird_Z, map_add, map_mul, map_neg, map_pow, MvPolynomial.map_C,
    MvPolynomial.map_X, map_ofNat, map_one, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_sub]

theorem kw_lrThirdOC_map_W :
    MvPolynomial.map f
        (aeval ![kw_lrThird_X W, kw_lrThird_Y W, kw_lrThird_Z W] W.toProjective.polynomial)
      = aeval ![kw_lrThird_X (W.map f), kw_lrThird_Y (W.map f), kw_lrThird_Z (W.map f)]
          (W.map f).toProjective.polynomial := by
  simp only [WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, MvPolynomial.map_C, MvPolynomial.algebraMap_eq,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    kw_lrThirdOC_map_X, kw_lrThirdOC_map_Y, kw_lrThirdOC_map_Z]

end Map

theorem kw_lrThirdOC_scaled_mem_span_of (l m : P₆)
    (hX : l * kw_lrThird_X W - m * kw_lrAdd_X W ∈ Ideal.span {WP₁, WP₂})
    (hY : l * kw_lrThird_Y W - m * kw_lrAdd_Y W ∈ Ideal.span {WP₁, WP₂})
    (hZ : l * kw_lrThird_Z W - m * kw_lrAdd_Z W ∈ Ideal.span {WP₁, WP₂}) :
    l^3 * aeval ![kw_lrThird_X W, kw_lrThird_Y W, kw_lrThird_Z W]
          W.toProjective.polynomial
      ∈ Ideal.span {WP₁, WP₂} := by
  have hdiff : l^3 * aeval ![kw_lrThird_X W, kw_lrThird_Y W, kw_lrThird_Z W]
        W.toProjective.polynomial
      - m^3 * aeval ![kw_lrAdd_X W, kw_lrAdd_Y W, kw_lrAdd_Z W]
        W.toProjective.polynomial ∈ Ideal.span {WP₁, WP₂} := by
    rw [← kw_lrSymOC_aeval_scale W l, ← kw_lrSymOC_aeval_scale W m,
        kw_lrSymOC_aeval_diff W
          (l * kw_lrThird_X W) (m * kw_lrAdd_X W)
          (l * kw_lrThird_Y W) (m * kw_lrAdd_Y W)
          (l * kw_lrThird_Z W) (m * kw_lrAdd_Z W)]
    exact add_mem (add_mem (Ideal.mul_mem_right _ _ hX) (Ideal.mul_mem_right _ _ hY))
      (Ideal.mul_mem_right _ _ hZ)
  have hAdd : m^3 * aeval ![kw_lrAdd_X W, kw_lrAdd_Y W, kw_lrAdd_Z W]
        W.toProjective.polynomial ∈ Ideal.span {WP₁, WP₂} :=
    Ideal.mul_mem_left _ _ (kw_lrAdd_onCurve_mem_span W)
  have := add_mem hdiff hAdd
  simpa using this

theorem kw_lrThirdOC_scaled_mem_span_Z :
    (kw_lrAdd_Z W)^3 * aeval ![kw_lrThird_X W, kw_lrThird_Y W, kw_lrThird_Z W]
          W.toProjective.polynomial
      ∈ Ideal.span {WP₁, WP₂} := by
  refine kw_lrThirdOC_scaled_mem_span_of W (kw_lrAdd_Z W) (kw_lrThird_Z W) ?_ ?_ ?_
  · have := kw_lrThird_minor_XZ_mem_span W
    rwa [show kw_lrThird_X W * kw_lrAdd_Z W - kw_lrThird_Z W * kw_lrAdd_X W
        = kw_lrAdd_Z W * kw_lrThird_X W - kw_lrThird_Z W * kw_lrAdd_X W from by ring] at this
  · have := kw_lrThird_minor_YZ_mem_span W
    rwa [show kw_lrThird_Y W * kw_lrAdd_Z W - kw_lrThird_Z W * kw_lrAdd_Y W
        = kw_lrAdd_Z W * kw_lrThird_Y W - kw_lrThird_Z W * kw_lrAdd_Y W from by ring] at this
  · rw [mul_comm, sub_self]; exact Ideal.zero_mem _

local notation "R₀" => MvPolynomial (Fin 5) ℤ
local notation "W₀" => kw_lrSymOC_W₀
local notation "P₆₀" => MvPolynomial (Fin 3 ⊕ Fin 3) R₀
local notation "WP₁₀" => kw_lrAdd_WP₁ W₀
local notation "WP₂₀" => kw_lrAdd_WP₂ W₀

theorem kw_lrThirdOC_univ_mem_span :
    aeval ![kw_lrThird_X W₀, kw_lrThird_Y W₀, kw_lrThird_Z W₀]
        kw_lrSymOC_W₀.toProjective.polynomial
      ∈ Ideal.span {WP₁₀, WP₂₀} := by
  haveI := kw_lrSymOC_isDomain_quotSpanPair
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hscaled := kw_lrThirdOC_scaled_mem_span_Z W₀
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow] at hscaled
  have hZne : (Ideal.Quotient.mk (Ideal.span {WP₁₀, WP₂₀})) (kw_lrAdd_Z W₀) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact kw_lrSymOC_lrAddZ_notMem_span
  exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero 3 hZne)

theorem kw_lrThirdCharts_onCurve_mem_span :
    aeval ![kw_lrThird_X W, kw_lrThird_Y W, kw_lrThird_Z W]
        W.toProjective.polynomial
      ∈ Ideal.span {kw_lrAdd_WP₁ W, kw_lrAdd_WP₂ W} := by
  let φ : R₀ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
  have hW : kw_lrSymOC_W₀.map φ = W := kw_lrSymOC_W₀_map W
  have hmem := Ideal.mem_map_of_mem
    (MvPolynomial.map φ : P₆₀ →+* MvPolynomial (Fin 3 ⊕ Fin 3) R)
    kw_lrThirdOC_univ_mem_span
  rw [Ideal.map_span, Set.image_pair, kw_lrSymOC_map_WP₁, kw_lrSymOC_map_WP₂,
    hW] at hmem
  have hrw := kw_lrThirdOC_map_W kw_lrSymOC_W₀ φ
  rw [hW] at hrw
  rw [← hrw]
  exact hmem

end WeierstrassProjModel

end

end MEGA_KwLRThirdOnCurve_lean

section MEGA_KwLRThirdQuotientGradedHom_lean
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

def kw_lrThird_vec : Fin 3 → P₆ := ![kw_lrThird_X W, kw_lrThird_Y W, kw_lrThird_Z W]

theorem kw_lrThird_vec_isHomogeneous (k : Fin 3) : (kw_lrThird_vec W k).IsHomogeneous 4 := by
  fin_cases k
  · exact kw_lrThird_X_isHomogeneous W
  · exact kw_lrThird_Y_isHomogeneous W
  · exact kw_lrThird_Z_isHomogeneous W

def kw_lrThird_substHom : MvPolynomial (Fin 3) R →ₐ[R] P₆ := aeval (kw_lrThird_vec W)

@[simp]
theorem kw_lrThird_substHom_X (k : Fin 3) :
    kw_lrThird_substHom W (X k) = kw_lrThird_vec W k := aeval_X _ _

theorem kw_lrThird_substHom_isHomogeneous {p : MvPolynomial (Fin 3) R} {n : ℕ}
    (hp : p.IsHomogeneous n) : (kw_lrThird_substHom W p).IsHomogeneous (4 * n) :=
  hp.aeval (kw_lrThird_vec W) (kw_lrThird_vec_isHomogeneous W)

theorem kw_lrThird_substHom_polynomial_mem :
    kw_lrThird_substHom W W.toProjective.polynomial ∈ (kw_lrComul_biIdeal W).toIdeal := by
  exact kw_lrThirdCharts_onCurve_mem_span W

noncomputable def kw_lrThird_comulHom : (ℬ) →ₐ[R] (ℬ²) :=
  Ideal.Quotient.liftₐ (projModelHomogeneousIdealCR W.toProjective).toIdeal
    ((Ideal.Quotient.mkₐ R (kw_lrComul_biIdeal W).toIdeal).comp (kw_lrThird_substHom W))
    (fun a ha => by
      refine (Ideal.Quotient.eq_zero_iff_mem).mpr ?_
      have hle : Ideal.span {W.toProjective.polynomial}
          ≤ (kw_lrComul_biIdeal W).toIdeal.comap (kw_lrThird_substHom W).toRingHom :=
        Ideal.span_le.mpr
          (Set.singleton_subset_iff.mpr (kw_lrThird_substHom_polynomial_mem W))
      exact hle ha)

theorem kw_lrThird_comulHom_mk (a : MvPolynomial (Fin 3) R) :
    kw_lrThird_comulHom W
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal a)
      = Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrThird_substHom W a) := by
  rfl

theorem kw_lrThird_comulHom_mk_X (k : Fin 3) :
    kw_lrThird_comulHom W
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X k))
      = Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrThird_vec W k) := by
  rw [kw_lrThird_comulHom_mk, kw_lrThird_substHom_X]

theorem kw_lrThird_comulHom_graded {n : ℕ} {x : ℬ}
    (hx : x ∈ projModelGradingCR W.toProjective n) :
    kw_lrThird_comulHom W x ∈ kw_lrComul_biGrading W (4 * n) := by
  obtain ⟨a, ha, rfl⟩ := (mem_quotGradingSubmodule_iff _ _).mp hx
  show Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrThird_substHom W a)
    ∈ kw_lrComul_biGrading W (4 * n)
  exact mk_mem_quotGradingSubmodule _ _
    ((mem_homogeneousSubmodule _ _).mpr
      (kw_lrThird_substHom_isHomogeneous W ((mem_homogeneousSubmodule _ _).mp ha)))

end WeierstrassProjModel

end

end MEGA_KwLRThirdQuotientGradedHom_lean

section MEGA_KwLRThirdChartHomAway_lean
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

theorem kw_lrThirdChart_mkSym_mem_four (k : Fin 3) :
    mk₆ (kw_lrThird_vec W k) ∈ kw_lrComul_biGrading W 4 :=
  mk_mem_quotGradingSubmodule _ _
    ((mem_homogeneousSubmodule _ _).mpr (kw_lrThird_vec_isHomogeneous W k))

set_option quotPrecheck false in

local notation "𝒜" k => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X k : MvPolynomial (Fin 3) R))

set_option quotPrecheck false in

local notation "𝒜²ₜ" k => HomogeneousLocalization.Away (kw_lrComul_biGrading W)
  (Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrThird_vec W k))

theorem kw_lrThirdChart_comulHom_mkX_pow (k : Fin 3) (n : ℕ) :
    kw_lrThird_comulHom W (mk₃ (X k : MvPolynomial (Fin 3) R) ^ n)
      = mk₆ (kw_lrThird_vec W k) ^ n := by
  rw [map_pow, kw_lrThird_comulHom_mk_X]

theorem kw_lrThirdChart_powers_comap_le (k : Fin 3) :
    Submonoid.powers (mk₃ (X k : MvPolynomial (Fin 3) R))
      ≤ (Submonoid.powers (mk₆ (kw_lrThird_vec W k))).comap
          (kw_lrThird_comulHom W).toRingHom := by
  rintro a ⟨n, rfl⟩
  exact ⟨n, (kw_lrThirdChart_comulHom_mkX_pow W k n).symm⟩

noncomputable def kw_lrThirdChart_locMap (k : Fin 3) :
    Localization.Away (mk₃ (X k : MvPolynomial (Fin 3) R))
      →+* Localization.Away (mk₆ (kw_lrThird_vec W k)) :=
  IsLocalization.map _ (kw_lrThird_comulHom W).toRingHom (kw_lrThirdChart_powers_comap_le W k)

noncomputable def kw_lrThirdChart_aux (k : Fin 3) :
    (𝒜 k) →+* Localization.Away (mk₆ (kw_lrThird_vec W k)) :=
  (kw_lrThirdChart_locMap W k).comp
    (algebraMap (𝒜 k) (Localization.Away (mk₃ (X k : MvPolynomial (Fin 3) R))))

theorem kw_lrThirdChart_aux_mk (k : Fin 3) (n : ℕ) (a : ℬ)
    (ha : a ∈ projModelGradingCR W.toProjective (n • 1)) :
    kw_lrThirdChart_aux W k
        (HomogeneousLocalization.Away.mk (projModelGradingCR W.toProjective)
          (kw_lrChart_mkX_mem_one W k) n a ha)
      = Localization.mk (kw_lrThird_comulHom W a)
          (⟨mk₆ (kw_lrThird_vec W k) ^ n, n, rfl⟩
            : Submonoid.powers (mk₆ (kw_lrThird_vec W k))) := by
  show kw_lrThirdChart_locMap W k
      (HomogeneousLocalization.Away.mk _ (kw_lrChart_mkX_mem_one W k) n a ha).val = _
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', kw_lrThirdChart_locMap,
    IsLocalization.map_mk', ← Localization.mk_eq_mk']
  congr 1
  exact Subtype.ext (kw_lrThirdChart_comulHom_mkX_pow W k n)

noncomputable def kw_lrThirdChart_witness (k : Fin 3) (n : ℕ) (a : ℬ)
    (ha : a ∈ projModelGradingCR W.toProjective (n • 1)) : (𝒜²ₜ k) :=
  HomogeneousLocalization.Away.mk (kw_lrComul_biGrading W)
    (kw_lrThirdChart_mkSym_mem_four W k) n (kw_lrThird_comulHom W a)
    (by
      have ha' : a ∈ projModelGradingCR W.toProjective n := by simpa using ha
      have h4n : kw_lrThird_comulHom W a ∈ kw_lrComul_biGrading W (4 * n) :=
        kw_lrThird_comulHom_graded W ha'
      simpa [smul_eq_mul, Nat.mul_comm] using h4n)

theorem kw_lrThirdChart_witness_val (k : Fin 3) (n : ℕ) (a : ℬ)
    (ha : a ∈ projModelGradingCR W.toProjective (n • 1)) :
    (kw_lrThirdChart_witness W k n a ha).val
      = kw_lrThirdChart_aux W k
          (HomogeneousLocalization.Away.mk (projModelGradingCR W.toProjective)
            (kw_lrChart_mkX_mem_one W k) n a ha) := by
  rw [kw_lrThirdChart_aux_mk]; rfl

theorem kw_lrThirdChart_aux_range_subset (k : Fin 3) :
    Set.range (kw_lrThirdChart_aux W k)
      ⊆ Set.range (algebraMap (𝒜²ₜ k) (Localization.Away (mk₆ (kw_lrThird_vec W k)))) := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (projModelGradingCR W.toProjective) (kw_lrChart_mkX_mem_one W k) z
  exact ⟨kw_lrThirdChart_witness W k n a ha,
    (HomogeneousLocalization.algebraMap_apply _).trans (kw_lrThirdChart_witness_val W k n a ha)⟩

theorem kw_lrThirdChart_aux_range_le (k : Fin 3) :
    (kw_lrThirdChart_aux W k).range
      ≤ (algebraMap (𝒜²ₜ k) (Localization.Away (mk₆ (kw_lrThird_vec W k)))).range := by
  rintro _ ⟨z, rfl⟩
  exact kw_lrThirdChart_aux_range_subset W k ⟨z, rfl⟩

noncomputable def kw_lrThirdChart_away (k : Fin 3) : (𝒜 k) →+* (𝒜²ₜ k) := by
  let e := RingEquiv.ofLeftInverse
    (f := algebraMap (𝒜²ₜ k) (Localization.Away (mk₆ (kw_lrThird_vec W k))))
    (h := (HomogeneousLocalization.val_injective _).hasLeftInverse.choose_spec)
  exact RingHom.comp (e.symm.toRingHom.comp
      (Subring.inclusion (kw_lrThirdChart_aux_range_le W k)))
    (kw_lrThirdChart_aux W k).rangeRestrict

end WeierstrassProjModel

end
end MEGA_KwLRThirdChartHomAway_lean

section MEGA_KwLRThirdChartHomToTensor_lean
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
local notation "𝒜²ₜ" k => HomogeneousLocalization.Away (kw_lrComul_biGrading W)
  (Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrThird_vec W k))

section ToTensor

variable (i j k : Fin 3)

noncomputable def kw_lrThirdChart_u : (𝒜 i) ⊗[R] (𝒜 j) :=
  kw_lrChart_ev' W i j (mk₆ (kw_lrThird_vec W k))

theorem kw_lrThirdChart_powers_ev'_comap_le :
    Submonoid.powers (mk₆ (kw_lrThird_vec W k))
      ≤ (Submonoid.powers (kw_lrThirdChart_u W i j k)).comap
          (kw_lrChart_ev' W i j).toRingHom := by
  rintro a ⟨n, rfl⟩
  exact ⟨n, by rw [map_pow]; rfl⟩

noncomputable def kw_lrThirdChart_toTensorLoc :
    Localization.Away (mk₆ (kw_lrThird_vec W k))
      →+* Localization.Away (kw_lrThirdChart_u W i j k) :=
  IsLocalization.map _ (kw_lrChart_ev' W i j).toRingHom
    (kw_lrThirdChart_powers_ev'_comap_le W i j k)

noncomputable def kw_lrThirdChart_toTensor :
    (𝒜²ₜ k) →+* Localization.Away (kw_lrThirdChart_u W i j k) :=
  (kw_lrThirdChart_toTensorLoc W i j k).comp
    (algebraMap (𝒜²ₜ k) (Localization.Away (mk₆ (kw_lrThird_vec W k))))

end ToTensor

section Composite

variable (i j k : Fin 3)

noncomputable def kw_lrThirdChart_tensor :
    (𝒜 k) →+* Localization.Away (kw_lrThirdChart_u W i j k) :=
  (kw_lrThirdChart_toTensor W i j k).comp (kw_lrThirdChart_away W k)

end Composite

end WeierstrassProjModel

end

end MEGA_KwLRThirdChartHomToTensor_lean

section MEGA_KwLRThirdU3_lean
set_option autoImplicit false

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

noncomputable def kw_lrThird_u₃ (i j : Fin 3) : Fin 3 → (𝒜 i) ⊗[R] (𝒜 j) :=
  fun k => kw_lrThirdChart_u W i j k

noncomputable def kw_lrThird_toE₃ (i j k : Fin 3) :
    Spec (CommRingCat.of (Localization.Away (kw_lrThird_u₃ W i j k)))
      ⟶ projModelCR W.toProjective :=
  Spec.map (CommRingCat.ofHom (kw_lrThirdChart_tensor W i j k))
    ≫ Proj.awayι (projModelGradingCR W.toProjective) _ (kw_lrChart_mkX_mem_one W k) one_pos

end WeierstrassProjModel

end

end MEGA_KwLRThirdU3_lean


