-- Prove2me | Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
-- name    : WeierstrassCurve_ProjModel_AddFormulas
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/a3db559a-4901-53ae-b356-f461d5d17ac7
-- title:
--   Bihomogeneous addition-law polynomials for the projective Weierstrass model
-- statement:
--   Fix a commutative ring $R$ and a Weierstrass curve $W$ over $R$, and work in $P_6 = R[X_0,X_1,X_2;X_0',X_1',X_2']$, the polynomial ring on two copies of $\mathrm{Fin}\,3$ indexed by `Sum.inl`/`Sum.inr`. `kw_lrAdd_WP₁` and `kw_lrAdd_WP₂` are the homogeneous Weierstrass cubic `W.toProjective.polynomial` renamed into the left and the right triple. `kw_lrAdd_c₂₁` and `kw_lrAdd_c₁₂` are explicit cubic forms, of bidegrees $(2,1)$ and $(1,2)$; `kw_lrAdd_chordCubic` identifies them as the two middle coefficients of the cubic restricted to the pencil, namely substituting $s\,X_i + t\,X_i'$ into the Weierstrass polynomial yields $s^3\,WP_1 + s^2t\,c_{21} + st^2\,c_{12} + t^3\,WP_2$ in a polynomial ring with two extra variables $s,t$; `kw_lrAdd_spec` is the $R$-algebra map sending the six variables to themselves and $(s,t)$ to $(c_{12},-c_{21})$. The triple `kw_lrAdd_starX/Y/Z` is $c_{12}X_i - c_{21}X_i'$, the third point of intersection of the chord, and `kw_lrAdd_X/Y/Z` is its image under $y \mapsto -y - a_1x - a_3z$; these are forms of total degree $4$ (bidegree $(2,2)$). The identities proved are invariance of the cubic under that involution over any $R$-algebra, $F(\mathrm{star}X,\mathrm{star}Y,\mathrm{star}Z) = c_{12}^3\,WP_1 - c_{21}^3\,WP_2$, the same for the chord-addition triple, and hence membership in the ideal $(WP_1,WP_2)$.
--
--   A second triple `kw_lrSym_X/Y/Z` is given by explicit coefficient lists in $a_1,\dots,a_6$ on the monomials of bidegree $(2,2)$, with coefficients symmetric under exchanging the two triples of variables, and is again homogeneous of total degree $4$. Six explicit cofactors `kw_lrSym_pXZ`, `kw_lrSym_qXZ`, `kw_lrSym_pXY`, `kw_lrSym_qXY`, `kw_lrSym_pYZ`, `kw_lrSym_qYZ`, of bidegrees $(1,4)$ and $(4,1)$, are defined; for the $XZ$ and $YZ$ pairs the corresponding $2\times 2$ minors of the two triples are shown to equal $p\,WP_1 + q\,WP_2$, and so to lie in $(WP_1,WP_2)$. Finally `kw_lrSym_dblX/Y/Z` are explicit quartic forms in three variables $X_0,X_1,X_2$ recording the doubling law. Small auxiliary lemmas record homogeneity of each form and of products $C(r)\cdot q$.
--
--   **Relation to Mathlib.** The cubic used throughout is Mathlib's `WeierstrassCurve.Projective.polynomial` of `W.toProjective`; the pair of bihomogeneous addition laws of bidegree $(2,2)$, their agreement cofactors and the doubling forms are the project's own.
--
--   **Where it is used.** These polynomial formulas are the input to the module supplying the group-law vocabulary for the projective Weierstrass model, where the addition morphism of the model is assembled from the two addition laws and their agreement minors; that construction underlies the treatment of elliptic curves used later in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_ProjModel_AddFormulas.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Ideal.Span

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false

section MEGA_KwLRChordAddFormulas_lean
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

noncomputable section

open MvPolynomial WeierstrassCurve

namespace WeierstrassProjModel

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

local notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R

local notation "P₈" => MvPolynomial ((Fin 3 ⊕ Fin 3) ⊕ Fin 2) R

local notation "Xl" i => (X (Sum.inl i) : P₆)

local notation "Xr" i => (X (Sum.inr i) : P₆)

def kw_lrAdd_WP₁ : P₆ := rename Sum.inl W.toProjective.polynomial

def kw_lrAdd_WP₂ : P₆ := rename Sum.inr W.toProjective.polynomial

local notation "WP₁" => kw_lrAdd_WP₁ W
local notation "WP₂" => kw_lrAdd_WP₂ W

local notation "ι" => (rename (Sum.inl : (Fin 3 ⊕ Fin 3) → (Fin 3 ⊕ Fin 3) ⊕ Fin 2) : P₆ →ₐ[R] P₈)

local notation "𝓈" => (X (Sum.inr 0) : P₈)
local notation "𝓉" => (X (Sum.inr 1) : P₈)

def kw_lrAdd_c₂₁ : P₆ :=
  - C (3:R) * (Xl 0)^2 * (Xr 0) + (Xl 1)^2 * (Xr 2) + C (2:R) * (Xl 1) * (Xr 1) * (Xl 2)
    - C (3:R) * C W.a₆ * (Xl 2)^2 * (Xr 2)
    + C W.a₁ * ((Xl 0)*(Xl 1)*(Xr 2) + (Xl 0)*(Xr 1)*(Xl 2) + (Xr 0)*(Xl 1)*(Xl 2))
    - C W.a₂ * ((Xl 0)^2*(Xr 2) + C (2:R)*(Xl 0)*(Xr 0)*(Xl 2))
    + C W.a₃ * (C (2:R)*(Xl 1)*(Xl 2)*(Xr 2) + (Xr 1)*(Xl 2)^2)
    - C W.a₄ * (C (2:R)*(Xl 0)*(Xl 2)*(Xr 2) + (Xr 0)*(Xl 2)^2)

def kw_lrAdd_c₁₂ : P₆ :=
  - C (3:R) * (Xl 0) * (Xr 0)^2 + C (2:R)*(Xl 1)*(Xr 1)*(Xr 2) + (Xr 1)^2*(Xl 2)
    - C (3:R) * C W.a₆ * (Xl 2)*(Xr 2)^2
    + C W.a₁ * ((Xl 0)*(Xr 1)*(Xr 2) + (Xr 0)*(Xl 1)*(Xr 2) + (Xr 0)*(Xr 1)*(Xl 2))
    - C W.a₂ * (C (2:R)*(Xl 0)*(Xr 0)*(Xr 2) + (Xr 0)^2*(Xl 2))
    + C W.a₃ * ((Xl 1)*(Xr 2)^2 + C (2:R)*(Xr 1)*(Xl 2)*(Xr 2))
    - C W.a₄ * ((Xl 0)*(Xr 2)^2 + C (2:R)*(Xr 0)*(Xl 2)*(Xr 2))

local notation "c₂₁" => kw_lrAdd_c₂₁ W
local notation "c₁₂" => kw_lrAdd_c₁₂ W

def kw_lrAdd_starX : P₆ := c₁₂ * (Xl 0) - c₂₁ * (Xr 0)

def kw_lrAdd_starY : P₆ := c₁₂ * (Xl 1) - c₂₁ * (Xr 1)

def kw_lrAdd_starZ : P₆ := c₁₂ * (Xl 2) - c₂₁ * (Xr 2)

def kw_lrAdd_X : P₆ := kw_lrAdd_starX W

def kw_lrAdd_Y : P₆ :=
  -(kw_lrAdd_starY W) - C W.a₁ * kw_lrAdd_starX W - C W.a₃ * kw_lrAdd_starZ W

def kw_lrAdd_Z : P₆ := kw_lrAdd_starZ W

theorem kw_lrAdd_isHomog_C_mul {σ : Type*} {n : ℕ} (r : R)
    {q : MvPolynomial σ R} (hq : q.IsHomogeneous n) : (C r * q).IsHomogeneous n :=
  Nat.zero_add n ▸ (isHomogeneous_C _ r).mul hq

theorem kw_lrAdd_c₂₁_isHomogeneous : (c₂₁).IsHomogeneous 3 := by
  unfold kw_lrAdd_c₂₁

  repeat' first
    | with_reducible apply IsHomogeneous.add | with_reducible apply IsHomogeneous.sub
    | with_reducible apply IsHomogeneous.neg
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible exact isHomogeneous_X _ _
    | with_reducible exact (isHomogeneous_X _ _).pow _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)
    | with_reducible refine kw_lrAdd_isHomog_C_mul _ ?_

theorem kw_lrAdd_c₁₂_isHomogeneous : (c₁₂).IsHomogeneous 3 := by
  unfold kw_lrAdd_c₁₂

  repeat' first
    | with_reducible apply IsHomogeneous.add | with_reducible apply IsHomogeneous.sub
    | with_reducible apply IsHomogeneous.neg
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible exact isHomogeneous_X _ _
    | with_reducible exact (isHomogeneous_X _ _).pow _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)
    | with_reducible refine kw_lrAdd_isHomog_C_mul _ ?_

theorem kw_lrAdd_X_isHomogeneous : (kw_lrAdd_X W).IsHomogeneous 4 := by
  show ((c₁₂) * (Xl 0) - (c₂₁) * (Xr 0)).IsHomogeneous 4
  exact ((kw_lrAdd_c₁₂_isHomogeneous W).mul (isHomogeneous_X _ _)).sub
    ((kw_lrAdd_c₂₁_isHomogeneous W).mul (isHomogeneous_X _ _))

theorem kw_lrAdd_Z_isHomogeneous : (kw_lrAdd_Z W).IsHomogeneous 4 := by
  show ((c₁₂) * (Xl 2) - (c₂₁) * (Xr 2)).IsHomogeneous 4
  exact ((kw_lrAdd_c₁₂_isHomogeneous W).mul (isHomogeneous_X _ _)).sub
    ((kw_lrAdd_c₂₁_isHomogeneous W).mul (isHomogeneous_X _ _))

theorem kw_lrAdd_Y_isHomogeneous : (kw_lrAdd_Y W).IsHomogeneous 4 := by
  unfold kw_lrAdd_Y
  have hX : (kw_lrAdd_starX W).IsHomogeneous 4 := kw_lrAdd_X_isHomogeneous W
  have hZ : (kw_lrAdd_starZ W).IsHomogeneous 4 := kw_lrAdd_Z_isHomogeneous W
  have hY : (kw_lrAdd_starY W).IsHomogeneous 4 :=
    ((kw_lrAdd_c₁₂_isHomogeneous W).mul (isHomogeneous_X _ _)).sub
      ((kw_lrAdd_c₂₁_isHomogeneous W).mul (isHomogeneous_X _ _))
  exact (hY.neg.sub ((isHomogeneous_C _ _).mul hX)).sub ((isHomogeneous_C _ _).mul hZ)

section OnCurve

noncomputable def kw_lrAdd_spec : P₈ →ₐ[R] P₆ :=
  aeval (Sum.elim X ![c₁₂, -c₂₁])

local notation "σ" => kw_lrAdd_spec W

theorem kw_lrAdd_spec_rename (p : P₆) : σ (ι p) = p := by
  show aeval (Sum.elim X ![c₁₂, -c₂₁]) (rename Sum.inl p) = p
  rw [aeval_rename, Sum.elim_comp_inl]
  exact congrFun (congrArg DFunLike.coe aeval_X_left) p

theorem kw_lrAdd_spec_s : σ 𝓈 = c₁₂ := by
  simp only [kw_lrAdd_spec, aeval_X, Sum.elim_inr, Matrix.cons_val_zero]

theorem kw_lrAdd_spec_t : σ 𝓉 = -c₂₁ := by
  simp only [kw_lrAdd_spec, aeval_X, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero]

theorem kw_lrAdd_chordCubic :
    aeval (fun i => 𝓈 * ι (Xl i) + 𝓉 * ι (Xr i)) W.toProjective.polynomial
      = 𝓈^3 * ι WP₁ + 𝓈^2 * 𝓉 * ι c₂₁ + 𝓈 * 𝓉^2 * ι c₁₂ + 𝓉^3 * ι WP₂ := by
  simp only [kw_lrAdd_WP₁, kw_lrAdd_WP₂, kw_lrAdd_c₂₁, kw_lrAdd_c₁₂,
    WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, rename_X, rename_C,
    aeval_X, aeval_C, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, MvPolynomial.algebraMap_eq]
  ring

theorem kw_lrAdd_negInvariant {S : Type u} [CommRing S] [Algebra R S] (x y z : S) :
    aeval ![x, -y - algebraMap R S W.a₁ * x - algebraMap R S W.a₃ * z, z]
        W.toProjective.polynomial
      = aeval ![x, y, z] W.toProjective.polynomial := by
  simp only [WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem kw_lrAdd_star_onCurve :
    aeval ![kw_lrAdd_starX W, kw_lrAdd_starY W, kw_lrAdd_starZ W]
        W.toProjective.polynomial
      = c₁₂^3 * WP₁ - c₂₁^3 * WP₂ := by

  have hcomp : (σ).comp (aeval (fun i => 𝓈 * ι (Xl i) + 𝓉 * ι (Xr i)))
      = (aeval ![kw_lrAdd_starX W, kw_lrAdd_starY W, kw_lrAdd_starZ W]
          : MvPolynomial (Fin 3) R →ₐ[R] P₆) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp only [AlgHom.comp_apply, map_add, map_mul, aeval_X, Fin.isValue,
        kw_lrAdd_spec_rename, kw_lrAdd_spec_s, kw_lrAdd_spec_t,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons,
        kw_lrAdd_starX, kw_lrAdd_starY, kw_lrAdd_starZ, neg_mul, ← sub_eq_add_neg] <;>
      rfl
  rw [show (aeval ![kw_lrAdd_starX W, kw_lrAdd_starY W, kw_lrAdd_starZ W]
        : MvPolynomial (Fin 3) R →ₐ[R] P₆) W.toProjective.polynomial
      = σ (aeval (fun i => 𝓈 * ι (Xl i) + 𝓉 * ι (Xr i)) W.toProjective.polynomial)
    from by rw [← AlgHom.comp_apply, hcomp], kw_lrAdd_chordCubic]

  simp only [map_add, map_mul, map_pow, kw_lrAdd_spec_rename,
    kw_lrAdd_spec_s, kw_lrAdd_spec_t]
  ring

theorem kw_lrAdd_onCurve :
    aeval ![kw_lrAdd_X W, kw_lrAdd_Y W, kw_lrAdd_Z W] W.toProjective.polynomial
      = c₁₂^3 * WP₁ - c₂₁^3 * WP₂ := by
  have hneg : aeval ![kw_lrAdd_X W, kw_lrAdd_Y W, kw_lrAdd_Z W] W.toProjective.polynomial
      = aeval ![kw_lrAdd_starX W, kw_lrAdd_starY W, kw_lrAdd_starZ W]
          W.toProjective.polynomial := by
    have := kw_lrAdd_negInvariant W (S := P₆)
      (kw_lrAdd_starX W) (kw_lrAdd_starY W) (kw_lrAdd_starZ W)
    simp only [kw_lrAdd_X, kw_lrAdd_Y, kw_lrAdd_Z, algebraMap_eq] at this ⊢
    exact this
  rw [hneg, kw_lrAdd_star_onCurve]

theorem kw_lrAdd_onCurve_mem_span :
    aeval ![kw_lrAdd_X W, kw_lrAdd_Y W, kw_lrAdd_Z W] W.toProjective.polynomial
      ∈ Ideal.span {WP₁, WP₂} := by
  rw [kw_lrAdd_onCurve]
  exact sub_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

end OnCurve

end WeierstrassProjModel

end

end MEGA_KwLRChordAddFormulas_lean

section MEGA_KwLRSymAddFormulas_lean
set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSimpArgs false

noncomputable section

open MvPolynomial WeierstrassCurve

namespace WeierstrassProjModel

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

local notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R
local notation "Xl" i => (X (Sum.inl i) : P₆)
local notation "Xr" i => (X (Sum.inr i) : P₆)
local notation "WP₁" => kw_lrAdd_WP₁ W
local notation "WP₂" => kw_lrAdd_WP₂ W

local notation "τ" => (rename (Sum.swap : Fin 3 ⊕ Fin 3 → Fin 3 ⊕ Fin 3) : P₆ →ₐ[R] P₆)

local notation "δ" => (aeval (Sum.elim X X) : P₆ →ₐ[R] MvPolynomial (Fin 3) R)

def kw_lrSym_X : P₆ :=
  C (-(2:R)*W.a₁*W.a₂) * (Xl 0)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C (W.a₁^ (2 : ℕ) - (2:R)*W.a₂) * (Xl 0)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C (-W.a₁^ (2 : ℕ)*W.a₃ - (3:R)*W.a₁*W.a₄ - W.a₂*W.a₃) * (Xl 0)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C (W.a₁) * (Xl 0)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C (-(2:R)*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (-W.a₁*W.a₃^ (2 : ℕ) - (3:R)*W.a₁*W.a₆ - W.a₃*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (2 : ℕ) - (2:R)*W.a₂) * (Xl 0)*(Xl 1)*(Xr 0)^ (2 : ℕ)
    + C ((4:R)*W.a₁) * (Xl 0)*(Xl 1)*(Xr 0)*(Xr 1)
    + C (-(4:R)*W.a₄) * (Xl 0)*(Xl 1)*(Xr 0)*(Xr 2)
    + C ((2:R)) * (Xl 0)*(Xl 1)*(Xr 1)^ (2 : ℕ)
    + C ((2:R)*W.a₃) * (Xl 0)*(Xl 1)*(Xr 1)*(Xr 2)
    + C (-W.a₃^ (2 : ℕ) - (6:R)*W.a₆) * (Xl 0)*(Xl 1)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁^ (2 : ℕ)*W.a₃ - (3:R)*W.a₁*W.a₄ - W.a₂*W.a₃) * (Xl 0)*(Xl 2)*(Xr 0)^ (2 : ℕ)
    + C (-(4:R)*W.a₄) * (Xl 0)*(Xl 2)*(Xr 0)*(Xr 1)
    + C (-(4:R)*W.a₁*W.a₃^ (2 : ℕ) - (12:R)*W.a₁*W.a₆ - (4:R)*W.a₃*W.a₄) * (Xl 0)*(Xl 2)*(Xr 0)*(Xr 2)
    + C (W.a₃) * (Xl 0)*(Xl 2)*(Xr 1)^ (2 : ℕ)
    + C (-(2:R)*W.a₃^ (2 : ℕ) - (12:R)*W.a₆) * (Xl 0)*(Xl 2)*(Xr 1)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₆ + W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (4:R)*W.a₁*W.a₂*W.a₆ + W.a₁*W.a₄^ (2 : ℕ) - (2:R)*W.a₃^ (3 : ℕ) - (9:R)*W.a₃*W.a₆) * (Xl 0)*(Xl 2)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁) * (Xl 1)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)) * (Xl 1)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C (W.a₃) * (Xl 1)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C (-(2:R)*W.a₄) * (Xl 1)*(Xl 2)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)*W.a₃) * (Xl 1)*(Xl 2)*(Xr 0)*(Xr 1)
    + C (-(2:R)*W.a₃^ (2 : ℕ) - (12:R)*W.a₆) * (Xl 1)*(Xl 2)*(Xr 0)*(Xr 2)
    + C (-(2:R)*W.a₁^ (2 : ℕ)*W.a₆ + (2:R)*W.a₁*W.a₃*W.a₄ - (2:R)*W.a₂*W.a₃^ (2 : ℕ) - (8:R)*W.a₂*W.a₆ + (2:R)*W.a₄^ (2 : ℕ)) * (Xl 1)*(Xl 2)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁*W.a₃^ (2 : ℕ) - (3:R)*W.a₁*W.a₆ - W.a₃*W.a₄) * (Xl 2)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C (-W.a₃^ (2 : ℕ) - (6:R)*W.a₆) * (Xl 2)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C (-W.a₁^ (3 : ℕ)*W.a₆ + W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (4:R)*W.a₁*W.a₂*W.a₆ + W.a₁*W.a₄^ (2 : ℕ) - (2:R)*W.a₃^ (3 : ℕ) - (9:R)*W.a₃*W.a₆) * (Xl 2)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C (-(2:R)*W.a₁^ (2 : ℕ)*W.a₆ + (2:R)*W.a₁*W.a₃*W.a₄ - (2:R)*W.a₂*W.a₃^ (2 : ℕ) - (8:R)*W.a₂*W.a₆ + (2:R)*W.a₄^ (2 : ℕ)) * (Xl 2)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (-(2:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₆ + (2:R)*W.a₁*W.a₃^ (2 : ℕ)*W.a₄ - (2:R)*W.a₂*W.a₃^ (3 : ℕ) - (8:R)*W.a₂*W.a₃*W.a₆ + (2:R)*W.a₃*W.a₄^ (2 : ℕ)) * (Xl 2)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)

def kw_lrSym_Y : P₆ :=
  C (-(2:R)*W.a₂^ (2 : ℕ) + (6:R)*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C (W.a₁*W.a₂ - (3:R)*W.a₃) * (Xl 0)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C (W.a₁^ (2 : ℕ)*W.a₄ - (2:R)*W.a₁*W.a₂*W.a₃ - (2:R)*W.a₂*W.a₄ + (3:R)*W.a₃^ (2 : ℕ) + (18:R)*W.a₆) * (Xl 0)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C (W.a₁*W.a₄ - W.a₂*W.a₃) * (Xl 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C ((3:R)*W.a₁^ (2 : ℕ)*W.a₆ - (2:R)*W.a₁*W.a₃*W.a₄ + W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₂*W.a₆ - (2:R)*W.a₄^ (2 : ℕ)) * (Xl 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁*W.a₂ - (3:R)*W.a₃) * (Xl 0)*(Xl 1)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)*W.a₁*W.a₄ - (2:R)*W.a₂*W.a₃) * (Xl 0)*(Xl 1)*(Xr 0)*(Xr 2)
    + C (W.a₁) * (Xl 0)*(Xl 1)*(Xr 1)^ (2 : ℕ)
    + C ((3:R)*W.a₁*W.a₆ - W.a₃*W.a₄) * (Xl 0)*(Xl 1)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (2 : ℕ)*W.a₄ - (2:R)*W.a₁*W.a₂*W.a₃ - (2:R)*W.a₂*W.a₄ + (3:R)*W.a₃^ (2 : ℕ) + (18:R)*W.a₆) * (Xl 0)*(Xl 2)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)*W.a₁*W.a₄ - (2:R)*W.a₂*W.a₃) * (Xl 0)*(Xl 2)*(Xr 0)*(Xr 1)
    + C ((12:R)*W.a₁^ (2 : ℕ)*W.a₆ - (8:R)*W.a₁*W.a₃*W.a₄ + (4:R)*W.a₂*W.a₃^ (2 : ℕ) + (24:R)*W.a₂*W.a₆ - (8:R)*W.a₄^ (2 : ℕ)) * (Xl 0)*(Xl 2)*(Xr 0)*(Xr 2)
    + C ((6:R)*W.a₁*W.a₆ - (2:R)*W.a₃*W.a₄) * (Xl 0)*(Xl 2)*(Xr 1)*(Xr 2)
    + C (W.a₁^ (4 : ℕ)*W.a₆ - W.a₁^ (3 : ℕ)*W.a₃*W.a₄ + W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ - W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) - (2:R)*W.a₁*W.a₂*W.a₃*W.a₄ - W.a₁*W.a₃^ (3 : ℕ) + (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (8:R)*W.a₂^ (2 : ℕ)*W.a₆ - (2:R)*W.a₂*W.a₄^ (2 : ℕ) - (3:R)*W.a₃^ (2 : ℕ)*W.a₄ - (6:R)*W.a₄*W.a₆) * (Xl 0)*(Xl 2)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁) * (Xl 1)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C ((2:R)) * (Xl 1)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C (W.a₃) * (Xl 1)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (W.a₁*W.a₄ - W.a₂*W.a₃) * (Xl 1)*(Xl 2)*(Xr 0)^ (2 : ℕ)
    + C ((6:R)*W.a₁*W.a₆ - (2:R)*W.a₃*W.a₄) * (Xl 1)*(Xl 2)*(Xr 0)*(Xr 2)
    + C (W.a₃) * (Xl 1)*(Xl 2)*(Xr 1)^ (2 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₆ - W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + W.a₁*W.a₂*W.a₃^ (2 : ℕ) + (4:R)*W.a₁*W.a₂*W.a₆ - W.a₁*W.a₄^ (2 : ℕ) - W.a₃^ (3 : ℕ) - (3:R)*W.a₃*W.a₆) * (Xl 1)*(Xl 2)*(Xr 2)^ (2 : ℕ)
    + C ((3:R)*W.a₁^ (2 : ℕ)*W.a₆ - (2:R)*W.a₁*W.a₃*W.a₄ + W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₂*W.a₆ - (2:R)*W.a₄^ (2 : ℕ)) * (Xl 2)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C ((3:R)*W.a₁*W.a₆ - W.a₃*W.a₄) * (Xl 2)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C (W.a₁^ (4 : ℕ)*W.a₆ - W.a₁^ (3 : ℕ)*W.a₃*W.a₄ + W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ - W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) - (2:R)*W.a₁*W.a₂*W.a₃*W.a₄ - W.a₁*W.a₃^ (3 : ℕ) + (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (8:R)*W.a₂^ (2 : ℕ)*W.a₆ - (2:R)*W.a₂*W.a₄^ (2 : ℕ) - (3:R)*W.a₃^ (2 : ℕ)*W.a₄ - (6:R)*W.a₄*W.a₆) * (Xl 2)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C (W.a₁^ (3 : ℕ)*W.a₆ - W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + W.a₁*W.a₂*W.a₃^ (2 : ℕ) + (4:R)*W.a₁*W.a₂*W.a₆ - W.a₁*W.a₄^ (2 : ℕ) - W.a₃^ (3 : ℕ) - (3:R)*W.a₃*W.a₆) * (Xl 2)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C ((2:R)*W.a₁^ (3 : ℕ)*W.a₃*W.a₆ - (2:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₄ + (2:R)*W.a₁^ (2 : ℕ)*W.a₄*W.a₆ + (2:R)*W.a₁*W.a₂*W.a₃^ (3 : ℕ) + (8:R)*W.a₁*W.a₂*W.a₃*W.a₆ - (4:R)*W.a₁*W.a₃*W.a₄^ (2 : ℕ) + (2:R)*W.a₂*W.a₃^ (2 : ℕ)*W.a₄ + (8:R)*W.a₂*W.a₄*W.a₆ - (2:R)*W.a₃^ (4 : ℕ) - (12:R)*W.a₃^ (2 : ℕ)*W.a₆ - (2:R)*W.a₄^ (3 : ℕ) - (18:R)*W.a₆^ (2 : ℕ)) * (Xl 2)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)

def kw_lrSym_Z : P₆ :=
  C ((6:R)*W.a₁) * (Xl 0)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C ((6:R)) * (Xl 0)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C (W.a₁^ (3 : ℕ) + (3:R)*W.a₁*W.a₂ + (3:R)*W.a₃) * (Xl 0)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C (W.a₁^ (2 : ℕ) + (2:R)*W.a₂) * (Xl 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (W.a₁^ (2 : ℕ)*W.a₃ + W.a₁*W.a₄ + W.a₂*W.a₃) * (Xl 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C ((6:R)) * (Xl 0)*(Xl 1)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)*W.a₁^ (2 : ℕ) + (4:R)*W.a₂) * (Xl 0)*(Xl 1)*(Xr 0)*(Xr 2)
    + C ((2:R)*W.a₁) * (Xl 0)*(Xl 1)*(Xr 1)*(Xr 2)
    + C ((2:R)*W.a₁*W.a₃ + (2:R)*W.a₄) * (Xl 0)*(Xl 1)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (3 : ℕ) + (3:R)*W.a₁*W.a₂ + (3:R)*W.a₃) * (Xl 0)*(Xl 2)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)*W.a₁^ (2 : ℕ) + (4:R)*W.a₂) * (Xl 0)*(Xl 2)*(Xr 0)*(Xr 1)
    + C ((4:R)*W.a₁^ (2 : ℕ)*W.a₃ + (4:R)*W.a₁*W.a₄ + (4:R)*W.a₂*W.a₃) * (Xl 0)*(Xl 2)*(Xr 0)*(Xr 2)
    + C (W.a₁) * (Xl 0)*(Xl 2)*(Xr 1)^ (2 : ℕ)
    + C ((4:R)*W.a₁*W.a₃ + (4:R)*W.a₄) * (Xl 0)*(Xl 2)*(Xr 1)*(Xr 2)
    + C ((3:R)*W.a₁*W.a₃^ (2 : ℕ) + (3:R)*W.a₁*W.a₆ + (3:R)*W.a₃*W.a₄) * (Xl 0)*(Xl 2)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁) * (Xl 1)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C ((2:R)) * (Xl 1)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (W.a₃) * (Xl 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (2 : ℕ) + (2:R)*W.a₂) * (Xl 1)*(Xl 2)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)*W.a₁) * (Xl 1)*(Xl 2)*(Xr 0)*(Xr 1)
    + C ((4:R)*W.a₁*W.a₃ + (4:R)*W.a₄) * (Xl 1)*(Xl 2)*(Xr 0)*(Xr 2)
    + C ((2:R)) * (Xl 1)*(Xl 2)*(Xr 1)^ (2 : ℕ)
    + C ((4:R)*W.a₃) * (Xl 1)*(Xl 2)*(Xr 1)*(Xr 2)
    + C ((3:R)*W.a₃^ (2 : ℕ) + (6:R)*W.a₆) * (Xl 1)*(Xl 2)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (2 : ℕ)*W.a₃ + W.a₁*W.a₄ + W.a₂*W.a₃) * (Xl 2)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)*W.a₁*W.a₃ + (2:R)*W.a₄) * (Xl 2)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C ((3:R)*W.a₁*W.a₃^ (2 : ℕ) + (3:R)*W.a₁*W.a₆ + (3:R)*W.a₃*W.a₄) * (Xl 2)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C (W.a₃) * (Xl 2)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C ((3:R)*W.a₃^ (2 : ℕ) + (6:R)*W.a₆) * (Xl 2)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C ((2:R)*W.a₃^ (3 : ℕ) + (6:R)*W.a₃*W.a₆) * (Xl 2)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)

theorem kw_lrSym_X_isHomogeneous : (kw_lrSym_X W).IsHomogeneous 4 := by
  unfold kw_lrSym_X
  repeat' first
    | with_reducible apply IsHomogeneous.add
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)

theorem kw_lrSym_Y_isHomogeneous : (kw_lrSym_Y W).IsHomogeneous 4 := by
  unfold kw_lrSym_Y
  repeat' first
    | with_reducible apply IsHomogeneous.add
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)

theorem kw_lrSym_Z_isHomogeneous : (kw_lrSym_Z W).IsHomogeneous 4 := by
  unfold kw_lrSym_Z
  repeat' first
    | with_reducible apply IsHomogeneous.add
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)

section OnCurve

end OnCurve

section Minors

def kw_lrSym_pXZ : P₆ :=
  C ((3:R)*W.a₁^ (2 : ℕ)) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₂ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃ - W.a₁*W.a₂^ (2 : ℕ) + (3:R)*W.a₁*W.a₄) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C ((3:R)*W.a₁) * (Xl 0)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (W.a₁^ (4 : ℕ) + W.a₁^ (2 : ℕ)*W.a₂ + (3:R)*W.a₁*W.a₃) * (Xl 0)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁^ (3 : ℕ)*W.a₄ - W.a₁*W.a₂*W.a₄ + (3:R)*W.a₁*W.a₃^ (2 : ℕ) + (9:R)*W.a₁*W.a₆) * (Xl 0)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C (W.a₁^ (3 : ℕ) + W.a₁*W.a₂) * (Xl 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₃ + W.a₁*W.a₂*W.a₃) * (Xl 0)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C (-W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + W.a₁*W.a₂*W.a₃^ (2 : ℕ) + (3:R)*W.a₁*W.a₂*W.a₆ - W.a₁*W.a₄^ (2 : ℕ)) * (Xl 0)*(Xr 2)^ (4 : ℕ)
    + C (-(3:R)*W.a₁^ (2 : ℕ)) * (Xl 1)*(Xr 0)^ (3 : ℕ)*(Xr 2)
    + C ((6:R)*W.a₁) * (Xl 1)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (-(5:R)*W.a₁^ (2 : ℕ)*W.a₂ + (6:R)*W.a₁*W.a₃ - (2:R)*W.a₂^ (2 : ℕ) + (6:R)*W.a₄) * (Xl 1)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C ((6:R)) * (Xl 1)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C ((5:R)*W.a₁^ (3 : ℕ) + (2:R)*W.a₁*W.a₂ + (6:R)*W.a₃) * (Xl 1)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C (-(5:R)*W.a₁^ (2 : ℕ)*W.a₄ - (2:R)*W.a₂*W.a₄ + (6:R)*W.a₃^ (2 : ℕ) + (18:R)*W.a₆) * (Xl 1)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C ((5:R)*W.a₁^ (2 : ℕ) + (2:R)*W.a₂) * (Xl 1)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C ((5:R)*W.a₁^ (2 : ℕ)*W.a₃ + (2:R)*W.a₂*W.a₃) * (Xl 1)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C (-(3:R)*W.a₁^ (2 : ℕ)*W.a₆ - (2:R)*W.a₁*W.a₃*W.a₄ + (2:R)*W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₂*W.a₆ - (2:R)*W.a₄^ (2 : ℕ)) * (Xl 1)*(Xr 2)^ (4 : ℕ)
    + C ((3:R)*W.a₁^ (2 : ℕ)) * (Xl 2)*(Xr 0)^ (3 : ℕ)*(Xr 1)
    + C ((9:R)*W.a₁) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C (W.a₁^ (4 : ℕ) - W.a₁^ (2 : ℕ)*W.a₂ + (15:R)*W.a₁*W.a₃ - (2:R)*W.a₂^ (2 : ℕ) + (6:R)*W.a₄) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ) - W.a₁^ (3 : ℕ)*W.a₄ - (5:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ + W.a₁*W.a₂^ (3 : ℕ) - (4:R)*W.a₁*W.a₂*W.a₄ + (9:R)*W.a₁*W.a₃^ (2 : ℕ) + (9:R)*W.a₁*W.a₆ - (2:R)*W.a₂^ (2 : ℕ)*W.a₃ + (6:R)*W.a₃*W.a₄) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C ((6:R)) * (Xl 2)*(Xr 0)*(Xr 1)^ (3 : ℕ)
    + C ((3:R)*W.a₁^ (3 : ℕ) + (3:R)*W.a₁*W.a₂ + (12:R)*W.a₃) * (Xl 2)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (-W.a₁^ (4 : ℕ)*W.a₂ + (6:R)*W.a₁^ (3 : ℕ)*W.a₃ - W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + W.a₁^ (2 : ℕ)*W.a₄ + (3:R)*W.a₁*W.a₂*W.a₃ - (2:R)*W.a₂*W.a₄ + (12:R)*W.a₃^ (2 : ℕ) + (18:R)*W.a₆) * (Xl 2)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₂*W.a₄ - (6:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + W.a₁*W.a₂^ (2 : ℕ)*W.a₄ + W.a₁*W.a₂*W.a₃^ (2 : ℕ) + (3:R)*W.a₁*W.a₂*W.a₆ - (4:R)*W.a₁*W.a₄^ (2 : ℕ) - (2:R)*W.a₂*W.a₃*W.a₄ + (6:R)*W.a₃^ (3 : ℕ) + (18:R)*W.a₃*W.a₆) * (Xl 2)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C ((2:R)*W.a₁^ (2 : ℕ) + (2:R)*W.a₂) * (Xl 2)*(Xr 1)^ (3 : ℕ)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₂ + (7:R)*W.a₁^ (2 : ℕ)*W.a₃ - W.a₁*W.a₂^ (2 : ℕ) + (3:R)*W.a₁*W.a₄ + (4:R)*W.a₂*W.a₃) * (Xl 2)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₃ + (5:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) - W.a₁*W.a₂^ (2 : ℕ)*W.a₃ + W.a₁*W.a₃*W.a₄ + (4:R)*W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₂*W.a₆ - (2:R)*W.a₄^ (2 : ℕ)) * (Xl 2)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₂*W.a₆ - (3:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₆ + W.a₁*W.a₂^ (2 : ℕ)*W.a₆ - (2:R)*W.a₁*W.a₃^ (2 : ℕ)*W.a₄ - (3:R)*W.a₁*W.a₄*W.a₆ + (2:R)*W.a₂*W.a₃^ (3 : ℕ) + (6:R)*W.a₂*W.a₃*W.a₆ - (2:R)*W.a₃*W.a₄^ (2 : ℕ)) * (Xl 2)*(Xr 2)^ (4 : ℕ)

def kw_lrSym_qXZ : P₆ :=
  C (-(9:R)*W.a₁) * (Xl 0)^ (2 : ℕ)*(Xl 1)^ (2 : ℕ)*(Xr 2)
    + C (-(3:R)*W.a₁^ (2 : ℕ)) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 0)
    + C (-(6:R)*W.a₁) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 1)
    + C (-W.a₁^ (4 : ℕ) + (4:R)*W.a₁^ (2 : ℕ)*W.a₂ - (15:R)*W.a₁*W.a₃ + (2:R)*W.a₂^ (2 : ℕ) - (6:R)*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 2)
    + C (W.a₁^ (3 : ℕ)*W.a₂ - (3:R)*W.a₁^ (2 : ℕ)*W.a₃ + W.a₁*W.a₂^ (2 : ℕ) - (3:R)*W.a₁*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C ((2:R)*W.a₁^ (2 : ℕ)*W.a₂ - (6:R)*W.a₁*W.a₃ + (2:R)*W.a₂^ (2 : ℕ) - (6:R)*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (-W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ) + W.a₁^ (3 : ℕ)*W.a₄ + (5:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ - W.a₁*W.a₂^ (3 : ℕ) + (4:R)*W.a₁*W.a₂*W.a₄ - (9:R)*W.a₁*W.a₃^ (2 : ℕ) - (9:R)*W.a₁*W.a₆ + (2:R)*W.a₂^ (2 : ℕ)*W.a₃ - (6:R)*W.a₃*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C (-(6:R)) * (Xl 0)*(Xl 1)^ (3 : ℕ)*(Xr 2)
    + C (-(3:R)*W.a₁) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 0)
    + C (-(6:R)) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 1)
    + C (-(6:R)*W.a₁^ (3 : ℕ) - (3:R)*W.a₁*W.a₂ - (12:R)*W.a₃) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 2)
    + C (-W.a₁^ (4 : ℕ) - W.a₁^ (2 : ℕ)*W.a₂ - (3:R)*W.a₁*W.a₃) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C (-(2:R)*W.a₁^ (3 : ℕ) - (2:R)*W.a₁*W.a₂ - (6:R)*W.a₃) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (W.a₁^ (4 : ℕ)*W.a₂ - (6:R)*W.a₁^ (3 : ℕ)*W.a₃ + W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + (2:R)*W.a₁^ (2 : ℕ)*W.a₄ - (3:R)*W.a₁*W.a₂*W.a₃ + (2:R)*W.a₂*W.a₄ - (12:R)*W.a₃^ (2 : ℕ) - (18:R)*W.a₆) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C (W.a₁^ (3 : ℕ)*W.a₄ + W.a₁*W.a₂*W.a₄ - (3:R)*W.a₁*W.a₃^ (2 : ℕ) - (9:R)*W.a₁*W.a₆) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 0)
    + C ((2:R)*W.a₁^ (2 : ℕ)*W.a₄ + (2:R)*W.a₂*W.a₄ - (6:R)*W.a₃^ (2 : ℕ) - (18:R)*W.a₆) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 1)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₄ + (6:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - W.a₁*W.a₂^ (2 : ℕ)*W.a₄ - W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (3:R)*W.a₁*W.a₂*W.a₆ + (4:R)*W.a₁*W.a₄^ (2 : ℕ) + (2:R)*W.a₂*W.a₃*W.a₄ - (6:R)*W.a₃^ (3 : ℕ) - (18:R)*W.a₃*W.a₆) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 2)
    + C (-(5:R)*W.a₁^ (2 : ℕ) - (2:R)*W.a₂) * (Xl 1)^ (3 : ℕ)*(Xl 2)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ) - W.a₁*W.a₂) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C (-(2:R)*W.a₁^ (2 : ℕ) - (2:R)*W.a₂) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (W.a₁^ (3 : ℕ)*W.a₂ - (10:R)*W.a₁^ (2 : ℕ)*W.a₃ + W.a₁*W.a₂^ (2 : ℕ) - (3:R)*W.a₁*W.a₄ - (4:R)*W.a₂*W.a₃) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₃ - W.a₁*W.a₂*W.a₃) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 0)
    + C (-(2:R)*W.a₁^ (2 : ℕ)*W.a₃ - (2:R)*W.a₂*W.a₃) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 1)
    + C (W.a₁^ (3 : ℕ)*W.a₂*W.a₃ - (5:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (3:R)*W.a₁^ (2 : ℕ)*W.a₆ + W.a₁*W.a₂^ (2 : ℕ)*W.a₃ - W.a₁*W.a₃*W.a₄ - (4:R)*W.a₂*W.a₃^ (2 : ℕ) - (6:R)*W.a₂*W.a₆ + (2:R)*W.a₄^ (2 : ℕ)) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 2)
    + C (W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (3:R)*W.a₁*W.a₂*W.a₆ + W.a₁*W.a₄^ (2 : ℕ)) * (Xl 2)^ (4 : ℕ)*(Xr 0)
    + C ((2:R)*W.a₁*W.a₃*W.a₄ - (2:R)*W.a₂*W.a₃^ (2 : ℕ) - (6:R)*W.a₂*W.a₆ + (2:R)*W.a₄^ (2 : ℕ)) * (Xl 2)^ (4 : ℕ)*(Xr 1)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₆ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₆ - W.a₁*W.a₂^ (2 : ℕ)*W.a₆ + (2:R)*W.a₁*W.a₃^ (2 : ℕ)*W.a₄ + (3:R)*W.a₁*W.a₄*W.a₆ - (2:R)*W.a₂*W.a₃^ (3 : ℕ) - (6:R)*W.a₂*W.a₃*W.a₆ + (2:R)*W.a₃*W.a₄^ (2 : ℕ)) * (Xl 2)^ (4 : ℕ)*(Xr 2)

def kw_lrSym_pXY : P₆ :=
  C (-(6:R)*W.a₁*W.a₂) * (Xl 0)*(Xr 0)^ (3 : ℕ)*(Xr 1)
    + C ((2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) - (6:R)*W.a₁*W.a₂*W.a₃ + (2:R)*W.a₂^ (3 : ℕ) - (6:R)*W.a₂*W.a₄) * (Xl 0)*(Xr 0)^ (3 : ℕ)*(Xr 2)
    + C ((3:R)*W.a₁^ (2 : ℕ) - (6:R)*W.a₂) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C (-(3:R)*W.a₁^ (3 : ℕ)*W.a₂ - (3:R)*W.a₁*W.a₂^ (2 : ℕ) - (3:R)*W.a₁*W.a₄ - (6:R)*W.a₂*W.a₃) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (W.a₁^ (3 : ℕ)*W.a₂*W.a₃ + (4:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄ - (3:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) + W.a₁*W.a₂^ (2 : ℕ)*W.a₃ - (9:R)*W.a₁*W.a₃*W.a₄ + (4:R)*W.a₂^ (2 : ℕ)*W.a₄ - (6:R)*W.a₂*W.a₃^ (2 : ℕ) - (18:R)*W.a₂*W.a₆ - (6:R)*W.a₄^ (2 : ℕ)) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C ((3:R)*W.a₁) * (Xl 0)*(Xr 0)*(Xr 1)^ (3 : ℕ)
    + C (W.a₁^ (4 : ℕ) - W.a₁^ (2 : ℕ)*W.a₂ - (2:R)*W.a₂^ (2 : ℕ) - (6:R)*W.a₄) * (Xl 0)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (-W.a₁^ (4 : ℕ)*W.a₃ - (3:R)*W.a₁^ (3 : ℕ)*W.a₄ - (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ - (3:R)*W.a₁*W.a₂*W.a₄ + (9:R)*W.a₁*W.a₆ - (2:R)*W.a₂^ (2 : ℕ)*W.a₃ - (6:R)*W.a₃*W.a₄) * (Xl 0)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₃*W.a₄ + (2:R)*W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) + (3:R)*W.a₁*W.a₂*W.a₃*W.a₄ - (3:R)*W.a₁*W.a₃^ (3 : ℕ) - (9:R)*W.a₁*W.a₃*W.a₆ - (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (6:R)*W.a₂^ (2 : ℕ)*W.a₆ + (4:R)*W.a₂*W.a₄^ (2 : ℕ) - (6:R)*W.a₃^ (2 : ℕ)*W.a₄ - (18:R)*W.a₄*W.a₆) * (Xl 0)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C (W.a₁^ (3 : ℕ) + W.a₁*W.a₂) * (Xl 0)*(Xr 1)^ (3 : ℕ)*(Xr 2)
    + C (-(2:R)*W.a₁^ (2 : ℕ)*W.a₄ - (2:R)*W.a₂*W.a₄) * (Xl 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁^ (3 : ℕ)*W.a₃^ (2 : ℕ) - (3:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + (3:R)*W.a₁*W.a₂*W.a₆ - W.a₁*W.a₄^ (2 : ℕ) - (2:R)*W.a₂*W.a₃*W.a₄) * (Xl 0)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C (W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₄ - W.a₁*W.a₂*W.a₃^ (3 : ℕ) - (3:R)*W.a₁*W.a₂*W.a₃*W.a₆ + (3:R)*W.a₁*W.a₃*W.a₄^ (2 : ℕ) - (2:R)*W.a₂*W.a₃^ (2 : ℕ)*W.a₄ - (6:R)*W.a₂*W.a₄*W.a₆ + (2:R)*W.a₄^ (3 : ℕ)) * (Xl 0)*(Xr 2)^ (4 : ℕ)
    + C ((6:R)*W.a₁*W.a₂) * (Xl 1)*(Xr 0)^ (4 : ℕ)
    + C (-W.a₁^ (3 : ℕ)*W.a₂ + (6:R)*W.a₁^ (2 : ℕ)*W.a₃ + (5:R)*W.a₁*W.a₂^ (2 : ℕ) + (9:R)*W.a₁*W.a₄) * (Xl 1)*(Xr 0)^ (3 : ℕ)*(Xr 2)
    + C ((9:R)*W.a₁) * (Xl 1)*(Xr 0)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C (W.a₁^ (4 : ℕ) - (10:R)*W.a₁^ (2 : ℕ)*W.a₂ + (9:R)*W.a₁*W.a₃ - (2:R)*W.a₂^ (2 : ℕ) + (6:R)*W.a₄) * (Xl 1)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₄ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ + (11:R)*W.a₁*W.a₂*W.a₄ + (3:R)*W.a₁*W.a₃^ (2 : ℕ) + (9:R)*W.a₁*W.a₆) * (Xl 1)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C ((6:R)) * (Xl 1)*(Xr 0)*(Xr 1)^ (3 : ℕ)
    + C ((6:R)*W.a₁^ (3 : ℕ) - (3:R)*W.a₁*W.a₂ + (6:R)*W.a₃) * (Xl 1)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (-(2:R)*W.a₁^ (3 : ℕ)*W.a₃ - (11:R)*W.a₁^ (2 : ℕ)*W.a₄ - (5:R)*W.a₁*W.a₂*W.a₃ - (2:R)*W.a₂*W.a₄ + (6:R)*W.a₃^ (2 : ℕ) + (18:R)*W.a₆) * (Xl 1)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C ((2:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + W.a₁*W.a₂*W.a₃^ (2 : ℕ) + (9:R)*W.a₁*W.a₂*W.a₆ + (5:R)*W.a₁*W.a₄^ (2 : ℕ)) * (Xl 1)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C ((5:R)*W.a₁^ (2 : ℕ) + (2:R)*W.a₂) * (Xl 1)*(Xr 1)^ (3 : ℕ)*(Xr 2)
    + C ((2:R)*W.a₁^ (2 : ℕ)*W.a₃ - (6:R)*W.a₁*W.a₄ + (2:R)*W.a₂*W.a₃) * (Xl 1)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-(3:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (3:R)*W.a₁^ (2 : ℕ)*W.a₆ - (8:R)*W.a₁*W.a₃*W.a₄ + (2:R)*W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₂*W.a₆ - (2:R)*W.a₄^ (2 : ℕ)) * (Xl 1)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C ((3:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₆ + (6:R)*W.a₁*W.a₄*W.a₆) * (Xl 1)*(Xr 2)^ (4 : ℕ)
    + C (-(2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + (6:R)*W.a₁*W.a₂*W.a₃ - (2:R)*W.a₂^ (3 : ℕ) + (6:R)*W.a₂*W.a₄) * (Xl 2)*(Xr 0)^ (4 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₂ - (6:R)*W.a₁^ (2 : ℕ)*W.a₃ + W.a₁*W.a₂^ (2 : ℕ) - (9:R)*W.a₁*W.a₄) * (Xl 2)*(Xr 0)^ (3 : ℕ)*(Xr 1)
    + C (-(2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (3 : ℕ) + (6:R)*W.a₁*W.a₂^ (2 : ℕ)*W.a₃ - (2:R)*W.a₂^ (4 : ℕ) + (6:R)*W.a₂^ (2 : ℕ)*W.a₄) * (Xl 2)*(Xr 0)^ (3 : ℕ)*(Xr 2)
    + C (-(3:R)*W.a₁*W.a₃ - (6:R)*W.a₄) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C (-W.a₁^ (4 : ℕ)*W.a₃ + (3:R)*W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ) - (2:R)*W.a₁^ (3 : ℕ)*W.a₄ - (10:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ + (3:R)*W.a₁*W.a₂^ (3 : ℕ) - (11:R)*W.a₁*W.a₂*W.a₄ - (9:R)*W.a₁*W.a₃^ (2 : ℕ) - (18:R)*W.a₁*W.a₆ - (6:R)*W.a₃*W.a₄) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ)*W.a₃ + W.a₁^ (3 : ℕ)*W.a₃*W.a₄ - (4:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₄ + (5:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ + (2:R)*W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) - W.a₁*W.a₂^ (3 : ℕ)*W.a₃ + (16:R)*W.a₁*W.a₂*W.a₃*W.a₄ - (9:R)*W.a₁*W.a₃^ (3 : ℕ) - (27:R)*W.a₁*W.a₃*W.a₆ - (4:R)*W.a₂^ (3 : ℕ)*W.a₄ + (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (6:R)*W.a₂^ (2 : ℕ)*W.a₆ + (14:R)*W.a₂*W.a₄^ (2 : ℕ) - (12:R)*W.a₃^ (2 : ℕ)*W.a₄ - (36:R)*W.a₄*W.a₆) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁^ (4 : ℕ)*W.a₂ + (2:R)*W.a₁^ (3 : ℕ)*W.a₃ + W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + W.a₁^ (2 : ℕ)*W.a₄ - (7:R)*W.a₁*W.a₂*W.a₃ + (2:R)*W.a₂^ (3 : ℕ) - (8:R)*W.a₂*W.a₄ - (6:R)*W.a₃^ (2 : ℕ) - (18:R)*W.a₆) * (Xl 2)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (W.a₁^ (4 : ℕ)*W.a₂*W.a₃ + (3:R)*W.a₁^ (3 : ℕ)*W.a₂*W.a₄ - (6:R)*W.a₁^ (3 : ℕ)*W.a₃^ (2 : ℕ) - (6:R)*W.a₁^ (3 : ℕ)*W.a₆ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₃ - (14:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + (3:R)*W.a₁*W.a₂^ (2 : ℕ)*W.a₄ - (9:R)*W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (6:R)*W.a₁*W.a₂*W.a₆ - (9:R)*W.a₁*W.a₄^ (2 : ℕ) + (2:R)*W.a₂^ (3 : ℕ)*W.a₃ - (8:R)*W.a₂*W.a₃*W.a₄ - (6:R)*W.a₃^ (3 : ℕ) - (18:R)*W.a₃*W.a₆) * (Xl 2)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₃*W.a₄ - (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₆ - (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄^ (2 : ℕ) + (6:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₄ + (6:R)*W.a₁^ (2 : ℕ)*W.a₄*W.a₆ - W.a₁*W.a₂^ (2 : ℕ)*W.a₃*W.a₄ - W.a₁*W.a₂*W.a₃^ (3 : ℕ) + (3:R)*W.a₁*W.a₂*W.a₃*W.a₆ + (12:R)*W.a₁*W.a₃*W.a₄^ (2 : ℕ) - (2:R)*W.a₂^ (3 : ℕ)*W.a₆ - (2:R)*W.a₂^ (2 : ℕ)*W.a₄^ (2 : ℕ) + (6:R)*W.a₂*W.a₄*W.a₆ - (6:R)*W.a₃^ (4 : ℕ) - (36:R)*W.a₃^ (2 : ℕ)*W.a₆ + (8:R)*W.a₄^ (3 : ℕ) - (54:R)*W.a₆^ (2 : ℕ)) * (Xl 2)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C (-W.a₁^ (3 : ℕ)*W.a₂ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃ - W.a₁*W.a₂^ (2 : ℕ) + (3:R)*W.a₁*W.a₄) * (Xl 2)*(Xr 1)^ (3 : ℕ)*(Xr 2)
    + C ((2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄ - (2:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (6:R)*W.a₁^ (2 : ℕ)*W.a₆ - (6:R)*W.a₁*W.a₃*W.a₄ + (2:R)*W.a₂^ (2 : ℕ)*W.a₄ - (2:R)*W.a₂*W.a₃^ (2 : ℕ) - (6:R)*W.a₂*W.a₆ - (6:R)*W.a₄^ (2 : ℕ)) * (Xl 2)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) + W.a₁^ (3 : ℕ)*W.a₂*W.a₆ + (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃*W.a₄ - (5:R)*W.a₁^ (2 : ℕ)*W.a₃^ (3 : ℕ) - (9:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₆ + W.a₁*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + W.a₁*W.a₂^ (2 : ℕ)*W.a₆ - (9:R)*W.a₁*W.a₃^ (2 : ℕ)*W.a₄ - (3:R)*W.a₁*W.a₄*W.a₆ + (2:R)*W.a₂^ (2 : ℕ)*W.a₃*W.a₄ - (2:R)*W.a₂*W.a₃^ (3 : ℕ) - (6:R)*W.a₂*W.a₃*W.a₆ - (6:R)*W.a₃*W.a₄^ (2 : ℕ)) * (Xl 2)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₃*W.a₆ - (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄*W.a₆ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₆ - W.a₁*W.a₂^ (2 : ℕ)*W.a₃*W.a₆ + (2:R)*W.a₁*W.a₃^ (3 : ℕ)*W.a₄ + (15:R)*W.a₁*W.a₃*W.a₄*W.a₆ - (2:R)*W.a₂^ (2 : ℕ)*W.a₄*W.a₆ - (2:R)*W.a₂*W.a₃^ (4 : ℕ) - (12:R)*W.a₂*W.a₃^ (2 : ℕ)*W.a₆ - (18:R)*W.a₂*W.a₆^ (2 : ℕ) + (2:R)*W.a₃^ (2 : ℕ)*W.a₄^ (2 : ℕ) + (12:R)*W.a₄^ (2 : ℕ)*W.a₆) * (Xl 2)*(Xr 2)^ (4 : ℕ)

def kw_lrSym_qXY : P₆ :=
  C (-(3:R)*W.a₁^ (2 : ℕ) + (6:R)*W.a₂) * (Xl 0)^ (2 : ℕ)*(Xl 1)^ (2 : ℕ)*(Xr 0)
    + C (-(9:R)*W.a₁) * (Xl 0)^ (2 : ℕ)*(Xl 1)^ (2 : ℕ)*(Xr 1)
    + C ((3:R)*W.a₁*W.a₃ + (6:R)*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xl 1)^ (2 : ℕ)*(Xr 2)
    + C ((3:R)*W.a₁^ (3 : ℕ)*W.a₂ - (3:R)*W.a₁*W.a₂^ (2 : ℕ) + (3:R)*W.a₁*W.a₄ + (6:R)*W.a₂*W.a₃) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 0)
    + C (-W.a₁^ (4 : ℕ) + (4:R)*W.a₁^ (2 : ℕ)*W.a₂ - (9:R)*W.a₁*W.a₃ + (2:R)*W.a₂^ (2 : ℕ) - (6:R)*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 1)
    + C (W.a₁^ (4 : ℕ)*W.a₃ + (2:R)*W.a₁^ (3 : ℕ)*W.a₄ - (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ - (4:R)*W.a₁*W.a₂*W.a₄ + (9:R)*W.a₁*W.a₃^ (2 : ℕ) + (18:R)*W.a₁*W.a₆ + (6:R)*W.a₃*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₃ + (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (3 : ℕ) - (4:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (7:R)*W.a₁*W.a₂^ (2 : ℕ)*W.a₃ + (9:R)*W.a₁*W.a₃*W.a₄ + (2:R)*W.a₂^ (4 : ℕ) - (10:R)*W.a₂^ (2 : ℕ)*W.a₄ + (6:R)*W.a₂*W.a₃^ (2 : ℕ) + (18:R)*W.a₂*W.a₆ + (6:R)*W.a₄^ (2 : ℕ)) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C (-W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ) + W.a₁^ (3 : ℕ)*W.a₄ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ - W.a₁*W.a₂^ (3 : ℕ) + (4:R)*W.a₁*W.a₂*W.a₄ - (3:R)*W.a₁*W.a₃^ (2 : ℕ) - (9:R)*W.a₁*W.a₆) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ)*W.a₃ - W.a₁^ (3 : ℕ)*W.a₃*W.a₄ + (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₄ - (5:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) - (6:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ - (2:R)*W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) + W.a₁*W.a₂^ (3 : ℕ)*W.a₃ - (10:R)*W.a₁*W.a₂*W.a₃*W.a₄ + (9:R)*W.a₁*W.a₃^ (3 : ℕ) + (27:R)*W.a₁*W.a₃*W.a₆ + (2:R)*W.a₂^ (3 : ℕ)*W.a₄ - (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (6:R)*W.a₂^ (2 : ℕ)*W.a₆ - (8:R)*W.a₂*W.a₄^ (2 : ℕ) + (12:R)*W.a₃^ (2 : ℕ)*W.a₄ + (36:R)*W.a₄*W.a₆) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C (-(3:R)*W.a₁) * (Xl 0)*(Xl 1)^ (3 : ℕ)*(Xr 0)
    + C (-(6:R)) * (Xl 0)*(Xl 1)^ (3 : ℕ)*(Xr 1)
    + C (-W.a₁^ (4 : ℕ) + (7:R)*W.a₁^ (2 : ℕ)*W.a₂ + (2:R)*W.a₂^ (2 : ℕ) + (6:R)*W.a₄) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 0)
    + C (-(6:R)*W.a₁^ (3 : ℕ) - (3:R)*W.a₁*W.a₂ - (6:R)*W.a₃) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 1)
    + C ((4:R)*W.a₁^ (3 : ℕ)*W.a₃ + (8:R)*W.a₁^ (2 : ℕ)*W.a₄ + W.a₁*W.a₂*W.a₃ + (2:R)*W.a₂*W.a₄ + (6:R)*W.a₃^ (2 : ℕ) + (18:R)*W.a₆) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 2)
    + C (W.a₁^ (4 : ℕ)*W.a₃ - (2:R)*W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ) + (3:R)*W.a₁^ (3 : ℕ)*W.a₄ + (9:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ - (2:R)*W.a₁*W.a₂^ (3 : ℕ) + (3:R)*W.a₁*W.a₂*W.a₄ - (9:R)*W.a₁*W.a₆ + (2:R)*W.a₂^ (2 : ℕ)*W.a₃ + (6:R)*W.a₃*W.a₄) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C (W.a₁^ (4 : ℕ)*W.a₂ - (4:R)*W.a₁^ (3 : ℕ)*W.a₃ + W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + (2:R)*W.a₁^ (2 : ℕ)*W.a₄ - W.a₁*W.a₂*W.a₃ + (2:R)*W.a₂*W.a₄ - (6:R)*W.a₃^ (2 : ℕ) - (18:R)*W.a₆) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (-W.a₁^ (4 : ℕ)*W.a₂*W.a₃ - (2:R)*W.a₁^ (3 : ℕ)*W.a₂*W.a₄ + (6:R)*W.a₁^ (3 : ℕ)*W.a₃^ (2 : ℕ) + (6:R)*W.a₁^ (3 : ℕ)*W.a₆ - W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₃ + (8:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - (2:R)*W.a₁*W.a₂^ (2 : ℕ)*W.a₄ + (3:R)*W.a₁*W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₁*W.a₂*W.a₆ + (2:R)*W.a₂*W.a₃*W.a₄ + (6:R)*W.a₃^ (3 : ℕ) + (18:R)*W.a₃*W.a₆) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₃*W.a₄ + (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₄ - (2:R)*W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) - (9:R)*W.a₁*W.a₂*W.a₃*W.a₄ + (3:R)*W.a₁*W.a₃^ (3 : ℕ) + (9:R)*W.a₁*W.a₃*W.a₆ + (2:R)*W.a₂^ (3 : ℕ)*W.a₄ + (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (6:R)*W.a₂^ (2 : ℕ)*W.a₆ - (10:R)*W.a₂*W.a₄^ (2 : ℕ) + (6:R)*W.a₃^ (2 : ℕ)*W.a₄ + (18:R)*W.a₄*W.a₆) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 0)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₄ + (4:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - W.a₁*W.a₂^ (2 : ℕ)*W.a₄ - W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (3:R)*W.a₁*W.a₂*W.a₆ + (4:R)*W.a₁*W.a₄^ (2 : ℕ)) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 1)
    + C (W.a₁^ (3 : ℕ)*W.a₂*W.a₃*W.a₄ + (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄^ (2 : ℕ) - (6:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₄ - (6:R)*W.a₁^ (2 : ℕ)*W.a₄*W.a₆ + W.a₁*W.a₂^ (2 : ℕ)*W.a₃*W.a₄ + W.a₁*W.a₂*W.a₃^ (3 : ℕ) + (3:R)*W.a₁*W.a₂*W.a₃*W.a₆ - (12:R)*W.a₁*W.a₃*W.a₄^ (2 : ℕ) + (2:R)*W.a₂^ (2 : ℕ)*W.a₄^ (2 : ℕ) + (6:R)*W.a₃^ (4 : ℕ) + (36:R)*W.a₃^ (2 : ℕ)*W.a₆ - (8:R)*W.a₄^ (3 : ℕ) + (54:R)*W.a₆^ (2 : ℕ)) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ) + (5:R)*W.a₁*W.a₂) * (Xl 1)^ (3 : ℕ)*(Xl 2)*(Xr 0)
    + C (-(5:R)*W.a₁^ (2 : ℕ) - (2:R)*W.a₂) * (Xl 1)^ (3 : ℕ)*(Xl 2)*(Xr 1)
    + C ((3:R)*W.a₁^ (2 : ℕ)*W.a₃ + (6:R)*W.a₁*W.a₄) * (Xl 1)^ (3 : ℕ)*(Xl 2)*(Xr 2)
    + C (-(2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + (2:R)*W.a₁^ (2 : ℕ)*W.a₄ + (12:R)*W.a₁*W.a₂*W.a₃ - (2:R)*W.a₂^ (3 : ℕ) + (8:R)*W.a₂*W.a₄) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C (W.a₁^ (3 : ℕ)*W.a₂ - (8:R)*W.a₁^ (2 : ℕ)*W.a₃ + W.a₁*W.a₂^ (2 : ℕ) - (3:R)*W.a₁*W.a₄ - (2:R)*W.a₂*W.a₃) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₃ - (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄ + (8:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (6:R)*W.a₁^ (2 : ℕ)*W.a₆ - W.a₁*W.a₂^ (2 : ℕ)*W.a₃ + (15:R)*W.a₁*W.a₃*W.a₄ - (2:R)*W.a₂^ (2 : ℕ)*W.a₄ + (2:R)*W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₂*W.a₆ + (6:R)*W.a₄^ (2 : ℕ)) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C (W.a₁^ (3 : ℕ)*W.a₃^ (2 : ℕ) - (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₃ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + (6:R)*W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (9:R)*W.a₁*W.a₂*W.a₆ + W.a₁*W.a₄^ (2 : ℕ) - (2:R)*W.a₂^ (3 : ℕ)*W.a₃ + (8:R)*W.a₂*W.a₃*W.a₄) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 0)
    + C (W.a₁^ (3 : ℕ)*W.a₂*W.a₃ - (3:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (3:R)*W.a₁^ (2 : ℕ)*W.a₆ + W.a₁*W.a₂^ (2 : ℕ)*W.a₃ - W.a₁*W.a₃*W.a₄ - (2:R)*W.a₂*W.a₃^ (2 : ℕ) - (6:R)*W.a₂*W.a₆ + (2:R)*W.a₄^ (2 : ℕ)) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 1)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) - (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃*W.a₄ + (5:R)*W.a₁^ (2 : ℕ)*W.a₃^ (3 : ℕ) + (3:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₆ - W.a₁*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (9:R)*W.a₁*W.a₃^ (2 : ℕ)*W.a₄ - (6:R)*W.a₁*W.a₄*W.a₆ - (2:R)*W.a₂^ (2 : ℕ)*W.a₃*W.a₄ + (2:R)*W.a₂*W.a₃^ (3 : ℕ) + (6:R)*W.a₂*W.a₃*W.a₆ + (6:R)*W.a₃*W.a₄^ (2 : ℕ)) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 2)
    + C ((2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₆ - W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₄ + W.a₁*W.a₂*W.a₃^ (3 : ℕ) - (3:R)*W.a₁*W.a₂*W.a₃*W.a₆ - (3:R)*W.a₁*W.a₃*W.a₄^ (2 : ℕ) + (2:R)*W.a₂^ (3 : ℕ)*W.a₆ + (2:R)*W.a₂*W.a₃^ (2 : ℕ)*W.a₄ - (2:R)*W.a₄^ (3 : ℕ)) * (Xl 2)^ (4 : ℕ)*(Xr 0)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₆ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₆ - W.a₁*W.a₂^ (2 : ℕ)*W.a₆ + (3:R)*W.a₁*W.a₄*W.a₆) * (Xl 2)^ (4 : ℕ)*(Xr 1)
    + C (W.a₁^ (3 : ℕ)*W.a₂*W.a₃*W.a₆ + (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄*W.a₆ - (3:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₆ + W.a₁*W.a₂^ (2 : ℕ)*W.a₃*W.a₆ - (2:R)*W.a₁*W.a₃^ (3 : ℕ)*W.a₄ - (15:R)*W.a₁*W.a₃*W.a₄*W.a₆ + (2:R)*W.a₂^ (2 : ℕ)*W.a₄*W.a₆ + (2:R)*W.a₂*W.a₃^ (4 : ℕ) + (12:R)*W.a₂*W.a₃^ (2 : ℕ)*W.a₆ + (18:R)*W.a₂*W.a₆^ (2 : ℕ) - (2:R)*W.a₃^ (2 : ℕ)*W.a₄^ (2 : ℕ) - (12:R)*W.a₄^ (2 : ℕ)*W.a₆) * (Xl 2)^ (4 : ℕ)*(Xr 2)

def kw_lrSym_pYZ : P₆ :=
  C (-(18:R)*W.a₁) * (Xl 0)*(Xr 0)^ (3 : ℕ)*(Xr 1)
    + C ((6:R)*W.a₁^ (2 : ℕ)*W.a₂ - (18:R)*W.a₁*W.a₃ + (6:R)*W.a₂^ (2 : ℕ) - (18:R)*W.a₄) * (Xl 0)*(Xr 0)^ (3 : ℕ)*(Xr 2)
    + C (-(18:R)) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C (-(9:R)*W.a₁^ (3 : ℕ) - (12:R)*W.a₁*W.a₂ - (18:R)*W.a₃) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (W.a₁^ (4 : ℕ)*W.a₂ - (3:R)*W.a₁^ (3 : ℕ)*W.a₃ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + (3:R)*W.a₁^ (2 : ℕ)*W.a₄ - (6:R)*W.a₁*W.a₂*W.a₃ + (2:R)*W.a₂^ (3 : ℕ) - (18:R)*W.a₃^ (2 : ℕ) - (54:R)*W.a₆) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-(9:R)*W.a₁^ (2 : ℕ) - (12:R)*W.a₂) * (Xl 0)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (-W.a₁^ (5 : ℕ) - (3:R)*W.a₁^ (3 : ℕ)*W.a₂ - (9:R)*W.a₁^ (2 : ℕ)*W.a₃ - (2:R)*W.a₁*W.a₂^ (2 : ℕ) - (12:R)*W.a₂*W.a₃) * (Xl 0)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (4 : ℕ)*W.a₄ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄ - (3:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (9:R)*W.a₁^ (2 : ℕ)*W.a₆ + (6:R)*W.a₁*W.a₃*W.a₄ + (2:R)*W.a₂^ (2 : ℕ)*W.a₄ - (12:R)*W.a₂*W.a₃^ (2 : ℕ) - (36:R)*W.a₂*W.a₆ + (6:R)*W.a₄^ (2 : ℕ)) * (Xl 0)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C (-W.a₁^ (4 : ℕ) - (3:R)*W.a₁^ (2 : ℕ)*W.a₂ - (2:R)*W.a₂^ (2 : ℕ)) * (Xl 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁^ (4 : ℕ)*W.a₃ - (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ - (2:R)*W.a₂^ (2 : ℕ)*W.a₃) * (Xl 0)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₃*W.a₄ - W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) - (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ + W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) + (2:R)*W.a₁*W.a₂*W.a₃*W.a₄ - (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (6:R)*W.a₂^ (2 : ℕ)*W.a₆ + (2:R)*W.a₂*W.a₄^ (2 : ℕ)) * (Xl 0)*(Xr 2)^ (4 : ℕ)
    + C ((18:R)*W.a₁) * (Xl 1)*(Xr 0)^ (4 : ℕ)
    + C ((3:R)*W.a₁^ (3 : ℕ) + (24:R)*W.a₁*W.a₂) * (Xl 1)*(Xr 0)^ (3 : ℕ)*(Xr 2)
    + C (-(21:R)*W.a₁^ (2 : ℕ)) * (Xl 1)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C ((4:R)*W.a₁^ (3 : ℕ)*W.a₂ - (3:R)*W.a₁^ (2 : ℕ)*W.a₃ + (7:R)*W.a₁*W.a₂^ (2 : ℕ) + (15:R)*W.a₁*W.a₄) * (Xl 1)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-(21:R)*W.a₁) * (Xl 1)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (-(4:R)*W.a₁^ (4 : ℕ) - (7:R)*W.a₁^ (2 : ℕ)*W.a₂ - (21:R)*W.a₁*W.a₃) * (Xl 1)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C ((4:R)*W.a₁^ (3 : ℕ)*W.a₄ + (7:R)*W.a₁*W.a₂*W.a₄ - (3:R)*W.a₁*W.a₃^ (2 : ℕ) + (9:R)*W.a₁*W.a₆) * (Xl 1)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C (-(4:R)*W.a₁^ (3 : ℕ) - (7:R)*W.a₁*W.a₂) * (Xl 1)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-(4:R)*W.a₁^ (3 : ℕ)*W.a₃ - (7:R)*W.a₁*W.a₂*W.a₃) * (Xl 1)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C ((3:R)*W.a₁^ (3 : ℕ)*W.a₆ + W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - W.a₁*W.a₂*W.a₃^ (2 : ℕ) + (3:R)*W.a₁*W.a₂*W.a₆ + W.a₁*W.a₄^ (2 : ℕ)) * (Xl 1)*(Xr 2)^ (4 : ℕ)
    + C (-(6:R)*W.a₁^ (2 : ℕ)*W.a₂ + (18:R)*W.a₁*W.a₃ - (6:R)*W.a₂^ (2 : ℕ) + (18:R)*W.a₄) * (Xl 2)*(Xr 0)^ (4 : ℕ)
    + C (-(3:R)*W.a₁^ (3 : ℕ) - (6:R)*W.a₁*W.a₂) * (Xl 2)*(Xr 0)^ (3 : ℕ)*(Xr 1)
    + C (-(6:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + (18:R)*W.a₁*W.a₂*W.a₃ - (6:R)*W.a₂^ (3 : ℕ) + (18:R)*W.a₂*W.a₄) * (Xl 2)*(Xr 0)^ (3 : ℕ)*(Xr 2)
    + C (-(6:R)*W.a₁^ (2 : ℕ) - (6:R)*W.a₂) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C (-W.a₁^ (5 : ℕ) + (4:R)*W.a₁^ (3 : ℕ)*W.a₂ - (30:R)*W.a₁^ (2 : ℕ)*W.a₃ + (5:R)*W.a₁*W.a₂^ (2 : ℕ) - (27:R)*W.a₁*W.a₄ - (6:R)*W.a₂*W.a₃) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (-W.a₁^ (4 : ℕ)*W.a₂^ (2 : ℕ) + W.a₁^ (4 : ℕ)*W.a₄ + (5:R)*W.a₁^ (3 : ℕ)*W.a₂*W.a₃ - (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (3 : ℕ) + (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄ - (9:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (9:R)*W.a₁^ (2 : ℕ)*W.a₆ + (8:R)*W.a₁*W.a₂^ (2 : ℕ)*W.a₃ + (6:R)*W.a₁*W.a₃*W.a₄ - (2:R)*W.a₂^ (4 : ℕ) + (4:R)*W.a₂^ (2 : ℕ)*W.a₄ - (6:R)*W.a₂*W.a₃^ (2 : ℕ) - (18:R)*W.a₂*W.a₆ + (12:R)*W.a₄^ (2 : ℕ)) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-(3:R)*W.a₁) * (Xl 2)*(Xr 0)*(Xr 1)^ (3 : ℕ)
    + C (-(2:R)*W.a₁^ (4 : ℕ) + (2:R)*W.a₁^ (2 : ℕ)*W.a₂ - (27:R)*W.a₁*W.a₃ + (4:R)*W.a₂^ (2 : ℕ) - (24:R)*W.a₄) * (Xl 2)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (W.a₁^ (5 : ℕ)*W.a₂ - (6:R)*W.a₁^ (4 : ℕ)*W.a₃ + (3:R)*W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ) - (4:R)*W.a₁^ (3 : ℕ)*W.a₄ - (5:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ + (2:R)*W.a₁*W.a₂^ (3 : ℕ) - (7:R)*W.a₁*W.a₂*W.a₄ - (27:R)*W.a₁*W.a₃^ (2 : ℕ) - (9:R)*W.a₁*W.a₆ + (4:R)*W.a₂^ (2 : ℕ)*W.a₃ - (24:R)*W.a₃*W.a₄) * (Xl 2)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁^ (4 : ℕ)*W.a₂*W.a₄ + (6:R)*W.a₁^ (3 : ℕ)*W.a₃*W.a₄ - (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₄ - W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) - (9:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ + (6:R)*W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) + (10:R)*W.a₁*W.a₂*W.a₃*W.a₄ - (6:R)*W.a₁*W.a₃^ (3 : ℕ) - (2:R)*W.a₂^ (3 : ℕ)*W.a₄ - (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (12:R)*W.a₂^ (2 : ℕ)*W.a₆ + (10:R)*W.a₂*W.a₄^ (2 : ℕ) - (6:R)*W.a₃^ (2 : ℕ)*W.a₄) * (Xl 2)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C (-W.a₁^ (3 : ℕ) - W.a₁*W.a₂) * (Xl 2)*(Xr 1)^ (3 : ℕ)*(Xr 2)
    + C (W.a₁^ (4 : ℕ)*W.a₂ - (6:R)*W.a₁^ (3 : ℕ)*W.a₃ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) - (5:R)*W.a₁^ (2 : ℕ)*W.a₄ - (9:R)*W.a₁*W.a₂*W.a₃ + (2:R)*W.a₂^ (3 : ℕ) - (8:R)*W.a₂*W.a₄) * (Xl 2)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (4 : ℕ)*W.a₂*W.a₃ - (5:R)*W.a₁^ (3 : ℕ)*W.a₃^ (2 : ℕ) + (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₃ - (4:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - (9:R)*W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (3:R)*W.a₁*W.a₂*W.a₆ + W.a₁*W.a₄^ (2 : ℕ) + (2:R)*W.a₂^ (3 : ℕ)*W.a₃ - (8:R)*W.a₂*W.a₃*W.a₄) * (Xl 2)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C (-W.a₁^ (4 : ℕ)*W.a₂*W.a₆ + (3:R)*W.a₁^ (3 : ℕ)*W.a₃*W.a₆ - (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₆ + (2:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₄ + (3:R)*W.a₁^ (2 : ℕ)*W.a₄*W.a₆ - (2:R)*W.a₁*W.a₂*W.a₃^ (3 : ℕ) + (4:R)*W.a₁*W.a₃*W.a₄^ (2 : ℕ) - (2:R)*W.a₂^ (3 : ℕ)*W.a₆ - (2:R)*W.a₂*W.a₃^ (2 : ℕ)*W.a₄ + (2:R)*W.a₄^ (3 : ℕ)) * (Xl 2)*(Xr 2)^ (4 : ℕ)

def kw_lrSym_qYZ : P₆ :=
  C ((18:R)) * (Xl 0)^ (2 : ℕ)*(Xl 1)^ (2 : ℕ)*(Xr 0)
    + C ((6:R)*W.a₁^ (2 : ℕ) + (6:R)*W.a₂) * (Xl 0)^ (2 : ℕ)*(Xl 1)^ (2 : ℕ)*(Xr 2)
    + C ((9:R)*W.a₁^ (3 : ℕ) - (6:R)*W.a₁*W.a₂ + (18:R)*W.a₃) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 0)
    + C ((3:R)*W.a₁^ (2 : ℕ)) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 1)
    + C (W.a₁^ (5 : ℕ) - W.a₁^ (3 : ℕ)*W.a₂ + (12:R)*W.a₁^ (2 : ℕ)*W.a₃ - (5:R)*W.a₁*W.a₂^ (2 : ℕ) + (9:R)*W.a₁*W.a₄ + (6:R)*W.a₂*W.a₃) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 2)
    + C (-W.a₁^ (4 : ℕ)*W.a₂ + (3:R)*W.a₁^ (3 : ℕ)*W.a₃ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) - (3:R)*W.a₁^ (2 : ℕ)*W.a₄ - (12:R)*W.a₁*W.a₂*W.a₃ + (4:R)*W.a₂^ (3 : ℕ) - (18:R)*W.a₂*W.a₄ + (18:R)*W.a₃^ (2 : ℕ) + (54:R)*W.a₆) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C (-W.a₁^ (3 : ℕ)*W.a₂ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃ - W.a₁*W.a₂^ (2 : ℕ) + (3:R)*W.a₁*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (W.a₁^ (4 : ℕ)*W.a₂^ (2 : ℕ) - W.a₁^ (4 : ℕ)*W.a₄ - (5:R)*W.a₁^ (3 : ℕ)*W.a₂*W.a₃ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (3 : ℕ) - (8:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄ + (9:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (9:R)*W.a₁^ (2 : ℕ)*W.a₆ - (8:R)*W.a₁*W.a₂^ (2 : ℕ)*W.a₃ + (12:R)*W.a₁*W.a₃*W.a₄ + (2:R)*W.a₂^ (4 : ℕ) - (10:R)*W.a₂^ (2 : ℕ)*W.a₄ + (6:R)*W.a₂*W.a₃^ (2 : ℕ) + (18:R)*W.a₂*W.a₆ + (6:R)*W.a₄^ (2 : ℕ)) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C ((3:R)*W.a₁) * (Xl 0)*(Xl 1)^ (3 : ℕ)*(Xr 2)
    + C ((27:R)*W.a₁^ (2 : ℕ) + (12:R)*W.a₂) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 0)
    + C ((3:R)*W.a₁) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 1)
    + C ((5:R)*W.a₁^ (4 : ℕ) + (10:R)*W.a₁^ (2 : ℕ)*W.a₂ + (9:R)*W.a₁*W.a₃ + (2:R)*W.a₂^ (2 : ℕ) + (6:R)*W.a₄) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 2)
    + C (W.a₁^ (5 : ℕ) - (3:R)*W.a₁^ (3 : ℕ)*W.a₂ + (27:R)*W.a₁^ (2 : ℕ)*W.a₃ - (4:R)*W.a₁*W.a₂^ (2 : ℕ) + (12:R)*W.a₂*W.a₃) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C (W.a₁^ (4 : ℕ) + W.a₁^ (2 : ℕ)*W.a₂ + (3:R)*W.a₁*W.a₃) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (-W.a₁^ (5 : ℕ)*W.a₂ + (6:R)*W.a₁^ (4 : ℕ)*W.a₃ - (3:R)*W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ) + W.a₁^ (3 : ℕ)*W.a₄ + (11:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ - (2:R)*W.a₁*W.a₂^ (3 : ℕ) + W.a₁*W.a₂*W.a₄ + (9:R)*W.a₁*W.a₃^ (2 : ℕ) + (9:R)*W.a₁*W.a₆ + (2:R)*W.a₂^ (2 : ℕ)*W.a₃ + (6:R)*W.a₃*W.a₄) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C (-W.a₁^ (4 : ℕ)*W.a₄ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (9:R)*W.a₁^ (2 : ℕ)*W.a₆ - (24:R)*W.a₁*W.a₃*W.a₄ + (4:R)*W.a₂^ (2 : ℕ)*W.a₄ + (12:R)*W.a₂*W.a₃^ (2 : ℕ) + (36:R)*W.a₂*W.a₆ - (24:R)*W.a₄^ (2 : ℕ)) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 0)
    + C (-W.a₁^ (3 : ℕ)*W.a₄ - W.a₁*W.a₂*W.a₄ + (3:R)*W.a₁*W.a₃^ (2 : ℕ) + (9:R)*W.a₁*W.a₆) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 1)
    + C (W.a₁^ (4 : ℕ)*W.a₂*W.a₄ - (6:R)*W.a₁^ (3 : ℕ)*W.a₃*W.a₄ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₄ + W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) + (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ - (6:R)*W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) - (10:R)*W.a₁*W.a₂*W.a₃*W.a₄ + (6:R)*W.a₁*W.a₃^ (3 : ℕ) + (18:R)*W.a₁*W.a₃*W.a₆ + (2:R)*W.a₂^ (3 : ℕ)*W.a₄ + (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (6:R)*W.a₂^ (2 : ℕ)*W.a₆ - (10:R)*W.a₂*W.a₄^ (2 : ℕ) + (6:R)*W.a₃^ (2 : ℕ)*W.a₄ + (18:R)*W.a₄*W.a₆) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 2)
    + C ((18:R)*W.a₁) * (Xl 1)^ (3 : ℕ)*(Xl 2)*(Xr 0)
    + C ((4:R)*W.a₁^ (3 : ℕ) + (7:R)*W.a₁*W.a₂) * (Xl 1)^ (3 : ℕ)*(Xl 2)*(Xr 2)
    + C (W.a₁^ (4 : ℕ) - (3:R)*W.a₁^ (2 : ℕ)*W.a₂ + (36:R)*W.a₁*W.a₃ - (4:R)*W.a₂^ (2 : ℕ) + (18:R)*W.a₄) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C (W.a₁^ (3 : ℕ) + W.a₁*W.a₂) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (-W.a₁^ (4 : ℕ)*W.a₂ + (9:R)*W.a₁^ (3 : ℕ)*W.a₃ - (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + (5:R)*W.a₁^ (2 : ℕ)*W.a₄ + (15:R)*W.a₁*W.a₂*W.a₃ - (2:R)*W.a₂^ (3 : ℕ) + (8:R)*W.a₂*W.a₄) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C (W.a₁^ (4 : ℕ)*W.a₃ - (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ + (18:R)*W.a₁*W.a₃^ (2 : ℕ) - (18:R)*W.a₁*W.a₆ - (4:R)*W.a₂^ (2 : ℕ)*W.a₃ + (18:R)*W.a₃*W.a₄) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 0)
    + C (W.a₁^ (3 : ℕ)*W.a₃ + W.a₁*W.a₂*W.a₃) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 1)
    + C (-W.a₁^ (4 : ℕ)*W.a₂*W.a₃ + (5:R)*W.a₁^ (3 : ℕ)*W.a₃^ (2 : ℕ) - (3:R)*W.a₁^ (3 : ℕ)*W.a₆ - (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₃ + (4:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + (9:R)*W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (3:R)*W.a₁*W.a₂*W.a₆ - W.a₁*W.a₄^ (2 : ℕ) - (2:R)*W.a₂^ (3 : ℕ)*W.a₃ + (8:R)*W.a₂*W.a₃*W.a₄) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₃*W.a₄ + W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) + (9:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ - W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) - (2:R)*W.a₁*W.a₂*W.a₃*W.a₄ - (18:R)*W.a₁*W.a₃*W.a₆ + (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (12:R)*W.a₂^ (2 : ℕ)*W.a₆ - (2:R)*W.a₂*W.a₄^ (2 : ℕ) - (18:R)*W.a₄*W.a₆) * (Xl 2)^ (4 : ℕ)*(Xr 0)
    + C (-W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + W.a₁*W.a₂*W.a₃^ (2 : ℕ) + (3:R)*W.a₁*W.a₂*W.a₆ - W.a₁*W.a₄^ (2 : ℕ)) * (Xl 2)^ (4 : ℕ)*(Xr 1)
    + C (W.a₁^ (4 : ℕ)*W.a₂*W.a₆ - (3:R)*W.a₁^ (3 : ℕ)*W.a₃*W.a₆ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₆ - (2:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₄ - (3:R)*W.a₁^ (2 : ℕ)*W.a₄*W.a₆ + (2:R)*W.a₁*W.a₂*W.a₃^ (3 : ℕ) - (4:R)*W.a₁*W.a₃*W.a₄^ (2 : ℕ) + (2:R)*W.a₂^ (3 : ℕ)*W.a₆ + (2:R)*W.a₂*W.a₃^ (2 : ℕ)*W.a₄ - (2:R)*W.a₄^ (3 : ℕ)) * (Xl 2)^ (4 : ℕ)*(Xr 2)

theorem kw_lrSym_minor_XZ :
    kw_lrSym_X W * kw_lrAdd_Z W - kw_lrSym_Z W * kw_lrAdd_X W
      = kw_lrSym_pXZ W * WP₁ + kw_lrSym_qXZ W * WP₂ := by
  simp only [kw_lrSym_X, kw_lrSym_Z, kw_lrAdd_X, kw_lrAdd_Y, kw_lrAdd_Z,
    kw_lrAdd_starX, kw_lrAdd_starY, kw_lrAdd_starZ, kw_lrAdd_c₂₁, kw_lrAdd_c₁₂,
    kw_lrSym_pXZ, kw_lrSym_qXZ, kw_lrAdd_WP₁, kw_lrAdd_WP₂,
    WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, rename_X, rename_C,
    MvPolynomial.algebraMap_eq]
  ring

theorem kw_lrSym_minor_XZ_mem_span :
    kw_lrSym_X W * kw_lrAdd_Z W - kw_lrSym_Z W * kw_lrAdd_X W
      ∈ Ideal.span {WP₁, WP₂} := by
  rw [kw_lrSym_minor_XZ]
  exact add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

theorem kw_lrSym_minor_YZ :
    kw_lrSym_Y W * kw_lrAdd_Z W - kw_lrSym_Z W * kw_lrAdd_Y W
      = kw_lrSym_pYZ W * WP₁ + kw_lrSym_qYZ W * WP₂ := by
  simp only [kw_lrSym_Y, kw_lrSym_Z, kw_lrAdd_X, kw_lrAdd_Y, kw_lrAdd_Z,
    kw_lrAdd_starX, kw_lrAdd_starY, kw_lrAdd_starZ, kw_lrAdd_c₂₁, kw_lrAdd_c₁₂,
    kw_lrSym_pYZ, kw_lrSym_qYZ, kw_lrAdd_WP₁, kw_lrAdd_WP₂,
    WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, rename_X, rename_C,
    MvPolynomial.algebraMap_eq]
  ring

theorem kw_lrSym_minor_YZ_mem_span :
    kw_lrSym_Y W * kw_lrAdd_Z W - kw_lrSym_Z W * kw_lrAdd_Y W
      ∈ Ideal.span {WP₁, WP₂} := by
  rw [kw_lrSym_minor_YZ]
  exact add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

end Minors

section Diag

def kw_lrSym_dblX : MvPolynomial (Fin 3) R :=
  C (-W.a₁*W.a₂) * (X 0)^ (4 : ℕ)
    + C (W.a₁^ (2 : ℕ) - (2:R)*W.a₂) * (X 0)^ (3 : ℕ)*(X 1)
    + C (-W.a₁^ (2 : ℕ)*W.a₃ - (3:R)*W.a₁*W.a₄ - W.a₂*W.a₃) * (X 0)^ (3 : ℕ)*(X 2)
    + C ((3:R)*W.a₁) * (X 0)^ (2 : ℕ)*(X 1)^ (2 : ℕ)
    + C (-(6:R)*W.a₄) * (X 0)^ (2 : ℕ)*(X 1)*(X 2)
    + C (-(3:R)*W.a₁*W.a₃^ (2 : ℕ) - (9:R)*W.a₁*W.a₆ - (3:R)*W.a₃*W.a₄) * (X 0)^ (2 : ℕ)*(X 2)^ (2 : ℕ)
    + C ((2:R)) * (X 0)*(X 1)^ (3 : ℕ)
    + C ((3:R)*W.a₃) * (X 0)*(X 1)^ (2 : ℕ)*(X 2)
    + C (-(3:R)*W.a₃^ (2 : ℕ) - (18:R)*W.a₆) * (X 0)*(X 1)*(X 2)^ (2 : ℕ)
    + C (-W.a₁^ (3 : ℕ)*W.a₆ + W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (4:R)*W.a₁*W.a₂*W.a₆ + W.a₁*W.a₄^ (2 : ℕ) - (2:R)*W.a₃^ (3 : ℕ) - (9:R)*W.a₃*W.a₆) * (X 0)*(X 2)^ (3 : ℕ)
    + C (-(2:R)*W.a₁^ (2 : ℕ)*W.a₆ + (2:R)*W.a₁*W.a₃*W.a₄ - (2:R)*W.a₂*W.a₃^ (2 : ℕ) - (8:R)*W.a₂*W.a₆ + (2:R)*W.a₄^ (2 : ℕ)) * (X 1)*(X 2)^ (3 : ℕ)
    + C (-W.a₁^ (2 : ℕ)*W.a₃*W.a₆ + W.a₁*W.a₃^ (2 : ℕ)*W.a₄ - W.a₂*W.a₃^ (3 : ℕ) - (4:R)*W.a₂*W.a₃*W.a₆ + W.a₃*W.a₄^ (2 : ℕ)) * (X 2)^ (4 : ℕ)

def kw_lrSym_dblY : MvPolynomial (Fin 3) R :=
  C (-W.a₂^ (2 : ℕ) + (3:R)*W.a₄) * (X 0)^ (4 : ℕ)
    + C (W.a₁*W.a₂ - (3:R)*W.a₃) * (X 0)^ (3 : ℕ)*(X 1)
    + C (W.a₁^ (2 : ℕ)*W.a₄ - (2:R)*W.a₁*W.a₂*W.a₃ - (2:R)*W.a₂*W.a₄ + (3:R)*W.a₃^ (2 : ℕ) + (18:R)*W.a₆) * (X 0)^ (3 : ℕ)*(X 2)
    + C ((3:R)*W.a₁*W.a₄ - (3:R)*W.a₂*W.a₃) * (X 0)^ (2 : ℕ)*(X 1)*(X 2)
    + C ((9:R)*W.a₁^ (2 : ℕ)*W.a₆ - (6:R)*W.a₁*W.a₃*W.a₄ + (3:R)*W.a₂*W.a₃^ (2 : ℕ) + (18:R)*W.a₂*W.a₆ - (6:R)*W.a₄^ (2 : ℕ)) * (X 0)^ (2 : ℕ)*(X 2)^ (2 : ℕ)
    + C (W.a₁) * (X 0)*(X 1)^ (3 : ℕ)
    + C ((9:R)*W.a₁*W.a₆ - (3:R)*W.a₃*W.a₄) * (X 0)*(X 1)*(X 2)^ (2 : ℕ)
    + C (W.a₁^ (4 : ℕ)*W.a₆ - W.a₁^ (3 : ℕ)*W.a₃*W.a₄ + W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ - W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) - (2:R)*W.a₁*W.a₂*W.a₃*W.a₄ - W.a₁*W.a₃^ (3 : ℕ) + (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (8:R)*W.a₂^ (2 : ℕ)*W.a₆ - (2:R)*W.a₂*W.a₄^ (2 : ℕ) - (3:R)*W.a₃^ (2 : ℕ)*W.a₄ - (6:R)*W.a₄*W.a₆) * (X 0)*(X 2)^ (3 : ℕ)
    + C ((1:R)) * (X 1)^ (4 : ℕ)
    + C (W.a₃) * (X 1)^ (3 : ℕ)*(X 2)
    + C (W.a₁^ (3 : ℕ)*W.a₆ - W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + W.a₁*W.a₂*W.a₃^ (2 : ℕ) + (4:R)*W.a₁*W.a₂*W.a₆ - W.a₁*W.a₄^ (2 : ℕ) - W.a₃^ (3 : ℕ) - (3:R)*W.a₃*W.a₆) * (X 1)*(X 2)^ (3 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₃*W.a₆ - W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₄ + W.a₁^ (2 : ℕ)*W.a₄*W.a₆ + W.a₁*W.a₂*W.a₃^ (3 : ℕ) + (4:R)*W.a₁*W.a₂*W.a₃*W.a₆ - (2:R)*W.a₁*W.a₃*W.a₄^ (2 : ℕ) + W.a₂*W.a₃^ (2 : ℕ)*W.a₄ + (4:R)*W.a₂*W.a₄*W.a₆ - W.a₃^ (4 : ℕ) - (6:R)*W.a₃^ (2 : ℕ)*W.a₆ - W.a₄^ (3 : ℕ) - (9:R)*W.a₆^ (2 : ℕ)) * (X 2)^ (4 : ℕ)

def kw_lrSym_dblZ : MvPolynomial (Fin 3) R :=
  C ((3:R)*W.a₁) * (X 0)^ (4 : ℕ)
    + C ((6:R)) * (X 0)^ (3 : ℕ)*(X 1)
    + C (W.a₁^ (3 : ℕ) + (3:R)*W.a₁*W.a₂ + (3:R)*W.a₃) * (X 0)^ (3 : ℕ)*(X 2)
    + C ((3:R)*W.a₁^ (2 : ℕ) + (6:R)*W.a₂) * (X 0)^ (2 : ℕ)*(X 1)*(X 2)
    + C ((3:R)*W.a₁^ (2 : ℕ)*W.a₃ + (3:R)*W.a₁*W.a₄ + (3:R)*W.a₂*W.a₃) * (X 0)^ (2 : ℕ)*(X 2)^ (2 : ℕ)
    + C ((3:R)*W.a₁) * (X 0)*(X 1)^ (2 : ℕ)*(X 2)
    + C ((6:R)*W.a₁*W.a₃ + (6:R)*W.a₄) * (X 0)*(X 1)*(X 2)^ (2 : ℕ)
    + C ((3:R)*W.a₁*W.a₃^ (2 : ℕ) + (3:R)*W.a₁*W.a₆ + (3:R)*W.a₃*W.a₄) * (X 0)*(X 2)^ (3 : ℕ)
    + C ((2:R)) * (X 1)^ (3 : ℕ)*(X 2)
    + C ((3:R)*W.a₃) * (X 1)^ (2 : ℕ)*(X 2)^ (2 : ℕ)
    + C ((3:R)*W.a₃^ (2 : ℕ) + (6:R)*W.a₆) * (X 1)*(X 2)^ (3 : ℕ)
    + C (W.a₃^ (3 : ℕ) + (3:R)*W.a₃*W.a₆) * (X 2)^ (4 : ℕ)

end Diag

end WeierstrassProjModel

end

end MEGA_KwLRSymAddFormulas_lean


