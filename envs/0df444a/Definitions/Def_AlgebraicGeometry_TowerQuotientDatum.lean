-- Prove2me | Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
-- name    : AlgebraicGeometry_TowerQuotientDatum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/2a46ca50-6b03-5191-adcc-18f9a7a14252
-- title:
--   Tower quotient data for finite group actions on π-adic towers
-- statement:
--   Fix a commutative ring $\mathcal O$ and an element $\pi$, and write $\mathcal O_n := \mathcal O/(\pi^{n+1})$. The input data are a sequence of schemes $X_n$ (in universe $0$) with structure morphisms $xb_n : X_n \to \operatorname{Spec}\mathcal O_n$, transition morphisms $xt_n : X_n \to X_{n+1}$, a group $G$, and for each $n$ a homomorphism $a_n : G \to \operatorname{Aut}(X_n)$. `TowerQuotientDatum` is a structure (in `Type 1`) whose inhabitants package a presentation of the quotient of this tower by $G$, level by level, all of the asserted properties being carried as fields rather than proved. The fields are: schemes $Y_n$ with morphisms $yb_n : Y_n \to \operatorname{Spec}\mathcal O_n$ and $yt_n : Y_n \to Y_{n+1}$ such that each square formed by $yt_n$, $yb_n$, $yb_{n+1}$ and $\operatorname{Spec}$ of the reduction $\mathcal O_{n+1} \to \mathcal O_n$ is a pullback (so $Y_n = Y_{n+1}\times_{\operatorname{Spec}\mathcal O_{n+1}}\operatorname{Spec}\mathcal O_n$), each $yb_n$ being proper and flat; morphisms $p_n : X_n \to Y_n$ with $p_n$ followed by $yb_n$ equal to $xb_n$, with $xt_n$ followed by $p_{n+1}$ equal to $p_n$ followed by $yt_n$, with that square a pullback ($X_n = X_{n+1}\times_{Y_{n+1}}Y_n$), with $G$-invariance $a_n(g)$ followed by $p_n$ equal to $p_n$, and with $p_n$ finite, surjective, and such that for every open $U \subseteq Y_n$ the restriction $p_n\mid_U$ is an epimorphism of schemes. The field `univ_loc` records a universal property for compatible families only: for a target $T$, opens $U_n \subseteq Y_n$ with $yt_n^{-1}(U_{n+1}) = U_n$, and morphisms $u_n : p_n^{-1}(U_n) \to T$ invariant under the restricted automorphisms $a_n(g)$ and compatible with the restrictions of $xt_n$, there exist $v_n : U_n \to T$ with $p_n\mid_{U_n}$ followed by $v_n$ equal to $u_n$ (uniqueness is not a separate field, being a consequence of the epimorphism field). Two point-counting fields complete the datum: `fib` says that for every algebraically closed field $k$ each $k$-point of $Y_n$ lifts to $X_n$ and the lifts form exactly one $G$-orbit; `adicFib` says that for a valuation domain $R$ that is an $\mathcal O$-algebra, complete for the adic topology of $(\pi)R$ and with algebraically closed fraction field, every compatible system of $\operatorname{Spec}(R/\pi^{n+1})$-points of the $Y_n$ lying over the canonical base points lifts to a compatible system of points of the $X_n$, and two such lifts differ by a single $g \in G$ simultaneously at all levels. In particular $Y_n$ is nowhere asserted to be the levelwise quotient $X_n/G$; the fields describe a quotient of the tower truncated modulo $\pi^{n+1}$.
--
--   **Relation to Mathlib.** Mathlib has no notion of a quotient of a π-adic tower of schemes by a finite group action; this structure is the project's own, assembled from Mathlib's morphism properties (`IsProper`, `Flat`, `IsFinite`, `Surjective`), `IsPullback` squares, and the restriction operations `Scheme.Hom.resLE` and `∣_` on opens.
--
--   **Where it is used.** The structure serves as the interface through which the rest of the development uses such quotients: an existence theorem produces an inhabitant from hypotheses on the input tower, and consumers argue only from the fields listed here (properness and flatness of the quotient levels, finiteness and local epimorphy of $p_n$, the local universal property, and the descriptions of geometric and $\pi$-adic points as $G$-orbits).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TowerQuotientDatum.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure TowerQuotientDatum
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (G : Type) [Group G] (a : ∀ n : ℕ, G →* Aut (X n)) : Type 1 where

  Y : ℕ → Scheme.{0}

  yb : ∀ n : ℕ, Y n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))

  yt : ∀ n : ℕ, Y n ⟶ Y (n + 1)

  yt_isPullback : ∀ n : ℕ, IsPullback (yt n) (yb n) (yb (n + 1))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))))))

  yb_isProper : ∀ n : ℕ, IsProper (yb n)

  yb_flat : ∀ n : ℕ, Flat (yb n)

  p : ∀ n : ℕ, X n ⟶ Y n

  p_over : ∀ n : ℕ, p n ≫ yb n = xb n

  p_xt : ∀ n : ℕ, xt n ≫ p (n + 1) = p n ≫ yt n

  p_isPullback : ∀ n : ℕ, IsPullback (xt n) (p n) (p (n + 1)) (yt n)

  p_inv : ∀ (n : ℕ) (g : G), (a n g).hom ≫ p n = p n

  p_isFinite : ∀ n : ℕ, IsFinite (p n)

  p_surjective : ∀ n : ℕ, Surjective (p n)

  p_epi_loc : ∀ (n : ℕ) (U : (Y n).Opens), Epi ((p n) ∣_ U)

  univ_loc : ∀ (T : Scheme.{0}) (U : ∀ n : ℕ, (Y n).Opens) (hU : ∀ n : ℕ, (yt n) ⁻¹ᵁ (U (n + 1)) = U n)
    (u : ∀ n : ℕ, (↑((p n) ⁻¹ᵁ (U n)) : Scheme.{0}) ⟶ T),
    (∀ (n : ℕ) (g : G),
      Scheme.Hom.resLE (a n g).hom ((p n) ⁻¹ᵁ (U n)) ((p n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, p_inv]) ≫ u n = u n) →
    (∀ n : ℕ,
      Scheme.Hom.resLE (xt n) ((p (n + 1)) ⁻¹ᵁ (U (n + 1))) ((p n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, p_xt, Scheme.Hom.comp_preimage, hU]) ≫ u (n + 1) = u n) →
    ∃ v : ∀ n : ℕ, (↑(U n) : Scheme.{0}) ⟶ T, ∀ n : ℕ, (p n) ∣_ (U n) ≫ v n = u n

  fib : ∀ (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] (y : Spec (CommRingCat.of k) ⟶ Y n),
    (∃ x : Spec (CommRingCat.of k) ⟶ X n, x ≫ p n = y) ∧
    ∀ x x' : Spec (CommRingCat.of k) ⟶ X n, x ≫ p n = y → (x' ≫ p n = y ↔ ∃ g : G, x' = x ≫ (a n g).hom)

  adicFib : ∀ (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra 𝒪 R],
    IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R → IsAlgClosed (FractionRing R) →
    ∀ (y : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {(algebraMap 𝒪 R π) ^ (n + 1)})) ⟶ Y n),
    (∀ n : ℕ, y n ≫ yb n = Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 R π) ^ (n + 1)}) (algebraMap 𝒪 R)
      (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))) →
    (∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ y (n + 1) = y n ≫ yt n) →
    (∃ x : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {(algebraMap 𝒪 R π) ^ (n + 1)})) ⟶ X n,
      (∀ n : ℕ, x n ≫ p n = y n) ∧
      ∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ x (n + 1) = x n ≫ xt n) ∧
    ∀ x x' : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {(algebraMap 𝒪 R π) ^ (n + 1)})) ⟶ X n,
      (∀ n : ℕ, x n ≫ p n = y n) → (∀ n : ℕ, x' n ≫ p n = y n) →
      (∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ x (n + 1) = x n ≫ xt n) →
      (∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ x' (n + 1) = x' n ≫ xt n) →
      ∃ g : G, ∀ n : ℕ, x' n = x n ≫ (a n g).hom

end AlgebraicGeometry


