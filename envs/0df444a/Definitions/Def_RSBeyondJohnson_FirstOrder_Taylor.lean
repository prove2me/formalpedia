-- Prove2me | Definitions.Def_RSBeyondJohnson_FirstOrder_Taylor
-- name    : RSBeyondJohnson_FirstOrder_Taylor
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:30:10.083846+00:00
-- url     : https://prove2.me/theorems/fdef5093-f35d-4eef-807c-d8f816e24b48
-- title:
--   Taylor reconstruction for a first-order equation (Kopparty's recurrence, §5.2)
-- statement:
--   Let $Q\in F[X,Z,Y_0,Y_1]$ and fix a Taylor center $x_0\in F$. At a point $(z,c_0,c_1)$ of an extension field $K$, write $P(x_0+T)=\sum_jc_jT^j$. Kopparty's recurrence determines the later coefficients one at a time: for $s\ge2$,
--   $$c_s=-\frac{[T^{s-1}]\,Q\big(x_0+T,\ z,\ \sum_{j<s}c_jT^j,\ \sum_{1\le j<s}jc_jT^{j-1}\big)}{s\cdot q},\qquad q=\frac{\partial Q}{\partial Y_1}(x_0,z,c_0,c_1),$$
--   because the coefficient of the new unknown $c_s$ in the coefficient of $T^{s-1}$ is $s$ times the separant $q$. **Taylor reconstruction through message degree $D$, with the coordinates $(Z,Z^2,\dots,Z^\ell,P)$ retained**, sends $(z,c_0,c_1)$ to $(z,z^2,\dots,z^\ell,P_0,\dots,P_D)$, where $P_i$ are the coefficients of $P(X)=\sum_{s=0}^Dc_s(X-x_0)^s$.
--
--   **Formalization Note.** The recurrence is meaningful where $q\ne0$ and $2,\dots,D$ are invertible; elsewhere Lean's division by zero returns $0$, and Lemma 5.4 only speaks about points with $q\neq0$ under its characteristic hypothesis.
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), pp. 31–32, §5.2 and Lemma 5.4

import Mathlib

open Polynomial

namespace RSBeyondJohnson.FirstOrder

/-!
# Taylor reconstruction for a first-order equation (§5.2, Lemma 5.4)

Dao, Kominers, Thaler, *Reed–Solomon Codes Beyond Johnson*, STOC 2027 submission (manuscript of
November 2, 2026), §5.2, pp. 31–32.

`Q ∈ F[X, Z, Y₀, Y₁]` is `(MvPolynomial (Option (Fin 2)) F)[X]` (outer variable `Z`; `none = X`,
`some 0 = Y₀`, `some 1 = Y₁`). At a Taylor center `x₀ ∈ F` and a point `(z, c₀, c₁)` of an extension
field `K` (challenge, value, first derivative), write `P(x₀ + T) = ∑_j c_j T^j`. Kopparty's
recurrence (p. 31) determines the later coefficients one at a time: the coefficient of `T^{s−1}`
in `Q(x₀ + T, z, P(x₀ + T), P^[1](x₀ + T))` is linear in `c_s` with coefficient `s` times the
separant `q = (∂Q/∂Y₁)(x₀, z, c₀, c₁)`, so for `s ≥ 2`
`c_s = −[T^{s−1}] Q(x₀ + T, z, ∑_{j<s} c_j T^j, ∑_{1≤j<s} j c_j T^{j−1}) / (s q)`.
(`P^[1]` is the first Hasse derivative, which is the ordinary derivative.) Taylor reconstruction
through message degree `D` is the point
`(z, z², …, z^ℓ, coefficients of P(X) = ∑_{s=0}^{D} c_s (X − x₀)^s)` of `K^{ℓ + D + 1}`. It is
meaningful where `q ≠ 0` and `2, …, D` are invertible (characteristic zero or `p > D`).
-/

/-- `Q(x₀ + T, z, S(T), S'(T))` as a polynomial in `T` over `K`, for a polynomial `S ∈ K[T]`. -/
noncomputable def substTaylor {F K : Type*} [Field F] [Field K] [Algebra F K]
    (Q : (MvPolynomial (Option (Fin 2)) F)[X]) (x₀ : F) (z : K) (S : K[X]) : K[X] :=
  (Q.map (MvPolynomial.eval₂Hom ((Polynomial.C).comp (algebraMap F K))
    (fun v : Option (Fin 2) => match v with
      | none => Polynomial.C (algebraMap F K x₀) + Polynomial.X
      | some j => if (j : ℕ) = 0 then S else Polynomial.derivative S))).eval (Polynomial.C z)

/-- The separant `q = (∂Q/∂Y₁)(x₀, z, c₀, c₁)` at a point. -/
noncomputable def separantAt {F K : Type*} [Field F] [Field K] [Algebra F K]
    (Q : (MvPolynomial (Option (Fin 2)) F)[X]) (x₀ : F) (z c₀ c₁ : K) : K :=
  ∑ i ∈ Finset.range (Q.natDegree + 1), z ^ i *
    MvPolynomial.eval₂ (algebraMap F K)
      (fun v : Option (Fin 2) => match v with
        | none => algebraMap F K x₀
        | some j => if (j : ℕ) = 0 then c₀ else c₁)
      (MvPolynomial.pderiv (some 1) (Q.coeff i))

/-- The value `Q(x₀, z, c₀, c₁)`. -/
noncomputable def evalAt {F K : Type*} [Field F] [Field K] [Algebra F K]
    (Q : (MvPolynomial (Option (Fin 2)) F)[X]) (x₀ : F) (z c₀ c₁ : K) : K :=
  ∑ i ∈ Finset.range (Q.natDegree + 1), z ^ i *
    MvPolynomial.eval₂ (algebraMap F K)
      (fun v : Option (Fin 2) => match v with
        | none => algebraMap F K x₀
        | some j => if (j : ℕ) = 0 then c₀ else c₁)
      (Q.coeff i)

/-- `taylorVec Q x₀ z c₀ c₁ s` is the coefficient sequence `(c₀, c₁, …, c_{s+1}, 0, 0, …)` given
by Kopparty's recurrence. -/
noncomputable def taylorVec {F K : Type*} [Field F] [Field K] [Algebra F K]
    (Q : (MvPolynomial (Option (Fin 2)) F)[X]) (x₀ : F) (z c₀ c₁ : K) : ℕ → ℕ → K
  | 0 => fun j => if j = 0 then c₀ else if j = 1 then c₁ else 0
  | s + 1 =>
    Function.update (taylorVec Q x₀ z c₀ c₁ s) (s + 2)
      (-(substTaylor Q x₀ z (∑ j ∈ Finset.range (s + 2),
            Polynomial.C (taylorVec Q x₀ z c₀ c₁ s j) * Polynomial.X ^ j)).coeff (s + 1) /
        (((s : K) + 2) * separantAt Q x₀ z c₀ c₁))

/-- **Taylor reconstruction through message degree `D`, with the coordinates
`(Z, Z², …, Z^ℓ, P)` retained** (Lemma 5.4): the point
`(z, z², …, z^ℓ, P_0, …, P_D) ∈ K^{ℓ + (D+1)}`, where `P_i` are the coefficients of
`P(X) = ∑_{s=0}^{D} c_s (X − x₀)^s` (and `c_s` is given by `taylorVec`). -/
noncomputable def taylorMap {F K : Type*} [Field F] [Field K] [Algebra F K]
    (Q : (MvPolynomial (Option (Fin 2)) F)[X]) (x₀ : F) (ℓ D : ℕ) (z c₀ c₁ : K) :
    Fin (ℓ + (D + 1)) → K :=
  Fin.append (fun t : Fin ℓ => z ^ ((t : ℕ) + 1))
    (fun i : Fin (D + 1) =>
      (∑ s ∈ Finset.range (D + 1), Polynomial.C (taylorVec Q x₀ z c₀ c₁ D s) *
        (Polynomial.X - Polynomial.C (algebraMap F K x₀)) ^ s).coeff i)

end RSBeyondJohnson.FirstOrder


