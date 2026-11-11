-- Prove2me | Definitions.Def_RSBeyondJohnson_FirstOrder_Geometry
-- name    : RSBeyondJohnson_FirstOrder_Geometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:31:26.312618+00:00
-- url     : https://prove2.me/theorems/6a5443a9-fef3-4b84-9576-f8642158bbde
-- title:
--   Coefficient space, lifted locus $\mathcal L_\ell$, agreement hyperplanes, witness graphs and generic fibers (§4.1)
-- statement:
--   Over a field $E$, the **coefficient space** of degree-$<k$ polynomials is $E^k$, the point $p$ standing for $\sum_{j<k}p_jX^j$. The **lifted locus** is
--   $$\mathcal L_\ell=\{(z,z^2,\dots,z^\ell,P):\deg P<k\}\subseteq E^{\ell+k},$$
--   with coordinates $T_1=z,T_2,\dots,T_\ell$ and the coefficients of $P$; $\mathcal L_1=E^{1+k}$ is the joint space of pairs $(z,P)$. Agreement with a received curve at position $i$ is the hyperplane $H_i=\{P(\alpha_i)=w_{0,i}+\sum_{t=1}^{\ell}T_tw_{t,i}\}$. The **witness graph** of $P_0,\dots,P_\ell$ (degree $<k$) is $\Gamma=\{(z,z^2,\dots,z^\ell,\sum_tz^tP_t):z\in E\}$; its common agreements are the positions with $P_t(\alpha_i)=w_{t,i}$ for all $t$. The union of the witness graphs with at least $L$ common agreements is excluded in Lemma 4.1.
--
--   For $V\subseteq E^{\ell+k}$ and $z^*$ transcendental over $E$, the **reduced fiber over $z^*$** after base change to an algebraic closure $K$ of $E(z^*)$ is the set of $p\in K^k$ such that $(z^*,\dots,z^{*\ell},p)$ is a zero of every polynomial over $E$ vanishing on $V$.
--
--   **Formalization Note.** $z^*$ is the variable of `RatFunc E` inside `AlgebraicClosure (RatFunc E)`. Algebraic sets, dimension (`algDim`) and total degree (`cdeg`, the sum of Heintz degrees of the irreducible components) come from the published definition `RSCapacity_AffineGeometry`.
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), pp. 25–27, §4.1

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Decoding
import Definitions.Def_RSBeyondJohnson_FirstOrder_Agreement

open Polynomial

namespace RSBeyondJohnson.FirstOrder

/-!
# Coefficient space, lifted locus, agreement hyperplanes and witness graphs (§4.1)

Dao, Kominers, Thaler, *Reed–Solomon Codes Beyond Johnson*, STOC 2027 submission (manuscript of
November 2, 2026), §4.1, pp. 25–26.

* The coefficient space of degree-`< k` polynomials over a field `E` is `Fin k → E`; the point
  `p` is the polynomial `∑_{j<k} p_j X^j` (`coeffPoly p`), and `coeffVec k P` is the coefficient
  vector of `P`.
* The lifted locus `L_ℓ = {(z, z², …, z^ℓ, P) : deg P < k}` lives in `E^{ℓ+k}` = `Fin (ℓ + k) → E`:
  the first `ℓ` coordinates are `T₁ = z, T₂, …, T_ℓ` (`liftChal x t` is `T_{t+1}`), the last `k`
  are the coefficients of `P` (`liftCoeff x`). For `ℓ = 1` it is the joint space `L₁` of pairs
  `(z, P)`, i.e. all of `E^{1+k}`.
* Agreement with a received curve at position `i` is the affine hyperplane
  `H_i = {P(α_i) = w_{0,i} + z w_{1,i} + ∑_{t=2}^{ℓ} T_t w_{t,i}}`; `liftAgrCount` counts the `i`
  with `x ∈ H_i`.
* The witness graph of `P₀, …, P_ℓ` (each of degree `< k`) is
  `Γ = {(z, z², …, z^ℓ, ∑_t z^t P_t) : z ∈ E}`; its common agreements are the positions `i` with
  `P_t(α_i) = w_{t,i}` for every `t` (`witnessAgrSet`).
* Algebraic sets, their dimension `algDim` and total (cumulative) degree `cdeg` (the sum of the
  degrees of the irreducible components, Heintz's degree) are those of the published definition
  `RSCapacity_AffineGeometry`, used over an algebraically closed field.
-/

/-- The polynomial `∑_{j<k} p_j X^j` with coefficient vector `p ∈ E^k`. -/
noncomputable def coeffPoly {E : Type*} [Field E] {k : ℕ} (p : Fin k → E) : E[X] :=
  ∑ j : Fin k, Polynomial.C (p j) * Polynomial.X ^ (j : ℕ)

/-- The coefficient vector `(P_0, …, P_{k−1}) ∈ E^k` of a polynomial `P` (of degree `< k`). -/
noncomputable def coeffVec {E : Type*} [Field E] (k : ℕ) (P : E[X]) : Fin k → E :=
  fun j => P.coeff j

/-- The point `(z, z², …, z^ℓ, p) ∈ E^{ℓ+k}`. -/
def liftPoint {E : Type*} [Field E] (ℓ k : ℕ) (z : E) (p : Fin k → E) : Fin (ℓ + k) → E :=
  Fin.append (fun t : Fin ℓ => z ^ ((t : ℕ) + 1)) p

/-- The coordinate `T_{t+1}` of a point of `E^{ℓ+k}`. -/
def liftChal {E : Type*} [Field E] {ℓ k : ℕ} (x : Fin (ℓ + k) → E) (t : Fin ℓ) : E :=
  x (Fin.castAdd k t)

/-- The coefficient coordinates of a point of `E^{ℓ+k}`. -/
def liftCoeff {E : Type*} [Field E] {ℓ k : ℕ} (x : Fin (ℓ + k) → E) : Fin k → E :=
  fun j => x (Fin.natAdd ℓ j)

/-- The lifted locus `L_ℓ = {(z, z², …, z^ℓ, P)} ⊆ E^{ℓ+k}` (p. 26). -/
def liftedLocus (E : Type*) [Field E] (ℓ k : ℕ) : Set (Fin (ℓ + k) → E) :=
  {x | ∃ z : E, ∀ t : Fin ℓ, liftChal x t = z ^ ((t : ℕ) + 1)}

/-- The number of agreement hyperplanes `H_i` containing the point `x ∈ E^{ℓ+k}`:
`#{i : P(α_i) = w_{0,i} + ∑_{t=1}^{ℓ} T_t w_{t,i}}` with `P = coeffPoly (liftCoeff x)`. -/
noncomputable def liftAgrCount {E : Type*} [Field E] {n ℓ k : ℕ} (α : Fin n → E)
    (w : Fin (ℓ + 1) → Fin n → E) (x : Fin (ℓ + k) → E) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin n =>
    (coeffPoly (liftCoeff x)).eval (α i) =
      w 0 i + ∑ t : Fin ℓ, liftChal x t * w t.succ i).card

/-- The witness graph `Γ_{P₀,…,P_ℓ} = {(z, z², …, z^ℓ, ∑_t z^t P_t) : z ∈ E}` (p. 26). -/
noncomputable def witnessGraph {E : Type*} [Field E] (ℓ k : ℕ) (Ps : Fin (ℓ + 1) → E[X]) :
    Set (Fin (ℓ + k) → E) :=
  {x | ∃ z : E, x = liftPoint ℓ k z
    (coeffVec k (∑ t : Fin (ℓ + 1), Polynomial.C (z ^ (t : ℕ)) * Ps t))}

/-- The union of the witness graphs with at least `L` common agreements: graphs of witnesses
`P₀, …, P_ℓ` of degree `< k` with `|S(P₀, …, P_ℓ)| ≥ L`. -/
noncomputable def highWitnessGraphs {E : Type*} [Field E] {n : ℕ} (ℓ k L : ℕ) (α : Fin n → E)
    (w : Fin (ℓ + 1) → Fin n → E) : Set (Fin (ℓ + k) → E) :=
  ⋃ (Ps : Fin (ℓ + 1) → E[X]) (_ : ∀ t, (Ps t).degree < (k : WithBot ℕ))
    (_ : L ≤ (witnessAgrSet α w Ps).card), witnessGraph ℓ k Ps

/-- The reduced fiber of `V ⊆ E^{ℓ+k}` over a challenge `z*` transcendental over `E` (Lemma 4.2,
p. 27): `z*` is the variable `X` of `E(z*) = RatFunc E`, viewed in the algebraic closure
`K = AlgebraicClosure (RatFunc E)`; the fiber is the set of `p ∈ K^k` such that
`(z*, z*², …, z*^ℓ, p)` is a zero of every polynomial over `E` vanishing on `V` (the base change of
`V` to `K`, cut by `T_t = z*^t`). As a set of points it is reduced. -/
noncomputable def genericFiber (E : Type*) [Field E] (ℓ k : ℕ) (V : Set (Fin (ℓ + k) → E)) :
    Set (Fin k → AlgebraicClosure (RatFunc E)) :=
  {p | ∀ f ∈ MvPolynomial.vanishingIdeal E V,
    MvPolynomial.eval (liftPoint ℓ k
      (algebraMap (RatFunc E) (AlgebraicClosure (RatFunc E)) RatFunc.X) p)
      (MvPolynomial.map (algebraMap E (AlgebraicClosure (RatFunc E))) f) = 0}

end RSBeyondJohnson.FirstOrder


