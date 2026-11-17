-- Prove2me | Definitions.Def_RSCapacity_Supplement_Defs
-- name    : RSCapacity_Supplement_Defs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:27:21.959226+00:00
-- url     : https://prove2.me/theorems/8848f4c3-c11b-44f2-a4af-ddc99e292270
-- title:
--   Mutual correlated agreement $\mathrm{Bad}^{(\ell)}_{C,\rho}$, $\mathrm{err}_{\mathrm{MCA}}$ (Definition 3.3) and the parametric solution locus $\mathrm{Sol}_d(Q)$
-- statement:
--   Let $F$ be a field, $D=\{\alpha_1,\dots,\alpha_n\}\subseteq F$ an evaluation set given by $\alpha:[n]\to F$, and $k$ a degree bound, so that $C=\mathrm{RS}_F(D,k)$ is the Reed–Solomon code of polynomials of degree below $k$.
--
--   1. For $u\in F^n$ and $P\in F[X]$, the **agreement support** is $\mathrm{Agr}(u,P)=\{i\in[n]: u_i=P(\alpha_i)\}$.
--   2. For **coefficient words** $f=(f_0,\dots,f_\ell)$, $f_j\in F^n$, the **curve** is $y(z)=\sum_{j=0}^{\ell} z^j f_j\in F^n$.
--   3. A set $S\subseteq[n]$ is **$f$-correlated** (jointly explained by $f$) if there are $P_0,\dots,P_\ell\in F[X]$ of degree below $k$ with $P_j(\alpha_i)=f_{j,i}$ for all $i\in S$ and $0\le j\le\ell$.
--   4. For a radius $\rho$, $A_\rho=n-\lfloor\rho n\rfloor$, and $\mathcal A_\rho(f)$ is the collection of inclusion-maximal $f$-correlated sets of cardinality at least $A_\rho$.
--   5. (Definition 3.3) The **bad curve parameters** are
--   $$\mathrm{Bad}^{(\ell)}_{C,\rho}(f)=\{z\in F:\ \exists P\in F[X],\ \deg P<k,\ |\mathrm{Agr}(y(z),P)|\ge A_\rho,\ \mathrm{Agr}(y(z),P)\notin\mathcal A_\rho(f)\},$$
--   and, for a finite field $F=\mathbb F_q$, the **MCA error** is
--   $$\mathrm{err}_{\mathrm{MCA}}(C,\rho)=\max_{f_0,f_1\in\mathbb F_q^n}\frac{|\mathrm{Bad}^{(1)}_{C,\rho}(f_0,f_1)|}{q}.$$
--
--   For the parametric solution locus, let $p=(p_0,\dots,p_d)\in F^{d+1}$ and $P_p(X)=\sum_{j=0}^d p_jX^j$. For $Q\in F[Z,X,Y_0,\dots,Y_r]$,
--   $$\mathrm{Sol}_d(Q)=\{(z,p)\in\mathbb A^{d+2}:\ Q(z,X,P_p,P_p^{[1]},\dots,P_p^{[r]})\equiv0\ \text{in } F[X]\},\tag{55}$$
--   where $P^{[j]}$ is the $j$-th Hasse derivative. $Q$ is **$Z$-primitive** if the gcd in $F[Z]$ of its coefficients, viewed as a polynomial in $X,Y_0,\dots,Y_r$ over $F[Z]$, is $1$.
--
--   $\mathrm{Bad}$ and $\mathrm{err}_{\mathrm{MCA}}$ are the quantities bounded by the paper's proximity-gap theorem (Theorem 1.2); $\mathrm{Sol}_d(Q)$ and $Z$-primitivity are the objects of the parametric jet decomposition (Theorem 6.5).
--
--   **Formalization Note** Subsets of $[n]$ are `Set (Fin n)` with `Set.ncard`; $A_\rho$ uses `Nat.floor`. The maximum in $\mathrm{err}_{\mathrm{MCA}}$ is a real `iSup` over the finite type of pairs $(f_0,f_1)$, divided by $|F|$. $F[Z,X,Y_0,\dots,Y_r]$ is `MvPolynomial (Fin (r + 3)) F` with $Z=0$, $X=1$, $Y_j=j+2$; $Q(z,X,Y)$ is the specialization $Z\mapsto z$ and the substitution of Hasse derivatives is the published `diffEval`. A point of $\mathbb A^{d+2}$ has coordinate $0$ equal to $z$ and coordinate $j+1$ equal to $p_j$. $Z$-primitivity is stated as: every common divisor in $F[Z]$ of the coefficients is a unit.
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), §3.3 and Definition 3.3, p.12 (PDF 14); §6.3, Equation (55) and Z-primitivity, p.25 (PDF 27)

import Mathlib
import Definitions.Def_RSCapacity_DiffSubst
import Definitions.Def_RSCapacity_AffineGeometry

open Polynomial

set_option autoImplicit false

namespace RSCapacity.Supplement

/-!
# Mutual correlated agreement (Definition 3.3) and the parametric solution locus Sol_d(Q)

Jeronimo, *Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon
Codes*, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…): §3.3 and
Definition 3.3, p.12 (PDF 14) (agreement supports, f-correlated sets, 𝒜_ρ(f), Bad, err_MCA);
§6.3, Equation (55) and the definition of Z-primitivity, p.25 (PDF 27).

**Formalization Note.**
* The code C = RS_F(D, k) is given by its data: an evaluation map `α : Fin n → F` (injective in
  every statement that uses it) and the degree bound `k`. Degrees are `Polynomial.degree`, so the
  zero polynomial has degree below every `k` (p.10).
* Subsets of [n] are `Set (Fin n)`; their sizes are `Set.ncard` (exact, since `Fin n` is
  finite).
* Coefficient words f = (f_0, …, f_ℓ), f_j ∈ F^n, are maps `Fin (ℓ + 1) → Fin n → F`, and
  y(z) = ∑_{j=0}^{ℓ} z^j f_j.
* A_ρ = n − ⌊ρn⌋ with `Nat.floor`; every statement using it has 0 ≤ ρ ≤ 1, where `Nat.floor`
  is the usual floor and the subtraction does not truncate.
* 𝒜_ρ(f) consists of the f-correlated sets S of size at least A_ρ such that no strict superset of
  S is f-correlated (inclusion-maximal among all f-correlated sets; a superset of a set of size
  ≥ A_ρ has size ≥ A_ρ, so this is the same as maximality among the large ones).
* err_MCA is the maximum over the finite nonempty set of pairs (f_0, f_1) (a real `iSup` over a
  finite type), divided by q = |F|.
* F[Z, X, Y_0, …, Y_r] is `MvPolynomial (Fin (r + 3)) F` with Z = 0, X = 1, Y_j = j + 2 (the
  layout of `RSCapacity.JetCoefficients`). Q(z, X, Y_0, …, Y_r) is the specialization Z ↦ z,
  a polynomial in `MvPolynomial (Fin (r + 2)) F` with X = 0, Y_j = j + 1, and
  Q(z, X, P, P^{[1]}, …, P^{[r]}) is `diffEval` of it (Hasse derivatives, `RSCapacity.DiffSubst`).
* A point of 𝔸^{d+2} is `x : Fin (d + 2) → F` with x 0 = z and x (j + 1) = p_j.
* Z-primitivity: the coefficient of the monomial X^a Y^b of Q, viewed as a polynomial in
  X, Y_0, …, Y_r over F[Z], is `zCoeff Q m` ∈ F[Z]; Q is Z-primitive when every common divisor in
  F[Z] of these coefficients is a unit (in the principal ideal domain F[Z] this is "gcd = 1").
-/

section MCA

variable {F : Type*} [Field F] {n : ℕ}

/-- The agreement support Agr(u, P) = {i ∈ [n] : u_i = P(α_i)} (§3.3, p.12). -/
def agr (α : Fin n → F) (u : Fin n → F) (P : F[X]) : Set (Fin n) :=
  {i | u i = P.eval (α i)}

/-- The curve y(z) = ∑_{j=0}^{ℓ} z^j f_j ∈ F^n of the coefficient words f = (f_0, …, f_ℓ). -/
def curve {ℓ : ℕ} (f : Fin (ℓ + 1) → Fin n → F) (z : F) : Fin n → F :=
  fun i => ∑ j : Fin (ℓ + 1), z ^ (j : ℕ) * f j i

/-- S ⊆ [n] is f-correlated (jointly explained by f): there are P_0, …, P_ℓ of degree below k
with P_j(α_i) = f_{j,i} for all i ∈ S and 0 ≤ j ≤ ℓ (§3.3, p.12). -/
def IsCorrelated (α : Fin n → F) (k : ℕ) {ℓ : ℕ} (f : Fin (ℓ + 1) → Fin n → F)
    (S : Set (Fin n)) : Prop :=
  ∃ P : Fin (ℓ + 1) → F[X], (∀ j, (P j).degree < k) ∧ ∀ i ∈ S, ∀ j, (P j).eval (α i) = f j i

/-- A_ρ = n − ⌊ρn⌋ (§3.3, p.12). -/
noncomputable def aRho (n : ℕ) (ρ : ℝ) : ℕ :=
  n - ⌊ρ * n⌋₊

/-- 𝒜_ρ(f): the inclusion-maximal f-correlated sets of cardinality at least A_ρ (§3.3, p.12). -/
def maxCorrelated (α : Fin n → F) (k : ℕ) {ℓ : ℕ} (f : Fin (ℓ + 1) → Fin n → F) (ρ : ℝ) :
    Set (Set (Fin n)) :=
  {S | IsCorrelated α k f S ∧ (∀ T : Set (Fin n), S ⊂ T → ¬ IsCorrelated α k f T) ∧
    aRho n ρ ≤ S.ncard}

/-- Definition 3.3 (Bad curve parameters), p.12: Bad^{(ℓ)}_{C,ρ}(f) is the set of z ∈ F for which
some P with deg P < k has |Agr(y(z), P)| ≥ A_ρ and Agr(y(z), P) ∉ 𝒜_ρ(f), for
C = RS_F(D, k). -/
def bad (α : Fin n → F) (k : ℕ) {ℓ : ℕ} (f : Fin (ℓ + 1) → Fin n → F) (ρ : ℝ) : Set F :=
  {z | ∃ P : F[X], P.degree < k ∧ aRho n ρ ≤ (agr α (curve f z) P).ncard ∧
    agr α (curve f z) P ∉ maxCorrelated α k f ρ}

/-- Definition 3.3, p.12: err_MCA(C, ρ) = max_{f_0, f_1 ∈ F^n} |Bad^{(1)}_{C,ρ}(f_0, f_1)| / q for
C = RS_F(D, k) over a finite field F with q = |F| elements. -/
noncomputable def errMCA [Fintype F] (α : Fin n → F) (k : ℕ) (ρ : ℝ) : ℝ :=
  (⨆ f : Fin (1 + 1) → Fin n → F, ((bad α k f ρ).ncard : ℝ)) / (Fintype.card F : ℝ)

end MCA

section SolLocus

variable {F : Type*} [Field F]

/-- The specialization Q(z, X, Y_0, …, Y_r) ∈ F[X, Y_0, …, Y_r] of Q ∈ F[Z, X, Y_0, …, Y_r] at
Z = z (variables: Z = 0, X = 1, Y_j = j + 2 before; X = 0, Y_j = j + 1 after). -/
noncomputable def specZ {r : ℕ} (z : F) (Q : MvPolynomial (Fin (r + 3)) F) :
    MvPolynomial (Fin (r + 2)) F :=
  MvPolynomial.aeval
    (Fin.cases (motive := fun _ => MvPolynomial (Fin (r + 2)) F) (MvPolynomial.C z)
      (fun i : Fin (r + 2) => MvPolynomial.X i)) Q

/-- Equation (55), p.25: Sol_d(Q) = {(z, p) ∈ 𝔸^{d+2} : Q(z, X, P_p, P_p^{[1]}, …, P_p^{[r]}) ≡ 0}
with P_p = ∑_{j=0}^{d} p_j X^j. -/
noncomputable def solLocus (r d : ℕ) (Q : MvPolynomial (Fin (r + 3)) F) :
    Set (Fin (d + 2) → F) :=
  {x | diffEval (specZ (x 0) Q) (polyOfVec (fun j : Fin (d + 1) => x j.succ)) = 0}

/-- The coefficient in F[Z] of the monomial X^{m_0} Y_0^{m_1} ⋯ Y_r^{m_{r+1}} of Q, when Q is
viewed as a polynomial in X, Y_0, …, Y_r with coefficients in F[Z]:
∑_a coeff_{Z^a X^{m_0} Y^{…}}(Q) Z^a. -/
noncomputable def zCoeff {r : ℕ} (Q : MvPolynomial (Fin (r + 3)) F) (m : Fin (r + 2) →₀ ℕ) :
    F[X] :=
  ∑ a ∈ Finset.range (Q.degreeOf 0 + 1), Polynomial.monomial a (Q.coeff (Finsupp.cons a m))

/-- Q ∈ F[Z, X, Y_0, …, Y_r] is Z-primitive (p.25): the gcd in F[Z] of its coefficients as a
polynomial in X, Y_0, …, Y_r is 1, i.e. every common divisor of them in F[Z] is a unit. -/
def IsZPrimitive {r : ℕ} (Q : MvPolynomial (Fin (r + 3)) F) : Prop :=
  ∀ c : F[X], (∀ m : Fin (r + 2) →₀ ℕ, c ∣ zCoeff Q m) → IsUnit c

end SolLocus

end RSCapacity.Supplement


