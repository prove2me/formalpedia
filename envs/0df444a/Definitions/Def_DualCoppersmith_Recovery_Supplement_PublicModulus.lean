-- Prove2me | Definitions.Def_DualCoppersmith_Recovery_Supplement_PublicModulus
-- name    : DualCoppersmith_Recovery_Supplement_PublicModulus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:35:19.591551+00:00
-- url     : https://prove2.me/theorems/1daf65df-612d-4fbe-a078-6c0d48270ce8
-- title:
--   Public-modulus instance, shifts, lattice $L_X^\perp$ modulo $N^m$, divisor $p$ and cofactor $q_0$
-- statement:
--   This module fixes the objects of §4.4 (extension to a composite modulus), where the known prime of the base construction is replaced by a public modulus that need not be prime.
--
--   A **public-modulus instance** consists of an integer $N\ge2$ (no primality assumed), integer polynomials $F=(f_1,\ldots,f_s)$ in $\ell\ge1$ variables, and positive integer bounds $X_1,\ldots,X_\ell$. A **bounded target** is an integer vector $r\in\mathbb Z^\ell$ with $|r_i|<X_i$ for every $i$; no congruence is required of it. The shift parameters are integers $m,t\ge1$.
--
--   The monomial coordinates are all $\alpha\in\mathbb N^\ell$ with $|\alpha|\le t$ (the set $T_t$, of size $n=|T_t|$), in a fixed order. For multiplicity vectors $i$ with $1\le|i|\le m$ and monomials $x^\beta$ with $\deg(x^\beta F^i)\le t$, the **total-degree shifts** are
--
--   $$g_{i,\beta}=N^{m-|i|}\,x^\beta f_1^{i_1}\cdots f_s^{i_s},$$
--
--   and their coefficient vectors form the rows of the public shift coefficient matrix $A$. The kernel and the scaled lattice are
--
--   $$K=\{z\in\mathbb Z^n : Az\equiv0\pmod{N^m}\},\qquad L_X^\perp=\{((\rho/X^\alpha)z_\alpha)_{\alpha\in T_t} : z\in K\}\subset\mathbb R^n,$$
--
--   with $\rho=\operatorname{lcm}\{X^\alpha:\alpha\in T_t\}$. For a target $r$, $z_r=(r^\alpha)_\alpha$ and $v_r=((\rho/X^\alpha)r^\alpha)_\alpha$. Finally the **divisor** and **cofactor** of $r$ are
--
--   $$p=\gcd(N,f_1(r),\ldots,f_s(r)),\qquad q_0=N/p .$$
--
--   These are the objects Theorem 4.6 speaks about; every formula coincides with the base mission's prime-modulus construction after replacing $p$ by $N$.
--
--   **Formalization Note** Indices are zero-based and the monomial order is the fixed equivalence of the published base module (`Monomial`, `monomialOrder`, `multiIndex` are reused, as is `integerEmbedding`). The base `Instance` cannot be reused because it carries a primality field, so the instance-dependent pieces are restated with the prefix `pub`. Identically zero shifts are omitted, since their rows impose only $0=0$. The divisor is a natural number computed with a gcd that includes $N$, so $p\mid N$ and $p\ge1$; with $s=0$ or all $f_a(r)=0$ one gets $p=N$ and $q_0=1$. The quotients $\rho/X^\alpha$ and $N/p$ are exact natural-number divisions.
-- source:
--   Taehun Kang, Jebin Kim, Changmin Lee, JeongHwan Lee, STOC 2027 submission #1253 (October 2026), p. 16, §4.4 and Theorem 4.6 with its proof (PDF p. 17); p. 4, Definitions 2.4–2.5 (PDF p. 5); p. 5, coefficient matrix (PDF p. 6)

import Mathlib
import Definitions.Def_DualCoppersmith_Recovery_Lattice

set_option autoImplicit false

namespace DualCoppersmith.Recovery.Supplement

open LLLFactor.RedBasis

/-- §4.4: a public modulus `N ≥ 2`, not assumed prime. The root is not part of the input. -/
structure PublicInstance where
  ell : ℕ
  ell_pos : 0 < ell
  s : ℕ
  N : ℕ
  two_le_N : 2 ≤ N
  F : Fin s → MvPolynomial (Fin ell) ℤ
  X : Fin ell → ℕ
  X_pos : ∀ i, 0 < X i

/-- Definition 2.4's strict box only; §4.4 assumes no congruence of the target. -/
def IsBoxed (I : PublicInstance) (r : Fin I.ell → ℤ) : Prop :=
  ∀ i, |r i| < (I.X i : ℤ)

structure PublicParameters (I : PublicInstance) where
  m : ℕ
  t : ℕ
  m_pos : 0 < m
  t_pos : 0 < t

abbrev pubDimension (I : PublicInstance) (P : PublicParameters I) :=
  Fintype.card (Monomial I.ell P.t)

noncomputable def pubExponent (I : PublicInstance) (P : PublicParameters I)
    (j : Fin (pubDimension I P)) : Fin I.ell →₀ ℕ :=
  multiIndex ((monomialOrder I.ell P.t).symm j)

/-- The coordinate of the constant monomial `x^0`. -/
noncomputable def pubConstantIndex (I : PublicInstance) (P : PublicParameters I) :
    Fin (pubDimension I P) :=
  monomialOrder I.ell P.t ⟨fun _ => ⟨0, by omega⟩, by simp⟩

/-- The coordinate of the linear monomial `x_i` (exponent `e_i`). -/
noncomputable def pubLinearIndex (I : PublicInstance) (P : PublicParameters I) (i : Fin I.ell) :
    Fin (pubDimension I P) :=
  monomialOrder I.ell P.t
    ⟨fun j => ⟨if j = i then 1 else 0, by split <;> have := P.t_pos <;> omega⟩,
      by simpa using (Nat.succ_le_of_lt P.t_pos)⟩

abbrev PubMultiplicity (I : PublicInstance) (P : PublicParameters I) :=
  Fin I.s → Fin (P.m + 1)

def pubMultiplicityDegree (I : PublicInstance) (P : PublicParameters I)
    (i : PubMultiplicity I P) : ℕ :=
  ∑ a, (i a).val

noncomputable def pubShiftCore (I : PublicInstance) (P : PublicParameters I)
    (i : PubMultiplicity I P) (beta : Monomial I.ell P.t) : MvPolynomial (Fin I.ell) ℤ :=
  MvPolynomial.monomial (multiIndex beta) 1 * ∏ a, I.F a ^ (i a).val

/-- Total-degree shifts `x^β F^i` with `1 ≤ |i| ≤ m` and degree at most `t`;
    identically zero shifts are omitted (their rows impose only `0 = 0`). -/
noncomputable def pubShiftIndices (I : PublicInstance) (P : PublicParameters I) :
    Finset (PubMultiplicity I P × Monomial I.ell P.t) := by
  classical
  exact Finset.univ.filter fun q =>
    1 ≤ pubMultiplicityDegree I P q.1 ∧ pubMultiplicityDegree I P q.1 ≤ P.m ∧
      pubShiftCore I P q.1 q.2 ≠ 0 ∧ (pubShiftCore I P q.1 q.2).totalDegree ≤ P.t

/-- The shift `g_{i,β} = N^(m-|i|) x^β F^i`. -/
noncomputable def pubShift (I : PublicInstance) (P : PublicParameters I)
    (q : PubMultiplicity I P × Monomial I.ell P.t) : MvPolynomial (Fin I.ell) ℤ :=
  MvPolynomial.C ((I.N : ℤ) ^ (P.m - pubMultiplicityDegree I P q.1)) *
    pubShiftCore I P q.1 q.2

/-- The public shift coefficient matrix `A`. -/
noncomputable def pubCoefficientMatrix (I : PublicInstance) (P : PublicParameters I) :
    Matrix (pubShiftIndices I P) (Fin (pubDimension I P)) ℤ :=
  fun q j => MvPolynomial.coeff (pubExponent I P j) (pubShift I P q.val)

/-- `K = {z ∈ ℤ^n : A z ≡ 0 (mod N^m)}`. -/
noncomputable def pubIntegerKernel (I : PublicInstance) (P : PublicParameters I) :
    Submodule ℤ (Fin (pubDimension I P) → ℤ) where
  carrier := {z | ∀ q, (I.N : ℤ) ^ P.m ∣ ∑ j, pubCoefficientMatrix I P q j * z j}
  zero_mem' := by simp
  add_mem' := by
    intro z y hz hy q
    simpa only [Pi.add_apply, mul_add, Finset.sum_add_distrib] using dvd_add (hz q) (hy q)
  smul_mem' := by
    intro c z hz q
    simpa only [Pi.smul_apply, smul_eq_mul, mul_left_comm, ← Finset.mul_sum]
      using dvd_mul_of_dvd_right (hz q) c

noncomputable def pubKernelLattice (I : PublicInstance) (P : PublicParameters I) :
    Submodule ℤ (Vec (pubDimension I P)) :=
  (pubIntegerKernel I P).map (integerEmbedding (pubDimension I P))

noncomputable def pubBoundMonomial (I : PublicInstance) (P : PublicParameters I)
    (j : Fin (pubDimension I P)) : ℕ :=
  ∏ i, I.X i ^ (pubExponent I P j i)

/-- `ρ = lcm{X^α : α ∈ T_t}`. -/
noncomputable def pubRho (I : PublicInstance) (P : PublicParameters I) : ℕ :=
  Finset.univ.lcm (pubBoundMonomial I P)

/-- Exact integer quotient `ρ / X^α`; every denominator divides the positive lcm. -/
noncomputable def pubDiagonalFactor (I : PublicInstance) (P : PublicParameters I)
    (j : Fin (pubDimension I P)) : ℕ :=
  pubRho I P / pubBoundMonomial I P j

noncomputable def pubDiagonalMap (I : PublicInstance) (P : PublicParameters I) :
    Vec (pubDimension I P) →ₗ[ℝ] Vec (pubDimension I P) where
  toFun v := WithLp.toLp 2 (fun j => (pubDiagonalFactor I P j : ℝ) * v j)
  map_add' := by intro v w; ext j; simp [mul_add]
  map_smul' := by intro c v; ext j; simp [mul_left_comm]

/-- `L_X^⊥ = {((ρ/X^α) z_α)_α : z ∈ K}`, built modulo `N^m`. -/
noncomputable def pubScaledLattice (I : PublicInstance) (P : PublicParameters I) :
    Submodule ℤ (Vec (pubDimension I P)) :=
  (pubKernelLattice I P).map ((pubDiagonalMap I P).restrictScalars ℤ)

/-- `z_r = (r^α)_α`. -/
noncomputable def pubMonomialRoot (I : PublicInstance) (P : PublicParameters I)
    (r : Fin I.ell → ℤ) : Fin (pubDimension I P) → ℤ :=
  fun j => ∏ i, r i ^ (pubExponent I P j i)

/-- `v_r = ((ρ/X^α) r^α)_α`. -/
noncomputable def pubRootVector (I : PublicInstance) (P : PublicParameters I)
    (r : Fin I.ell → ℤ) : Vec (pubDimension I P) :=
  pubDiagonalMap I P (integerEmbedding (pubDimension I P) (pubMonomialRoot I P r))

/-- `p = gcd(N, f_1(r), …, f_s(r))` as a natural number; it divides `N`. -/
noncomputable def divisor (I : PublicInstance) (r : Fin I.ell → ℤ) : ℕ :=
  Nat.gcd I.N (Finset.univ.gcd fun a => (MvPolynomial.eval r (I.F a)).natAbs)

/-- `q_0 = N / p`, an exact quotient since `p ∣ N`. -/
noncomputable def cofactor (I : PublicInstance) (r : Fin I.ell → ℤ) : ℕ :=
  I.N / divisor I r

end DualCoppersmith.Recovery.Supplement


