-- Prove2me | Definitions.Def_QRH_arith
-- name    : QRH_arith
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-20T12:01:51.676553+00:00
-- url     : https://prove2.me/theorems/bc92fc36-b5f0-4a21-ac7c-dc2998bbfa6f
-- title:
--   The arithmetic of primary Eisenstein elements: the sextic residue symbol and normalized Gauss sums
-- statement:
--   A QRHWorld is an abstract interface for the arithmetic of the primary elements of the Eisenstein integers Z[omega] used by the source: a commutative monoid of primary elements with multiplication and unit, powers of elements, the squarefree elements, the elements prime to a fixed finite excluded set S (containing the primes above 2 and 3 and the conductor of the character), the primary primes, a positive multiplicative norm N into the reals, finite divisor sets with a complementary divisor b/d, the Mobius function with its inversion principle (the divisor sum is 1 at the unit and 0 elsewhere), the sextic residue symbol chi with its multiplicativity in both arguments, the sixth-power identity chi_n(p^6) = 0 when p divides n and 1 otherwise, cubic reciprocity chi_a(b)^2 = chi_b(a)^2, the phase alpha of modulus one, a fixed ray class group with its inverse and a symmetric plus-or-minus-one-valued reciprocity bicharacter, the ray class factor G with its cocycle identity G(vw) = G(v) G(w) R(v, w), the normalized Gauss sums gamma_j with the Gauss-Jacobi identities (gamma_2(n)^3 = mu(n) alpha(n), gamma_1(n) gamma_2(n) = mu(n) alpha(n) G(n), gamma_1(n) gamma_{-1}(n) = chi_n(-1), and the multiplicativity of gamma_2 up to the quadratic twist), and a fixed auxiliary ray class character xi. The structure is the carrier of the standard arithmetic identities of the source (Lemma 4.1 and Appendix B): unique factorization and the reciprocity law are not constructed, and every theorem that uses the world carries it as a hypothesis. The cubic Gauss-sum coefficient a_xi(n) = conj(alpha n) gamma_2(n) xi(n) of the dual family is defined from these data.
-- source:
--   The Quasi-Riemann Hypothesis, October 2026, Sections 2-4 (pp. 2-10) and Appendix B.

import Mathlib

universe u

/-!
# The Quasi-Riemann Hypothesis: the arithmetic world

An abstract interface for the arithmetic of the primary elements of the
Eisenstein integers Z[ω] that underlies the cubic theta argument of the
source: the commutative monoid of primary elements, the norm, the Möbius
function with its inversion principle, divisor sets with complementary
divisors, the sextic residue symbol, the phase function, the normalized
Gauss sums with their Gauss-Jacobi identities, and the ray class data of
the fixed modulus (section 4.1 and Appendix B of the paper). The
interface carries the standard identities as fields: unique
factorization and the reciprocity laws are not constructed, and every
statement built on the world carries the world as a hypothesis.
-/

namespace QRH

/-- The arithmetic world of the source: the multiplicative structure of
the primary Eisenstein integers with the norm, the Möbius function, the
divisor structure, the sextic residue symbol, the phase, the normalized
Gauss sums, and the ray class data of the fixed modulus. The fields
asserting equations are the standard arithmetic identities of the source
(Lemma 4.1 and Appendix B): the Gauss-Jacobi identities, the quadratic
Gauss-sum evaluations, and cubic reciprocity live in these fields. -/
structure QRHWorld where
  /-- the primary elements of the Eisenstein integers -/
  E : Type u
  /-- multiplication of primary elements -/
  mul : E → E → E
  /-- the unit element: the class of the unit ideal -/
  one : E
  mul_assoc : ∀ (a b c : E), mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ (a b : E), mul a b = mul b a
  one_mul : ∀ (a : E), mul one a = a
  mul_one : ∀ (a : E), mul a one = a
  /-- powers of an element -/
  wpow : E → ℕ → E
  wpow_zero : ∀ (a : E), wpow a 0 = one
  wpow_succ : ∀ (a : E) (k : ℕ), wpow a (k + 1) = mul a (wpow a k)
  wpow_mul : ∀ (a b : E) (k : ℕ), wpow (mul a b) k = mul (wpow a k) (wpow b k)
  /-- the squarefree primary elements -/
  IsSqf : E → Prop
  sqf_one : IsSqf one
  /-- the elements prime to the fixed finite set S of excluded primes:
  2, 3, and the primes dividing the conductor of the character -/
  Sgood : E → Prop
  Sgood_one : Sgood one
  Sgood_mul : ∀ (a b : E), Sgood a → Sgood b → Sgood (mul a b)
  Sgood_wpow : ∀ (a : E) (k : ℕ), Sgood a → Sgood (wpow a k)
  /-- the primary primes -/
  IsP : E → Prop
  prime_sqf : ∀ (p : E), IsP p → IsSqf p
  prime_sgood : ∀ (p : E), IsP p → Sgood p
  pow6_inj : ∀ (p q : E), IsP p → IsP q → wpow p 6 = wpow q 6 → p = q
  /-- the norm -/
  N : E → ℝ
  N_pos : ∀ (a : E), 0 < N a
  N_one : N one = 1
  N_mul : ∀ (a b : E), N (mul a b) = N a * N b
  N_wpow : ∀ (a : E) (k : ℕ), N (wpow a k) = N a ^ k
  /-- the finitely many divisors of an element -/
  divs : E → Finset E
  divs_refl : ∀ (a : E), a ∈ divs a
  divs_one : ∀ (d : E), d ∈ divs one → d = one
  divs_mul : ∀ (a b c d : E), a ∈ divs b → c ∈ divs d → mul a c ∈ divs (mul b d)
  /-- the complementary divisor: for d a divisor of b, the quotient b/d -/
  coDiv : E → E → E
  codiv_mul : ∀ (b d : E), d ∈ divs b → mul d (coDiv b d) = b
  codiv_mem : ∀ (b d : E), d ∈ divs b → coDiv b d ∈ divs b
  codiv_invol : ∀ (b d : E), d ∈ divs b → coDiv b (coDiv b d) = d
  /-- the Möbius function -/
  mu : E → ℂ
  mu_inversion_one : ∑ d ∈ divs one, mu d = 1
  mu_inversion_ne : ∀ (b : E), b ≠ one → ∑ d ∈ divs b, mu d = 0
  mu_sqf : ∀ (n : E), IsSqf n → mu n * mu n = 1
  mu_zero : ∀ (n : E), ¬ IsSqf n → mu n = 0
  /-- the sextic residue symbol; the first argument is the denominator -/
  chi : E → E → ℂ
  chi_mul_den : ∀ (a b u : E), chi (mul a b) u = chi a u * chi b u
  chi_mul_num : ∀ (n a b : E), chi n (mul a b) = chi n a * chi n b
  chi_one_num : ∀ (n : E), chi n one = 1
  chi_triv : ∀ (n u : E), chi n u = 0 ∨ ‖chi n u‖ = 1
  chi_sixth_mem : ∀ (n p : E), IsP p → p ∈ divs n → chi n (wpow p 6) = 0
  chi_sixth_coprime : ∀ (n p : E), IsP p → ¬ (p ∈ divs n) → chi n (wpow p 6) = 1
  recip_cubic : ∀ (a b : E), chi a b ^ 2 = chi b a ^ 2
  /-- the phase: alpha a is the unit complex number a / |a| -/
  alpha : E → ℂ
  alpha_mul : ∀ (a b : E), alpha (mul a b) = alpha a * alpha b
  alpha_abs : ∀ (a : E), ‖alpha a‖ = 1
  /-- the fixed ray class group of the fixed modulus -/
  C : Type u
  mulC : C → C → C
  oneC : C
  invC : C → C
  mulC_assoc : ∀ (a b c : C), mulC (mulC a b) c = mulC a (mulC b c)
  mulC_comm : ∀ (a b : C), mulC a b = mulC b a
  oneC_mul : ∀ (a : C), mulC oneC a = a
  mulC_one : ∀ (a : C), mulC a oneC = a
  invC_mul_cancel : ∀ (a : C), mulC (invC a) a = oneC
  mulC_inv_cancel : ∀ (a : C), mulC a (invC a) = oneC
  mulC_inv : ∀ (a b : C), invC (mulC a b) = mulC (invC a) (invC b)
  /-- the ray class of a primary element -/
  cl : E → C
  cl_mul : ∀ (a b : E), cl (mul a b) = mulC (cl a) (cl b)
  cl_one : cl one = oneC
  /-- the symmetric ±1-valued bicharacter of cubic reciprocity -/
  Rcl : C → C → ℂ
  Rcl_abs : ∀ (a b : C), ‖Rcl a b‖ = 1
  Rcl_real : ∀ (a b : C), Rcl a b = 1 ∨ Rcl a b = -1
  Rcl_symm : ∀ (a b : C), Rcl a b = Rcl b a
  Rcl_mul_left : ∀ (a a' b : C), Rcl (mulC a a') b = Rcl a b * Rcl a' b
  Rcl_mul_right : ∀ (a b b' : C), Rcl a (mulC b b') = Rcl a b * Rcl a b'
  Rcl_one_left : ∀ (a : C), Rcl oneC a = 1
  Rcl_one_right : ∀ (a : C), Rcl a oneC = 1
  /-- the value chi_n(-1) of the sextic symbol at -1 -/
  chiNeg : E → ℂ
  chiNeg_abs : ∀ (a : E), ‖chiNeg a‖ = 1
  /-- the fixed ray class factor G of the source -/
  Gcl : C → ℂ
  Gcl_abs : ∀ (a : C), ‖Gcl a‖ = 1
  Gcl_mul : ∀ (a b : C), Gcl (mulC a b) = Gcl a * Gcl b * Rcl a b
  Gcl_invC : ∀ (a : E), Gcl (invC (cl a)) = chiNeg a * (Gcl (cl a))⁻¹
  /-- the normalized Gauss sums gamma_j(n) of the source (equation 2.7) -/
  gamma : ℤ → E → ℂ
  gamma_abs : ∀ (j : ℤ) (n : E), IsSqf n → Sgood n → ‖gamma j n‖ = 1
  gamma_2_cube : ∀ (n : E), IsSqf n → Sgood n → gamma 2 n ^ 3 = mu n * alpha n
  gamma_1_2 : ∀ (n : E), IsSqf n → Sgood n →
    gamma 1 n * gamma 2 n = mu n * alpha n * Gcl (cl n)
  gamma_1_m1 : ∀ (n : E), IsSqf n → Sgood n → gamma 1 n * gamma (-1) n = chiNeg n
  gamma_2_mul : ∀ (a b : E), IsSqf a → IsSqf b → Sgood a → Sgood b →
    (∀ d : E, d ∈ divs a → d ∈ divs b → d = one) →
    gamma 2 (mul a b) = gamma 2 a * gamma 2 b * chi a b ^ 2 * chi b a ^ 2
  /-- the fixed auxiliary ray class character of the source, carrying the
  original twist and the residue-class factors -/
  xi : E → ℂ
  xi_mul : ∀ (a b : E), xi (mul a b) = xi a * xi b
  xi_one : xi one = 1

/-- The cubic Gauss-sum coefficient a_ξ(n) = conj(α n) γ₂(n) ξ(n) of the
dual family B_h of the source (section 4, the arithmetic identities of
Lemma 4.1). -/
def axi (W : QRHWorld) (n : W.E) : ℂ :=
  star (W.alpha n) * W.gamma 2 n * W.xi n

end QRH


