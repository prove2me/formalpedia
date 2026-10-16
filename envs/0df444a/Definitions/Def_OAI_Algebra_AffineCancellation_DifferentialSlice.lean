-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_DifferentialSlice
-- name    : OAI_Algebra_AffineCancellation_DifferentialSlice
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:41:23.819873+00:00
-- url     : https://prove2.me/theorems/d9f71d04-0524-47ae-bfe9-69bc1ee5db80
-- title:
--   Field of constants of a derivation, and elements killed by a power of $D$ are polynomials in a slice
-- statement:
--   Let $k$ be a commutative ring, $K$ a field that is a $k$-algebra, and $D\colon K\to K$ a $k$-linear derivation, so that $D(xy)=x\,D(y)+y\,D(x)$ for all $x,y\in K$. An element $t\in K$ with $D(t)=1$ is called a *slice* of $D$. For $n\ge 0$, $D^n$ denotes the $n$-fold iterate of $D$; for a polynomial $p$, $p'$ is its formal derivative and $p(t)$ its value at $t$.
--
--   1. **Field of constants.** The set
--   $$K^D=\{\,r\in K : D(r)=0\,\}$$
--   is a subfield of $K$, the field of constants of $D$.
--   2. **Differentiating along a slice.** If $D(t)=1$, then for every polynomial $p\in K^D[X]$ with constant coefficients,
--   $$D\bigl(p(t)\bigr)=p'(t).$$
--   3. **A slice is transcendental over the constants.** If $K$ has characteristic zero and $D(t)=1$, then the evaluation homomorphism $K^D[X]\to K$, $p\mapsto p(t)$, is injective.
--   4. **Antiderivatives.** If $F$ is any field of characteristic zero, every $p\in F[X]$ has an antiderivative: there is $q\in F[X]$ with $q'=p$.
--   5. **Elements annihilated by a power of $D$.** If $K$ has characteristic zero, $D(t)=1$, and $r\in K$ satisfies $D^n(r)=0$ for some $n\ge0$, then there is $p\in K^D[X]$ with
--   $$p(t)=r.$$
--
--   Since item 2 gives $D^m(p(t))=p^{(m)}(t)$, every element of $K^D[t]$ is killed by a power of $D$. Together with items 3 and 5 this shows that, in characteristic zero, the elements of $K$ on which $D$ acts nilpotently form exactly the subring $K^D[t]$, and that this subring is a polynomial ring in $t$ over $K^D$. This is a field-level version of the classical slice construction for locally nilpotent derivations; it is applied to the extension of a locally nilpotent derivation of a domain to its fraction field.
--
--   **Formalization Note** The field of constants is `constants D : Subfield K`, and evaluation at $t$ is `Polynomial.aeval t` for the algebra structure of $K$ over this subfield. Items 2 to 5 are `derivative_eval` (proved without the characteristic-zero assumption), `eval_injective`, `exists_antiderivative` and `nilpotent_is_polynomial`; the iterate is written `(D : K → K)^[n] r`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/DifferentialSlice.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/DifferentialSlice.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ComplexCancellation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DegenerationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveInvariant
import Definitions.Def_OAI_Algebra_AffineCancellation_RelativeClearing
import Definitions.Def_OAI_Algebra_AffineCancellation_FractionDerivation

namespace OAI

noncomputable section

namespace ComplexCancellation.DifferentialSlice
open Polynomial
variable {k K : Type*} [CommRing k] [Field K] [CharZero K] [Algebra k K]

/-- The field of constants of a derivation on a field. -/
def constants (D : Derivation k K K) : Subfield K where
  carrier := {r | D r = 0}
  zero_mem' := map_zero D
  one_mem' := D.map_one_eq_zero
  add_mem' := by
    intro r s hr hs
    change D r = 0 at hr
    change D s = 0 at hs
    change D (r+s) = 0
    rw [map_add, hr, hs, add_zero]
  mul_mem' := by
    intro r s hr hs
    change D r = 0 at hr
    change D s = 0 at hs
    change D (r*s) = 0
    rw [Derivation.leibniz, hr, hs, smul_zero, smul_zero, add_zero]
  neg_mem' := by
    intro r hr
    change D r = 0 at hr
    change D (-r) = 0
    rw [map_neg, hr, neg_zero]
  inv_mem' := by
    intro r hr
    change D r = 0 at hr
    change D r⁻¹ = 0
    rw [Derivation.leibniz_inv, hr, smul_zero]

omit [CharZero K] in
lemma derivative_eval (D : Derivation k K K) {t : K} (ht : D t = 1)
    (p : Polynomial (constants D)) :
    D (aeval t p) = aeval t p.derivative := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n c =>
    simp only [aeval_monomial, derivative_monomial, map_mul, map_natCast,
      aeval_monomial, Derivation.leibniz, Derivation.leibniz_pow, ht, smul_eq_mul, nsmul_eq_mul]
    have hc : D (c : K) = 0 := c.property
    change (c:K) * ((n:K) * (t^(n-1) * 1)) + t^n * D (c:K) =
      (c:K) * (n:K) * t^(n-1)
    rw [hc]
    ring

lemma eval_injective (D : Derivation k K K) {t : K} (ht : D t = 1) :
    Function.Injective (aeval t : Polynomial (constants D) →ₐ[constants D] K) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro p
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    intro hp
    by_cases hdeg : p.natDegree = 0
    · rw [eq_C_of_natDegree_eq_zero hdeg] at hp ⊢
      simp only [aeval_C, map_eq_zero] at hp ⊢
      exact hp
    · have hder : p.derivative = 0 := ih p.derivative.natDegree (by rw [← hn]; exact natDegree_derivative_lt hdeg) p.derivative rfl (by
        rw [← derivative_eval D ht, hp, map_zero])
      have hc := eq_C_of_derivative_eq_zero hder
      rw [hc] at hp ⊢
      simp only [aeval_C, map_eq_zero] at hp ⊢
      exact hp

lemma exists_antiderivative {F : Type*} [Field F] [CharZero F] (p : Polynomial F) :
    ∃ q : Polynomial F, q.derivative = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨p', hp'⟩ := hp
    obtain ⟨q', hq'⟩ := hq
    exact ⟨p'+q', by rw [derivative_add, hp', hq']⟩
  | monomial n c =>
    refine ⟨monomial (n+1) (c / (n+1)), ?_⟩
    rw [derivative_monomial]
    have hn : (n:F)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simp [hn]

lemma nilpotent_is_polynomial (D : Derivation k K K) {t r : K} (ht : D t = 1)
    (hr : ∃ n : ℕ, (D : K → K)^[n] r = 0) :
    ∃ p : Polynomial (constants D), aeval t p = r := by
  obtain ⟨n, hr⟩ := hr
  induction n generalizing r with
  | zero => exact ⟨0, by simpa using hr.symm⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply] at hr
    obtain ⟨p, hp⟩ := ih hr
    obtain ⟨q, hqp⟩ := exists_antiderivative p
    have hq : D (aeval t q) = D r := by
      rw [derivative_eval D ht]
      rw [hqp, hp]
    let c : constants D := ⟨r - aeval t q, by change D (r-aeval t q) = 0; rw [map_sub, hq, sub_self]⟩
    refine ⟨q + C c, ?_⟩
    simp only [map_add, aeval_C]
    change aeval t q + (r - aeval t q) = r
    ring

end ComplexCancellation.DifferentialSlice

end

end OAI


