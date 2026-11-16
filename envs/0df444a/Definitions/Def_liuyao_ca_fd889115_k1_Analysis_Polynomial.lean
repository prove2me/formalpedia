-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Polynomial
-- name    : liuyao_ca_fd889115_k1_Analysis_Polynomial
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:50:45.235577+00:00
-- url     : https://prove2.me/theorems/525c4263-065d-40c5-8d5e-08fa808317dd
-- title:
--   Computable analysis · Polynomial · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/Polynomial.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Basic

set_option autoImplicit true

namespace ComputableAnalysis

namespace Polynomial

def eval (coeffs : List Rat) (x : Rat) : Rat := coeffs.foldr (fun c acc => c + x * acc) 0

def derivative : List Rat -> List Rat
  | [] => []
  | _ :: cs => cs.zipIdx.map (fun (c, i) => ((i + 1 : Nat) : Rat) * c)

/-- The zero-constant formal antiderivative of a rational polynomial.
Coefficient `c_i` is shifted to degree `i+1` and divided by `i+1`; hence the
construction is finite and executable over rationals. -/
def primitive (coeffs : List Rat) : List Rat :=
  0 :: coeffs.zipIdx.map
    (fun (c, i) => c / (((i + 1 : Nat) : Rat)))

private theorem derivative_primitive_aux (coeffs : List Rat) (index : Nat) :
    (((coeffs.zipIdx index).map
        (fun (c, i) => c / (((i + 1 : Nat) : Rat)))).zipIdx index).map
      (fun (c, i) => (((i + 1 : Nat) : Rat)) * c) = coeffs := by
  induction coeffs generalizing index with
  | nil => simp
  | cons coefficient rest ih =>
      simp only [List.zipIdx, List.map_cons]
      congr 1
      · have hne : (((index + 1 : Nat) : Rat)) ≠ 0 :=
          Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.succ_pos index))
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      · exact ih (index + 1)

/-- Formal differentiation is a left inverse of the executable rational
polynomial primitive. -/
theorem derivative_primitive (coeffs : List Rat) :
    derivative (primitive coeffs) = coeffs := by
  unfold derivative primitive
  exact derivative_primitive_aux coeffs 0

/-- Executable pointwise evaluation of the formal derivative list.  The
coefficient index is carried explicitly so the construction remains a finite
natural-number recursion. -/
def derivativeEvalAux : List Rat -> Nat -> Rat -> Rat
  | [], _index, _x => 0
  | c :: cs, index, x =>
      ((index + 1 : Nat) : Rat) * c * x ^ index +
        derivativeEvalAux cs (index + 1) x

def derivativeEval (coeffs : List Rat) (x : Rat) : Rat :=
  match coeffs with
  | [] => 0
  | _ :: cs => derivativeEvalAux cs 0 x

theorem pow_mul_eval_zipIdx_eq_derivativeEvalAux
    (coeffs : List Rat) (index : Nat) (x : Rat) :
    x ^ index * eval (coeffs.zipIdx index |>.map
      (fun (c, i) => ((i + 1 : Nat) : Rat) * c)) x =
      derivativeEvalAux coeffs index x := by
  induction coeffs generalizing index with
  | nil =>
      simp [eval, derivativeEvalAux]
  | cons coefficient tail ih =>
      change x ^ index *
        ((((index + 1 : Nat) : Rat) * coefficient) +
          x * eval
            ((tail.zipIdx (index + 1)).map
              (fun (c, i) => ((i + 1 : Nat) : Rat) * c)) x) =
        ((index + 1 : Nat) : Rat) * coefficient * x ^ index +
          derivativeEvalAux tail (index + 1) x
      have hih := ih (index + 1)
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
        Rat.pow_succ]

theorem eval_derivative_eq_derivativeEval (coeffs : List Rat) (x : Rat) :
    eval (derivative coeffs) x = derivativeEval coeffs x := by
  cases coeffs with
  | nil =>
      simp [derivative, derivativeEval, eval]
  | cons constant tail =>
      change eval
          ((tail.zipIdx 0).map
            (fun (c, i) => ((i + 1 : Nat) : Rat) * c)) x =
        derivativeEvalAux tail 0 x
      simpa using pow_mul_eval_zipIdx_eq_derivativeEvalAux tail 0 x

theorem eval_derivative_linear (c₀ c₁ x : Rat) :
    eval (derivative [c₀, c₁]) x = c₁ := by
  simp [derivative, eval]
  grind

theorem eval_derivative_quadratic (c₀ c₁ c₂ x : Rat) :
    eval (derivative [c₀, c₁, c₂]) x = c₁ + 2 * c₂ * x := by
  simp [derivative, eval]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem eval_derivative_cubic (c₀ c₁ c₂ c₃ x : Rat) :
    eval (derivative [c₀, c₁, c₂, c₃]) x =
      c₁ + 2 * c₂ * x + 3 * c₃ * x ^ 2 := by
  simp [derivative, eval]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem eval_derivative_quartic (c₀ c₁ c₂ c₃ c₄ x : Rat) :
    eval (derivative [c₀, c₁, c₂, c₃, c₄]) x =
      c₁ + 2 * c₂ * x + 3 * c₃ * x ^ 2 + 4 * c₄ * x ^ 3 := by
  simp [derivative, eval]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem eval_derivative_quintic (c₀ c₁ c₂ c₃ c₄ c₅ x : Rat) :
    eval (derivative [c₀, c₁, c₂, c₃, c₄, c₅]) x =
      c₁ + 2 * c₂ * x + 3 * c₃ * x ^ 2 + 4 * c₄ * x ^ 3 +
        5 * c₅ * x ^ 4 := by
  simp [derivative, eval]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem eval_derivative_sextic (c₀ c₁ c₂ c₃ c₄ c₅ c₆ x : Rat) :
    eval (derivative [c₀, c₁, c₂, c₃, c₄, c₅, c₆]) x =
      c₁ + 2 * c₂ * x + 3 * c₃ * x ^ 2 + 4 * c₄ * x ^ 3 +
        5 * c₅ * x ^ 4 + 6 * c₆ * x ^ 5 := by
  simp [derivative, eval]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem eval_derivative_septic (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ x : Rat) :
    eval (derivative [c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇]) x =
      c₁ + 2 * c₂ * x + 3 * c₃ * x ^ 2 + 4 * c₄ * x ^ 3 +
        5 * c₅ * x ^ 4 + 6 * c₆ * x ^ 5 + 7 * c₇ * x ^ 6 := by
  simp [derivative, eval]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

/-! Exact finite secant identities expose the constructive content behind the
quadratic mean-value example.  The error from the left derivative is a
literal rational multiple of the step; no intermediate real point is used. -/

theorem quadratic_secant_quotient (c₀ c₁ c₂ x h : Rat) (hh : h ≠ 0) :
    (eval [c₀, c₁, c₂] (x + h) - eval [c₀, c₁, c₂] x) / h =
      c₁ + c₂ * (2 * x + h) := by
  simp [eval]
  rw [Rat.div_def]
  have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
    Rat.mul_comm, Rat.pow_succ]

theorem quadratic_secant_minus_derivative (c₀ c₁ c₂ x h : Rat) (hh : h ≠ 0) :
    ((eval [c₀, c₁, c₂] (x + h) - eval [c₀, c₁, c₂] x) / h) -
        eval (derivative [c₀, c₁, c₂]) x = c₂ * h := by
  rw [quadratic_secant_quotient c₀ c₁ c₂ x h hh,
    eval_derivative_quadratic]
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

def asFunRaw (coeffs : List Rat) : RealFunRaw := RealFunRaw.exact (eval coeffs)

def syntheticDivide (r : Rat) : List Rat -> List Rat × Rat
  | [] => ([], 0)
  | c :: cs =>
      let qr := syntheticDivide r cs
      (qr.2 :: qr.1, c + r * qr.2)

theorem syntheticDivide_spec (r x : Rat) (coeffs : List Rat) :
    let qr := syntheticDivide r coeffs
    eval coeffs x = qr.2 + (x - r) * eval qr.1 x := by
  induction coeffs with
  | nil =>
      simp [syntheticDivide, eval]
      grind
  | cons c cs ih =>
      have hih :
          List.foldr (fun c acc => c + x * acc) 0 cs =
            (syntheticDivide r cs).2 +
              (x - r) *
                List.foldr (fun c acc => c + x * acc) 0
                  (syntheticDivide r cs).1 := by
        simpa [eval] using ih
      simp only [syntheticDivide, eval, List.foldr]
      rw [hih]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm]

theorem syntheticDivide_factor_of_root
    {r x : Rat} {coeffs : List Rat}
    (hroot : eval coeffs r = 0) :
    let qr := syntheticDivide r coeffs
    eval coeffs x = (x - r) * eval qr.1 x := by
  have hspec := syntheticDivide_spec r x coeffs
  have hroot_spec := syntheticDivide_spec r r coeffs
  simp at hroot_spec
  dsimp at hspec ⊢
  grind [Rat.sub_eq_add_neg]

theorem syntheticDivide_remainder_eq_eval (r : Rat) (coeffs : List Rat) :
    (syntheticDivide r coeffs).2 = eval coeffs r := by
  have hspec := syntheticDivide_spec r r coeffs
  simp at hspec
  grind

/-! A reusable finite remainder certificate.

The quotient and remainder are data produced by the rational synthetic
division algorithm.  The certificate packages the two facts needed by the
linear/quadratic/cubic/quartic interfaces below: evaluation is a remainder
plus a finite factor times the quotient, and the remainder is the evaluation
at the supplied rational point.  This is an interface for a finite list of
coefficients, not an arbitrary-degree existence theorem. -/

structure RemainderCertificate (coeffs : List Rat) (r : Rat) where
  quotient : List Rat
  remainder : Rat
  factor_remainder : ∀ x : Rat,
    eval coeffs x = remainder + (x - r) * eval quotient x
  remainder_value : remainder = eval coeffs r

def syntheticRemainderCertificate (r : Rat) (coeffs : List Rat) :
    RemainderCertificate coeffs r where
  quotient := (syntheticDivide r coeffs).1
  remainder := (syntheticDivide r coeffs).2
  factor_remainder x := by
    simpa using syntheticDivide_spec r x coeffs
  remainder_value := syntheticDivide_remainder_eq_eval r coeffs

theorem RemainderCertificate.factor_remainder_at
    {coeffs : List Rat} {r x : Rat}
    (certificate : RemainderCertificate coeffs r) :
    eval coeffs x = certificate.remainder +
      (x - r) * eval certificate.quotient x := by
  exact certificate.factor_remainder x

theorem RemainderCertificate.remainder_eq_eval
    {coeffs : List Rat} {r : Rat}
    (certificate : RemainderCertificate coeffs r) :
    certificate.remainder = eval coeffs r := by
  exact certificate.remainder_value

theorem RemainderCertificate.factor_of_root
    {coeffs : List Rat} {r x : Rat}
    (certificate : RemainderCertificate coeffs r)
  (hroot : eval coeffs r = 0) :
    eval coeffs x = (x - r) * eval certificate.quotient x := by
  rw [certificate.factor_remainder x, certificate.remainder_value, hroot]
  grind

theorem RemainderCertificate.remainder_eq_zero_iff
    {coeffs : List Rat} {r : Rat}
    (certificate : RemainderCertificate coeffs r) :
    certificate.remainder = 0 ↔ eval coeffs r = 0 := by
  rw [certificate.remainder_value]

theorem syntheticRemainderCertificate_factor_remainder
    (r x : Rat) (coeffs : List Rat) :
    eval coeffs x = eval coeffs r +
      (x - r) * eval (syntheticDivide r coeffs).1 x := by
  rw [← syntheticDivide_remainder_eq_eval r coeffs]
  exact syntheticDivide_spec r x coeffs

theorem syntheticRemainderCertificate_factor_of_root
    {r x : Rat} {coeffs : List Rat}
  (hroot : eval coeffs r = 0) :
    eval coeffs x = (x - r) * eval (syntheticDivide r coeffs).1 x := by
  exact syntheticDivide_factor_of_root hroot

theorem syntheticDivide_remainder_eq_zero_iff (r : Rat) (coeffs : List Rat) :
    (syntheticDivide r coeffs).2 = 0 ↔ eval coeffs r = 0 := by
  rw [syntheticDivide_remainder_eq_eval]

theorem syntheticDivide_secant_quotient
    (x h : Rat) (coeffs : List Rat) (hh : h ≠ 0) :
    (eval coeffs (x + h) - eval coeffs x) / h =
      eval (syntheticDivide x coeffs).1 (x + h) := by
  let qr := syntheticDivide x coeffs
  have hright : eval coeffs (x + h) =
      qr.2 + ((x + h) - x) * eval qr.1 (x + h) := by
    simpa [qr] using syntheticDivide_spec x (x + h) coeffs
  have hleft : eval coeffs x = qr.2 := by
    have hspec := syntheticDivide_spec x x coeffs
    have hxx : x - x = 0 := by grind
    rw [hxx] at hspec
    simpa [qr, Rat.add_zero] using hspec
  rw [hright, hleft, Rat.div_def]
  have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem linear_remainder (c a x : Rat) :
    eval [c, a] x = eval [c, a] 0 + a * x := by
  simp [eval]
  grind

theorem linear_factor_of_root {c a r x : Rat}
    (hroot : eval [c, a] r = 0) :
    eval [c, a] x = a * (x - r) := by
  simp [eval] at hroot ⊢
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem linear_root_iff_constant_eq_neg_mul {c a r : Rat} :
    eval [c, a] r = 0 ↔ c = -(a * r) := by
  simp [eval]
  constructor <;> intro h
  · grind
  · grind

/-! A factorized polynomial with a supplied finite list of rational roots.

This representation is deliberately finite: its root witness is exactly a
membership proof in the supplied list, with no appeal to completeness or a
general fundamental theorem of algebra. -/

def factorizedEval (constant : Rat) (roots : List Rat) (x : Rat) : Rat :=
  constant * roots.foldr (fun r acc => (x - r) * acc) 1

theorem factorizedEval_append
    (constant x : Rat) (roots extraRoots : List Rat) :
    factorizedEval constant (roots ++ extraRoots) x =
      factorizedEval 1 roots x * factorizedEval constant extraRoots x := by
  have hfold : ∀ xs : List Rat,
      (xs ++ extraRoots).foldr (fun r acc => (x - r) * acc) 1 =
        xs.foldr (fun r acc => (x - r) * acc) 1 *
          extraRoots.foldr (fun r acc => (x - r) * acc) 1 := by
    intro xs
    induction xs with
    | nil => simp
    | cons r xs ih =>
        simp only [List.cons_append, List.foldr]
        rw [ih]
        grind [Rat.mul_assoc, Rat.mul_comm]
  unfold factorizedEval
  rw [hfold roots]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem factorizedEval_root_witness
    {constant x : Rat} {roots : List Rat}
    (hconstant : constant ≠ 0) :
    factorizedEval constant roots x = 0 ↔ x ∈ roots := by
  unfold factorizedEval
  induction roots with
  | nil =>
      simp [hconstant]
  | cons r roots ih =>
      simp only [List.foldr, Rat.mul_eq_zero, hconstant, false_or]
      have hsub : x - r = 0 ↔ x = r := by
        constructor <;> intro h
        · grind
        · grind
      have htail :
          roots.foldr (fun r acc => (x - r) * acc) 1 = 0 ↔ x ∈ roots := by
        constructor
        · intro hzero
          exact ih.mp (by
            rw [hzero]
            simp)
        · intro hmem
          have hzero := ih.mpr hmem
          rcases Rat.mul_eq_zero.mp hzero with hconstantzero | htailzero
          · exact False.elim (hconstant hconstantzero)
          · exact htailzero
      rw [hsub, htail]
      simp

theorem quadratic_factor_of_root {c₀ c₁ c₂ r x : Rat}
    (hroot : eval [c₀, c₁, c₂] r = 0) :
    eval [c₀, c₁, c₂] x =
      (x - r) * (c₂ * x + c₁ + c₂ * r) := by
  simp [eval] at hroot ⊢
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

/-! A monic quadratic with two supplied rational factors has an exact finite
root certificate: a rational input is a zero precisely when it is one of the
two factor roots.  This is a rational root-count consequence, not a claim
about arbitrary quadratic or higher-degree roots. -/

theorem monic_quadratic_root_iff
    (r s x : Rat) :
    eval [r * s, -(r + s), 1] x = 0 ↔ x = r ∨ x = s := by
  have hfactor :
      eval [r * s, -(r + s), 1] x = (x - r) * (x - s) := by
    simp [eval]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
  rw [hfactor]
  constructor
  · intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hleft | hright
    · left
      grind
    · right
      grind
  · intro hroot
    rcases hroot with hroot | hroot
    · subst x
      grind [Rat.sub_eq_add_neg]
    · subst x
      grind [Rat.sub_eq_add_neg]

/-! The factor certificate gives a finite rational root-count bound: among any
three rational candidates, at least two coincide.  This is deliberately a
bounded statement about supplied rational factors, not a general theorem
about real roots or arbitrary-degree polynomials. -/

theorem monic_quadratic_root_count_le_two
    (r s x y z : Rat)
    (hx : eval [r * s, -(r + s), 1] x = 0)
    (hy : eval [r * s, -(r + s), 1] y = 0)
    (hz : eval [r * s, -(r + s), 1] z = 0) :
    x = y ∨ x = z ∨ y = z := by
  have hx' := (monic_quadratic_root_iff r s x).mp hx
  have hy' := (monic_quadratic_root_iff r s y).mp hy
  have hz' := (monic_quadratic_root_iff r s z).mp hz
  rcases hx' with hxr | hxs <;>
    rcases hy' with hyr | hys <;>
      rcases hz' with hzr | hzs <;>
        grind

theorem quadratic_remainder (c₀ c₁ c₂ r x : Rat) :
    eval [c₀, c₁, c₂] x = eval [c₀, c₁, c₂] r +
      (x - r) * (c₂ * x + c₁ + c₂ * r) := by
  simp [eval]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem cubic_remainder (c₀ c₁ c₂ c₃ r x : Rat) :
    eval [c₀, c₁, c₂, c₃] x = eval [c₀, c₁, c₂, c₃] r +
      (x - r) *
        (c₃ * x ^ 2 + (c₂ + c₃ * r) * x +
          (c₁ + c₂ * r + c₃ * r ^ 2)) := by
  simp [eval]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem cubic_factor_of_root {c₀ c₁ c₂ c₃ r x : Rat}
    (hroot : eval [c₀, c₁, c₂, c₃] r = 0) :
    eval [c₀, c₁, c₂, c₃] x =
      (x - r) *
        (c₃ * x ^ 2 + (c₂ + c₃ * r) * x +
          (c₁ + c₂ * r + c₃ * r ^ 2)) := by
  rw [cubic_remainder, hroot]
  grind

theorem cubic_example_factorization (x : Rat) :
    eval [-6, 11, -6, 1] x = (x - 1) * (x - 2) * (x - 3) := by
  simp [eval]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem cubic_example_roots :
    eval [-6, 11, -6, 1] 1 = 0 ∧
      eval [-6, 11, -6, 1] 2 = 0 ∧
        eval [-6, 11, -6, 1] 3 = 0 := by
  simp only [cubic_example_factorization]
  decide +kernel

theorem cubic_example_root_iff (x : Rat) :
    eval [-6, 11, -6, 1] x = 0 ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  rw [cubic_example_factorization]
  constructor
  · intro h
    rcases Rat.mul_eq_zero.mp h with h12 | h3
    · rcases Rat.mul_eq_zero.mp h12 with h1 | h2
      · left
        grind
      · right
        left
        grind
    · right
      right
      grind
  · rintro (rfl | rfl | rfl) <;> decide +kernel

theorem quartic_example_factorization (x : Rat) :
    eval [4, 0, -5, 0, 1] x =
      (x - 2) * (x + 2) * (x - 1) * (x + 1) := by
  simp [eval]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem quartic_example_roots :
    eval [4, 0, -5, 0, 1] (-2) = 0 ∧
      eval [4, 0, -5, 0, 1] (-1) = 0 ∧
        eval [4, 0, -5, 0, 1] 1 = 0 ∧
          eval [4, 0, -5, 0, 1] 2 = 0 := by
  simp only [quartic_example_factorization]
  decide +kernel

theorem quartic_example_root_iff (x : Rat) :
    eval [4, 0, -5, 0, 1] x = 0 ↔
      x = -2 ∨ x = -1 ∨ x = 1 ∨ x = 2 := by
  rw [quartic_example_factorization]
  constructor
  · intro h
    rcases Rat.mul_eq_zero.mp h with h123 | h4
    · rcases Rat.mul_eq_zero.mp h123 with h12 | h3
      · rcases Rat.mul_eq_zero.mp h12 with h1 | h2
        · right
          right
          right
          grind
        · left
          grind
      · right
        right
        left
        grind
    · right
      left
      grind
  · rintro (rfl | rfl | rfl | rfl) <;> decide +kernel

theorem quartic_remainder (c₀ c₁ c₂ c₃ c₄ r x : Rat) :
    eval [c₀, c₁, c₂, c₃, c₄] x = eval [c₀, c₁, c₂, c₃, c₄] r +
      (x - r) *
        (c₄ * x ^ 3 + (c₃ + c₄ * r) * x ^ 2 +
          (c₂ + c₃ * r + c₄ * r ^ 2) * x +
          (c₁ + c₂ * r + c₃ * r ^ 2 + c₄ * r ^ 3)) := by
  simp [eval]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

/-! A rational root of a quartic produces an explicit cubic quotient.  This
is the finite factorization certificate used here; it is not a general FTA
claim or a quartic root formula. -/

theorem quartic_factor_of_root {c₀ c₁ c₂ c₃ c₄ r x : Rat}
    (hroot : eval [c₀, c₁, c₂, c₃, c₄] r = 0) :
    eval [c₀, c₁, c₂, c₃, c₄] x =
      (x - r) *
        (c₄ * x ^ 3 + (c₃ + c₄ * r) * x ^ 2 +
          (c₂ + c₃ * r + c₄ * r ^ 2) * x +
          (c₁ + c₂ * r + c₃ * r ^ 2 + c₄ * r ^ 3)) := by
  rw [quartic_remainder, hroot]
  grind

def signChangeCount : List Rat -> Nat
  | [] => 0
  | [_] => 0
  | a :: b :: cs =>
      (if a * b < 0 then 1 else 0) + signChangeCount (b :: cs)

def signChangeCountIgnoringZeros (coeffs : List Rat) : Nat :=
  signChangeCount (coeffs.filter (fun c => c != 0))

theorem signChangeCountIgnoringZeros_quadratic
    {a b c : Rat} (ha : 0 < a) (hb : b < 0) (hc : 0 < c) :
    signChangeCountIgnoringZeros [a, b, c] = 2 := by
  have ha0 : a ≠ 0 := Rat.ne_of_gt ha
  have hb0 : b ≠ 0 := Rat.ne_of_lt hb
  have hc0 : c ≠ 0 := Rat.ne_of_gt hc
  have hab : a * b < 0 := (Rat.mul_neg_iff_of_pos_left ha).2 hb
  have hbc : b * c < 0 := (Rat.mul_neg_iff_of_pos_right hc).2 hb
  simp [signChangeCountIgnoringZeros, signChangeCount, ha0, hb0, hc0,
    hab, hbc]

/-! A finite discriminant certificate complements the quadratic sign count.
For a rational root of `a*x^2 + b*x + c`, the discriminant is the square of
the rational witness `2*a*x + b`.  Thus a negative rational discriminant is
an executable root-exclusion certificate. -/

theorem quadratic_root_discriminant_nonneg
    {a b c x : Rat} (hroot : eval [c, b, a] x = 0) :
    0 <= b * b - 4 * a * c := by
  have hsq : 0 <= (2 * a * x + b) * (2 * a * x + b) := by
    by_cases h : 0 <= 2 * a * x + b
    · exact Rat.mul_nonneg h h
    · have hneg : 0 <= -(2 * a * x + b) := by grind
      have hsq' := Rat.mul_nonneg hneg hneg
      grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
  simp [eval] at hroot
  grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem no_rational_root_of_quadratic_discriminant_neg
    {a b c : Rat} (hdisc : b * b - 4 * a * c < 0) :
    ¬ Exists fun x : Rat => eval [c, b, a] x = 0 := by
  rintro ⟨x, hroot⟩
  have hnonneg := quadratic_root_discriminant_nonneg hroot
  grind

theorem quadratic_three_distinct_roots_impossible
    {a b c x y z : Rat} (ha : a ≠ 0)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : eval [c, b, a] x = 0)
    (hy : eval [c, b, a] y = 0)
    (hz : eval [c, b, a] z = 0) :
    False := by
  simp [eval] at hx hy hz
  have hxy_factor : (x - y) * (b + a * (x + y)) = 0 := by
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hxz_factor : (x - z) * (b + a * (x + z)) = 0 := by
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hxy_sum : b + a * (x + y) = 0 := by
    rcases Rat.mul_eq_zero.mp hxy_factor with h | h
    · exact False.elim (hxy (by grind))
    · exact h
  have hxz_sum : b + a * (x + z) = 0 := by
    rcases Rat.mul_eq_zero.mp hxz_factor with h | h
    · exact False.elim (hxz (by grind))
    · exact h
  have hyz_zero : a * (y - z) = 0 := by
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  rcases Rat.mul_eq_zero.mp hyz_zero with h | h
  · exact False.elim (ha h)
  · exact hyz (by grind)

theorem eval_nonneg_of_nonneg_coeffs {coeffs : List Rat} {x : Rat}
    (hcoeffs : forall c, c ∈ coeffs -> 0 <= c) (hx : 0 <= x) :
    0 <= eval coeffs x := by
  induction coeffs with
  | nil => simp [eval]
  | cons c cs ih =>
      simp only [eval, List.foldr]
      exact Rat.add_nonneg (hcoeffs c (by simp))
        (Rat.mul_nonneg hx (ih (fun d hd => hcoeffs d (by simp [hd]))))

theorem eval_nonpos_of_nonpos_coeffs {coeffs : List Rat} {x : Rat}
    (hcoeffs : forall c, c ∈ coeffs -> c <= 0) (hx : 0 <= x) :
    eval coeffs x <= 0 := by
  induction coeffs with
  | nil => simp [eval]
  | cons c cs ih =>
      simp only [eval, List.foldr]
      have htail : eval cs x <= 0 :=
        ih (fun d hd => hcoeffs d (by simp [hd]))
      have hneg : 0 <= -(eval cs x) := by grind
      have hterm0 : 0 <= x * (-(eval cs x)) := Rat.mul_nonneg hx hneg
      have hterm : x * eval cs x <= 0 := by
        grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg]
      have hc : c <= 0 := hcoeffs c (by simp)
      change c + x * eval cs x <= 0
      grind

theorem eval_pos_of_nonneg_coeffs_of_pos
    {coeffs : List Rat} {x : Rat}
    (hcoeffs : forall c, c ∈ coeffs -> 0 <= c) (hx : 0 < x)
    {c₀ : Rat} (hc₀ : c₀ ∈ coeffs) (hc₀pos : 0 < c₀) :
    0 < eval coeffs x := by
  induction coeffs with
  | nil => simp at hc₀
  | cons c cs ih =>
      simp only [eval, List.foldr]
      have htail_nonneg : 0 <= eval cs x :=
        eval_nonneg_of_nonneg_coeffs
          (fun d hd => hcoeffs d (by simp [hd])) (Rat.le_of_lt hx)
      by_cases hhead : c₀ = c
      · subst c₀
        have hsum : 0 < c + x * eval cs x := by
          have hmul : 0 <= x * eval cs x :=
            Rat.mul_nonneg (Rat.le_of_lt hx) htail_nonneg
          grind
        exact hsum
      · have htail : c₀ ∈ cs := by
          simpa [hhead] using hc₀
        have hih := ih
          (fun d hd => hcoeffs d (by simp [hd])) htail
        have hc : 0 <= c := hcoeffs c (by simp)
        have hmul_pos : 0 < x * eval cs x := Rat.mul_pos hx hih
        change 0 < c + x * eval cs x
        grind

theorem eval_ne_zero_of_nonneg_coeffs_of_pos
    {coeffs : List Rat} {x : Rat}
    (hcoeffs : forall c, c ∈ coeffs -> 0 <= c) (hx : 0 < x)
    {c₀ : Rat} (hc₀ : c₀ ∈ coeffs) (hc₀pos : 0 < c₀) :
    eval coeffs x ≠ 0 := by
  exact Rat.ne_of_gt (eval_pos_of_nonneg_coeffs_of_pos
    hcoeffs hx hc₀ hc₀pos)

theorem eval_pos_of_nonneg_cons_of_pos
    {c₀ : Rat} {cs : List Rat} {x : Rat}
    (hc₀pos : 0 < c₀)
    (hcoeffs : forall c, c ∈ cs -> 0 <= c) (hx : 0 <= x) :
    0 < eval (c₀ :: cs) x := by
  simp only [eval, List.foldr]
  have htail : 0 <= eval cs x :=
    eval_nonneg_of_nonneg_coeffs hcoeffs hx
  have hmul : 0 <= x * eval cs x := Rat.mul_nonneg hx htail
  change 0 < c₀ + x * eval cs x
  grind

theorem no_nonnegative_root_of_nonneg_cons_of_pos
    {c₀ : Rat} {cs : List Rat}
    (hc₀pos : 0 < c₀)
    (hcoeffs : forall c, c ∈ cs -> 0 <= c) :
    ¬ Exists fun x : Rat => 0 <= x ∧ eval (c₀ :: cs) x = 0 := by
  intro hroot
  rcases hroot with ⟨x, hx, hzero⟩
  have hpos := eval_pos_of_nonneg_cons_of_pos hc₀pos hcoeffs hx
  grind

theorem no_positive_root_of_nonneg_coeffs_of_pos
    {coeffs : List Rat}
    (hcoeffs : forall c, c ∈ coeffs -> 0 <= c)
    {c₀ : Rat} (hc₀ : c₀ ∈ coeffs) (hc₀pos : 0 < c₀) :
    ¬ Exists fun x : Rat => 0 < x /\ eval coeffs x = 0 := by
  intro hroot
  rcases hroot with ⟨x, hx, hzero⟩
  exact eval_ne_zero_of_nonneg_coeffs_of_pos hcoeffs hx hc₀ hc₀pos hzero

theorem signChangeCount_zero_of_nonneg
    {coeffs : List Rat}
    (hcoeffs : forall c, c ∈ coeffs -> 0 <= c) :
    signChangeCount coeffs = 0 := by
  induction coeffs with
  | nil => rfl
  | cons a cs ih =>
      cases cs with
      | nil => rfl
      | cons b cs =>
          have ha : 0 <= a := hcoeffs a (by simp)
          have hb : 0 <= b := hcoeffs b (by simp)
          have hab : 0 <= a * b := Rat.mul_nonneg ha hb
          have hrest : signChangeCount (b :: cs) = 0 := by
            apply ih
            intro d hd
            exact hcoeffs d (by simp [hd])
          have habnot : ¬ a * b < 0 := by grind
          simp [signChangeCount, hrest, habnot]

theorem signChangeCountIgnoringZeros_zero_of_nonneg_coeffs
    {coeffs : List Rat}
    (hcoeffs : forall c, c ∈ coeffs -> 0 <= c) :
    signChangeCountIgnoringZeros coeffs = 0 := by
  apply signChangeCount_zero_of_nonneg
  intro c hc
  exact hcoeffs c (List.mem_filter.mp hc).1

theorem signChangeCount_zero_of_nonpos
    {coeffs : List Rat}
    (hcoeffs : forall c, c ∈ coeffs -> c <= 0) :
    signChangeCount coeffs = 0 := by
  induction coeffs with
  | nil => rfl
  | cons a cs ih =>
      cases cs with
      | nil => rfl
      | cons b cs =>
          have ha : a <= 0 := hcoeffs a (by simp)
          have hb : b <= 0 := hcoeffs b (by simp)
          have hna : 0 <= -a := by grind
          have hnb : 0 <= -b := by grind
          have hneg : 0 <= (-a) * (-b) := Rat.mul_nonneg hna hnb
          have hab : 0 <= a * b := by
            grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg]
          have hrest : signChangeCount (b :: cs) = 0 := by
            apply ih
            intro d hd
            exact hcoeffs d (by simp [hd])
          have habnot : ¬ a * b < 0 := by grind
          simp [signChangeCount, hrest, habnot]

theorem signChangeCountIgnoringZeros_zero_of_nonpos_coeffs
    {coeffs : List Rat}
    (hcoeffs : forall c, c ∈ coeffs -> c <= 0) :
    signChangeCountIgnoringZeros coeffs = 0 := by
  apply signChangeCount_zero_of_nonpos
  intro c hc
  exact hcoeffs c (List.mem_filter.mp hc).1

theorem eval_neg_of_nonpos_coeffs_of_neg
    {coeffs : List Rat} {x : Rat}
    (hcoeffs : forall c, c ∈ coeffs -> c <= 0) (hx : 0 < x)
    {c₀ : Rat} (hc₀ : c₀ ∈ coeffs) (hc₀neg : c₀ < 0) :
    eval coeffs x < 0 := by
  induction coeffs with
  | nil => simp at hc₀
  | cons c cs ih =>
      simp only [eval, List.foldr]
      have htail_nonpos : eval cs x <= 0 :=
        eval_nonpos_of_nonpos_coeffs
          (fun d hd => hcoeffs d (by simp [hd])) (Rat.le_of_lt hx)
      by_cases hhead : c₀ = c
      · subst c₀
        have hnegTail : 0 <= -(eval cs x) := by grind
        have hterm0 : 0 <= x * (-(eval cs x)) :=
          Rat.mul_nonneg (Rat.le_of_lt hx) hnegTail
        have hterm : x * eval cs x <= 0 := by
          grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg]
        have hc : c < 0 := hc₀neg
        change c + x * eval cs x < 0
        grind
      · have htail : c₀ ∈ cs := by
          simpa [hhead] using hc₀
        have hih := ih
          (fun d hd => hcoeffs d (by simp [hd])) htail
        have hc : c <= 0 := hcoeffs c (by simp)
        have hterm : x * eval cs x < 0 :=
          by simpa [Rat.mul_comm] using
            (Rat.mul_neg_iff_of_pos_right hx).2 hih
        change c + x * eval cs x < 0
        grind

theorem no_positive_root_of_nonpos_coeffs_of_neg
    {coeffs : List Rat}
    (hcoeffs : forall c, c ∈ coeffs -> c <= 0)
    {c₀ : Rat} (hc₀ : c₀ ∈ coeffs) (hc₀neg : c₀ < 0) :
    ¬ Exists fun x : Rat => 0 < x /\ eval coeffs x = 0 := by
  intro hroot
  rcases hroot with ⟨x, hx, hzero⟩
  have hneg := eval_neg_of_nonpos_coeffs_of_neg hcoeffs hx hc₀ hc₀neg
  grind

/-! A restricted cubic sign pattern gives a sharp finite positive-root bound.

The coefficient list `[a, -b, -c, -d]` has one sign variation when all four
parameters are positive.  Rather than claiming Descartes' rule in general,
we prove the matching bound directly: the polynomial is strictly decreasing
on positive rational inputs, so any two positive rational roots coincide.
The proof is an explicit finite difference factorization. -/

theorem signChangeCount_cubic_one_variation
    {a b c d : Rat}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    signChangeCountIgnoringZeros [a, -b, -c, -d] = 1 := by
  have ha0 : a ≠ 0 := Rat.ne_of_gt ha
  have hb0 : -b ≠ 0 := by
    intro h
    grind
  have hc0 : -c ≠ 0 := by
    intro h
    grind
  have hd0 : -d ≠ 0 := by
    intro h
    grind
  have habpos : 0 < a * b := Rat.mul_pos ha hb
  have hab : a * (-b) < 0 := by
    have hneg : a * (-b) = -(a * b) := by
      grind [Rat.mul_neg, Rat.neg_mul]
    rw [hneg]
    grind
  have hbc_eq : (-b) * (-c) = b * c := by
    grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg]
  have hbc : 0 < (-b) * (-c) := by
    rw [hbc_eq]
    exact Rat.mul_pos hb hc
  have hcd_eq : (-c) * (-d) = c * d := by
    grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg]
  have hcd : 0 < (-c) * (-d) := by
    rw [hcd_eq]
    exact Rat.mul_pos hc hd
  have hbcnot : ¬ (-b) * (-c) < 0 := by
    intro h
    grind
  have hcdnot : ¬ (-c) * (-d) < 0 := by
    intro h
    grind
  simp [signChangeCountIgnoringZeros, signChangeCount, ha0, hb0, hc0,
    hd0, hab, hbcnot, hcdnot]

theorem cubic_at_most_one_positive_root_of_sign_pattern
    {a b c d x y : Rat}
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hx : 0 < x) (hy : 0 < y)
    (hxroot : eval [a, -b, -c, -d] x = 0)
    (hyroot : eval [a, -b, -c, -d] y = 0) :
    x = y := by
  have hdiff :
      eval [a, -b, -c, -d] x - eval [a, -b, -c, -d] y =
        (x - y) *
          (-(b + c * (x + y) + d * (x ^ 2 + x * y + y ^ 2))) := by
    simp [eval]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
  have hsum_pos :
      0 < b + c * (x + y) + d * (x ^ 2 + x * y + y ^ 2) := by
    have hxy : 0 < x + y := by grind
    have hcx : 0 < c * (x + y) := Rat.mul_pos hc hxy
    have hxx : 0 < x ^ 2 := by
      simpa [Rat.pow_succ] using (Rat.mul_pos hx hx)
    have hxyprod : 0 < x * y := Rat.mul_pos hx hy
    have hyy : 0 < y ^ 2 := by
      simpa [Rat.pow_succ] using (Rat.mul_pos hy hy)
    have hsquare : 0 < x ^ 2 + x * y + y ^ 2 := by grind
    have hdsquare : 0 < d * (x ^ 2 + x * y + y ^ 2) :=
      Rat.mul_pos hd hsquare
    have hbnonneg : 0 <= b := Rat.le_of_lt hb
    have hcxnonneg : 0 <= c * (x + y) := Rat.le_of_lt hcx
    have hdsquarenonneg : 0 <= d * (x ^ 2 + x * y + y ^ 2) :=
      Rat.le_of_lt hdsquare
    grind
  have hfactor_ne :
      -(b + c * (x + y) + d * (x ^ 2 + x * y + y ^ 2)) ≠ 0 := by
    intro hzero
    grind
  have hzero :
      (x - y) *
          (-(b + c * (x + y) + d * (x ^ 2 + x * y + y ^ 2))) = 0 := by
    rw [← hdiff]
    grind
  rcases Rat.mul_eq_zero.mp hzero with hxy | hfactor
  · grind [Rat.sub_eq_add_neg]
  · exact False.elim (hfactor_ne hfactor)

/-! A restricted quartic sign pattern gives the corresponding finite
positive-root exclusion certificate.  The list `[a, -b, -c, -d, -e]` has one
sign variation when all parameters are positive.  As with the cubic
certificate above, the root bound is proved directly from a rational finite
difference factorization rather than by invoking a general Descartes rule. -/

theorem signChangeCount_quartic_one_variation
    {a b c d e : Rat}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) :
    signChangeCountIgnoringZeros [a, -b, -c, -d, -e] = 1 := by
  have ha0 : a ≠ 0 := Rat.ne_of_gt ha
  have hb0 : -b ≠ 0 := by
    intro h
    grind
  have hc0 : -c ≠ 0 := by
    intro h
    grind
  have hd0 : -d ≠ 0 := by
    intro h
    grind
  have he0 : -e ≠ 0 := by
    intro h
    grind
  have hab : a * (-b) < 0 := by
    have hneg : a * (-b) = -(a * b) := by
      grind [Rat.mul_neg, Rat.neg_mul]
    rw [hneg]
    grind [Rat.mul_pos ha hb]
  have hbc : ¬ (-b) * (-c) < 0 := by
    have hpos : 0 < (-b) * (-c) := by
      have hbc_eq : (-b) * (-c) = b * c := by
        grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg]
      rw [hbc_eq]
      exact Rat.mul_pos hb hc
    grind
  have hcd : ¬ (-c) * (-d) < 0 := by
    have hpos : 0 < (-c) * (-d) := by
      have hcd_eq : (-c) * (-d) = c * d := by
        grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg]
      rw [hcd_eq]
      exact Rat.mul_pos hc hd
    grind
  have hde : ¬ (-d) * (-e) < 0 := by
    have hpos : 0 < (-d) * (-e) := by
      have hde_eq : (-d) * (-e) = d * e := by
        grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg]
      rw [hde_eq]
      exact Rat.mul_pos hd he
    grind
  simp [signChangeCountIgnoringZeros, signChangeCount, ha0, hb0, hc0,
    hd0, he0, hab, hbc, hcd, hde]

theorem quartic_at_most_one_positive_root_of_sign_pattern
    {a b c d e x y : Rat}
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hx : 0 < x) (hy : 0 < y)
    (hxroot : eval [a, -b, -c, -d, -e] x = 0)
    (hyroot : eval [a, -b, -c, -d, -e] y = 0) :
    x = y := by
  have hdiff :
      eval [a, -b, -c, -d, -e] x - eval [a, -b, -c, -d, -e] y =
        (x - y) *
          (-(b + c * (x + y) + d * (x ^ 2 + x * y + y ^ 2) +
            e * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3))) := by
    simp [eval]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
  have hxy : 0 < x + y := by grind
  have hcx : 0 < c * (x + y) := Rat.mul_pos hc hxy
  have hxx : 0 < x ^ 2 := by
    simpa [Rat.pow_succ] using (Rat.mul_pos hx hx)
  have hxyprod : 0 < x * y := Rat.mul_pos hx hy
  have hyy : 0 < y ^ 2 := by
    simpa [Rat.pow_succ] using (Rat.mul_pos hy hy)
  have hdsquare : 0 < x ^ 2 + x * y + y ^ 2 := by grind
  have hdsquare_term : 0 < d * (x ^ 2 + x * y + y ^ 2) :=
    Rat.mul_pos hd hdsquare
  have hxxx : 0 < x ^ 3 := by
    simpa [Rat.pow_succ] using (Rat.mul_pos hxx hx)
  have hxxy : 0 < x ^ 2 * y := Rat.mul_pos hxx hy
  have hxyy : 0 < x * y ^ 2 := Rat.mul_pos hx hyy
  have hyyy : 0 < y ^ 3 := by
    simpa [Rat.pow_succ] using (Rat.mul_pos hyy hy)
  have hcubic :
      0 < x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 := by grind
  have hcubic_term :
      0 < e * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) :=
    Rat.mul_pos he hcubic
  have hsum_pos :
      0 < b + c * (x + y) + d * (x ^ 2 + x * y + y ^ 2) +
        e * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) := by
    have hbnonneg : 0 <= b := Rat.le_of_lt hb
    have hcxnonneg : 0 <= c * (x + y) := Rat.le_of_lt hcx
    have hdsquarenonneg :
        0 <= d * (x ^ 2 + x * y + y ^ 2) := Rat.le_of_lt hdsquare_term
    have hcubicnonneg :
        0 <= e * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) :=
      Rat.le_of_lt hcubic_term
    grind
  have hfactor_ne :
      -(b + c * (x + y) + d * (x ^ 2 + x * y + y ^ 2) +
        e * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3)) ≠ 0 := by
    intro hzero
    grind
  have hzero :
      (x - y) *
          (-(b + c * (x + y) + d * (x ^ 2 + x * y + y ^ 2) +
            e * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3))) = 0 := by
    rw [← hdiff]
    grind
  rcases Rat.mul_eq_zero.mp hzero with hxy_eq | hfactor
  · grind [Rat.sub_eq_add_neg]
  · exact False.elim (hfactor_ne hfactor)

theorem signChangeCount_quadratic_example :
    signChangeCount [2, -3, 1] = 2 := by
  decide +kernel

theorem signChangeCountIgnoringZeros_example :
    signChangeCountIgnoringZeros [1, 0, -1, 0, 1] = 2 := by
  decide +kernel

end Polynomial

inductive RatExpr where
  | var
  | const (q : Rat)
  | neg (e : RatExpr)
  | add (a b : RatExpr)
  | mul (a b : RatExpr)
  | inv (e : RatExpr)
deriving Repr, DecidableEq

namespace RatExpr

def eval : RatExpr -> Rat -> Option Rat
  | var, x => some x
  | const q, _ => some q
  | neg e, x => (eval e x).map (fun y => -y)
  | add a b, x => match eval a x, eval b x with | some y, some z => some (y + z) | _, _ => none
  | mul a b, x => match eval a x, eval b x with | some y, some z => some (y * z) | _, _ => none
  | inv e, x => match eval e x with | some y => if y = 0 then none else some (1 / y) | none => none

def sub (a b : RatExpr) : RatExpr := add a (neg b)
def div (a b : RatExpr) : RatExpr := mul a (inv b)
def square : RatExpr := mul var var
def oneDivOnePlusSquare : RatExpr := inv (add (const 1) square)

end RatExpr

/-- A rational function as numerator and denominator polynomials.

The value is defined exactly on rational inputs where the denominator is
nonzero.  There is no placeholder value outside the domain.
-/
structure RatFun where
  num : List Rat
  den : List Rat

namespace RatFun

def denominator (f : RatFun) (x : Rat) : Rat := Polynomial.eval f.den x
def numerator (f : RatFun) (x : Rat) : Rat := Polynomial.eval f.num x
def DefinedAt (f : RatFun) (x : Rat) : Prop := f.denominator x != 0
def undefinedAt (f : RatFun) (x : Rat) : Bool := decide (f.denominator x = 0)

def eval? (f : RatFun) (x : Rat) : Option Rat :=
  let d := f.denominator x
  if d = 0 then none else some (f.numerator x / d)

def evalOnDomain (f : RatFun) (x : Rat) (_h : f.DefinedAt x) : Rat :=
  f.numerator x / f.denominator x

def polynomial (coeffs : List Rat) : RatFun where
  num := coeffs
  den := [1]

def oneOverX : RatFun where
  num := [1]
  den := [0, 1]

def oneOverOnePlusSquare : RatFun where
  num := [1]
  den := [1, 0, 1]

/-- `1 / (x^2 - 2)`.  It has no rational pole, but it should still fail the
interval-regularity certificate on `[1,2]`, because the denominator is not
apart from zero there. -/
def oneOverXSquareMinusTwo : RatFun where
  num := [1]
  den := [-2, 0, 1]

end RatFun

end ComputableAnalysis


