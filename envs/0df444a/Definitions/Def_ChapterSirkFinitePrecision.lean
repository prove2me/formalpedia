-- Prove2me | Definitions.Def_ChapterSirkFinitePrecision
-- name    : ChapterSirkFinitePrecision
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-07T14:19:19.439301+00:00
-- url     : https://prove2.me/theorems/9d97fdc1-ddf5-49ea-900f-85f1e8af95f1
-- title:
--   SIRK finite-precision certificate layer (T1-T5)
-- statement:
--   Formal definitions for the SIRK finite-precision certificate layer (T1-T5) of the timepiece Lean 4 formalization (module `BookProof.SirkFinitePrecision`, source chapter `BookProof/ChapterSirkFinitePrecision.lean`).
--
--   `CONSOLIDATED_PLAN.md` §13.3, `MASS_GAP_CERTIFIED.md` §4: the SIRK/Hashimoto reliability chain of §12 is stated in *exact* arithmetic, while the kernel runs in `f64`. This chapter formalises the layers that turn a computed number into a *rigorous enclosure*, with every constant explicit. Nothing here trusts a floating-point value: the theorems consume only residuals, backward-error bounds and interval enclosures, all of which enter as hypotheses or as certified data.
--
--   * `HasRealEigenvalue` — a real eigenvalue of an operator; `rayleigh` — the Rayleigh quotient `re ⟪x, T x⟫`, the quantity the kernel reports as a Ritz value. * The spectral expansion of a symmetric operator in its eigenbasis (`repr_apply_of_symmetric`, `norm_sq_eq_sum_repr`, `rayleigh_eq_sum_eigenvalues`, `norm_apply_sq_eq_sum_eigenvalues`). * **T2 (Rayleigh–Ritz residual bound, Layer 3, §4.3)** `exists_eigenvalue_dist_le_residual` / `exists_eigenvalue_dist_le_residual_unit`: for *any* vector `x ≠ 0` and any real `θ` there is an eigenvalue `lam` of the exact operator with `|lam − θ| · ‖x‖ ≤ ‖T x − θ x‖`. This is Parlett's a-posteriori bound: it applies to the *computed* vector and the *exact* operator, so no infinite-precision hypothesis is needed at the theorem level. * **T1/T3 (backward error + Weyl, Layer 1, §4.1)** `backward_error_weyl` and `backward_error_weyl_symm`: if the computed eigenpairs are exact eigenpairs of a perturbed operator `S` with `‖T x − S x‖ ≤ ε ‖x‖` (the LAPACK backward-error model, `ε = c(n) · u · ‖Ĝ‖`), then the eigenvalues of `S` and of `T` are within `ε` of each other. This is Weyl's inequality in the enclosure (Hausdorff) form — the form the certificate consumes. * **The Rayleigh–Ritz upper bound** `ground_le_rayleigh`: the lowest eigenvalue never exceeds a computed Rayleigh quotient — the direction that is unconditionally sound. * **Temple's inequality** `temple_lower_bound`: the rigorous *lower* bound for the lowest eigenvalue from a computed Rayleigh quotient and an a-priori separation constant `β`. (The bound `λ₀ ≥ θ − ‖r‖` used informally in `MASS_GAP_CERTIFIED.md` §3.4 step 1 is *not* valid without extra information — a small residual only certifies that *some* eigenvalue is near `θ`. Temple's inequality and `ground_ge_of_no_eigenvalue_below` are the two honest replacements, and they are what `ChapterSirkCertifiedGap` uses.) * **T4 (certified-observable propagation, §5.2)** `observable_propagation`: `|⟨O⟩_u − ⟨O⟩_w| ≤ ‖O‖ (‖u‖ + ‖w‖) ‖u − w‖`, and the `2‖O‖ · band · ‖v‖` form `observable_propagation_band`. * **T5 (the interval-enclosure core, Layer 2, §4.2/§4.4)** `CertInterval` with `add`/`neg`/`sub`/`mul`/`widen` and their soundness theorems (`mem_add`, `mem_neg`, `mem_sub`, `mem_mul`, `mem_widen`), the outward-rounding model `mem_ofRounded`, the certified supremum `le_sup_bound_of_isotone` / `abs_le_of_isotone`, and the half-width extraction `dist_le_width`.
--
--   Everything is `sorry`-free and `axiom`-free.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean

import Mathlib

/-!
# Chapter SirkFinitePrecision — the finite-precision certificate layer (T1–T5)

`CONSOLIDATED_PLAN.md` §13.3, `MASS_GAP_CERTIFIED.md` §4: the SIRK/Hashimoto
reliability chain of §12 is stated in *exact* arithmetic, while the kernel runs in
`f64`.  This chapter formalises the layers that turn a computed number into a
*rigorous enclosure*, with every constant explicit.  Nothing here trusts a
floating-point value: the theorems consume only residuals, backward-error bounds and
interval enclosures, all of which enter as hypotheses or as certified data.

## Deliverables

* `HasRealEigenvalue` — a real eigenvalue of an operator; `rayleigh` — the Rayleigh
  quotient `re ⟪x, T x⟫`, the quantity the kernel reports as a Ritz value.
* The spectral expansion of a symmetric operator in its eigenbasis
  (`repr_apply_of_symmetric`, `norm_sq_eq_sum_repr`, `rayleigh_eq_sum_eigenvalues`,
  `norm_apply_sq_eq_sum_eigenvalues`).
* **T2 (Rayleigh–Ritz residual bound, Layer 3, §4.3)**
  `exists_eigenvalue_dist_le_residual` / `exists_eigenvalue_dist_le_residual_unit`:
  for *any* vector `x ≠ 0` and any real `θ` there is an eigenvalue `lam` of the
  exact operator with `|lam − θ| · ‖x‖ ≤ ‖T x − θ x‖`.  This is Parlett's
  a-posteriori bound: it applies to the *computed* vector and the *exact* operator,
  so no infinite-precision hypothesis is needed at the theorem level.
* **T1/T3 (backward error + Weyl, Layer 1, §4.1)** `backward_error_weyl` and
  `backward_error_weyl_symm`: if the computed eigenpairs are exact eigenpairs of a
  perturbed operator `S` with `‖T x − S x‖ ≤ ε ‖x‖` (the LAPACK backward-error
  model, `ε = c(n) · u · ‖Ĝ‖`), then the eigenvalues of `S` and of `T` are within
  `ε` of each other.  This is Weyl's inequality in the enclosure (Hausdorff) form —
  the form the certificate consumes.
* **The Rayleigh–Ritz upper bound** `ground_le_rayleigh`: the lowest eigenvalue
  never exceeds a computed Rayleigh quotient — the direction that is
  unconditionally sound.
* **Temple's inequality** `temple_lower_bound`: the rigorous *lower* bound for the
  lowest eigenvalue from a computed Rayleigh quotient and an a-priori separation
  constant `β`.  (The bound `λ₀ ≥ θ − ‖r‖` used informally in
  `MASS_GAP_CERTIFIED.md` §3.4 step 1 is *not* valid without extra information — a
  small residual only certifies that *some* eigenvalue is near `θ`.  Temple's
  inequality and `ground_ge_of_no_eigenvalue_below` are the two honest
  replacements, and they are what `ChapterSirkCertifiedGap` uses.)
* **T4 (certified-observable propagation, §5.2)** `observable_propagation`:
  `|⟨O⟩_u − ⟨O⟩_w| ≤ ‖O‖ (‖u‖ + ‖w‖) ‖u − w‖`, and the `2‖O‖ · band · ‖v‖` form
  `observable_propagation_band`.
* **T5 (the interval-enclosure core, Layer 2, §4.2/§4.4)** `CertInterval` with
  `add`/`neg`/`sub`/`mul`/`widen` and their soundness theorems
  (`mem_add`, `mem_neg`, `mem_sub`, `mem_mul`, `mem_widen`), the outward-rounding
  model `mem_ofRounded`, the certified supremum `le_sup_bound_of_isotone` /
  `abs_le_of_isotone`, and the half-width extraction `dist_le_width`.

Everything is `sorry`-free and `axiom`-free.
-/

noncomputable section

namespace BookProof.SirkFinitePrecision

open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-! ## 0. Eigenvalues and Rayleigh quotients -/

/-- `lam` is a real eigenvalue of `T`: some nonzero vector is scaled by `lam`. -/
def HasRealEigenvalue (T : E →ₗ[ℂ] E) (lam : ℝ) : Prop :=
  ∃ x : E, x ≠ 0 ∧ T x = (lam : ℂ) • x

/-- The Rayleigh quotient (numerator) of `x`: `re ⟪x, T x⟫`.  For a symmetric `T`
this is real and, for a unit vector, is the quantity the kernel reports as a Ritz
value. -/
def rayleigh (T : E →ₗ[ℂ] E) (x : E) : ℝ := (inner ℂ x (T x)).re

/-- The `i`-th coordinate of `x` in the eigenbasis of the symmetric operator `T`. -/
def coeff {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n) (x : E)
    (i : Fin n) : ℂ :=
  ((hT.eigenvectorBasis hn).repr x).ofLp i

/-! ## 1. The spectral expansion of a symmetric operator -/













/-! ## 2. T2 — the Rayleigh–Ritz (Parlett/Weinstein) residual bound -/





/-! ## 3. T1/T3 — backward error of the eigendecomposition, and Weyl -/





/-! ## 4. The two-sided a-posteriori bracket for the lowest eigenvalue -/







/-! ## 5. T4 — certified propagation to observables -/





/-! ## 6. T5 — the interval-enclosure core

The only new *trusted* component of the certificate architecture is the
directed-rounding interval layer.  Here it is: a two-sided enclosure type, the
soundness of its arithmetic, an explicit outward-rounding model (a computed endpoint
pair is admissible as soon as it brackets the exact value, which is exactly what
directed rounding guarantees), and the two consequences the mass-gap certificate
uses — a certified supremum over a box from an inclusion-isotone extension, and the
extraction of a certified half-width from an enclosure. -/

/-- A closed real interval, used as an enclosure. -/
structure CertInterval where
  /-- The (rounded-down) lower endpoint. -/
  lo : ℝ
  /-- The (rounded-up) upper endpoint. -/
  hi : ℝ

namespace CertInterval

/-- Membership: `x` is enclosed by `I`. -/
def Mem (I : CertInterval) (x : ℝ) : Prop := I.lo ≤ x ∧ x ≤ I.hi

/-- The width of an enclosure. -/
def width (I : CertInterval) : ℝ := I.hi - I.lo

/-- The midpoint of an enclosure — the "delivered value". -/
def mid (I : CertInterval) : ℝ := (I.lo + I.hi) / 2

/-- Interval addition. -/
def add (I J : CertInterval) : CertInterval := ⟨I.lo + J.lo, I.hi + J.hi⟩

/-- Interval negation. -/
def neg (I : CertInterval) : CertInterval := ⟨-I.hi, -I.lo⟩

/-- Interval subtraction. -/
def sub (I J : CertInterval) : CertInterval := ⟨I.lo - J.hi, I.hi - J.lo⟩

/-- Interval multiplication (the four-corner rule). -/
def mul (I J : CertInterval) : CertInterval :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩

/-- Outward inflation by `ε ≥ 0` — the directed-rounding step. -/
def widen (I : CertInterval) (ε : ℝ) : CertInterval := ⟨I.lo - ε, I.hi + ε⟩























/-- Horner evaluation of a polynomial (coefficients in increasing degree) at a real
point. -/
def polyEval : List ℝ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => polyEval cs x * x + c

/-- The interval (Horner) evaluation of the same polynomial: the *interval extension*
that an interval-arithmetic evaluator computes. -/
def evalHorner : List ℝ → CertInterval → CertInterval
  | [], _ => CertInterval.mk 0 0
  | c :: cs, I => ((evalHorner cs I).mul I).add (CertInterval.mk c c)









end CertInterval

end BookProof.SirkFinitePrecision


