-- Prove2me | Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
-- name    : AlgebraicCurve_PlaceTaylorCoeff
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/a0564ba4-b4eb-522a-9885-d2445e293226
-- title:
--   Taylor coefficients at places, jet matrices, confluent patterns
-- statement:
--   Throughout, $F/K$ is an extension of fields and $v$ is a place of $F/K$ in the project's sense (a proper valuation subring of $F$ containing $K$ whose ideals are principal), with the total evaluation map $\mathrm{evalAt}_v \colon F \to K$ which sends $f$ in the valuation subring to its residue read back along $K \to \kappa(v)$ and sends $f$ outside the valuation subring to $0$. For $t, f \in F$ the Taylor remainders are defined by the recursion $\rho_0 = f$ and $\rho_{r+1} = (\rho_r - \mathrm{evalAt}_v(\rho_r))\,t^{-1}$, where the scalar is transported to $F$ by the structure map, and the $r$-th Taylor coefficient of $f$ at $v$ along $t$ is $a_r = \mathrm{evalAt}_v(\rho_r) \in K$. Thus $a_0$ is the value of $f$ at $v$, and the recursion involves no derivations or factorials. Two identities are recorded: $\rho_r = a_r + t\,\rho_{r+1}$ and, for $t \neq 0$ and every $n$, the finite expansion $f = \sum_{q<n} a_q t^q + t^n \rho_n$.
--
--   For $M$ places $P_1,\dots,P_M$, elements $t_1,\dots,t_M$, orders $e_1,\dots,e_M \in \mathbb{N}$ and functions $f_1,\dots,f_M$, the jet matrix is the $M \times M$ matrix over $K$ with $(i,j)$ entry the $e_i$-th Taylor coefficient of $f_j$ at $P_i$ along $t_i$; for all orders zero it is the matrix of values $\mathrm{evalAt}_{P_i}(f_j)$. The multiplicity $\mathrm{jetMult}$ of a place $v$ is the number of indices $i$ with $P_i = v$, and $\mathrm{jetDivisor}$ is the divisor $\sum_i P_i$, whose coefficient at $v$ is that multiplicity. Finally, $(P,t,e)$ is a confluent pattern when equal places carry equal elements $t$, the assignment $i \mapsto (P_i, e_i)$ is injective, and $e_i < \mathrm{jetMult}(P_i)$ for every $i$; so at each place the orders occurring are exactly $0,\dots,n_v-1$ where $n_v$ is the multiplicity.
--
--   **Relation to Mathlib.** Mathlib's Taylor expansions concern polynomials; the expansion of an element of a field extension along an element at a place, together with jet matrices and confluence patterns, is the project's own, built on its `Place` structure and the total evaluation `evalAt`.
--
--   **Where it is used.** These notions belong to the project's layer on places and divisors of a curve presented through its function field: the Taylor coefficients give a total, characteristic-free higher-order evaluation at a place, and jet matrices together with confluent patterns express interpolation conditions with multiplicities supported on the divisor $\sum_i P_i$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_PlaceTaylorCoeff.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

def taylorRem (v : Place K F) (t f : F) : ℕ → F
  | 0 => f
  | r + 1 => (taylorRem v t f r - algebraMap K F (v.evalAt (taylorRem v t f r))) * t⁻¹

def taylorCoeff (v : Place K F) (t : F) (r : ℕ) (f : F) : K :=
  v.evalAt (taylorRem v t f r)

variable (v : Place K F) (t f : F)

@[simp]
theorem taylorRem_zero : taylorRem v t f 0 = f := rfl

theorem taylorRem_succ (r : ℕ) :
    taylorRem v t f (r + 1)
      = (taylorRem v t f r - algebraMap K F (v.evalAt (taylorRem v t f r))) * t⁻¹ := rfl

@[simp]
theorem taylorCoeff_zero : taylorCoeff v t 0 f = v.evalAt f := rfl

theorem taylorCoeff_eq (r : ℕ) : taylorCoeff v t r f = v.evalAt (taylorRem v t f r) := rfl

theorem taylorRem_succ' (r : ℕ) :
    taylorRem v t f (r + 1)
      = (taylorRem v t f r - algebraMap K F (taylorCoeff v t r f)) * t⁻¹ := rfl

theorem taylorRem_eq_add_mul_succ {t : F} (ht : t ≠ 0) (f : F) (r : ℕ) :
    taylorRem v t f r
      = algebraMap K F (taylorCoeff v t r f) + t * taylorRem v t f (r + 1) := by
  rw [taylorRem_succ', mul_comm _ t⁻¹, ← mul_assoc, mul_inv_cancel₀ ht, one_mul]
  abel

theorem eq_sum_taylorCoeff_mul_pow_add_pow_mul_taylorRem {t : F} (ht : t ≠ 0) (f : F) (n : ℕ) :
    f = (∑ q ∈ Finset.range n, algebraMap K F (taylorCoeff v t q f) * t ^ q)
        + t ^ n * taylorRem v t f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nth_rewrite 1 [ih]
    rw [taylorRem_eq_add_mul_succ v ht f n]
    ring

end Place

def jetMatrix {M : ℕ} (P : Fin M → Place K F) (t : Fin M → F) (e : Fin M → ℕ)
    (f : Fin M → F) : Matrix (Fin M) (Fin M) K :=
  Matrix.of fun i j => (P i).taylorCoeff (t i) (e i) (f j)

theorem jetMatrix_apply {M : ℕ} (P : Fin M → Place K F) (t : Fin M → F) (e : Fin M → ℕ)
    (f : Fin M → F) (i j : Fin M) :
    jetMatrix P t e f i j = (P i).taylorCoeff (t i) (e i) (f j) := rfl

@[simp]
theorem jetMatrix_order_zero {M : ℕ} (P : Fin M → Place K F) (t : Fin M → F)
    (f : Fin M → F) :
    jetMatrix P t (fun _ => 0) f = Matrix.of fun i j => (P i).evalAt (f j) := rfl

open Classical in

def jetMult {M : ℕ} (P : Fin M → Place K F) (v : Place K F) : ℕ :=
  (Finset.univ.filter fun i => P i = v).card

def jetDivisor {M : ℕ} (P : Fin M → Place K F) : Divisor K F :=
  ∑ i, Finsupp.single (P i) 1

theorem jetDivisor_apply {M : ℕ} (P : Fin M → Place K F) (v : Place K F) :
    jetDivisor P v = (jetMult P v : ℤ) := by
  classical
  simp only [jetDivisor, jetMult, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply,
    Finset.sum_boole]

def IsConfluentPattern {M : ℕ} (P : Fin M → Place K F) (t : Fin M → F) (e : Fin M → ℕ) :
    Prop :=
  (∀ i i', P i = P i' → t i = t i') ∧
  (∀ i i', P i = P i' → e i = e i' → i = i') ∧
  (∀ i, e i < jetMult P (P i))

end AlgebraicCurve

end


