-- Prove2me | Definitions.Def_TeschlQM_OneParticle_multiplicationOperator
-- name    : TeschlQM_OneParticle_multiplicationOperator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T07:25:17.567966+00:00
-- url     : https://prove2.me/theorems/e791afbf-9250-433c-831f-1e2fa4429846
-- title:
--   L²(ℝⁿ) and the maximally defined multiplication operator (2.21)
-- statement:
--   Let $L^2(\mathbb R^n)$ be the complex Hilbert space of square integrable functions on $\mathbb R^n$ with respect to Lebesgue measure. For a function $A : \mathbb R^n \to \mathbb C$ the **multiplication operator** is
--   $$(Af)(x) = A(x) f(x), \qquad \mathfrak D(A) = \{ f \in L^2(\mathbb R^n) \mid A f \in L^2(\mathbb R^n) \},$$
--   defined on its maximal domain.
--
--   For a real potential $V : \mathbb R^n \to \mathbb R$ this is the operator $V$ in the one-particle Hamiltonian $H = H_0 + V$ of (10.1).
--
--   **Formalization Note.** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` with `volume` (Lebesgue measure) and `L2 n` is Mathlib's `Lp ℂ 2 volume`. `multDomain A` is the submodule of classes $f$ for which $x \mapsto A(x) f(x)$ is in $L^2$ (`MemLp … 2`); `multOp A` is the corresponding `LinearPMap` `L2 n →ₗ.[ℂ] L2 n`, whose value is the $L^2$ class of $A f$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 59, Section 2.2, Eq. (2.21)

import Mathlib

namespace TeschlQM.OneParticle

open MeasureTheory

/-- `L²(ℝⁿ)`: the complex Hilbert space `L²(ℝⁿ, dⁿx)` of Teschl, Sec. 7.2, with `ℝⁿ` realised as
`EuclideanSpace ℝ (Fin n)` and Lebesgue measure `volume`. -/
abbrev L2 (n : ℕ) : Type := Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))

/-- Teschl (2.21), p. 59: the maximal domain `𝔇(A) = {f ∈ L²(ℝⁿ) | A f ∈ L²(ℝⁿ)}` of the
operator of multiplication by the function `A : ℝⁿ → ℂ`. -/
def multDomain {n : ℕ} (A : EuclideanSpace ℝ (Fin n) → ℂ) : Submodule ℂ (L2 n) where
  carrier := {f | MemLp (fun x => A x * f x) 2 volume}
  zero_mem' := by
    refine (MemLp.zero (ε := ℂ)).ae_eq ?_
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))] with x hx
    have hx' : A x * ((0 : L2 n) : _ → ℂ) x = 0 := by rw [hx, Pi.zero_apply, mul_zero]
    exact hx'.symm
  add_mem' := by
    intro f g hf hg
    refine (MemLp.add hf hg).ae_eq ?_
    filter_upwards [Lp.coeFn_add f g] with x hx
    have hx' : A x * ((f + g : L2 n) : _ → ℂ) x = A x * f x + A x * g x := by
      rw [hx, Pi.add_apply, mul_add]
    exact hx'.symm
  smul_mem' := by
    intro c f hf
    refine (MemLp.const_smul hf c).ae_eq ?_
    filter_upwards [Lp.coeFn_smul c f] with x hx
    have hx' : A x * ((c • f : L2 n) : _ → ℂ) x = c • (A x * f x) := by
      rw [hx, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      ring
    exact hx'.symm

/-- Teschl (2.21), p. 59: the **multiplication operator** `(A f)(x) = A(x) f(x)` on its maximal
domain `𝔇(A) = {f ∈ L²(ℝⁿ) | A f ∈ L²(ℝⁿ)}`, as a `LinearPMap` on `L²(ℝⁿ)`. For a potential
`V : ℝⁿ → ℝ` this is the operator `V` of Teschl (10.1). -/
noncomputable def multOp {n : ℕ} (A : EuclideanSpace ℝ (Fin n) → ℂ) : L2 n →ₗ.[ℂ] L2 n where
  domain := multDomain A
  toFun :=
    { toFun := fun f => (show MemLp (fun x => A x * (f : L2 n) x) 2 volume from f.2).toLp _
      map_add' := by
        intro f g
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_add (f : L2 n) (g : L2 n)] with x hx
        rw [Submodule.coe_add, Pi.add_apply, hx, Pi.add_apply, mul_add]
      map_smul' := by
        intro c f
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_smul c (f : L2 n)] with x hx
        rw [Submodule.coe_smul, hx, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        ring }

end TeschlQM.OneParticle


