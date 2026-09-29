-- Prove2me | Definitions.Def_MilnorConjecture_GaloisSymbol
-- name    : MilnorConjecture_GaloisSymbol
-- status  : Definition
-- author  : @vatsj
-- created : 2026-09-24T21:11:11.471054+00:00
-- url     : https://prove2.me/theorems/b155e0cb-519b-4dc4-acbd-7df7cfcc4d36
-- title:
--   Galois symbol $(F^\times)^n \to H^n(F,\mathbb{Z}/2)$
-- statement:
--   Let $F$ be a field with $\operatorname{char} F \neq 2$, $F^{\mathrm{sep}}$ a separable closure and $G_F = \operatorname{Gal}(F^{\mathrm{sep}}/F)$ with its Krull topology. Write $H^n(F,\mathbb{Z}/2) = H^n_{\mathrm{cts}}(G_F,\mathbb{Z}/2)$ for continuous cohomology with trivial coefficients $\mathbb{Z}/2 \cong \mu_2$.
--
--   For $a \in F^\times$ fix a square root $\sqrt a \in F^{\mathrm{sep}}$. The **Kummer character** is
--   $$\chi_a(\sigma) = \begin{cases}0 & \sigma(\sqrt a) = \sqrt a,\\ 1 & \text{otherwise,}\end{cases}$$
--   a continuous homomorphism $G_F\to\mathbb{Z}/2$ representing the Kummer class $\delta a \in H^1(F,\mu_2)$ (the boundary of the Kummer sequence). For $a_1,\dots,a_n\in F^\times$, the **Galois symbol** is the class of the homogeneous cocycle
--   $$(x_0,\dots,x_n) \longmapsto \prod_{j=1}^{n}\bigl(\chi_{a_j}(x_j) - \chi_{a_j}(x_{j-1})\bigr) \;\in\; H^n(F,\mathbb{Z}/2),$$
--   the homogeneous form of $(\sigma_1,\dots,\sigma_n)\mapsto \chi_{a_1}(\sigma_1)\cdots\chi_{a_n}(\sigma_n)$, i.e. the cup product $\delta a_1 \cup \cdots \cup \delta a_n$. For $n = 0$ it is the class of the constant $1$.
--
--   These are exactly the values of the norm residue homomorphism on symbols.
--
--   **Formalization Note** `H F n`, `kummerChar a` and `galoisSymbol a` are sorry-free; continuity, additivity, invariance and the cocycle identity are proved in the file. The class does not depend on the choice of $\sqrt a$, since $\chi_a$ does not.
-- source:
--   V. Voevodsky, Motivic cohomology with Z/2-coefficients, Publ. Math. IHES 98 (2003), 59-104, https://doi.org/10.1007/s10240-003-0010-6, p. 59 (Introduction, eqs. (1)-(3)): the Kummer boundary k^* -> H^1(k, mu_2) and its multiplicative extension K^M_*(k) -> H^*(k, mu_2^{(x)*}).

import Mathlib
import Definitions.Def_MilnorConjecture_HomogeneousCochains

/-!
# The Galois symbol `(F^×)ⁿ → Hⁿ(F, ℤ/2)`

For a field `F` with `2 ≠ 0` in `F`, write `F^sep` for its separable closure and
`G_F = Gal(F^sep/F)` for the absolute Galois group with its Krull topology. For `a ∈ F^×` fix a
square root `√a ∈ F^sep` and let `χ_a : G_F → ℤ/2` be the Kummer character,
`χ_a(σ) = 0` if `σ(√a) = √a` and `χ_a(σ) = 1` otherwise.

The Galois symbol of `(a₁, …, aₙ)` is the class in `Hⁿ_cts(G_F, ℤ/2)` of the homogeneous
cocycle `(x₀, …, xₙ) ↦ ∏ⱼ (χ_{aⱼ}(xⱼ) - χ_{aⱼ}(xⱼ₋₁))`, which is the homogeneous form of the
inhomogeneous cocycle `(σ₁, …, σₙ) ↦ χ_{a₁}(σ₁) ⋯ χ_{aₙ}(σₙ)`, i.e. of the cup product
`δa₁ ∪ ⋯ ∪ δaₙ` of Kummer classes.
-/

namespace MilnorConjecture

section Cochain

variable {G R : Type*} [CommRing R]

/-- Function-level homogeneous coboundary `(δf)(y) = ∑ᵢ (-1)ⁱ f(y ∘ ∂ᵢ)`. -/
def fcob {m : ℕ} (f : (Fin m → G) → R) (y : Fin (m + 1) → G) : R :=
  ∑ i : Fin (m + 1), (-1 : R) ^ (i : ℕ) * f (y ∘ i.succAbove)

/-- `(x₀, …, xₙ) ↦ ∏ⱼ (χⱼ(xⱼ) - χⱼ(xⱼ₋₁))` for functions `χ₁, …, χₙ : G → R`. -/
def prodCochain {n : ℕ} (χ : Fin n → G → R) (x : Fin (n + 1) → G) : R :=
  ∏ j : Fin n, (χ j (x j.succ) - χ j (x j.castSucc))

lemma prodCochain_succ {n : ℕ} (χ : Fin (n + 1) → G → R) (x : Fin (n + 2) → G) :
    prodCochain χ x = (χ 0 (x 1) - χ 0 (x 0)) * prodCochain (Fin.tail χ) (Fin.tail x) := by
  rw [prodCochain, Fin.prod_univ_succ]
  rfl

/-- Leibniz rule for multiplying by the coboundary of a `0`-cochain:
`δ(δχ · Ψ) = -(δχ · δΨ)`. -/
lemma fcob_mul_tail {m : ℕ} (χ : G → R) (Ψ : (Fin (m + 1) → G) → R) (y : Fin (m + 3) → G) :
    fcob (fun x : Fin (m + 2) → G ↦ (χ (x 1) - χ (x 0)) * Ψ (Fin.tail x)) y =
      -((χ (y 1) - χ (y 0)) * fcob Ψ (Fin.tail y)) := by
  simp only [fcob]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ (n := m + 1), mul_add, neg_add,
    ← add_assoc]
  congr 1
  · have h1 : (Fin.succ 0 : Fin (m + 3)).succAbove 1 = 2 := by
      rw [show (1 : Fin (m + 2)) = Fin.succ 0 from rfl, Fin.succ_succAbove_succ]; rfl
    have h2 : Fin.tail (y ∘ (Fin.succ 0 : Fin (m + 3)).succAbove) = fun i ↦ y i.succ.succ := by
      funext i
      simp only [Fin.tail, Function.comp_apply, Fin.succ_succAbove_succ, Fin.succAbove_zero]
    simp only [Function.comp_apply, h1, h2, Fin.succ_succAbove_zero, Fin.succAbove_zero]
    have e3 : Fin.tail (y ∘ Fin.succ) = fun i ↦ y i.succ.succ := rfl
    have e4 : Fin.tail y ∘ Fin.succ = fun i ↦ y i.succ.succ := rfl
    rw [Fin.succ_one_eq_two, Fin.succ_zero_eq_one, e3, e4]
    simp only [Fin.val_one, Fin.val_zero, pow_one, pow_zero, one_mul]
    ring
  · rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have h0 : (y ∘ j.succ.succ.succAbove) 0 = y 0 := by simp
    have h1 : (y ∘ j.succ.succ.succAbove) 1 = y 1 := by
      rw [Function.comp_apply, ← Fin.succ_zero_eq_one, Fin.succ_succAbove_succ,
        Fin.succ_succAbove_zero, Fin.succ_zero_eq_one]
    have h2 : Fin.tail (y ∘ j.succ.succ.succAbove) = Fin.tail y ∘ j.succ.succAbove := by
      funext i
      simp only [Fin.tail, Function.comp_apply, Fin.succ_succAbove_succ]
    rw [h0, h1, h2]
    simp only [Fin.val_succ]
    ring

lemma fcob_prodCochain {n : ℕ} (χ : Fin n → G → R) (y : Fin (n + 2) → G) :
    fcob (prodCochain χ) y = 0 := by
  induction n with
  | zero => simp [fcob, prodCochain, Fin.sum_univ_two]
  | succ n ih =>
    have : prodCochain χ =
        fun x ↦ (χ 0 (x 1) - χ 0 (x 0)) * prodCochain (Fin.tail χ) (Fin.tail x) :=
      funext (prodCochain_succ χ)
    rw [this, fcob_mul_tail, ih, mul_zero, neg_zero]

end Cochain

variable (F : Type) [Field F]

/-- The absolute Galois group `Gal(F^sep/F)`, with its Krull topology. -/
abbrev AbsGal : Type := Gal(SeparableClosure F/F)

/-- `Hⁿ(F, ℤ/2) := Hⁿ_cts(Gal(F^sep/F), ℤ/2)`, with `ℤ/2` a trivial representation. -/
abbrev H (n : ℕ) : Type := continuousCohomology n (trivialRep (ZMod 2) (AbsGal F) (ZMod 2))

variable [NeZero (2 : F)] {F}

instance : NeZero ((2 : ℕ) : SeparableClosure F) :=
  ⟨by
    rw [Nat.cast_ofNat, ← map_ofNat (algebraMap F (SeparableClosure F)) 2]
    exact (map_ne_zero _).mpr (NeZero.ne (2 : F))⟩

/-- A chosen square root of `a` in `F^sep`. -/
noncomputable def sqrtSep (a : Fˣ) : SeparableClosure F :=
  (IsSepClosed.exists_pow_nat_eq (algebraMap F (SeparableClosure F) a) 2).choose

lemma sqrtSep_sq (a : Fˣ) : sqrtSep a ^ 2 = algebraMap F (SeparableClosure F) a :=
  (IsSepClosed.exists_pow_nat_eq (algebraMap F (SeparableClosure F) a) 2).choose_spec

/-- The Kummer character `χ_a : Gal(F^sep/F) → ℤ/2`: `χ_a(σ) = 0` iff `σ(√a) = √a`. -/
noncomputable def kummerCharFun (a : Fˣ) (σ : AbsGal F) : ZMod 2 :=
  by classical exact if σ (sqrtSep a) = sqrtSep a then 0 else 1

lemma sqrtSep_ne_zero (a : Fˣ) : sqrtSep a ≠ 0 := by
  intro h
  have := sqrtSep_sq a
  rw [h, zero_pow two_ne_zero, eq_comm, map_eq_zero] at this
  exact a.ne_zero this

lemma neg_sqrtSep_ne (a : Fˣ) : -sqrtSep a ≠ sqrtSep a := by
  intro h
  have h2 : (2 : SeparableClosure F) * sqrtSep a = 0 := by rw [two_mul]; nth_rw 1 [← h]; ring
  rcases mul_eq_zero.mp h2 with h2 | h2
  · exact NeZero.ne ((2 : ℕ) : SeparableClosure F) (by exact_mod_cast h2)
  · exact sqrtSep_ne_zero a h2

lemma apply_sqrtSep (a : Fˣ) (σ : AbsGal F) :
    σ (sqrtSep a) = sqrtSep a ∨ σ (sqrtSep a) = -sqrtSep a := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [← map_pow, sqrtSep_sq, AlgEquiv.commutes]

lemma kummerCharFun_mul (a : Fˣ) (σ τ : AbsGal F) :
    kummerCharFun a (σ * τ) = kummerCharFun a σ + kummerCharFun a τ := by
  have hne := neg_sqrtSep_ne a
  rcases apply_sqrtSep a τ with hτ | hτ <;> rcases apply_sqrtSep a σ with hσ | hσ <;>
    simp [kummerCharFun, AlgEquiv.mul_apply, hτ, hσ, map_neg, hne]
  decide

lemma continuous_kummerCharFun (a : Fˣ) : Continuous (kummerCharFun a) := by
  let S := MulAction.stabilizer (AbsGal F) (sqrtSep a)
  have hS : ∀ σ : AbsGal F, σ ∈ S ↔ σ (sqrtSep a) = sqrtSep a := fun σ ↦ Iff.rfl
  let E := IntermediateField.adjoin F {sqrtSep a}
  have : FiniteDimensional F E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (sqrtSep a))
  have hle : E.fixingSubgroup ≤ S := fun σ hσ ↦
    (hS σ).mpr ((IntermediateField.mem_fixingSubgroup_iff E σ).mp hσ _
      (IntermediateField.mem_adjoin_simple_self F _))
  have hopen : IsOpen (S : Set (AbsGal F)) := Subgroup.isOpen_mono hle E.fixingSubgroup_isOpen
  have hclosed : IsClosed (S : Set (AbsGal F)) := Subgroup.isClosed_of_isOpen S hopen
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_isOpen_fiber_apply]
  intro σ
  by_cases hσ : σ (sqrtSep a) = sqrtSep a
  · convert hopen using 1
    ext τ
    by_cases hτ : τ (sqrtSep a) = sqrtSep a <;> simp [kummerCharFun, hS, hσ, hτ]
  · convert hclosed.isOpen_compl using 1
    ext τ
    by_cases hτ : τ (sqrtSep a) = sqrtSep a <;> simp [kummerCharFun, hS, hσ, hτ]

/-- The Kummer character as a continuous map. -/
noncomputable def kummerChar (a : Fˣ) : C(AbsGal F, ZMod 2) :=
  ⟨kummerCharFun a, continuous_kummerCharFun a⟩

/-- The homogeneous cocycle `(x₀, …, xₙ) ↦ ∏ⱼ (χ_{aⱼ}(xⱼ) - χ_{aⱼ}(xⱼ₋₁))`. -/
noncomputable def symbolCochain {n : ℕ} (a : Fin n → Fˣ) : C(Fin (n + 1) → AbsGal F, ZMod 2) :=
  ⟨prodCochain (fun j ↦ kummerChar (a j)), by
    unfold prodCochain; fun_prop⟩

lemma symbolCochain_invariant {n : ℕ} (a : Fin n → Fˣ) (g : AbsGal F)
    (v : Fin (n + 1) → AbsGal F) : symbolCochain a (fun i ↦ g * v i) = symbolCochain a v := by
  simp only [symbolCochain, ContinuousMap.coe_mk, prodCochain, kummerChar, kummerCharFun_mul]
  congr 1; funext j; ring

lemma coboundary_symbolCochain {n : ℕ} (a : Fin n → Fˣ) :
    coboundary (n + 1) (symbolCochain a) = 0 := by
  ext y
  rw [coboundary_apply, ContinuousMap.zero_apply]
  have := fcob_prodCochain (fun j ↦ kummerChar (a j)) y
  simpa [fcob, symbolCochain, zsmul_eq_mul] using this

/-- The Galois symbol `(a₁, …, aₙ) ↦ δa₁ ∪ ⋯ ∪ δaₙ ∈ Hⁿ(F, ℤ/2)`. -/
noncomputable def galoisSymbol {n : ℕ} (a : Fin n → Fˣ) : H F n :=
  classOf (ZMod 2) n (symbolCochain a) (symbolCochain_invariant a) (coboundary_symbolCochain a)

end MilnorConjecture


