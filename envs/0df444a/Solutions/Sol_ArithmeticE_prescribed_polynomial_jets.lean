-- Prove2me | solution 1 for ArithmeticE.prescribed_polynomial_jets
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T16:38:38.380026+00:00
-- url     : https://prove2.me/submissions/a1cff657-0a6e-4ee9-8efb-ace7420cf47a

import Mathlib
open Polynomial
namespace BeukersJets
lemma prescribed_jets {K : Type*} [Field K] [CharZero K]
    (ξ : K) (N : ℕ) (a : ℕ → K) :
    ∃ P : Polynomial K, ∀ k < N, (Polynomial.derivative^[k] P).eval ξ = a k := by
  classical
  let Q : Polynomial K := ∑ k ∈ Finset.range N, monomial k (a k / (k.factorial : K))
  let P := taylor (-ξ) Q
  have hshift : taylor ξ P = Q := by
    simp [P, taylor_apply, Polynomial.comp_assoc]
  refine ⟨P, ?_⟩
  intro k hk
  have hc : (taylor ξ P).coeff k = a k / (k.factorial : K) := by
    rw [hshift]
    simp [Q, coeff_monomial, hk]
  rw [taylor_coeff] at hc
  have hd := congrFun (factorial_smul_hasseDeriv (R := K) (k := k)) P
  change k.factorial • hasseDeriv k P = Polynomial.derivative^[k] P at hd
  rw [← hd]
  have hf : (k.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  simp [hc]
  field_simp
end BeukersJets

theorem solution {K : Type*} [Field K] [CharZero K]
    (ξ : K) (N : ℕ) (a : ℕ → K) :
    ∃ P : Polynomial K, ∀ k < N, (Polynomial.derivative^[k] P).eval ξ = a k := by
  exact BeukersJets.prescribed_jets ξ N a
#print axioms solution
