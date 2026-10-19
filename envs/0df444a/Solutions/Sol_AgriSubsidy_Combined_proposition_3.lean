-- Prove2me | solution 1 for AgriSubsidy.Combined.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T10:06:29.788394+00:00
-- url     : https://prove2.me/submissions/723a08a8-f778-4c09-87d4-7d1a7c96b729

import Mathlib
import Definitions.Def_AgriSubsidy_Combined_Setting
import Definitions.Def_AgriSubsidy_Combined_Majorization
set_option autoImplicit false
namespace AgriResearch
open AgriSubsidy.Combined
open scoped BigOperators
lemma foc {N : ℕ} (P : Params) (z t q : Fin N → ℝ)
    (eq : IsEquilibrium P z t q) (hpos : ∀j,0<q j) (j : Fin N) :
    P.α-z j*P.cP-P.cH+t j-P.β*(∑ i,q i)=P.β*q j := by
  classical
  let R := ∑ i ∈ Finset.univ \ {j}, q i
  have hsum : ∑i, q i=q j+R := by
    have hh := Finset.sum_update_of_mem (Finset.mem_univ j) q (q j)
    simpa [R] using hh
  let f : ℝ → ℝ := fun x => (P.α-z j*P.cP-P.cH+t j-P.β*(x+R))*x
  have hf : ∀x,profit P z t (Function.update q j x) j=f x := by
    intro x
    simp [profit,Finset.sum_update_of_mem, R,f]
  have hm : IsMaxOn f (Set.Ici 0) (q j) := by
    intro x hx
    have he := eq.2 j x hx
    rw [hf] at he
    have hself := hf (q j)
    simp only [Function.update_eq_self] at hself
    exact he.trans_eq hself
  have hd : HasDerivAt f (P.α-z j*P.cP-P.cH+t j-P.β*R-2*P.β*q j) (q j) := by
    convert (((hasDerivAt_const (q j) (P.α-z j*P.cP-P.cH+t j)).sub
      (((hasDerivAt_id (q j)).add_const R).const_mul P.β)).mul (hasDerivAt_id (q j))) using 1 <;>
      (try dsimp [f]) <;> first | rfl | ring
  have hh := (hm.isLocalMax (Ici_mem_nhds (hpos j))).hasDerivAt_eq_zero hd
  rw [hsum]
  nlinarith
lemma equilibrium_formula {N : ℕ} (P : Params) (z : Fin N → ℝ)
    (h : Standing P z) (sP sH : ℝ) (q : Fin N → ℝ)
    (eq : IsEquilibrium P z (combined z sP sH) q) (hpos : ∀j,0<q j) :
    (∀j,q j=(1/P.β)*(abar P z sP sH/((N:ℝ)+1)-(z j-zbar z)*(P.cP-sP))) ∧
    (∀j,profit P z (combined z sP sH) q j=P.β*(q j)^2) := by
  have hf := foc P z (combined z sP sH) q eq hpos
  have hsum := congrArg (fun f : Fin N→ℝ => ∑j,f j) (funext hf)
  simp only [combined,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  simp only [← Finset.sum_mul,← Finset.mul_sum] at hsum
  have hβ : P.β≠0 := ne_of_gt h.2.2.1
  have hN : (N:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt h.1
  have hN1 : (N:ℝ)+1≠0 := by positivity
  constructor
  · intro j
    have hj := hf j
    dsimp [combined] at hj
    dsimp [abar,zbar]
    field_simp
    nlinarith [congrArg (fun x : ℝ => (N:ℝ)*x) hj,
      congrArg (fun x : ℝ => ((N:ℝ)+1)*x) hj]
  · intro j
    unfold profit
    rw [hf j]
    ring
end AgriResearch

open AgriSubsidy.Combined

theorem solution {N : ℕ} (P : Params) (z : Fin N → ℝ)
    (h : Standing P z) (sP sH : ℝ) (q : Fin N → ℝ)
    (eq : IsEquilibrium P z (combined z sP sH) q)
    (hpos : ∀ j, 0 < q j) :
    (∀ j, q j = (1 / P.β) *
      (abar P z sP sH / ((N : ℝ) + 1) - (z j - zbar z) * (P.cP - sP))) ∧
    (∀ j, profit P z (combined z sP sH) q j = P.β * (q j) ^ 2) := by exact AgriResearch.equilibrium_formula P z h sP sH q eq hpos


#print axioms solution
