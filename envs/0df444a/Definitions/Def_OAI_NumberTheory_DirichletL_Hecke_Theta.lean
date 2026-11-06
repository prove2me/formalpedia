-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
-- name    : OAI_NumberTheory_DirichletL_Hecke_Theta
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:41:19.563507+00:00
-- url     : https://prove2.me/theorems/f54ea05e-aa03-466f-b692-3f9bbabd5aab
-- title:
--   Theta
-- statement:
--   Definitions and structural lemmas for Theta, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/Theta.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_parityPair_k
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
attribute [local simp] OAI.SevenEighths.EisensteinTheta.parityPair_k
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k


set_option autoImplicit false
namespace OAI
noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
namespace SevenEighths.HeckeTheta
open EisensteinTheta
theorem locallyIntegrableOn_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℂ) (hf : ∀ i ∈ s, LocallyIntegrableOn (f i) (Ioi 0)) :
    LocallyIntegrableOn (∑ i ∈ s, f i) (Ioi 0) := by
  exact Finset.sum_induction f (fun g => LocallyIntegrableOn g (Ioi 0))
    (fun _ _ => LocallyIntegrableOn.add) (locallyIntegrableOn_const 0) hf
def finitePair {ι : Type*} [Fintype ι] (P : ι → WeakFEPair ℂ)
    (hk : ∀ i, (P i).k = 1) (w : ι → ℂ) : WeakFEPair ℂ where
  f := ∑ i, w i • (P i).f
  g := ∑ i, (w i * (P i).ε) • (P i).g
  k := 1
  ε := 1
  f₀ := ∑ i, w i * (P i).f₀
  g₀ := ∑ i, w i * (P i).ε * (P i).g₀
  hf_int := locallyIntegrableOn_sum Finset.univ _
    (fun i _ => (P i).hf_int.smul (w i))
  hg_int := locallyIntegrableOn_sum Finset.univ _
    (fun i _ => (P i).hg_int.smul (w i * (P i).ε))
  hk := by norm_num
  hε := one_ne_zero
  h_feq x hx := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, one_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [(P i).h_feq x hx, hk i]
    simp only [smul_eq_mul]
    ring
  hf_top r := by
    have h := Asymptotics.IsBigO.fun_sum (s := Finset.univ)
      (fun i _ => ((P i).hf_top r).const_mul_left (w i))
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib,
      mul_sub] using h
  hg_top r := by
    have h := Asymptotics.IsBigO.fun_sum (s := Finset.univ)
      (fun i _ => ((P i).hg_top r).const_mul_left (w i * (P i).ε))
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib,
      mul_sub] using h
def regroup (N : ℕ) : ((ℤ × Fin N) × (ℤ × Fin N)) ≃ ((Fin N × Fin N) × (ℤ × ℤ)) where
  toFun p := ((p.1.2, p.2.2), (p.1.1, p.2.1))
  invFun p := ((p.2.1, p.1.1), (p.2.2, p.1.2))
  left_inv _ := rfl
  right_inv _ := rfl
def residueEquiv (N : ℕ) [NeZero N] : (ℤ × ℤ) ≃ ((Fin N × Fin N) × (ℤ × ℤ)) :=
  (Equiv.prodCongr (Int.divModEquiv N) (Int.divModEquiv N)).trans (regroup N)
def periodicCoeff {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (n : ℤ × ℤ) : ℂ :=
  w (residueEquiv N n).1
def theta {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℤ × ℤ, periodicCoeff w n *
    (Real.exp (-Real.pi * normForm n.1 n.2 * t) : ℂ)
def pair {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) : WeakFEPair ℂ :=
  finitePair (fun p : (Fin N × Fin N) × Fin 2 =>
    parityPair p.1.1 p.1.2 N (Nat.cast_pos.mpr (NeZero.pos N)) p.2)
    (fun _ => ThetaProduct.rectangularPair_k ..) (fun p => w p.1)
def dualScalar (N : ℕ) : ℂ :=
  ((((N : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    (((3 * (N : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
def completed {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) : ℂ → ℂ := (pair w).Λ
def latticeL {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹ * completed w s
def regularizedCompleted {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (s : ℂ) : ℂ :=
  (s - 1) * ((pair w).Λ₀ s - s⁻¹ * (pair w).f₀) + (pair w).g₀
def regularizedLatticeL {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹ * regularizedCompleted w s
end SevenEighths.HeckeTheta
end
end OAI


