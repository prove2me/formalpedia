-- Prove2me | Definitions.Def_HellingerSubadd_mixKernel
-- name    : HellingerSubadd_mixKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:48:36.992115+00:00
-- url     : https://prove2.me/theorems/9e0f0412-afaf-4e7c-bc3c-d81095ff7ca1
-- title:
--   Mixture kernels $P^{(i)}_\lambda=(1-\lambda)P^{(i)}+\lambda Q^{(i)}$
-- statement:
--   For kernels $\kappa_k,\eta_k$ from $\mathcal X_0\times\dots\times\mathcal X_k$ to $\mathcal X_{k+1}$ and a parameter $\lambda$, the **mixture kernels** are
--
--   $$
--   (\kappa_\lambda)_k(\cdot\mid x)=(1-\lambda)\,\kappa_k(\cdot\mid x)+\lambda\,\eta_k(\cdot\mid x).
--   $$
--
--   With $\kappa_{i-1}=P^{(i)}$ and $\eta_{i-1}=Q^{(i)}$ these are the kernels $P^{(i)}_\lambda$ of the proof of Lemma A.13, and the sequential law they generate is $\mathbb P_\lambda$. For $\lambda\in[0,1]$ the mixture of two probability kernels is a probability kernel.
--
--   **Formalization Note** The weights are `ENNReal.ofReal (1 - λ)` and `ENNReal.ofReal λ`, which are $1-\lambda$ and $\lambda$ for $\lambda\in[0,1]$; every statement of the mission that uses the mixture assumes $0<\lambda<e^{-1}$. The definition contains the structural proof that a mixture of kernels is measurable in its argument.
-- source:
--   Foster, Kakade, Qian & Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, proof of Lemma A.13, p. 73

import Mathlib

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace HellingerSubadd

/-- **Mixture kernels** `P^(i)_λ(· | x_{1:i−1}) = (1 − λ)P^(i)(· | x_{1:i−1}) + λQ^(i)(· | x_{1:i−1})`.
Foster, Kakade, Qian & Rakhlin, *The Statistical Complexity of Interactive Decision Making*,
arXiv:2112.13487v3, proof of Lemma A.13, p. 73.

`mixKernel κ η lam k` is the kernel `x ↦ (1 − lam) • κ k x + lam • η k x`. The law `P_λ` of the
proof is `seqLaw (mixKernel κ η lam) n x₀`.

**Formalization Note.** The weights are `ENNReal.ofReal (1 − lam)` and `ENNReal.ofReal lam`; for
`0 ≤ lam ≤ 1` they are the paper's `1 − λ` and `λ`, and the mixture of two Markov kernels is
Markov. Every theorem of the mission that uses `mixKernel` assumes `0 < lam < e⁻¹`, the paper's
range. The measurability field is the structural proof that a mixture of kernels is a kernel. -/
noncomputable def mixKernel {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]
    (κ η : (k : ℕ) → Kernel (Π i : Iic k, X i) (X (k + 1))) (lam : ℝ) :
    (k : ℕ) → Kernel (Π i : Iic k, X i) (X (k + 1)) :=
  fun k =>
    { toFun := fun x => ENNReal.ofReal (1 - lam) • κ k x + ENNReal.ofReal lam • η k x
      measurable' := by
        refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
        simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
        exact (((κ k).measurable_coe hs).const_mul _).add (((η k).measurable_coe hs).const_mul _) }

end HellingerSubadd


