-- Prove2me | Definitions.Def_XuMannorRobust_Standard_Supplement_DoeblinChain
-- name    : XuMannorRobust_Standard_Supplement_DoeblinChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:59:37.886+00:00
-- url     : https://prove2.me/theorems/36bcb64d-cb4d-4b59-a067-0d6d01f09172
-- title:
--   Definition 4 — Doeblin minorization and the finite-prefix chain law
-- statement:
--   Let $Z$ be an arbitrary measurable state space and $P$ a probability transition kernel. The chain is **Doeblin with parameters $\alpha,T$** when $\alpha>0$, $T\ge1$ is an integer, and there is a probability measure $\phi$ such that
--
--   $$P^T(z,B)\ge\alpha\phi(B)\qquad(z\in Z,\ B\text{ measurable}).$$
--
--   For any initial probability law $\rho$ and sample size $n$, $\operatorname{chainPrefixLaw}(P,\rho,n)$ is the law of the first $n$ observations. It is constructed from Mathlib's trajectory law using the history kernel that reads only the current state, then restricting the path to its first $n$ coordinates. A structural instance verifies that this law is a probability.
--
--   This representation supplies the sampling law for Theorem 3 without restricting the state space or the initial law. Kernel powers and invariant measures use Mathlib directly.
--
--   **Formalization Note** Indices $0,\ldots,n-1$ correspond to the paper's $s_1,\ldots,s_n$; $\rho$ is the law of the first observed state. Transition kernels are measurable by their Mathlib type. The prefix projection is measurable, including at $n=0$ (the unique empty prefix), so no zero-measure fallback of `Measure.map` is used. `IsDoeblin` describes the minorization; the transition is separately required to be a Markov kernel in Theorem 3.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 400, Definition 4; pp. 400–401, §4.2.

import Mathlib

open MeasureTheory ProbabilityTheory

namespace XuMannorRobust.Standard.Supplement

/-- Definition 4: uniform T-step minorization on an arbitrary measurable state space.
The probability transition itself is Mathlib's `Kernel` with `IsMarkovKernel`. -/
def IsDoeblin {Z : Type*} [MeasurableSpace Z] (P : Kernel Z Z)
    (α : ℝ) (T : ℕ) : Prop :=
  0 < α ∧ 1 ≤ T ∧ ∃ φ : Measure Z, IsProbabilityMeasure φ ∧
    ∀ z : Z, ∀ B : Set Z, MeasurableSet B →
      ENNReal.ofReal α * φ B ≤ (P ^ T) z B


/-- Law of the first n outputs of a homogeneous chain, indexed from zero.
The initial law is that of the first observed state, and may be any probability.
At time t the history kernel reads only the state at t. The restriction map is
measurable on every measurable space, so `Measure.map` cannot take its junk branch. -/
noncomputable def chainPrefixLaw {Z : Type*} [MeasurableSpace Z]
    (P : Kernel Z Z) [IsMarkovKernel P] (ρ : Measure Z) (n : ℕ) :
    Measure (Fin n → Z) :=
  (ProbabilityTheory.Kernel.trajMeasure (X := fun _ : ℕ => Z) ρ
    (fun t => P.comap
      (fun x : (i : Finset.Iic t) → Z => x ⟨t, Finset.mem_Iic.mpr le_rfl⟩)
      (measurable_pi_apply _))).map (fun x : ℕ → Z => fun i : Fin n => x i.val)

/-- The derived prefix law is a probability under any probability initial law. -/
instance {Z : Type*} [MeasurableSpace Z] (P : Kernel Z Z) [IsMarkovKernel P]
    (ρ : Measure Z) [IsProbabilityMeasure ρ] (n : ℕ) :
    IsProbabilityMeasure (chainPrefixLaw P ρ n) := by
  unfold chainPrefixLaw
  exact Measure.isProbabilityMeasure_map
    (Measurable.aemeasurable (measurable_pi_iff.mpr fun i => measurable_pi_apply i.val))

end XuMannorRobust.Standard.Supplement


