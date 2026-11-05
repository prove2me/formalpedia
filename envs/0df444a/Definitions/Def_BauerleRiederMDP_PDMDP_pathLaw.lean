-- Prove2me | Definitions.Def_BauerleRiederMDP_PDMDP_pathLaw
-- name    : BauerleRiederMDP_PDMDP_pathLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:15.311242+00:00
-- url     : https://prove2.me/theorems/eef7bfe1-db9e-4ae4-98fe-980c8a5959cb
-- title:
--   Law of a marked point process with exponential sojourns
-- statement:
--   Given Markov kernels $\kappa_n$ on a space $S$ and a start $s_0$, the module defines the law on $S^{\mathbb N}$ of the chain with these transition kernels (Ionescu–Tulcea). The **jump step** is the kernel of the marked point process: from $(T_n,Z_n)=(t,z)$, the sojourn $T_{n+1}-T_n$ is exponential with rate $\lambda$, and given that it equals $s$, the mark $Z_{n+1}$ has law $Q(\cdot|g((t,z),s))$. So
--   $$
--   \mathbb P\big(T_{n+1}-T_n\le t,\ Z_{n+1}\in B\mid\dots\big)=\lambda\int_0^te^{-\lambda s}Q\big(B\mid g(\dots,s)\big)\,ds.
--   $$
--   The index $n$ with $T_n\le t<T_{n+1}$ is `jumpIndex`.
--
--   **Formalization Note** The path space is $(\mathbb R\times E)^{\mathbb N}$ with the coordinates $(T_n,Z_n)$. `jumpIndex` is the supremum of $\{n:T_n\le t\}$, which is that index on every path whose jump times increase to infinity, that is, on almost every path.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), the law of (T_n, Z_n), p.245

import Mathlib

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.PDMDP

/-- The law on the path space `ℕ → S` of a Markov chain with transition kernels `κ n` started at
`s₀` (Ionescu–Tulcea). The chapter applies it to `S = ℝ × E`, whose points are the pairs
`(T_n, Z_n)` of the marked point process (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.245, PDF 256). -/
noncomputable def pathLaw {S : Type*} [MeasurableSpace S] (κ : ℕ → Kernel S S)
    [∀ n, IsMarkovKernel (κ n)] (s₀ : S) : Measure (ℕ → S) :=
  Kernel.traj (X := fun _ => S)
    (fun n => (κ n).comap (fun h : (Π _ : Finset.Iic n, S) => h ⟨n, Finset.mem_Iic.2 le_rfl⟩)
      (measurable_pi_apply _)) 0 (fun _ => s₀)

/-- One step of the marked point process (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.245, PDF 256): from `(T_n, Z_n) = (t, z)`, the
sojourn `S = T_{n+1} - T_n` is exponential with rate `λ` and, given `S = s`, the mark `Z_{n+1}`
has law `Q(·|g((t,z),s))`, where `g((t,z),s)` is the state and the control action at the jump. So
`IP(T_{n+1} - T_n ≤ t, Z_{n+1} ∈ B | …) = λ ∫_0^t e^{-λs} Q(B|g(…,s)) ds`. -/
noncomputable def jumpStep {E U : Type*} [MeasurableSpace E] [MeasurableSpace U] (lam : ℝ)
    (Q : Kernel (E × U) E) (g : (ℝ × E) × ℝ → E × U) (hg : Measurable g) :
    Kernel (ℝ × E) (ℝ × E) :=
  ((Kernel.id ×ₖ (Kernel.const (ℝ × E) (expMeasure lam) ⊗ₖ Q.comap g hg))).map
    fun p => (p.1.1 + p.2.1, p.2.2)

/-- `jumpStep` is a Markov kernel when `λ > 0` and `Q` is a Markov kernel. -/
theorem isMarkovKernel_jumpStep {E U : Type*} [MeasurableSpace E] [MeasurableSpace U] {lam : ℝ}
    (hlam : 0 < lam) (Q : Kernel (E × U) E) [IsMarkovKernel Q] (g : (ℝ × E) × ℝ → E × U)
    (hg : Measurable g) : IsMarkovKernel (jumpStep lam Q g hg) := by
  have := isProbabilityMeasure_expMeasure hlam
  unfold jumpStep
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- The index `n` of the sojourn containing the time `t`: `T_n ≤ t < T_{n+1}` on a path whose jump
times increase to infinity, which is almost every path. -/
noncomputable def jumpIndex {E : Type*} (ω : ℕ → ℝ × E) (t : ℝ) : ℕ :=
  sSup {n | (ω n).1 ≤ t}

end BauerleRiederMDP.PDMDP


