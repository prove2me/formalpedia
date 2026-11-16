-- Prove2me | Definitions.Def_ArbLindbladLearn_Supplement_expectedTime
-- name    : ArbLindbladLearn_Supplement_expectedTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:21:40.963784+00:00
-- url     : https://prove2.me/theorems/7e20a2ff-85c9-4bd3-bb77-32c0f47b0b57
-- title:
--   Expected total evolution time $\mathbb E_{\mathcal L}T_{\mathrm{tot}}$ of an open-ended protocol
-- statement:
--   For an open-ended protocol run against a generator $\mathcal L$, the total evolution time is $T_{\mathrm{tot}}=\sum_j t_j$, the sum of the durations of the queries made, and its expectation is
--   $$\mathbb E_{\mathcal L}T_{\mathrm{tot}}=\sum_j\sum_h t_h\,p(h),$$
--   the duration chosen at each history weighted by the probability of reaching that history and querying there.
--
--   **Formalization Note** Computed as the supremum over $N$ of the expected evolution time of the first $N$ queries, a value in $[0,\infty]$; $\mathbb E T_{\mathrm{tot}}=\infty$ is allowed.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), §1.1, p.2; proof of Theorem 5.8, p.47

import Mathlib
import Definitions.Def_ArbLindbladLearn_Supplement_OpenProtocol

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn.Supplement

open MeasureTheory
open LindbladTolerant.Testing

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The expected evolution time of the next `q` queries from history `h` with unnormalized state `ρ`:
if the run continues at `h`, the duration `t_h` weighted by the probability `tr ρ` of reaching `h`,
plus the same quantity from each successor history. -/
def timeUpTo (p : OpenProtocol n Ω) (g : Super (Qubits n) (Qubits n)) :
    (q : ℕ) → (h : List Ω) → Op (Qubits n × Fin (p.memory h)) → ℝ≥0∞
  | 0, _, _ => 0
  | q + 1, h, ρ => if p.stop h then 0 else
      ENNReal.ofReal (p.duration h * ρ.trace.re) +
      ∫⁻ o, timeUpTo p g q (h ++ [o])
        (applySuper ((p.instrument h).branch o)
          (tensorId (evolution g (p.duration h)) ρ)) ∂(p.instrument h).base

/-- The expected total evolution time `𝔼_ℒ T_tot = 𝔼 Σ_j t_j` of the open-ended protocol `p` run
against the generator `g` (§1.1, p.2; proof of Theorem 5.8, p.47, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…):
`Σ_j Σ_b t_jb p_d(jb) = 𝔼_d Σ_j t_j = 𝔼_d T_tot`).

**Formalization Note** The supremum over `q` of the truncated expectations `timeUpTo … q` (nondecreasing
in `q`); a value in `ℝ≥0∞`, so `𝔼 T_tot = ∞` is allowed. -/
def expectedTime (p : OpenProtocol n Ω) (g : Super (Qubits n) (Qubits n)) : ℝ≥0∞ :=
  ⨆ q : ℕ, timeUpTo p g q [] p.initial

end ArbLindbladLearn.Supplement


