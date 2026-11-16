-- Prove2me | Definitions.Def_NKtLB_Supplement_RrnKt
-- name    : NKtLB_Supplement_RrnKt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:25:28.676103+00:00
-- url     : https://prove2.me/theorems/ce781607-7d7a-4a2f-8bb3-dd393a52b74d
-- title:
--   $R_{rn\mathrm{Kt}}[s]$ — strings of high rnKt complexity
-- statement:
--   For $s:\mathbb N\to\mathbb R$,
--   $$
--   R_{rn\mathrm{Kt}}[s]=\{x\in\{0,1\}^* : rn\mathrm{Kt}(x)\ge s(|x|)\},
--   $$
--   "defined in the natural way using rnKt instead of nKt" (p.12), parallel to the base $R_{n\mathrm{Kt}}[s]$. Theorem 9 shows that no dense subset of $R_{rn\mathrm{Kt}}[s]$ is easy, for several thresholds $s$.
--
--   **Formalization Note** $rn\mathrm{Kt}=rn\mathrm{Kt}_{2/3}$; real-valued threshold, as in the base `NKtLB.RnKt`.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §1.2.4, p.12

import Mathlib
import Definitions.Def_NKtLB_Supplement_rnKt
import Definitions.Def_NKtLB_toEReal

namespace NKtLB.Supplement

/-- **`R_{rnKt}[s]`** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §1.2.4, p.12): "Similarly to `R_{nKt}[s]`, we can also consider the set
`R_{rnKt}[s]`, which is defined in the natural way using rnKt instead of nKt", i.e.
`R_{rnKt}[s] = {x ∈ {0,1}^* | rnKt(x) ≥ s(|x|)}`.

**Formalization Note.** `s : ℕ → ℝ` as in the base `RnKt`; `rnKt = rnKt_{2/3}`. -/
def RrnKt (U : Machine) (s : ℕ → ℝ) : Set (List Bool) :=
  {x | ((s x.length : ℝ) : EReal) ≤ toEReal (rnKt U ∅ (2 / 3) x [])}

end NKtLB.Supplement


