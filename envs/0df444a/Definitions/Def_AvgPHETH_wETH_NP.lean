-- Prove2me | Definitions.Def_AvgPHETH_wETH_NP
-- name    : AvgPHETH_wETH_NP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:54.03621+00:00
-- url     : https://prove2.me/theorems/9c9361bf-624d-4af6-adbe-b19276c3ad65
-- title:
--   The hypothesis $\mathrm{wETH}^{\mathrm{NP}}$
-- statement:
--   $\mathrm{wETH}^{\mathrm{NP}}$ is the hypothesis that $\Sigma_2\mathrm{SAT}$ on $N$ variables cannot be solved in time $2^{O(N/\log N)}\cdot\mathrm{poly}(n)$ by deterministic algorithms with an NP oracle: there are no constant $c$, language $B\in\mathrm{NP}$ and machine $M$ such that on every instance $\varphi$ of input length $n$ the machine $M^B$ halts within
--
--   $$\left\lceil 2^{cN/\log_2\max(N,2)}\cdot(n+2)^c\right\rceil$$
--
--   steps and accepts if and only if $\exists y\,\forall z\,\varphi(y,z)$.
--
--   **Formalization Note** One constant $c$ stands for both the constant of $O(\cdot)$ and the degree of $\mathrm{poly}(n)$, by taking the larger. The term $\max(N,2)$ only excludes $N\le1$, where the logarithm vanishes.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §1.1, p.2 (PDF 4); Definition 1.3, p.3 (PDF 5)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_HaltsWithin
import Definitions.Def_KarpLiptonOM_tupleEnc
import Definitions.Def_AvgPHETH_acceptsAt
import Definitions.Def_AvgPHETH_SigmaPO
import Definitions.Def_AvgPHETH_Inst3DNF_N
import Definitions.Def_AvgPHETH_Inst3DNF_value
import Definitions.Def_AvgPHETH_Inst3DNF_enc
open KarpLiptonOM

namespace AvgPHETH

/-- The hypothesis `wETH^NP` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §1.1, p.2 (PDF 4); Definition 1.3, p.3 (PDF 5), `wETH^{Σ₁^p}`):
`Σ₂SAT` on `N` variables cannot be solved in time `2^{O(N/log N)} · poly(n)` by deterministic
algorithms with an NP oracle. There are no constant `c`, language `B ∈ NP` and machine `M` such that
on **every** instance `φ` the machine with oracle `B` halts within
`⌈2^{c N / log₂ max(N, 2)} · (n + 2)^c⌉` steps and accepts iff `φ` is true.

**Formalization Note** One `c` stands for both the `O(·)` and the degree of `poly(n)`, taking the
larger. `max(N, 2)` only excludes `N ≤ 1`, where `log₂ N = 0`. -/
def wETH_NP : Prop :=
  ¬ ∃ (c : ℕ) (B : Set (List Bool)) (M : OracleTM), B ∈ SigmaPO ∅ 1 ∧ ∀ φ : Inst3DNF,
    let T := ⌈(2 : ℝ) ^ ((c : ℝ) * (φ.N : ℝ) / Real.logb 2 (max (φ.N : ℝ) 2)) *
      ((φ.enc.length : ℝ) + 2) ^ c⌉₊
    M.HaltsWithin B T (tupleEnc [φ.enc]) ∧ (acceptsAt M B T (tupleEnc [φ.enc]) ↔ φ.value)

end AvgPHETH


