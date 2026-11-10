-- Prove2me | Definitions.Def_TolProdTest_zk
-- name    : TolProdTest_zk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:26:21.587584+00:00
-- url     : https://prove2.me/theorems/ff435ab3-0515-4dc1-b5ac-c60fbb3e390e
-- title:
--   Acceptance probabilities $Z_k(\rho)$ and $Z_{k,C}(\rho)$
-- statement:
--   The acceptance probability of the $k$-copy product test (Protocol 2.1) on $\rho$ is
--
--   $$
--   Z_k(\rho)=\mathrm{Tr}\big[Q_k\,\rho^{\otimes k}\big],
--   $$
--
--   and the acceptance probability of the blockwise test for a coloring $C$ is $Z_{k,C}(\rho)=\mathrm{Tr}[Q_{k,C}\,\rho^{\otimes k}]$. The same formula is used for non-normalized positive operators.
--
--   $Z_k$ is the statistic the tester estimates; $Z_{k,C}\ge Z_k$ is its blockwise counterpart used in the analysis.
--
--   **Formalization Note** $\rho^{\otimes k}$ is the published `ShadowTomography.UpperBound.tensorPow ρ k`. The value is the real part of the trace, which is real and nonnegative for positive semidefinite $\rho$.
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eq. (21), p.8; p.10; p.14

import Mathlib
import Definitions.Def_TolProdTest_symProjOn
import Definitions.Def_ShadowTomography_UpperBound_tensorPow

set_option autoImplicit false

namespace TolProdTest

/-- **Blockwise test acceptance** `Z_{k,C}(ρ) := Tr[Q_{k,C} ρ^{⊗k}]`, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), p.10 (`k = 2`, `Z_{2,C}`) and p.14:
"Set Q_{k,C} := ∏_{c∈[q]} Q_{k,c} and Z_{k,C}(ρ) := Tr[Q_{k,C} ρ^{⊗k}]."

**Formalization Note** `ρ^{⊗k}` is the published `ShadowTomography.UpperBound.tensorPow ρ k` (copy `j` is coordinate
`j`). The value is the real part of the trace; for positive semidefinite `ρ` the trace is real and
nonnegative. The same formula is used for non-normalized positive operators (Lemma 3.6). -/
noncomputable def zkC {S ι : Type} [Fintype S] [DecidableEq S] [Fintype ι] [DecidableEq ι] {d : ℕ}
    (C : S → ι) (ρ : Matrix (S → Fin d) (S → Fin d) ℂ) (k : ℕ) : ℝ :=
  (symProjBlocks d C k * ShadowTomography.UpperBound.tensorPow ρ k).trace.re

/-- **Acceptance probability of the `k`-copy product test** `Z_k(ρ) := Tr[Q_k ρ^{⊗k}]`, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eq. (21),
p.8 (Protocol 2.1): every site is its own block. -/
noncomputable def zk {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    (ρ : Matrix (S → Fin d) (S → Fin d) ℂ) (k : ℕ) : ℝ :=
  zkC (id : S → S) ρ k

end TolProdTest


