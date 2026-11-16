-- Prove2me | Definitions.Def_OnlineShadow_LogRate_Supplement_expectedRegret
-- name    : OnlineShadow_LogRate_Supplement_expectedRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:55:26.761524+00:00
-- url     : https://prove2.me/theorems/7f890285-0177-48cf-8d30-4f4b70eb428c
-- title:
--   Expected regret $\mathbb E_{j\sim M(\rho^{\otimes n})}[\mu_*-\mu_j]$ of a Best Observable Selection POVM
-- statement:
--   Let $A_1,\dots,A_m$ be observables on $\mathbb C^d$ and $M=(M_1,\dots,M_m)$ a measurement on $n$ copies $(\mathbb C^d)^{\otimes n}$. Measuring $\rho^{\otimes n}$ with $M$ outputs $j$ with probability $\mathrm{Tr}(M_j\rho^{\otimes n})$. With $\mu_i:=\mathrm{Tr}(\rho A_i)$ and $\mu_*:=\max_i\mu_i$, the **regret** of output $j$ is $r_\rho(j)=\mu_*-\mu_j$ (Definition A.1), and the **expected regret** at $\rho$ is
--   $$\mathbb E_{j\sim M(\rho^{\otimes n})}[r_\rho(j)]=\sum_{j=1}^m\mathrm{Tr}(M_j\rho^{\otimes n})\,(\mu_*-\mu_j).$$
--
--   This is the payoff in the Best Observable Selection problem of Appendix A.
--
--   **Formalization Note** Outputs are indexed by `Fin m`. $\mu_*$ is the supremum over the finite index set, which is the maximum when $m\ge1$ (the theorems using this definition assume $m\ge1$). Traces are real parts of complex traces.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition A.1, p. 25

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow

namespace OnlineShadow.LogRate.Supplement

/-- The **expected regret** of a Best Observable Selection algorithm (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition A.1, p.25).
Given observables `A₁, …, A_m` on `ℂ^d` and a POVM `M = (M₁, …, M_m)` on `n` copies `(ℂ^d)^{⊗n}`, the
algorithm measures `ρ^{⊗n}` with `M` and outputs `j` with probability `Tr(M_j ρ^{⊗n})`. With
`μ_i := Tr(ρA_i)` and `μ_* := max_i μ_i`, the regret of output `j` is `r_ρ(j) = μ_* − μ_j`, and the
expected regret at `ρ` is
`E_{j∼M(ρ^{⊗n})}[r_ρ(j)] = ∑_j Tr(M_j ρ^{⊗n}) (μ_* − μ_j)`.

**Formalization Note** Outputs are `Fin m` (0-based). `μ_*` is the supremum `⨆ i` over the finite index
set, which is the maximum when `m ≥ 1` (the theorems using this definition assume `m ≥ 1`). Traces are
real parts of complex traces. Adaptive measurements and internal randomness compose into one POVM, so
this covers every learner. -/
noncomputable def expectedRegret {d n m : ℕ} (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (M : Fin m → Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ j, (M j * ShadowTomography.UpperBound.tensorPow ρ n).trace.re *
    ((⨆ i, (A i * ρ).trace.re) - (A j * ρ).trace.re)

end OnlineShadow.LogRate.Supplement


