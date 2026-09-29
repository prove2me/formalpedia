-- Prove2me | Definitions.Def_HighDimStat_UniformLaws_symmetrizedProcess
-- name    : HighDimStat_UniformLaws_symmetrizedProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:27:54.963986+00:00
-- url     : https://prove2.me/theorems/a77a882f-b4fa-4d39-a0b5-5be5d35dd4a8
-- title:
--   The symmetrized process ||Sn||_F (Eq. 4.19)
-- statement:
--   **Eq. (4.19).** The **symmetrized process**
--
--   $$
--   \|S_n\|_F \;:=\; \sup_{f\in F}\Big|\frac1n\sum_{i=1}^n \varepsilon_i f(X_i)\Big|,
--   $$
--
--   for an independent Rademacher sequence $\varepsilon_1,\dots,\varepsilon_n$. Its expectation
--   is the Rademacher complexity $R_n(F)$; it is the object Proposition 4.11's sandwich bound
--   relates to $\|\mathbb P_n-P\|_F$.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 107 (PDF p. 127), Eq. (4.19)

import Mathlib

namespace HighDimStat.UniformLaws

/-- **Eq. (4.19)**, Wainwright, *High-Dimensional Statistics* (2019), p. 107. The symmetrized
process `‖Sₙ‖_F := sup_{f∈F} |(1/n)∑ᵢεᵢf(Xᵢ)|`, for a function class `F = {f_j, j∈ι}`, a sample
`X₁,...,Xₙ`, and an independent Rademacher sequence `ε₁,...,εₙ`. -/
noncomputable def symmetrizedProcess {D ι Ω : Type*} [MeasurableSpace D] (f : ι → D → ℝ)
    (Xs : ℕ → Ω → D) (eps : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ⨆ j : ι, |(1 / (n : ℝ)) * ∑ i ∈ Finset.range n, eps i ω * f j (Xs i ω)|

end HighDimStat.UniformLaws


