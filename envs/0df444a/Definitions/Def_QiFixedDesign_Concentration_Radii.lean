-- Prove2me | Definitions.Def_QiFixedDesign_Concentration_Radii
-- name    : QiFixedDesign_Concentration_Radii
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:59:50.948194+00:00
-- url     : https://prove2.me/theorems/2723ba66-f72f-4c63-9ba4-956dbeb595aa
-- title:
--   The three printed concentration radii and their sum
-- statement:
--   For $N\ge1$, $0<\eta<1$, $a>1$, $c_1\ge1$ and $c_2>0$, define
--   $$r_{1,N}=\begin{cases}(\log(c_1/\eta)/(c_2N))^{1/2},&N\ge\log(c_1/\eta)/c_2,\\(\log(c_1/\eta)/(c_2N))^{1/a},&N<\log(c_1/\eta)/c_2.\end{cases}$$
--   For a finite nonnegative variance bound $\kappa$, define $r_{2,N}=\sqrt{p\kappa/N}/\eta$ and $r_{3,N}=\sqrt{\kappa c^T G_N^{-1}c/\eta}$. The sum radius in (53)–(54) evaluates all three at confidence $\eta/3$ and uses $\kappa=(2(A-1))^{1/a}$. These formulas are total in Lean; only the stated parameter domains and nonsingular positive prefixes have the paper's interpretation. The goal retains an existential radius sequence rather than requiring this particular witness.
-- source:
--   Qi, Cao and Shen (2021), Distributionally Robust Conditional Quantile Prediction with Fixed Design, DOI 10.1287/mnsc.2020.3903, supplied source.pdf, (38)–(39), (46), (53)–(54), PDF/printed pp. 17, 19, 21

import Mathlib
import Definitions.Def_QiFixedDesign_Concentration_Design
import Definitions.Def_QiFixedDesign_Concentration_LightTail

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace QiFixedDesign.Concentration

noncomputable def radiusOne (a c₁ c₂ η : ℝ) (N : ℕ) : ℝ :=
  if Real.log (c₁ / η) / c₂ ≤ (N : ℝ) then
    (Real.log (c₁ / η) / (c₂ * N)) ^ (1 / 2 : ℝ)
  else (Real.log (c₁ / η) / (c₂ * N)) ^ (1 / a)

noncomputable def radiusTwo (p : ℕ) (κ η : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt ((p : ℝ) * κ / N) / η

noncomputable def radiusThree {p : ℕ} (x : ℕ → Fin p → ℝ)
    (c : Fin p → ℝ) (κ η : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (κ * (c ⬝ᵥ ((gram x N)⁻¹ *ᵥ c)) / η)

noncomputable def radiusSum {p : ℕ} (x : ℕ → Fin p → ℝ)
    (c : Fin p → ℝ) (a A c₁ c₂ η : ℝ) (N : ℕ) : ℝ :=
  radiusOne a c₁ c₂ (η / 3) N + radiusTwo p (kappa a A) (η / 3) N +
    radiusThree x c (kappa a A) (η / 3) N

end QiFixedDesign.Concentration


