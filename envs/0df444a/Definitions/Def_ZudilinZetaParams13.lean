-- Prove2me | Definitions.Def_ZudilinZetaParams13
-- name    : ZudilinZetaParams13
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-22T17:53:16.019754+00:00
-- url     : https://prove2.me/theorems/fe0a70fd-e440-445f-8245-366c2daad7bf
-- title:
--   The parameter set $r = 3$, $q = 13$, $\eta_0 = 91$ used in the proof
-- statement:
--   The concrete parameters chosen in the last paragraph of Zudilin's note: $r = 3$, $q = 13$ and
--   $$\eta_0 = 91,\quad \eta_1 = \eta_2 = \eta_3 = 27,\quad \eta_4 = 29,\ \eta_5 = 30,\ \eta_6 = 31,\ \dots,\ \eta_{12} = 37,\ \eta_{13} = 38,$$
--   i.e. $\eta_j = 25 + j$ for $4 \le j \le 13$. `params13` bundles these with machine-checked proofs that they satisfy every admissibility condition of `Params`, in particular $2\eta_{13} = 76 < 91 = \eta_0$ and $2(\eta_1 + \dots + \eta_{13}) = 832 \le 910 = \eta_0 (q - r)$.
-- source:
--   W. V. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Uspekhi Mat. Nauk 56:4 (2001), 149–150, https://doi.org/10.4213/rm427 (English transl.: Russian Math. Surveys 56:4 (2001), 774–776)

import Definitions.Def_ZudilinZetaSetup

/-!
# Zudilin (2001): the parameter set used to prove the theorem

`r = 3`, `q = 13`, `η₀ = 91`, `η₁ = η₂ = η₃ = 27`, `η₄ = 29`, `η₅ = 30`, `η₆ = 31`, …,
`η₁₂ = 37`, `η₁₃ = 38`.
-/

namespace ZudilinZeta

/-- The parameters `η₀ = 91`, `η₁ = η₂ = η₃ = 27`, and `η_j = 25 + j` for `4 ≤ j ≤ 13`
(so `η₄ = 29`, `η₅ = 30`, `η₆ = 31`, …, `η₁₂ = 37`, `η₁₃ = 38`). -/
def eta13 (j : ℕ) : ℕ :=
  if j = 0 then 91 else if j ≤ 3 then 27 else if j ≤ 13 then 25 + j else 0

/-- The admissible parameter set `r = 3`, `q = 13` with the `η`'s of `eta13`,
used in Zudilin's note to prove the theorem. -/
def params13 : Params where
  q := 13
  r := 3
  eta := eta13
  q_odd := by decide
  r_odd := by decide
  q_ge := by decide
  eta_pos := by decide
  eta_mono := by decide
  eta_lt := by decide
  sum_le := by decide

end ZudilinZeta


