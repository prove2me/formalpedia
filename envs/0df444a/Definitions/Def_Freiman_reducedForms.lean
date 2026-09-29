-- Prove2me | Definitions.Def_Freiman_reducedForms
-- name    : Freiman_reducedForms
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T10:45:07.891976+00:00
-- url     : https://prove2.me/theorems/927c69e1-b553-455b-9234-4bc6cf85ac16
-- title:
--   Reduced quadratic forms and their two-sided continued-fraction orbit
-- statement:
--   The reduced form has coefficients 1/(α+β), (β−α)/(α+β), −αβ/(α+β), exactly (found:reduced-form). A ReducedOrbit is data satisfying the report’s positive, irrational forward recurrences at every integer position. Its existence is an open theorem, not a field assumed for arbitrary forms. The definitions also give the explicit integer change of variables and the natural descent measure |p|+|q|.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §§1.1–1.3

import Definitions.Def_Freiman_markovSpectrum
import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Definitions.Def_Freiman_continuants

namespace Freiman

noncomputable def reducedA (α β : ℝ) : ℝ := 1 / (α + β)
noncomputable def reducedB (α β : ℝ) : ℝ := (β - α) / (α + β)
noncomputable def reducedC (α β : ℝ) : ℝ := -α * β / (α + β)
noncomputable def reducedValue (α β : ℝ) (p q : ℤ) : ℝ :=
  quadraticValue (reducedA α β) (reducedB α β) (reducedC α β) p q
noncomputable def reducedMinimum (α β : ℝ) : ℝ :=
  quadraticMinimum (reducedA α β) (reducedB α β) (reducedC α β)
def formUnimodular (a b c d : ℤ) : Prop := a*d-b*c=1 ∨ a*d-b*c = -1
def transformedA (A B C : ℝ) (a b c d : ℤ) : ℝ :=
  A*(a:ℝ)^2+B*(a:ℝ)*(c:ℝ)+C*(c:ℝ)^2
def transformedB (A B C : ℝ) (a b c d : ℤ) : ℝ :=
  2*A*(a:ℝ)*(b:ℝ)+B*((a:ℝ)*(d:ℝ)+(b:ℝ)*(c:ℝ))+2*C*(c:ℝ)*(d:ℝ)
def transformedC (A B C : ℝ) (a b c d : ℤ) : ℝ :=
  A*(b:ℝ)^2+B*(b:ℝ)*(d:ℝ)+C*(d:ℝ)^2
structure ReducedOrbit where
  digits : ℤ → ℕ+
  alpha : ℤ → ℝ
  beta : ℤ → ℝ
  alpha_gt : ∀ n, 1 < alpha n
  beta_pos : ∀ n, 0 < beta n
  beta_lt : ∀ n, beta n < 1
  alpha_irr : ∀ n, Irrational (alpha n)
  beta_irr : ∀ n, Irrational (beta n)
  digit_floor : ∀ n, ((digits n : ℕ) : ℤ) = Int.floor (alpha n)
  alpha_step : ∀ n, alpha (n+1) = 1 / (alpha n - ((digits n : ℕ) : ℝ))
  beta_step : ∀ n, beta (n+1) = 1 / (((digits n : ℕ) : ℝ) + beta n)
noncomputable def orbitReciprocalInfimum (R : ReducedOrbit) : ℝ :=
  sInf (Set.range (fun n : ℤ => 1 / (R.alpha n + R.beta n)))
def latticeSize (p q : ℤ) : ℕ := p.natAbs + q.natAbs

end Freiman


