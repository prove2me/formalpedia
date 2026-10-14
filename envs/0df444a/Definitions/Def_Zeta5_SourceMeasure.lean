-- Prove2me | Definitions.Def_Zeta5_SourceMeasure
-- name    : Zeta5_SourceMeasure
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-11T23:33:55.877027+00:00
-- url     : https://prove2.me/theorems/239224bf-b452-429d-b421-5f6a7b952711
-- title:
--   Zeta5: comparison measure constants and the energy $I(\rho)$
-- statement:
--   This module fixes the constants of Section 6 and Appendix A of the source: the slopes $\lambda = 37/40$ and $\alpha = 3/40$, the constant $C^*$ of (6.3),
--
--   $$C^* = -2\lambda + 12\alpha\lambda\,(1-\log\alpha) + 3\lambda^2 - 2\lambda^2\log(2\lambda),$$
--
--   $M_0 = -1329/200$ of (6.2), Table 1 (the sixteen triples of $10^{12}$-scaled arcsine endpoints), the functions $a_j$, $b_j$, $c_j$ reading the $j$-th table row, the partial sums $S_j = \sum_{i \le j} c_i$, and the logarithmic energy
--
--   $$I(\rho) = \sum_{j=1}^{16} \bigl(S_j^2 - S_{j-1}^2\bigr)\log\frac{b_j - a_j}{4}$$
--
--   by formula (A.2), where $\rho$ is the comparison measure of Appendix A. The table entries are stored as naturals scaled by $10^{12}$ and divided by $10^{12}$ on reading, so that $a_j, b_j, c_j$ are the exact rational values displayed in the source. Outside the sixteen rows the functions are total and read the default triple $(0,0,0)$, as in the source. These are exactly the objects in which the numerical inequalities of Section 6 are stated.
--
--   **Formalization Note** The declarations are `noncomputable abbrev`/`def` in the `Apery` namespace and use `List.getD` with a default of `(0,0,0)` for the total extension, matching the source module verbatim.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Measure.lean#L10-L57

import Mathlib

/-!
# The comparison measure of Appendix A and the constants of Section 6

`λ`, `α`, `C*` (6.3), `M₀` (6.2), Table 1 (the sixteen arcsine components of `ρ`), the partial
sums `S_j`, and the energy `I(ρ)` by formula (A.2).

Source: mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, `Apery/Measure.lean`,
lines 10–57.
-/

open Finset

namespace Apery

/-- `λ = 37/40`. -/
noncomputable abbrev lam : ℝ := 37 / 40
/-- `α = 3/40`. -/
noncomputable abbrev alph : ℝ := 3 / 40

/-- The constant `C*` of (6.3). -/
noncomputable def Cstar : ℝ :=
  -2 * lam + 12 * alph * lam * (1 - Real.log alph) + 3 * lam ^ 2 - 2 * lam ^ 2 * Real.log (2 * lam)

/-- `M₀ = -1329/200` of (6.2). -/
noncomputable abbrev M0 : ℝ := -1329 / 200

/-- Table 1: `10¹² a_j`, `10¹² b_j`, `10¹² c_j`. -/
def table1 : List (ℕ × ℕ × ℕ) :=
  [(3906748086, 8992695531, 10515596180),
   (2312248264, 15340997855, 29471737793),
   (1402286665, 25730180724, 42934365099),
   (881725356, 41909578246, 58204231966),
   (578197906, 65851089563, 69037621310),
   (396324613, 99481037884, 78873099189),
   (283911191, 144325727458, 84856120711),
   (212206188, 201105762729, 88396082127),
   (165097686, 269345996903, 88303382125),
   (133347132, 347089554156, 85472321255),
   (111522114, 430806704415, 78899184238),
   (96349355, 515561896511, 70353471918),
   (85815639, 595448778546, 58838976615),
   (78667711, 664241383483, 44421321106),
   (74129565, 716160577112, 30462865791),
   (71741310, 746637295669, 5959622577)]

/-- `a_j`, `b_j`, `c_j` (1-indexed; `0` outside the table). -/
noncomputable def aρ (j : ℕ) : ℝ := ((table1.getD (j - 1) (0, 0, 0)).1 : ℝ) / 10 ^ 12
noncomputable def bρ (j : ℕ) : ℝ := ((table1.getD (j - 1) (0, 0, 0)).2.1 : ℝ) / 10 ^ 12
noncomputable def cρ (j : ℕ) : ℝ := ((table1.getD (j - 1) (0, 0, 0)).2.2 : ℝ) / 10 ^ 12

/-- Partial sums `S_j = ∑_{i ≤ j} c_i`. -/
noncomputable def Sρ (j : ℕ) : ℝ := ∑ i ∈ Icc 1 j, cρ i

/-- The logarithmic energy `I(ρ)` of the measure `ρ`, formula (A.2). -/
noncomputable def Irho : ℝ :=
  ∑ j ∈ Icc 1 16, (Sρ j ^ 2 - Sρ (j - 1) ^ 2) * Real.log ((bρ j - aρ j) / 4)

end Apery


