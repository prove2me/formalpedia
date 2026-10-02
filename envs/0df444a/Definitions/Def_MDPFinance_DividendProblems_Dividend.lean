-- Prove2me | Definitions.Def_MDPFinance_DividendProblems_Dividend
-- name    : MDPFinance_DividendProblems_Dividend
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:12:36.343981+00:00
-- url     : https://prove2.me/theorems/a7f4541a-826d-45dc-90e8-3c6b0e6ddf7c
-- title:
--   The discrete dividend model (§9.2)
-- statement:
--   The classical discrete-time De Finetti dividend problem: an insurer's risk reserve $x \in \mathbb Z$ evolves by i.i.d. increments $Z_n$ (premia minus claims) unless a dividend $a \in \{0,\dots,x\}$ is paid first; once the reserve goes negative the company is ruined and no further action or reward is possible ($D(x)=\{0\}$, $r(x,0)=0$ for $x<0$), so the ruin time and the vanishing of $J_\infty^\pi$ past ruin are automatic consequences of the model's own data rather than separate constructions. `q_k := \mathbb P(Z=k)$ is given via a `PMF ℤ` (Mathlib's probability-mass-function type), which supplies the summing-to-one property for free. $G(x) := \beta\sum_{k=-x}^\infty J_\infty(x+k)q_k$ is the one-step-lookahead quantity every later result in this section is built from, and `IsLargestMaximizer` pins down "$f^*$, *the* largest maximizer of $J_\infty$" (p. 274), the specific decision rule Theorem 9.2.3c) onward is about.
--
--   **Formalization Note.** `EZ`/`EZplus` are plain real `tsum`s, junk-safe (returning $0$) if not summable, matching this series' total-convention throughout; the model's own standing assumption `hEZplus` (`\mathbb E\,Z^+<\infty`) is exactly what makes `EZplus` non-junk.
--
--   **Moderation note.** The draft's `J_∞`, `G` and the maximizer notion were real-valued suprema over arbitrary maps (junk, see `StationaryMDM`); now they are `[0,∞]`-valued and over `F^∞`. The standing non-triviality assumption `ℙ(Z < 0) > 0` was a structure field, which made Corollary 9.2.4 b) (`ℙ(Z ≥ 0) = 1`) vacuous; no numbered result of §9.2 uses it, so it is now the separate predicate `IsNonTrivial`. `𝔼Z⁺ < ∞` stays in the model.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 271-274, PDF 281-284, §9.2's opening model formulation and the unnumbered display of $G$ preceding Theorem 9.2.3

import Mathlib
import Definitions.Def_MDPFinance_DividendProblems_MDM

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter

namespace MDPFinance.DividendProblems

/-- The discrete **dividend model** (Bäuerle–Rieder, §9.2, pp. 271-272, PDF 281-282): risk
reserve `x \in \mathbb Z`, dividend `a \in \mathbb N_0`, `D(x) := \{0,\dots,x\}` for `x \ge 0`
and `D(x) := \{0\}` for `x < 0` (ruin), i.i.d. reserve changes `Z_n` with law `(q_k)_{k \in
\mathbb Z}`, transition (9.3), reward `r(x,a) := a`, discount `\beta \in (0,1)`, and the standing
integrability assumption `\mathbb E Z^+ < \infty`. The book's non-triviality assumption
`\mathbb P(Z < 0) > 0` is recorded separately as `IsNonTrivial`: no numbered result of §9.2 uses
it, and Corollary 9.2.4 b) (`\mathbb P(Z \ge 0) = 1`) is incompatible with it. -/
structure DividendModel where
  Zpmf : PMF ℤ
  β : ℝ
  hβ : β ∈ Set.Ioo (0 : ℝ) 1
  hEZplus : Summable fun k : ℤ => (Zpmf k).toReal * max (k : ℝ) 0

/-- `\mathbb P(Z < 0) > 0` (Bäuerle–Rieder, p. 272). -/
def DividendModel.IsNonTrivial (M : DividendModel) : Prop :=
  0 < M.Zpmf.toMeasure {k : ℤ | k < 0}

/-- `q_k := \mathbb P(Z = k)`. -/
noncomputable def DividendModel.q (M : DividendModel) (k : ℤ) : ℝ := (M.Zpmf k).toReal

/-- `\mathbb E Z^+ := \sum_k q_k \max(k,0)` (summable by the standing assumption). -/
noncomputable def DividendModel.EZplus (M : DividendModel) : ℝ :=
  ∑' k : ℤ, M.q k * max (k : ℝ) 0

/-- `\mathbb E Z := \sum_k k\,q_k`, used only by Corollary 9.2.4 b), whose hypothesis
`\mathbb P(Z \ge 0) = 1` makes it the summable `\mathbb E Z^+`. -/
noncomputable def DividendModel.EZ (M : DividendModel) : ℝ :=
  ∑' k : ℤ, M.q k * (k : ℝ)

/-- `q^+ := \mathbb P(Z \ge 0)` (Bäuerle–Rieder, p. 274). -/
noncomputable def DividendModel.qplus (M : DividendModel) : ℝ :=
  (M.Zpmf.toMeasure {k : ℤ | 0 ≤ k}).toReal

def DividendModel.D (x : ℤ) : Set ℕ := if 0 ≤ x then {a | (a : ℤ) ≤ x} else {0}

/-- `T(x,a,z)` (Eq. (9.3)). -/
def DividendModel.Tnext (x : ℤ) (a : ℕ) (z : ℤ) : ℤ := if 0 ≤ x then x - a + z else x

/-- The stationary (positive) Markov Decision Model of §9.2 (Bäuerle–Rieder, p. 272). -/
noncomputable def DividendModel.toMDM (M : DividendModel) : StationaryMDM ℤ ℕ where
  D := {xa | xa.2 ∈ DividendModel.D xa.1}
  hD_nonempty := fun x => ⟨0, by
    show (0 : ℕ) ∈ DividendModel.D x
    unfold DividendModel.D
    split_ifs with h <;> simp [h]⟩
  step := ⟨fun xa => (M.Zpmf.map (DividendModel.Tnext xa.1 xa.2)).toMeasure,
    measurable_of_countable _⟩
  isMarkov := ⟨fun xa => PMF.toMeasure.isProbabilityMeasure _⟩
  r := fun xa => (xa.2 : ℝ≥0∞)
  β := M.β
  hβ := M.hβ.1

/-- `J_\infty` of the dividend model, in `[0,\infty]`; `J_\infty(x) = 0` for `x < 0` is automatic
from the data (`D(x) = \{0\}`, `r(x,0) = 0`, the state frozen), which is the book's ruin time
`\tau := \inf\{n \mid X_n < 0\}` at work. -/
noncomputable def DividendModel.Jinf (M : DividendModel) : ℤ → ℝ≥0∞ :=
  MDPFinance.DividendProblems.Jinf M.toMDM

/-- `G(x) := \beta \sum_{k \ge -x} J_\infty(x+k) q_k`, `x \ge 0` (Bäuerle–Rieder, p. 274). -/
noncomputable def DividendModel.G (M : DividendModel) (x : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal M.β * ∑' k : ℤ, if -x ≤ k then M.Zpmf k * M.Jinf (x + k) else 0

/-- "`f^*` is the largest maximizer of `J_\infty`" (Bäuerle–Rieder, p. 274): a maximizer of
`J_\infty` dominating every other maximizer pointwise. -/
def DividendModel.IsLargestMaximizer (M : DividendModel) (fstar : ℤ → ℕ) : Prop :=
  M.toMDM.IsMaximizerOf M.Jinf fstar ∧
    ∀ g : ℤ → ℕ, M.toMDM.IsMaximizerOf M.Jinf g → ∀ x, g x ≤ fstar x

end MDPFinance.DividendProblems


