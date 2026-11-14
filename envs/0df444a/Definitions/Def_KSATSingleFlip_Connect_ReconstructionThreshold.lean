-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_ReconstructionThreshold
-- name    : KSATSingleFlip_Connect_ReconstructionThreshold
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T07:12:06.105207+00:00
-- url     : https://prove2.me/theorems/4a6042fc-0a62-4b2e-910c-86e9b91d8e73
-- title:
--   Random k-SAT reconstruction rate and first onset
-- statement:
--   With $k$ and $\alpha$ fixed, let $R_k(\alpha)$ be the limit as $r\to\infty$ of the fixed-radius limit superior of the expected reconstruction signal. Define satisfiability with high probability by convergence of the satisfiability probability to one as $n\to\infty$, and define the first reconstruction onset as the infimum of nonnegative, satisfiable-with-high-probability densities at which $R_k(\alpha)>0$. No monotonicity in density is assumed. The Lean limit is specified using the limit operator; a theorem using it must establish convergence of the underlying profile.
-- source:
--   Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, paragraph preceding Theorem 1.2, printed p. 3 (PDF p. 5), STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_Reconstruction

noncomputable section
open scoped Classical BigOperators
open Filter Topology
namespace KSATSingleFlip.Connect
open OAI.FixedClauseThreshold

/-- The outer r→∞ limit in the source definition of reconstruction. -/
def reconstructionRate (k : ℕ) (α : ℝ) : ℝ :=
  atTop.limUnder (reconstructionProfile k α)

/-- Satisfiability with high probability in the fixed-k, fixed-density limit. -/
def satisfiableWhp (k : ℕ) (α : ℝ) : Prop :=
  Tendsto (fun n => formulaProb n k ⌊α * n⌋₊ (fun F => FSatPossible (ofFormula F)))
    atTop (𝓝 1)
where
  FSatPossible {n : ℕ} (Φ : GFormula (Fin n)) : Prop := ∃ x, FSat x Φ

/-- First reconstruction onset among nonnegative densities at which the formula
is satisfiable with high probability; no monotonicity in density is assumed. -/
def reconstructionThreshold (k : ℕ) : ℝ :=
  sInf {α : ℝ | 0 ≤ α ∧ satisfiableWhp k α ∧ 0 < reconstructionRate k α}

end KSATSingleFlip.Connect


