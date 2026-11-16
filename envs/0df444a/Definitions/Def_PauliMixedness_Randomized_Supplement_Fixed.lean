-- Prove2me | Definitions.Def_PauliMixedness_Randomized_Supplement_Fixed
-- name    : PauliMixedness_Randomized_Supplement_Fixed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:55:35.551231+00:00
-- url     : https://prove2.me/theorems/07cc81dd-46bf-42de-b3e2-b44aa5a85520
-- title:
--   Fixed schedules and two-sided Pauli testing success
-- statement:
--   A fixed Pauli protocol uses the published protocol model with its schedule law equal to a point mass at a single complete schedule $s$. Its outcome-only kernel may still use decision coins. For error parameter $\delta$, write $p_\rho$ for its published acceptance probability. The two-sided success predicate is
--
--   $$p_{\rho_{\rm mm}}\ge1-\delta,\qquad 1-p_\rho\ge1-\delta\quad\text{for every density matrix }\rho\text{ with }\|\rho-\rho_{\rm mm}\|_1\ge\varepsilon.$$
--
--   The trace norm is unhalved. This interface keeps every allocation of copies to Pauli bases, without a random schedule or adaptive measurements.
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #231 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/231.pdf, §1.1 p.2; §4.1 pp.13–15; §5.3 pp.21–22

import Definitions.Def_PauliMixedness_Randomized_Protocol

noncomputable section

namespace PauliMixedness.Randomized.Supplement

/-- A single schedule chosen before measuring any input copy; decision coins
are still allowed by the published outcome-only acceptance kernel. -/
def IsFixed {N n : ℕ} (A : PauliProtocol N n) : Prop :=
  ∃ s : Schedule N n, A.scheduleLaw = PMF.pure s

/-- §1.1 p.2: confidence 1-δ on both hypotheses, unhalved trace distance. -/
def PauliSucceeds {N n : ℕ} (A : PauliProtocol N n) (ε δ : ℝ) : Prop :=
  1 - δ ≤ acceptProbability A (maximallyMixed N) ∧
    ∀ ρ : Operator N, QAlgorithms.IsDensityMatrix ρ →
      ε ≤ QAlgorithms.traceNorm (ρ - maximallyMixed N) →
        1 - δ ≤ 1 - acceptProbability A ρ

end PauliMixedness.Randomized.Supplement


