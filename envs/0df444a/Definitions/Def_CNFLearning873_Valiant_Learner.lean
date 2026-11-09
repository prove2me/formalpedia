-- Prove2me | Definitions.Def_CNFLearning873_Valiant_Learner
-- name    : CNFLearning873_Valiant_Learner
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T05:08:06.659827+00:00
-- url     : https://prove2.me/theorems/ee380a76-417e-491f-82e3-b29d40a0450b
-- title:
--   Valiant survivor rule and its independent sample law
-- statement:
--   Given only $n,k$ and ordered samples $x_1,\ldots,x_N$, Valiant's learner retains precisely the width-$k$ candidates satisfied by every sample:
--
--   $$\widehat C=\{c\in C^*: \forall i,\ x_i\text{ satisfies }c\}.$$
--
--   The sample law is the published product $\mu_F^{\otimes N}$, including the empty product. Success means the output has a nonempty solution set and its uniform solution law is within total variation $\varepsilon$ of $\mu_F$. The target formula enters the probability law and success comparison, and never enters the learner input.
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf, Valiant’s algorithm, p.2; Problem 1.3, p.3; proof of Theorem 4.1, p.14 (PDF pp.2–3,14)

import Definitions.Def_CNFLearning873_Valiant_Thresholds

namespace CNFLearning873.Valiant

/-- The p.2 survivor semantics, depending only on n,k and the observed samples. -/
noncomputable def output {n N : ℕ} (k : ℕ) (xs : Fin N → Assignment n) : CNF n := by
  classical
  exact (candidates n k).filter fun c => ∀ i, Sat (xs i) c

noncomputable def sampleLaw {n : ℕ} (F : CNF n) (h : (solutions F).Nonempty) (N : ℕ) :=
  RandomQueryXOR.piDist (fun _ : Fin N => solutionLaw F h)

/-- Success includes output satisfiability, so TV is never taken against an empty law. -/
def Success {n N : ℕ} (F : CNF n) (h : (solutions F).Nonempty)
    (k : ℕ) (ε : ℝ) (xs : Fin N → Assignment n) : Prop :=
  ∃ hout : (solutions (output k xs)).Nonempty,
    HybridXorLift.tvDist (solutionLaw F h).prob (solutionLaw (output k xs) hout).prob ≤ ε

end CNFLearning873.Valiant


