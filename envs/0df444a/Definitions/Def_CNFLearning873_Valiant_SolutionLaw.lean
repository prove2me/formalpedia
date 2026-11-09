-- Prove2me | Definitions.Def_CNFLearning873_Valiant_SolutionLaw
-- name    : CNFLearning873_Valiant_SolutionLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T05:04:12.693298+00:00
-- url     : https://prove2.me/theorems/3a097938-9d2c-466b-9dd9-f13a9999adb4
-- title:
--   Uniform solution law and clause violation probability
-- statement:
--   For a finite CNF $F$ with a nonempty solution set, use the published uniform law on $\Omega(F)$. For an event $E$ and a clause $c$, define
--
--   $$\Pr_{\mu_F}(E)=\sum_x\mu_F(x)\mathbf1_E(x),\qquad q_c=\Pr_{\mu_F}(X\text{ violates }c).$$
--
--   The law requires an explicit proof of nonemptiness. The theorems establish this nonemptiness rather than assuming a satisfactory target. General finite total variation and independent product laws are reused from published definitions.
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf, §3, pp.11–12 (PDF pp.11–12)

import Definitions.Def_CNFLearning873_Valiant_CNF
import Definitions.Def_RandomQueryXOR_uniformOn
import Definitions.Def_HybridXorLift_tvDist

namespace CNFLearning873.Valiant

open scoped BigOperators

/-- Only nonempty solution sets have a probability law. -/
noncomputable def solutionLaw {n : ℕ} (F : CNF n) (h : (solutions F).Nonempty) :=
  RandomQueryXOR.uniformOn (solutions F) h

noncomputable def eventProb {α : Type} [Fintype α]
    (p : WildeQIT.FinDist α) (E : α → Prop) : ℝ := by
  classical
  exact ∑ x, if E x then p.prob x else 0

noncomputable def q {n : ℕ} (F : CNF n) (h : (solutions F).Nonempty)
    (c : Clause n) : ℝ := eventProb (solutionLaw F h) (Violates c)

end CNFLearning873.Valiant


