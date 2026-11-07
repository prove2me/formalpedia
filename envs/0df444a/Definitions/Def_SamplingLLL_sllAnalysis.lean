-- Prove2me | Definitions.Def_SamplingLLL_sllAnalysis
-- name    : SamplingLLL_sllAnalysis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:58:36.5402+00:00
-- url     : https://prove2.me/theorems/d2aabd0c-ba72-4277-9b74-f8611a0640a3
-- title:
--   Search nodes, (A2), (A3) and $\bar a_t=u_t$ of Appendix G
-- statement:
--   The quantities used to verify the hypotheses of Theorem 5.1 in Appendix G: the nodes $(Y,N)$ of the search; the proposal probability
--   $$
--   q_c(t)=\prod_{b\in Y\setminus\{c\}}\frac{x_b}{2}\prod_{d\in N\cup F_1}\Big(1-\frac{x_d}{2}\Big);
--   $$
--   the domination mass $\bar a_t=u_t=\lambda(\bigcap_{b\in Y}\mathrm{Bad}_b)$; and
--   $$
--   B_a=\frac{x_a}4,\quad\sigma_a=1-B_a,\quad\theta_a=\frac{1-x_a}{(1-x_a/4)(1-x_a/2)},\quad h_a=1-\theta_a.
--   $$
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Appendix G, eqs. (A2), (A3), p.67

import Mathlib
import Definitions.Def_SamplingLLL_sllData
import Definitions.Def_SamplingLLL_ExecAnalysis

set_option autoImplicit false

namespace SamplingLLL

variable {n m : ℕ}

namespace AtomicCSP

variable (I : AtomicCSP n m) (G : Finset (Fin m)) (x : Fin m → ℚ)

/-- The nodes `(Y, N)` of the search of Appendix G for the task `(S, c)` ("at every stage", p.66). -/
inductive SearchNode (S : Finset (Fin m)) (c : Fin m) : Leaf m → Prop
  | root : SearchNode S c ({c}, ∅)
  | yes {t : Leaf m} {b : Fin m} : SearchNode S c t → I.nextQ G S c t.1 t.2 = some b →
      SearchNode S c (insert b t.1, t.2)
  | no {t : Leaf m} {b : Fin m} : SearchNode S c t → I.nextQ G S c t.1 t.2 = some b →
      SearchNode S c (t.1, insert b t.2)

/-- `q_c(t) = ∏_{b∈Y∖{c}} (x_b/2) ∏_{d∈N∪F1} (1 - x_d/2)`, (A3), p.67. -/
def qFormula (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : ℚ :=
  (∏ b ∈ t.1.erase c, x b / 2) * ∏ d ∈ t.2 ∪ I.F1 S c t, (1 - x d / 2)

/-- `ā_t = u_t = λ(⋂_{b∈Y} Bad_b)`, p.67, the domination mass of Appendix G. -/
def ubar (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : ℝ :=
  let _ := S; let _ := c; ((I.jointBad t.1 : ℚ) : ℝ)

/-- `σ_a = 1 - x_a/4`, (A2), p.67. -/
noncomputable def sigmaA (a : Fin m) : ℝ := 1 - (x a : ℝ) / 4

/-- `θ_a = (1 - x_a) / ((1 - x_a/4)(1 - x_a/2))`, (A2), p.67. -/
noncomputable def thetaA (a : Fin m) : ℝ :=
  (1 - (x a : ℝ)) / ((1 - (x a : ℝ) / 4) * (1 - (x a : ℝ) / 2))

/-- `h_a = 1 - θ_a`, (A2), p.67. -/
noncomputable def hA (a : Fin m) : ℝ := 1 - thetaA x a

/-- The potential of a task: `h_a` for a task whose inserted event is `a`, p.68. -/
noncomputable def hTask (i : Finset (Fin m) × Fin m) : ℝ := hA x i.2

/-- The elements `D_t` as a finite set, p.67. -/
def Dset (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : Finset (Fin m) :=
  t.1.erase c ∪ t.2 ∪ I.F1 S c t

end AtomicCSP

end SamplingLLL


