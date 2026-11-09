-- Prove2me | Definitions.Def_ExactLearningSeparation678_Randomized_Experiments
-- name    : ExactLearningSeparation678_Randomized_Experiments
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:35.609781+00:00
-- url     : https://prove2.me/theorems/50ba5601-a58b-49bb-99aa-3fa520d89634
-- title:
--   The hard distribution, three hybrid laws, and event (12)
-- statement:
--   Sample the slope $s$ and all lower coefficients of the monic polynomial independently and uniformly from $F=\mathbb F_{t^6}$; their concept induces the hard input distribution $\mu$. A fixed deterministic learner returns a concept in $C_t$, as normalized in the section preamble. Its real success is the probability that its output equals the target function.
--
--   The three experiments compute joint laws of $(s,T)$, where $T$ includes queries, answers and final output. In H1 the polynomial block answers are unchanged and all sheet answers are zero. In H2 sample $s$ and an independent uniform function $g:F\to\mathbb F_2^{2m}$, answer a block by $\mathbf1[g(c+xs)=z]$, and answer sheets by zero. In H3 sample $s$ and an independent uniform label $U_{x,c}$ for each block, answer by $\mathbf1[U_{x,c}=z]$, and answer sheets by zero. Labels are sampled once and reused on repetitions.
--
--   The common event is
--   $$A=\{\text{a queried sheet has address }s\}\cup\{\widehat s(T)=s\}.$$
--   Here $\widehat s$ is the slope selected from the output concept's parameter preimage; Fact 3.4 establishes uniqueness. No recognition of the active sheet is required. Define
--   $$\varepsilon_D=\binom Dt(2/t^2)^t,\qquad \eta_D=\binom D2/t^6.$$
--
--   These are concrete finite probability laws and event predicates, used by the hybrid milestones. The learner is fixed before sampling, and has no direct access to the parameters.
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), §3.4, pp.21–27; Eq. (12), p.23; Lemmas 3.10–3.11, pp.25–26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Construction
import Definitions.Def_ExactLearningSeparation678_Randomized_Observations

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized

abbrev Learner (m : Size) := QAlgorithms.DecisionTree (Domain m) Bool (Concept m)
abbrev LearningTranscript (m : Size) (D : ℕ) := Transcript (Domain m) (Concept m) D

/-- H1 keeps the same polynomial block and answers every sheet by zero. -/
noncomputable def oracleH1 (m : Size) (p : Parameters m) : Domain m → Bool
  | .inl (x, c, z) => decide (z = pTrunc m p.1 (c + x * p.2))
  | .inr _ => false

/-- H2 samples one random function g, reused throughout. -/
noncomputable def oracleH2 (m : Size) (s : F m) (g : F m → Label m) : Domain m → Bool
  | .inl (x, c, z) => decide (g (c + x * s) = z)
  | .inr _ => false

/-- H3 samples one independent label per block, reused on repeated queries. -/
noncomputable def oracleH3 (m : Size) (u : (F m × F m) → Label m) : Domain m → Bool
  | .inl (x, c, z) => decide (u (x, c) = z)
  | .inr _ => false

/-- The uniform coefficient/slope product is exactly the paper's hard distribution μ. -/
noncomputable def hardDistribution (m : Size) : PMF (Domain m → Bool) :=
  (PMF.uniformOfFintype (Parameters m)).map (concept m)

noncomputable def realSuccess (m : Size) (D : ℕ) (A : Learner m) : ℝ :=
  probability (PMF.uniformOfFintype (Parameters m))
    (fun p => (record D A (concept m p)).2.val = concept m p)

noncomputable def lawH1 (m : Size) (D : ℕ) (A : Learner m) :
    PMF (F m × LearningTranscript m D) :=
  (PMF.uniformOfFintype (Parameters m)).map
    (fun p => (p.2, record D A (oracleH1 m p)))

noncomputable def lawH2 (m : Size) (D : ℕ) (A : Learner m) :
    PMF (F m × LearningTranscript m D) :=
  (PMF.uniformOfFintype (F m × (F m → Label m))).map
    (fun p => (p.1, record D A (oracleH2 m p.1 p.2)))

noncomputable def lawH3 (m : Size) (D : ℕ) (A : Learner m) :
    PMF (F m × LearningTranscript m D) :=
  (PMF.uniformOfFintype (F m × ((F m × F m) → Label m))).map
    (fun p => (p.1, record D A (oracleH3 m p.2)))

/-- Equation (12): querying the sheet address suffices, regardless of its answer. -/
noncomputable def eventA (m : Size) (D : ℕ) (w : F m × LearningTranscript m D) : Prop :=
  (∃ (i : Fin D) (j : Fin (t m)) (b : F m) (answer : Bool),
    w.2.1 i = some (Sum.inr (w.1, j, b), answer)) ∨
  (outputParameters m w.2.2).2 = w.1

noncomputable def epsilon (m : Size) (D : ℕ) : ℝ :=
  (D.choose (t m) : ℝ) * (2 / (t m : ℝ) ^ 2) ^ t m

noncomputable def collisionError (m : Size) (D : ℕ) : ℝ :=
  (D.choose 2 : ℝ) / (t m : ℝ) ^ 6

end ExactLearningSeparation678.Randomized


