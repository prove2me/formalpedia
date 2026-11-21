-- Prove2me | Definitions.Def_MoranYanPAC_Learner
-- name    : MoranYanPAC_Learner
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-20T15:31:47.248624+00:00
-- url     : https://prove2.me/theorems/a819a1f8-0da9-407e-b2ef-d4a62ca38d63
-- title:
--   The learner of Theorem 1 (structural exponential mechanism on the candidate set of Algorithm 3)
-- statement:
--   The learner of Section 7.4 of the paper, as a function of the class $H$, the dimension parameter $d$, a witness assignment $A_w$ and the privacy parameters $\varepsilon,\delta$.
--
--   - `candidateOut H d Aw S` is the candidate set $C(S)$ of Algorithm 3 (the published `MoranYanPAC.Main.candidates`) as a finite set, when $C(S)$ is finite and nonempty; otherwise it is the single constant predictor `false`. Under the standing hypotheses of Theorem 1 (with a witness assignment as in Lemma 6), $C(S)$ is always finite and nonempty (Lemmas 10 and 11), so the fallback is never used there.
--   - `candidateData H d Aw` is the structural data of Section 7.3: outputs $\mathrm{Out}(S) = C(S)$, score $q_S(h) = |S| - \ell_S(h)$ (the number of records of $S$ that $h$ labels correctly) and rank $\rho(h)$ (`PrivLittlestone.rankOf`).
--   - `littlestoneLearner H d Aw ε δ` is Algorithm 1 (`MoranYanPAC.Main.structuralMechanism`) on these data with $\Delta = 1$ and $B = 4(d+1)$: on input $S$ it outputs $h \in \mathrm{Out}(S)$ with probability proportional to $\exp\big(\tfrac{\varepsilon}{2}(q_S(h) + \beta\,\rho(h))\big)$, where $\beta = 1 + \tfrac{2}{\varepsilon}\log(32(d+1)/\delta)$.
--
--   The candidate set does not look at the observed labels; the labels enter only through the score.
-- source:
--   Nearly Linear Private Learning of Littlestone Classes, STOC 2027 submission 772, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/772.pdf, pp. 22–25, the learner of Theorem 1 (Algorithm 3, Section 7.3 and Section 7.4)

import Mathlib
import Definitions.Def_MoranYanPAC_Main_Candidates
import Definitions.Def_MoranYanPAC_Main_StructuralMechanism
import Definitions.Def_MoranYanPAC_Main_EmpiricalLoss

set_option autoImplicit false

namespace MoranYanPAC.Learner

open MoranYanPAC.Main

open Classical in
/-- Section 7.3, p. 24: `Out(S) = C(S)`, the candidate set of Algorithm 3 as a finite set when it is
finite and nonempty; otherwise the single constant predictor `false`. -/
noncomputable def candidateOut {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (Aw : (X → Bool) → Finset X) (S : List (X × Bool)) : Finset (X → Bool) :=
  if h : (candidates H d Aw S).Finite ∧ (candidates H d Aw S).Nonempty then h.1.toFinset
  else {fun _ => false}

theorem candidateOut_nonempty {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (Aw : (X → Bool) → Finset X) (S : List (X × Bool)) : (candidateOut H d Aw S).Nonempty := by
  classical
  unfold candidateOut
  split_ifs with h
  · exact h.1.toFinset_nonempty.mpr h.2
  · exact Finset.singleton_nonempty _

/-- Section 7.3, p. 24: the structural data of the learner, with score `q_S(h) = |S| − ℓ_S(h)`
and the structural rank `ρ`. -/
noncomputable def candidateData {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (Aw : (X → Bool) → Finset X) : StructuralData (X × Bool) (X → Bool) where
  out := candidateOut H d Aw
  nonempty := candidateOut_nonempty H d Aw
  rank := PrivLittlestone.rankOf H d
  score S h := (S.length : ℝ) - (empiricalLoss S h : ℝ)

/-- Section 7.4, p. 25: the learner of Theorem 1, Algorithm 1 run on the candidate set of
Algorithm 3 with `Δ = 1` and `B = 4(d + 1)`. -/
noncomputable def littlestoneLearner {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (Aw : (X → Bool) → Finset X) (ε δ : ℝ) : List (X × Bool) → PMF (X → Bool) :=
  structuralMechanism (candidateData H d Aw) ε δ 1 (4 * ((d : ℝ) + 1))

end MoranYanPAC.Learner


