-- Prove2me | Definitions.Def_BinarySketchTruncation_Opposite_Experiments
-- name    : BinarySketchTruncation_Opposite_Experiments
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:04.606117+00:00
-- url     : https://prove2.me/theorems/741ca31b-a932-410c-80ed-495f453432fd
-- title:
--   Finite experiments and exact rectangular Blackwell simulation
-- statement:
--   A finite experiment on an alphabet $S$ consists of two probability distributions $P_0,P_1$. For experiments $P$ on $S$ and $Q$ on $T$, a real matrix $K(t\mid s)$ is row-stochastic when every entry is nonnegative and every row sums to one. It simulates $Q$ from $P$ when
--
--   $$
--   Q_h(t)=\sum_{s\in S}P_h(s)K(t\mid s)\qquad(h=0,1).
--   $$
--
--   Blackwell dominance $P\succeq Q$ means that one such matrix exists, simultaneously for both hypotheses. The definition places the kernel existential before the hypothesis quantifier. Every row is normalized, including rows at inputs of zero probability.
--
--   For experiments $P,Q$ on an additive alphabet, the independent-sum experiment draws independently from $P_h$ and $Q_h$ under each $h$ and returns the sum. The deterministic-shift experiment adds zero under $h=0$ and a specified value $v$ under $h=1$.
--
--   These definitions are the common interface for all five results. The independent-sum operation imposes no equality between the two conditional laws of the added variable.
--
--   **Formalization Note** Laws are Mathlib PMFs. Real-valued kernel equations use their finite real masses. No bound or regularity condition is added to any distribution.
-- source:
--   Robinson D.H. Cung, Adway Girish, Emre Telatar, STOC 2027 submission #341 (October 2026), p. 5, Definition 4 and Eq. (1) (PDF p. 6); p. 7, Lemma 1 (PDF p. 8)

import Mathlib

namespace BinarySketchTruncation.Opposite

/-- Finite experiments, indexed by the two hypotheses false = 0 and true = 1.
Cung–Girish–Telatar, §2, Definition 4, printed p. 5 (PDF 6). -/
abbrev Experiment (S : Type) := Bool → PMF S

/-- Rectangular stochastic kernels: all rows, including null-probability inputs,
are nonnegative and normalized. No relation between the two alphabets is required. -/
def RowStochastic {S T : Type} [Fintype T] (K : S → T → ℝ) : Prop :=
  (∀ s t, 0 ≤ K s t) ∧ (∀ s, ∑ t, K s t = 1)

/-- The same kernel realizes equation (1) simultaneously for both hypotheses. -/
def Simulates {S T : Type} [Fintype S] [Fintype T]
    (P : Experiment S) (Q : Experiment T) (K : S → T → ℝ) : Prop :=
  RowStochastic K ∧ ∀ h t, (Q h t).toReal = ∑ s, (P h s).toReal * K s t

/-- Definition 4: exact Blackwell dominance, not a single testing-error bound. -/
def Dominates {S T : Type} [Fintype S] [Fintype T]
    (P : Experiment S) (Q : Experiment T) : Prop :=
  ∃ K : S → T → ℝ, Simulates P Q K

/-- Independent addition, conditional on each hypothesis. The second law
may depend on the hypothesis, as in Lemma 1 and Proposition 2. -/
noncomputable def independentSum {S : Type} [Add S]
    (P Q : Experiment S) : Experiment S :=
  fun h => (P h).bind (fun u => (Q h).map (fun v => u + v))

/-- Add zero under hypothesis 0 and the prescribed deterministic value under 1. -/
noncomputable def shiftUnderOne {S : Type} [AddZeroClass S]
    (P : Experiment S) (v : S) : Experiment S :=
  fun h => (P h).map (fun u => u + if h then v else 0)

end BinarySketchTruncation.Opposite


