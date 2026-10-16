-- Prove2me | Definitions.Def_HumanMachine_Alone_model
-- name    : HumanMachine_Alone_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T19:28:34.083362+00:00
-- url     : https://prove2.me/theorems/f5146a2e-6ae7-4b52-9987-05fb2ef131c3
-- title:
--   Binary rational-inattention decision model and Theorem 1 expressions
-- statement:
--   A decision maker faces a good state with prior probability $\mu$ and a bad state with probability $1-\mu$. Write $p_g$ and $p_b$ for the conditional probabilities of choosing the good-state action in the two states. A feasible strategy is any pair $(p_g,p_b)\in[0,1]^2$. Its unconditional choice probability $p$, accuracy $A$, entropy cost $C$, and net value $V$ are
--
--   $$
--   p=\mu p_g+(1-\mu)p_b,\quad A=\mu p_g+(1-\mu)(1-p_b),\quad C=\lambda[H(p)-(1-\mu)H(p_b)-\mu H(p_g)],\quad V=A-C.
--   $$
--
--   Here $H$ is binary entropy with natural logarithms. A pair is optimal if it is feasible and its value is at least that of every feasible pair. The lower and upper prior thresholds are $\underline\mu=1/(e^{1/\lambda}+1)$ and $\overline\mu=e^{1/\lambda}/(e^{1/\lambda}+1)$. The algebraic interior candidate is $\bar p=\mu/(1-e^{-1/\lambda})-(1-\mu)/(e^{1/\lambda}-1)$; the piecewise expression $p_{\mathrm{closed}}$ equals zero when $\mu\le\underline\mu$, $\bar p$ when $\underline\mu<\mu<\overline\mu$, and one when $\mu\ge\overline\mu$, exactly as in display (11).
--
--   These definitions specify the decision problem and the expressions appearing in Theorem 1. The closed-form expression is a comparison target, not the definition of an optimum.
--
--   **Formalization Note** This is the paper's §4 choice-probability reduction of its general-signal problem (2), adopted from Matějka and McKay (2015). The general-signal equivalence is not formalized here. All real inputs make these functions total in Lean; theorem hypotheses establish the source domain.
-- source:
--   Boyacı, Canyakmaz & de Véricourt, Human and Machine: The Impact of Machine Input on Decision-Making Under Cognitive Limitations, ESMT Working Paper 20-02 (Nov. 30, 2020), pp. 7–12 (PDF pp. 8–13), equations (1), (2), (4), (7), (8), (11); Appendix A p. 32 (PDF p. 33).

import Mathlib

noncomputable section

namespace HumanMachine.Alone

/-- The unconditional probability of choosing `y`; equation (4). -/
def choiceProb (mu pg pb : ℝ) : ℝ := mu * pg + (1 - mu) * pb

/-- The probability of making the correct choice; equation (7). -/
def accuracy (mu pg pb : ℝ) : ℝ := mu * pg + (1 - mu) * (1 - pb)

/-- Entropy-based cognitive cost in the choice-probability representation; equation (8). -/
def cost (lam mu pg pb : ℝ) : ℝ :=
  lam * (Real.binEntropy (choiceProb mu pg pb) -
    (1 - mu) * Real.binEntropy pb - mu * Real.binEntropy pg)

/-- Expected accuracy net of cognitive cost, corresponding to problem (2). -/
def value (lam mu pg pb : ℝ) : ℝ := accuracy mu pg pb - cost lam mu pg pb

/-- An optimal pair of conditional choice probabilities in the paper's §4 reduction. -/
def IsOptimal (lam mu pg pb : ℝ) : Prop :=
  pg ∈ Set.Icc (0 : ℝ) 1 ∧ pb ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ qg ∈ Set.Icc (0 : ℝ) 1, ∀ qb ∈ Set.Icc (0 : ℝ) 1,
      value lam mu qg qb ≤ value lam mu pg pb

/-- The lower prior threshold in Theorem 1. -/
def muLow (lam : ℝ) : ℝ := 1 / (Real.exp (1 / lam) + 1)

/-- The upper prior threshold in Theorem 1. -/
def muHigh (lam : ℝ) : ℝ := Real.exp (1 / lam) / (Real.exp (1 / lam) + 1)

/-- The algebraic interior candidate from the proof of Theorem 1, p. 32. -/
def pBar (lam mu : ℝ) : ℝ :=
  mu / (1 - Real.exp (-(1 / lam))) - (1 - mu) / (Real.exp (1 / lam) - 1)

/-- The right-hand side of equation (11), not a definition of the optimal probability. -/
def pClosed (lam mu : ℝ) : ℝ :=
  if mu ≤ muLow lam then 0 else if mu < muHigh lam then pBar lam mu else 1

end HumanMachine.Alone


