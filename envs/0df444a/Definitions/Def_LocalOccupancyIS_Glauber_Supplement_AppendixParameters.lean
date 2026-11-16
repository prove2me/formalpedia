-- Prove2me | Definitions.Def_LocalOccupancyIS_Glauber_Supplement_AppendixParameters
-- name    : LocalOccupancyIS_Glauber_Supplement_AppendixParameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:59:46.473884+00:00
-- url     : https://prove2.me/theorems/f8117f71-1cc7-4699-a1b4-8779342c6bc3
-- title:
--   Appendix A parameters, admissible families and finite tails
-- statement:
--   For $\Delta\ge3$, integer $t\ge1$ and $b\ge0$, reuse $s=(b+1)^{1/(2t-1)}$, and define
--
--   $$L=\log\Delta,\quad H=\log\frac{\Delta}{sL^t},\quad \lambda_A=\frac1{sL^{t-1}H^{2t}},\quad M_A=\frac{4eL}{\lambda_A},\quad c_A=\exp\!\left(-\frac{4t(4e)^{1-1/t}}{H^2}\right).$$
--
--   Set $q=1-1/H$, $z_0=H-(2t+3)\log H$, $\epsilon_A=\sqrt{8\log H/H}$, $a_A=\lfloor(1-\epsilon_A)c_Az_0\rfloor$, $\beta_A=e^{z_0}/p$ and $\gamma_A=1/(qa_A)$, where $p=\lambda_A/(1+\lambda_A)$. The integer floor retains negative startup values; its eventual positivity is a theorem. The relative error is $E_A=\sqrt{\log H/H}+t\log H/H$.
--
--   Admissible sequences have precisely the parameter signs, $H_i\to\infty$ and $t_i\log H_i/H_i\to0$. This predicate includes no graph property or desired conclusion. The tail functions are finite sums of the normalized hard-core law for the events $|I|\le r$ and $|I|\ge a$. No independence of occupation indicators is imposed.
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), pp.23–24, equations (29)–(31), Lemma 14, Proposition 15

import Definitions.Def_LocalOccupancyIS_Glauber_Supplement_MadParameters

open scoped BigOperators

namespace LocalOccupancyIS.Glauber.Supplement
noncomputable section

def appL (Δ : ℝ) : ℝ := Real.log Δ
def appH (Δ : ℝ) (t : ℕ) (b : ℝ) : ℝ := Real.log (Δ / (scale t b * appL Δ ^ t))
def appLam (Δ : ℝ) (t : ℕ) (b : ℝ) : ℝ :=
  1 / (scale t b * appL Δ ^ (t-1) * appH Δ t b ^ (2*t))
def appM (Δ : ℝ) (t : ℕ) (b : ℝ) : ℝ := 4 * Real.exp 1 * appL Δ / appLam Δ t b
def appC (Δ : ℝ) (t : ℕ) (b : ℝ) : ℝ :=
  Real.exp (-(4 * (t : ℝ) * (4 * Real.exp 1)^(1 - 1/(t : ℝ)) / appH Δ t b ^ 2))
def appQ (Δ : ℝ) (t : ℕ) (b : ℝ) : ℝ := 1 - 1 / appH Δ t b
def appZ (Δ : ℝ) (t : ℕ) (b : ℝ) : ℝ :=
  appH Δ t b - (2*(t : ℝ)+3) * Real.log (appH Δ t b)
def appEps (Δ : ℝ) (t : ℕ) (b : ℝ) : ℝ :=
  Real.sqrt (8 * Real.log (appH Δ t b) / appH Δ t b)
/-- Integer floor, without truncating negative startup values. -/
def appA (Δ : ℝ) (t : ℕ) (b : ℝ) : ℤ :=
  ⌊(1 - appEps Δ t b) * appC Δ t b * appZ Δ t b⌋
def appBeta (Δ : ℝ) (t : ℕ) (b : ℝ) : ℝ :=
  Real.exp (appZ Δ t b) / p (appLam Δ t b)
def appGamma (Δ : ℝ) (t : ℕ) (b : ℝ) : ℝ :=
  1 / (appQ Δ t b * (appA Δ t b : ℝ))
def appError (Δ : ℝ) (t : ℕ) (b : ℝ) : ℝ :=
  Real.sqrt (Real.log (appH Δ t b) / appH Δ t b) +
    t * Real.log (appH Δ t b) / appH Δ t b

/-- No graph or successful conclusion in this input predicate. -/
def AppAdmissible (Δ : ℕ → ℝ) (t : ℕ → ℕ) (b : ℕ → ℝ) : Prop :=
  (∀ i, 3 ≤ Δ i ∧ 1 ≤ t i ∧ 0 ≤ b i) ∧
  Filter.Tendsto (fun i => appH (Δ i) (t i) (b i)) Filter.atTop Filter.atTop ∧
  Filter.Tendsto (fun i => (t i : ℝ) * Real.log (appH (Δ i) (t i) (b i)) /
    appH (Δ i) (t i) (b i)) Filter.atTop (nhds 0)

/-- A finite probability, so there is no nonintegrable/default-expectation issue. -/
def sizeLE {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lam r : ℝ) : ℝ :=
  ∑ σ : State G, if (size σ.val : ℝ) ≤ r then HardCoreBochner.hcLaw G lam σ else 0

def sizeGE {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (a : ℕ) : ℝ :=
  ∑ σ : State G, if a ≤ size σ.val then HardCoreBochner.hcLaw G lam σ else 0

end
end LocalOccupancyIS.Glauber.Supplement


