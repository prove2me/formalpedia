-- Prove2me | Definitions.Def_GainShareOpt_StochBalance_NodalCert
-- name    : GainShareOpt_StochBalance_NodalCert
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:47:33.815634+00:00
-- url     : https://prove2.me/theorems/54e3a89f-d656-4e1b-8960-ffd35151b6bd
-- title:
--   Validated-profile data of App. M.2: $h,\eta,K,a,b$, the nodal interpolant, $m_u$ and hypotheses (93)–(97)
-- statement:
--   Let $a=0.5802$, $b=0.5805$, $h=1/96000$, $\eta=33/50$, $K=\eta/h=63360$ and $t_i=ih$. Given nodal values $u_0,\dots,u_K$, let $u$ be their linear interpolant on $[0,\eta]$, extended by $1/e$ on $[\eta,1]$, and
--   $$m_u(t)=\min_{0\le s\le t}H_u(t,s).$$
--   For $\alpha\in\{a,b\}$, hypotheses (93)–(97) are:
--   1. $u_0=\alpha$, $u_K=1/e$, and $1/e\le u_{i+1}\le u_i\le1$, $(u_i-u_{i+1})/h\le1/2$ for $0\le i<K$;
--   2. $e^{-t_{i+1}}-u_i>7/50$ for $0\le i<K$;
--   3. $m_u(t_i)\ge\alpha-10^{-6}$ for $0\le i\le K$;
--   4. $m_u(t_i)\le\alpha+10^{-6}$ for $0\le i\le K$ with $u_i>1/e$;
--   5. $m_u(\eta)>\alpha+1/1000$.
--
--   These finite tests are what the paper's exact-arithmetic verifier checks; Lemmas 18–19 turn them into rigorous bounds.
--
--   **Formalization Note** Nodal data is `ℕ → ℝ`; only indices $0,\dots,K$ enter. The interpolant uses `⌊t/h⌋₊`. The concrete supplementary profiles are not part of any statement.
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), pp. 61–62, App. M.2, (93)–(97)

import Mathlib
import Definitions.Def_GainShareOpt_StochBalance_Normalized

namespace GainShareOpt.StochBalance

/-- The mesh `h = 1/96000` of Appendix M.2. -/
noncomputable def meshH : ℝ := 1 / 96000

/-- The interval end `η = 33/50` of Appendix M.2. -/
noncomputable def etaM : ℝ := 33 / 50

/-- The number of cells `K = η/h = 63360`. -/
def nodesK : ℕ := 63360

/-- The lower endpoint `a = 0.5802`. -/
noncomputable def endA : ℝ := 2901 / 5000

/-- The upper endpoint `b = 0.5805`. -/
noncomputable def endB : ℝ := 1161 / 2000

/-- The linear interpolant of nodal values `u_i` at `t_i = i h` on `[0, η]`, extended constantly by
`1/e` on `[η, ∞)`. -/
noncomputable def nodalInterp (uN : ℕ → ℝ) (t : ℝ) : ℝ :=
  if etaM ≤ t then Real.exp (-1)
  else uN ⌊t / meshH⌋₊ + (t - (⌊t / meshH⌋₊ : ℝ) * meshH) / meshH
    * (uN (⌊t / meshH⌋₊ + 1) - uN ⌊t / meshH⌋₊)

/-- The envelope `m_u(t) = min_{0 ≤ s ≤ t} H_u(t, s)`. -/
noncomputable def envelopeMin (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  sInf ((fun s => testH u t s) '' Set.Icc 0 t)

/-- The finite hypotheses (93)–(97) on the nodal values `u_0, …, u_K` at level `α`,
for the interpolant `u = nodalInterp uN`. -/
def NodalHyp (α : ℝ) (uN : ℕ → ℝ) : Prop :=
  uN 0 = α ∧ uN nodesK = Real.exp (-1) ∧
  (∀ i < nodesK, Real.exp (-1) ≤ uN (i + 1) ∧ uN (i + 1) ≤ uN i ∧ uN i ≤ 1 ∧
    (uN i - uN (i + 1)) / meshH ≤ 1 / 2) ∧
  (∀ i < nodesK, 7 / 50 < Real.exp (-(((i + 1 : ℕ) : ℝ) * meshH)) - uN i) ∧
  (∀ i ≤ nodesK, α - 1 / 10 ^ 6 ≤ envelopeMin (nodalInterp uN) ((i : ℝ) * meshH)) ∧
  (∀ i ≤ nodesK, Real.exp (-1) < uN i →
    envelopeMin (nodalInterp uN) ((i : ℝ) * meshH) ≤ α + 1 / 10 ^ 6) ∧
  α + 1 / 1000 < envelopeMin (nodalInterp uN) etaM

end GainShareOpt.StochBalance


