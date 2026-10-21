-- Prove2me | Definitions.Def_ShortTermDisclosure_Equilibrium_Model
-- name    : ShortTermDisclosure_Equilibrium_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:24.982067+00:00
-- url     : https://prove2.me/theorems/79da01a1-06ed-498b-86fc-6cd799a3562a
-- title:
--   §2–§4 — disclosure game and equilibrium
-- statement:
--   The current firm value is uniform on $[\underline v,\bar v]$, and the alternative value is uniform on $[0,\bar\mu]$. The manager observes the current value with probability $p$; an informed manager can disclose it truthfully. A shareholder privately observes the alternative value and chooses whether to intervene. Investors price the firm conditional on disclosure and intervention. The maintained restrictions are $\bar\mu/2<\underline v<\bar v<\bar\mu$ and $0<p<1$.
--
--   An equilibrium consists of a measurable disclosure set, a Bayes belief after silence, and shareholder intervention thresholds. The shareholder best responds at each private type; the manager chooses the higher expected liquidation value, disclosing at a tie. The belief after silence is
--
--   $$E[v\mid ND]=\frac{p\Pr(v\in ND)E[v\mid v\in ND]+(1-p)E[v]}{p\Pr(v\in ND)+1-p}.$$
--
--   This definition is shared by the target and its milestones. **Formalization Note** Expectations are interval integrals for the two uniform priors. The restriction $0<p<1$ keeps the Bayes denominator positive.
-- source:
--   Jia & Menon, Shareholder short-termism, corporate control and voluntary disclosure, authors' manuscript (SSRN 4029096, Minerva Access copy), pp. 6–16 (PDF 9–19), §2–§4, Assumption 1, (1)–(4), (7)–(8), (11)

import Mathlib

namespace ShortTermDisclosure.Equilibrium

/-- Parameters of the uniform current-value and alternative-value model. -/
structure Params where
  vlo : ℝ
  vhi : ℝ
  muhi : ℝ
  p : ℝ

/-- Assumption 1 and a nondegenerate probability of an informed manager. -/
def Params.Standing (P : Params) : Prop :=
  P.muhi / 2 < P.vlo ∧ P.vlo < P.vhi ∧ P.vhi < P.muhi ∧
  0 < P.p ∧ P.p < 1

/-- The paper's transformation of the shareholder's price weight. -/
noncomputable def lam (η : ℝ) : ℝ := η / (2 - η)

/-- Mean alternative value conditional on intervention under a threshold strategy. -/
noncomputable def condMeanAbove (muhi t : ℝ) : ℝ :=
  if t < muhi then (∫ mu in t..muhi, mu) / (muhi - t) else muhi

/-- Gain to a shareholder of type `mu` from intervening rather than abstaining. -/
noncomputable def netBenefit (η muhi x t mu : ℝ) : ℝ :=
  η * condMeanAbove muhi t + (1 - η) * mu - x

/-- A threshold strategy is a weak best response at every shareholder type. -/
def IsSHBestResponse (η muhi x t : ℝ) : Prop :=
  0 ≤ t ∧ t ≤ muhi ∧
  (∀ mu ∈ Set.Icc 0 muhi, t ≤ mu → 0 ≤ netBenefit η muhi x t mu) ∧
  (∀ mu ∈ Set.Icc 0 muhi, mu < t → netBenefit η muhi x t mu ≤ 0)

/-- Expected liquidation value of an informed manager with current value `v`. -/
noncomputable def managerValue (muhi t v : ℝ) : ℝ :=
  (∫ mu in (0 : ℝ)..muhi, if t ≤ mu then mu else v) / muhi

/-- Bayes' belief about current value after no disclosure, equation (11). -/
noncomputable def belief (P : Params) (ND : Set ℝ) : ℝ :=
  let L := P.vhi - P.vlo
  (P.p * ((∫ v in ND, v) / L) +
    (1 - P.p) * ((P.vlo + P.vhi) / 2)) /
    (P.p * ((MeasureTheory.volume ND).toReal / L) + (1 - P.p))

/-- Disclosure set, nondisclosure belief, and shareholder thresholds. -/
structure Profile where
  D : Set ℝ
  N : ℝ
  tD : ℝ → ℝ
  tN : ℝ

/-- Perfect Bayesian equilibrium of the paper's game with a long-term manager. -/
def IsEquilibrium (P : Params) (η : ℝ) (E : Profile) : Prop :=
  E.D ⊆ Set.Icc P.vlo P.vhi ∧ MeasurableSet E.D ∧
  E.N = belief P (Set.Icc P.vlo P.vhi \ E.D) ∧
  (∀ v ∈ Set.Icc P.vlo P.vhi, IsSHBestResponse η P.muhi v (E.tD v)) ∧
  IsSHBestResponse η P.muhi E.N E.tN ∧
  (∀ v ∈ Set.Icc P.vlo P.vhi,
    v ∈ E.D ↔ managerValue P.muhi E.tN v ≤ managerValue P.muhi (E.tD v) v)

end ShortTermDisclosure.Equilibrium


