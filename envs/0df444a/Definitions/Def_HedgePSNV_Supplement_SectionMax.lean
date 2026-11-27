-- Prove2me | Definitions.Def_HedgePSNV_Supplement_SectionMax
-- name    : HedgePSNV_Supplement_SectionMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:52:00.257347+00:00
-- url     : https://prove2.me/theorems/4c46e711-f651-4ba3-ba9b-0b59821f4839
-- title:
--   Section maximizers $P^{NV(M)}(R)$ and $R^{NV(M)}(P)$ of $V_0$ over the sections of $D$
-- statement:
--   Throughout, the standing model of §3.1 holds (the published `HedgePSNV.Model.Standing`): $B,\tilde B$ independent Brownian motions with augmented filtrations $\mathcal F\supseteq\mathcal G$, the asset $dX_t=X_t(\mu_t\,dt+\sigma_t\,dB_t)$, the demand component $C$ with $A_T=C_T+\tilde\sigma\tilde B_T$, the two Markov hypotheses, and $\mathbb P^M$ with $d\mathbb P^M/d\mathbb P=Z_T$ (12); $V_0(P,R)=\mathbb E^M[H_T(P,R)]$, and $D=\{(P,R):P\ge c,\ R-bP\ge0\}$.
--
--   **Price section maximizer.** $P$ is a section maximizer of $V_0(\cdot,R)$ when $(P,R)\in D$ and
--   $$
--   V_0(P',R)\le V_0(P,R)\quad\text{for every }P'\text{ with }(P',R)\in D,\ \text{i.e. }c\le P'\le R/b .
--   $$
--   **VPQ section maximizer.** $R$ is a section maximizer of $V_0(P,\cdot)$ when $(P,R)\in D$ and $V_0(P,R')\le V_0(P,R)$ for every $R'\ge bP$.
--
--   These are the partial maximizers $P^{NV(M)}(R):=\arg\max_PV_0(P,R)$ and $R^{NV(M)}(P):=\arg\max_RV_0(P,R)$ of (EC.8.2) and (EC.8.9). They define the critical values $P_1,R_1,P_2,P_3$ (Definition EC.1), the critical point $(P^*,R^*)$ (EC.8.10) and $P^\circ$ of Theorem 3.
--
--   **Formalization Note** The paper's closed forms $P^{NV(M)}(R)=(bc+\mathbb E^M(R\wedge A_T))/(2b)$ and $R^{NV(M)}(P)=F_M^{-1}((P-c)/(P-s))$ are the unconstrained stationary points; they are the section maximizers wherever they lie in the section. Reading the partial arg max over the sections of $D$ is the convention of the published Lemma EC.7 (p.9: the domain constraints are non-binding constraints of the same problems).
-- source:
--   Wang–Yao–Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, (EC.8.2) p.ec49, (EC.8.9) p.ec52

import Mathlib
import Definitions.Def_HedgePSNV_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV.Supplement

open HedgePSNV

/-- The price section maximizer `P^NV(M)(R) := arg max_P V_0(P,R)` of (EC.8.2) and (EC.8.9),
arXiv:2201.01026v4, pp.ec49, ec52: `P` maximizes the expected production payoff under the
risk-neutral measure, `V_0(·, R) = E^M[H_T(·, R)]`, over the section
`{P' : (P', R) ∈ D} = {P' : c ≤ P' ≤ R/b}` of the decision domain, and `(P, R) ∈ D`.

**Formalization Note** The paper's closed form `P^NV(M)(R) = (bc + E^M(R ∧ A_T))/(2b)` is the
stationary point of the concave quadratic `V_0(·, R)`; it is the section maximizer whenever it
lies in the section. Following the published mission (`HedgePSNV.lemma_ec_7`), every partial
arg max of the paper is read over the sections of `D` (p.9: the domain constraints are
non-binding constraints of the same problems). -/
def IsSecMaxP {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω) (P R : ℝ) : Prop :=
  (P, R) ∈ decisionDomain p ∧
    ∀ P' : ℝ, (P', R) ∈ decisionDomain p → M.V0 P' R ≤ M.V0 P R

/-- The VPQ section maximizer `R^NV(M)(P) := arg max_R V_0(P,R)` of (EC.8.2) and (EC.8.9),
arXiv:2201.01026v4, pp.ec49, ec52: `R` maximizes `V_0(P, ·)` over the section
`{R' : (P, R') ∈ D} = {R' : R' ≥ bP}` of the decision domain, and `(P, R) ∈ D`.

**Formalization Note** The paper's closed form `R^NV(M)(P) = F_M^{-1}((P − c)/(P − s))`, with
`F_M` the distribution function of `A_T` under `P^M`, is the unconstrained maximizer; it is the
section maximizer whenever it is at least `bP`. -/
def IsSecMaxR {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω) (P R : ℝ) : Prop :=
  (P, R) ∈ decisionDomain p ∧
    ∀ R' : ℝ, (P, R') ∈ decisionDomain p → M.V0 P R' ≤ M.V0 P R

end HedgePSNV.Supplement


