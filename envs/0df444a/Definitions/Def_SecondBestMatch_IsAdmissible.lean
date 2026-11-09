-- Prove2me | Definitions.Def_SecondBestMatch_IsAdmissible
-- name    : SecondBestMatch_IsAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:35.806915+00:00
-- url     : https://prove2.me/theorems/d6e349fd-cccd-412e-ad18-114f6395c45d
-- title:
--   Admissible mechanism: Borel kernel into $\Delta(\mathcal F)$, finite transfer expectations
-- statement:
--   A mechanism $(q,p,r)$ is **admissible** if
--
--   1. its allocation rule is a Borel kernel $q:[0,1]^K\to\Delta(\mathcal F)$: each $\boldsymbol t\mapsto q_M(\boldsymbol t)$ is measurable, and at every report profile in $[0,1]^K$ the numbers $q_M(\boldsymbol t)$ are nonnegative, vanish for $M\notin\mathcal F$ and sum to one over $\mathcal F$;
--   2. all transfer expectations are finite and well defined: every payment $p_i$ and receipt $r_j$ is integrable under the product prior, also with the agent's own report fixed at any $z\in[0,1]$ (these are the interim transfers of Definition 2.1).
--
--   Item 2 is the paper's standing assumption "we assume throughout that all transfer expectations appearing below are finite and well defined".
--
--   **Formalization Note** The allocation is a function on all of $\mathbb R^K$ and is required measurable there; its values off $[0,1]^K$ are unconstrained and never enter any quantity, and every Borel kernel on $[0,1]^K$ extends measurably.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Sections 2.1–2.2, pp.7–8 (standing assumption, p.8)

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_Mechanism
import Definitions.Def_SecondBestMatch_InUnitCube

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- The standing conditions on a mechanism (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §2.1–2.2, pp.7–8): the allocation rule is a
Borel kernel `q : [0,1]^K → Δ(ℱ)` (measurable, and a probability distribution over `ℱ` at every
report profile), and "all transfer expectations appearing below are finite and well defined"
(p.8): every payment and receipt is integrable under the prior, also with the agent's own report
fixed at any `z ∈ [0, 1]` (the interim transfers of Definition 2.1).

**Formalization Note** The allocation is a function on all of `ℝ^K`; its values off `[0,1]^K`
are unconstrained and never enter any quantity (the prior lives on `[0,1]^K` and reports are in
`[0, 1]`). Measurability is required on `ℝ^K`; a Borel kernel on `[0,1]^K` extends measurably. -/
structure IsAdmissible {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
    (m : Market B S) (A : Mechanism B S) : Prop where
  alloc_measurable : ∀ M, Measurable fun t => A.alloc t M
  alloc_nonneg : ∀ t, InUnitCube t → ∀ M, 0 ≤ A.alloc t M
  alloc_feasible : ∀ t, InUnitCube t → ∀ M, M ∉ m.family → A.alloc t M = 0
  alloc_sum : ∀ t, InUnitCube t → ∑ M ∈ m.family, A.alloc t M = 1
  pay_integrable : ∀ i, Integrable (fun t => A.pay t i) (typeMeasure m)
  pay_interim_integrable : ∀ i, ∀ z ∈ Icc (0 : ℝ) 1,
    Integrable (fun t => A.pay (updateBuyer t i z) i) (typeMeasure m)
  recv_integrable : ∀ j, Integrable (fun t => A.recv t j) (typeMeasure m)
  recv_interim_integrable : ∀ j, ∀ z ∈ Icc (0 : ℝ) 1,
    Integrable (fun t => A.recv (updateSeller t j z) j) (typeMeasure m)

end SecondBestMatch


