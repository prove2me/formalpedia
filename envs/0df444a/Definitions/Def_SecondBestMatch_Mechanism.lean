-- Prove2me | Definitions.Def_SecondBestMatch_Mechanism
-- name    : SecondBestMatch_Mechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:00.520878+00:00
-- url     : https://prove2.me/theorems/e45becdd-792a-46ec-a496-b9b19d80bcab
-- title:
--   Direct mechanism $(q, p, r)$
-- statement:
--   A **direct mechanism** $(q,p,r)$ consists of a randomized allocation rule $q$, with $q_M(\boldsymbol t)$ the probability of selecting the matching $M$ at the report profile $\boldsymbol t = (\boldsymbol v, \boldsymbol c)$, a buyer payment rule $p_i(\boldsymbol t)\in\mathbb R$ (buyer $i$'s expected payment to the mechanism, conditional on $\boldsymbol t$) and a seller receipt rule $r_j(\boldsymbol t)\in\mathbb R$ (seller $j$'s expected receipt).
--
--   Transfers are deterministic given the reports and may be negative: no ex-post guarantee and no sign constraint is imposed. The conditions that make $q$ a Borel kernel into $\Delta(\mathcal F)$ are collected in `IsAdmissible`.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Sections 2.1–2.2, pp.7–8

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- A direct mechanism `(q, p, r)` (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §2.1–2.2, pp.7–8): a randomized allocation rule
`q(t) = (q_M(t))_M` (the probability of selecting the matching `M` at the report profile `t`), the
buyers' expected payments `pᵢ(t) ∈ ℝ` and the sellers' expected receipts `rⱼ(t) ∈ ℝ`, both
conditional on `t`.

**Formalization Note** Transfers are deterministic given the reports (p.8) and signed: no sign
constraint is imposed. The conditions that make `q` a Borel kernel into `Δ(ℱ)` are in
`IsAdmissible`. -/
structure Mechanism (B S : Type*) where
  /-- `q_M(t)`, the probability of selecting `M` at the report profile `t` -/
  alloc : Profile B S → Finset (B × S) → ℝ
  /-- `pᵢ(t)`, buyer `i`'s expected payment at `t` -/
  pay : Profile B S → B → ℝ
  /-- `rⱼ(t)`, seller `j`'s expected receipt at `t` -/
  recv : Profile B S → S → ℝ

end SecondBestMatch


