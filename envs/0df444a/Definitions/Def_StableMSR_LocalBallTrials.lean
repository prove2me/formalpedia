-- Prove2me | Definitions.Def_StableMSR_LocalBallTrials
-- name    : StableMSR_LocalBallTrials
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-21T13:12:57.543684+00:00
-- url     : https://prove2.me/theorems/8f77a621-ca2c-4c21-bee3-6211453dc09a
-- title:
--   Local ownership and cost certificates for a regional menu trial
-- statement:
--   A successful geometric trial assigns a point region and a cost budget to each relevant state. Every incoming menu option covers the points newly owned by the destination and supplies distinct centers outside the predecessor region. Viable states admit one affordable incoming extension. All witnesses are mathematical certificates for regional menus in the distance oracle model.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1, equation (2), and Appendix A.4–A.6. Real-distance oracle implementation and witness reconstruction for the Prove2Me recovery mission.

import Definitions.Def_StableMSR_RegionalBallDP
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.FewBallRows
open StableMSR.Recovery.RegionalBallDP
set_option autoImplicit false
namespace StableMSR.Recovery.RegionalBallDP
noncomputable def edgeCost (x : World) (v q : ℕ) : ℝ :=
  ∑j ∈ Finset.range x.k, if width x (parent x q)≤j ∧ j<width x v then
    MinSumFPT.oracleAnswer x.dist (payload x q j false) (payload x q j true) else 0
noncomputable def containsPoint (x : World) (u : Word) (j i : ℕ) : Prop :=
  MinSumFPT.oracleAnswer x.dist (u j false) (i:ℤ) ≤ MinSumFPT.oracleAnswer x.dist (u j false) (u j true)
/-- Semantic certificate for a successful geometric trial. Only one edge and its new balls
are inspected at a time. The region predicates and budgets are mathematical witnesses. -/
structure LocalTrial (x : World) (v : ℕ) (B : ℝ) where
  region : ℕ→ℤ→Prop
  tracked : ℕ→Prop
  viable : ℕ→Prop
  budget : ℕ→ℝ
  terminal : vertex x v
  fullWidth : width x v=x.k
  trackedEnd : tracked v
  viableEnd : viable v
  fullRegion : ∀i<x.n,region v (i:ℤ)
  emptyRoot : ∀i<x.n,¬region 1 (i:ℤ)
  owned : ∀t,vertex x t → tracked t → ∀q,link x t q →
    tracked (parent x q) ∧ (∀z,region (parent x q) z → region t z) ∧
    (∀j,width x (parent x q)≤j → j<width x t →
      region t (payload x q j false) ∧ ¬region (parent x q) (payload x q j false)) ∧
    (∀j,width x (parent x q)≤j → j<width x t →
      ∀l,width x (parent x q)≤l → l<width x t →
      payload x q j false=payload x q l false → j=l) ∧
    (∀i<x.n,region t (i:ℤ) → ¬region (parent x q) (i:ℤ) →
      ∃j,width x (parent x q)≤j ∧ j<width x t ∧ containsPoint x (payload x q) j i)
  rootBudget : 0≤budget 1
  extendBudget : ∀t,vertex x t → viable t → t≠1 →
    ∃q,link x t q ∧ viable (parent x q) ∧ budget (parent x q)+edgeCost x t q≤budget t
  terminalBudget : budget v≤B
def localSpec (e : ℚ) (a b : ℕ) (cmd : Cmd) (n k : ℕ) (d : Point n→Point n→ℝ) : Prop :=
  ∃s z H,Executes d cmd (initialStore n k) s z ∧
    z≤a*n^(b*parameterEnvelope (e:ℝ)) ∧ H≤a*n^(b*parameterEnvelope (e:ℝ)) ∧
    let x:=worldOf k H d s
    Ready x s ∧ shape x ∧ ∀O,Stable d k (1+(e:ℝ)) O →
      fewBound (e:ℝ)<(largeClusters d O (e:ℝ)).card →
      ∃v,Nonempty (LocalTrial x v (cost d O))
end StableMSR.Recovery.RegionalBallDP


