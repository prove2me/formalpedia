-- Prove2me | Definitions.Def_SecondBestTrade_HalfEfficiency_PaymentTransforms
-- name    : SecondBestTrade_HalfEfficiency_PaymentTransforms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:35.348537+00:00
-- url     : https://prove2.me/theorems/cd9fc483-03b6-4dfa-953d-0c491c53ccc5
-- title:
--   Appendix A.1 — Own-report, shift and common-pool transfers
-- statement:
--   For signed transfers $t_a$, define the own-report transfer by $\widehat t_a(r)=\mathbb E_{-a}t_a(r,v_{-a})$. A constant shift $d_a$ adds $d_a$ to the signed payment, decreasing utility by $d_a$ on both sides. Let $m_a=\min_s U_a(s;s)$.
--
--   For nonnegative own-report buyer payments $p_i$ and seller receipts $p_j$, put $B(v)=\sum_i p_i(v_i)$, $S(c)=\sum_j p_j(c_j)$ and $N=\sum_i\mathbb E p_i$. The common-pool transfers are
--   $$\widetilde p_i(v,c)=p_i(v_i)S(c)/N,\qquad \widetilde p_j(v,c)=p_j(c_j)B(v)/N\quad(N>0).$$
--   They are zero when $N=0$. `poolCorrect` states nonnegativity, reportwise balance and preservation of every own-report expected payment or receipt.
--
--   These are concrete transformations used by the payment-normalization lemmas. The definition does not assert that they preserve utilities or feasibility; those conclusions remain theorem targets. The minimum is over a finite nonempty support. Seller receipts in the formulas are stored as negative signed payments.
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), Appendix A.1, Lemmas A.3–A.5 and their displayed definitions, printed p. 20 (PDF p. 21)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_Mechanisms

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

def ownPayment (N : Market) (m : SignedMechanism N) (a : Agent N) (r : Ty N a) : ℝ :=
  expect N (fun v => m.t a (overwrite N v a r))
def ownReport (N : Market) (m : SignedMechanism N) : SignedMechanism N where
  q := m.q
  t := fun a v => ownPayment N m a (v a)

/-- Positive d lowers the agent's utility; for a seller it lowers its receipt. -/
def shifted (N : Market) (m : SignedMechanism N) (d : Agent N → ℝ) : SignedMechanism N where
  q := m.q
  t := fun a v => m.t a v + d a
noncomputable def minUtility (N : Market) (m : SignedMechanism N) (a : Agent N) : ℝ :=
  sInf (Set.range (fun t : Ty N a => U N m a t t))

def buyerTotal (N : Market) (p : ∀ a, Ty N a → ℝ) (v : Profile N) : ℝ :=
  ∑ i : Fin N.nb, p (.inl i) (v (.inl i))
def sellerTotal (N : Market) (p : ∀ a, Ty N a → ℝ) (v : Profile N) : ℝ :=
  ∑ j : Fin N.ns, p (.inr j) (v (.inr j))
def poolSize (N : Market) (p : ∀ a, Ty N a → ℝ) : ℝ :=
  ∑ i : Fin N.nb, ∑ t, N.mass (.inl i) t * p (.inl i) t

noncomputable def poolTransfers (N : Market) (p : ∀ a, Ty N a → ℝ) (a : Agent N) (v : Profile N) : ℝ := by
  classical
  exact if poolSize N p = 0 then 0 else
    Sum.elim (fun i => p (.inl i) (v (.inl i)) * sellerTotal N p v / poolSize N p)
      (fun j => -(p (.inr j) (v (.inr j)) * buyerTotal N p v / poolSize N p)) a

def poolCorrect (N : Market) (p : ∀ a, Ty N a → ℝ)
    (q : Agent N → Profile N → ℝ) : Prop :=
  (∀ i v, 0 ≤ q (.inl i) v) ∧ (∀ j v, 0 ≤ -q (.inr j) v) ∧
  (∀ v, ∑ a, q a v = 0) ∧
  ∀ a r, expect N (fun v => q a (overwrite N v a r)) =
    Sum.elim (fun _ => p a r) (fun _ => -p a r) a

end SecondBestTrade.HalfEfficiency


