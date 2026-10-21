-- Prove2me | Definitions.Def_LossAverseAuction_CPERevenue_Model
-- name    : LossAverseAuction_CPERevenue_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:41.475815+00:00
-- url     : https://prove2.me/theorems/1fefd135-8ba9-48e3-90f5-fdd51b612d60
-- title:
--   §2 and §4 — gain–loss utility, CPE, payments, and risk terms
-- statement:
--   For item and money dimensions $l\in\{g,m\}$, let $\Lambda^l=\eta^l(\lambda^l-1)$ and let $\mu^l(x)$ equal $\eta^lx$ for $x\ge0$ or $\eta^l\lambda^lx$ for $x<0$. Outcome $(V,p)$ compared with $(r^V,r^p)$ has utility
--
--   $$U((V,p)\mid(r^V,r^p))=V-p+\mu^g(V-r^V)+\mu^m(r^p-p).$$
--
--   A symmetric choice-acclimating personal equilibrium (CPE) maximizes expected utility, for every type and nonnegative bid, relative to the lottery induced by that same bid.
--
--   The module builds first- and second-price outcome lotteries, interim utility and payment, seller revenue, and the conditional value and risk terms used later.
--
--   **Formalization Note** Strategies are measurable and strictly increasing on the support. Ties lose, a null event. Intensive risk is a double expectation and uses the deviation’s reference lottery.
-- source:
--   Balzer & Rosato, Expectations-Based Loss Aversion in Auctions with Interdependent Values, Management Science (Articles in Advance, 2020; doi:10.1287/mnsc.2019.3563), §2, pp. 4–5 (PDF 5–6), eq. (1), Definition 1, Assumption 1; §4, pp. 9–11 (PDF 10–12), eqs. (10), (12)

import Mathlib
import Definitions.Def_LossAverseAuction_CPERevenue_AuctionCore

namespace LossAverseAuction.CPERevenue

open MeasureTheory

/-- The paper's auction data together with gain and loss preferences for goods and money. -/
structure Env (m : ℕ) extends AuctionCore m where
  etag : ℝ
  lamg : ℝ
  etam : ℝ
  lamm : ℝ

noncomputable def Env.F {m : ℕ} (E : Env m) (t : ℝ) : ℝ := E.toAuctionCore.F t
noncomputable def Env.F1 {m : ℕ} (E : Env m) (t : ℝ) : ℝ := E.toAuctionCore.F1 t
noncomputable def Env.f1 {m : ℕ} (E : Env m) (t : ℝ) : ℝ := E.toAuctionCore.f1 t
noncomputable def Env.signalLaw {m : ℕ} (E : Env m) : Measure ℝ := E.toAuctionCore.signalLaw
noncomputable def Env.oppLaw {m : ℕ} (E : Env m) : Measure (Fin (m + 1) → ℝ) :=
  E.toAuctionCore.oppLaw
noncomputable def Env.allLaw {m : ℕ} (E : Env m) : Measure (Fin (m + 2) → ℝ) :=
  E.toAuctionCore.allLaw

def Env.Lg {m : ℕ} (E : Env m) : ℝ := E.etag * (E.lamg - 1)
def Env.Lm {m : ℕ} (E : Env m) : ℝ := E.etam * (E.lamm - 1)

def Env.Standing {m : ℕ} (E : Env m) : Prop :=
  E.toAuctionCore.Standing ∧ 0 ≤ E.etag ∧ 1 < E.lamg ∧ 0 ≤ E.etam ∧ 1 < E.lamm

def Env.Assumption1 {m : ℕ} (E : Env m) : Prop := E.Lg ≤ 1

noncomputable def gainLoss (η lam x : ℝ) : ℝ :=
  if 0 ≤ x then η * x else η * lam * x

noncomputable def Env.U {m : ℕ} (E : Env m) (o r : ℝ × ℝ) : ℝ :=
  o.1 - o.2 + gainLoss E.etag E.lamg (o.1 - r.1) +
    gainLoss E.etam E.lamm (r.2 - o.2)

noncomputable def Env.EU {m : ℕ} (E : Env m) (G H : Measure (ℝ × ℝ)) : ℝ :=
  ∫ o, ∫ r, E.U o r ∂H ∂G

inductive Format
  | FPA
  | SPA

deriving DecidableEq

/-- A bidder wins if her bid is strictly higher than every opponent bid; ties lose. -/
noncomputable def Env.outcome {m : ℕ} (E : Env m) (k : Format) (β : ℝ → ℝ)
    (b t : ℝ) (s : Fin (m + 1) → ℝ) : ℝ × ℝ :=
  if ∀ j, β (s j) < b then
    (E.v t s, match k with
      | .FPA => b
      | .SPA => Finset.univ.sup' Finset.univ_nonempty (fun j => β (s j)))
  else (0, 0)

noncomputable def Env.Γ {m : ℕ} (E : Env m) (k : Format) (β : ℝ → ℝ)
    (b t : ℝ) : Measure (ℝ × ℝ) :=
  E.oppLaw.map (E.outcome k β b t)

/-- Definition 1, restricted to symmetric, nonnegative, strictly increasing strategies. -/
def Env.IsSymCPE {m : ℕ} (E : Env m) (k : Format) (β : ℝ → ℝ) : Prop :=
  Measurable β ∧ StrictMonoOn β (Set.Icc E.tl E.th) ∧
  (∀ t ∈ Set.Icc E.tl E.th, 0 ≤ β t) ∧
  ∀ t ∈ Set.Icc E.tl E.th, ∀ b : ℝ, 0 ≤ b →
    E.EU (E.Γ k β b t) (E.Γ k β b t) ≤
      E.EU (E.Γ k β (β t) t) (E.Γ k β (β t) t)

noncomputable def Env.eqUtil {m : ℕ} (E : Env m) (k : Format) (β : ℝ → ℝ)
    (t : ℝ) : ℝ :=
  E.EU (E.Γ k β (β t) t) (E.Γ k β (β t) t)

noncomputable def Env.interimPayment {m : ℕ} (E : Env m) (k : Format)
    (β : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s, (E.outcome k β (β t) t s).2 ∂E.oppLaw

noncomputable def Env.revenue {m : ℕ} (E : Env m) (k : Format)
    (β : ℝ → ℝ) : ℝ :=
  ∫ σ, ∑ i : Fin (m + 2),
    (E.outcome k β (β (σ i)) (σ i) (fun j => σ (i.succAbove j))).2 ∂E.allLaw

def Env.winSet {m : ℕ} (_E : Env m) (t' : ℝ) : Set (Fin (m + 1) → ℝ) :=
  {s | ∀ j, s j < t'}

noncomputable def Env.Vint {m : ℕ} (E : Env m) (t' t : ℝ) : ℝ :=
  ∫ s in E.winSet t', E.v t s ∂E.oppLaw

noncomputable def Env.Vc {m : ℕ} (E : Env m) (t' t : ℝ) : ℝ :=
  E.Vint t' t / E.F1 t'

noncomputable def Env.Psi {m : ℕ} (E : Env m) (t' t : ℝ) : ℝ :=
  E.Lg * (1 - E.F1 t') * E.F1 t' * E.Vc t' t

/-- Intensive item risk: both outcomes are drawn from the deviation's winning lottery. -/
noncomputable def Env.Omega {m : ℕ} (E : Env m) (t' t : ℝ) : ℝ :=
  E.Lg * ∫ s in E.winSet t', ∫ s' in E.winSet t',
    max (E.v t s - E.v t s') 0 ∂E.oppLaw ∂E.oppLaw

noncomputable def Env.TI {m : ℕ} (E : Env m) (β : ℝ → ℝ) (t' : ℝ) : ℝ :=
  E.F1 t' * β t' * (1 + E.Lm * (1 - E.F1 t'))

noncomputable def Env.TII {m : ℕ} (E : Env m) (β : ℝ → ℝ) (t' : ℝ) : ℝ :=
  (∫ τ in E.tl..t', β τ * E.f1 τ) * (1 + E.Lm * (1 - E.F1 t')) +
    E.Lm * ∫ x in E.tl..t',
      (∫ y in E.tl..x, (β x - β y) * E.f1 y) * E.f1 x

noncomputable def Env.V1 {m : ℕ} (E : Env m) (x t : ℝ) : ℝ :=
  deriv (fun a => E.Vc a t) x
noncomputable def Env.V2 {m : ℕ} (E : Env m) (x t : ℝ) : ℝ :=
  deriv (fun b => E.Vc x b) t
noncomputable def Env.Psi1 {m : ℕ} (E : Env m) (x t : ℝ) : ℝ :=
  deriv (fun a => E.Psi a t) x
noncomputable def Env.Psi2 {m : ℕ} (E : Env m) (x t : ℝ) : ℝ :=
  deriv (fun b => E.Psi x b) t
noncomputable def Env.Omega1 {m : ℕ} (E : Env m) (x t : ℝ) : ℝ :=
  deriv (fun a => E.Omega a t) x
noncomputable def Env.Omega2 {m : ℕ} (E : Env m) (x t : ℝ) : ℝ :=
  deriv (fun b => E.Omega x b) t

noncomputable def Env.A1 {m : ℕ} (E : Env m) (t : ℝ) : ℝ :=
  E.f1 t * E.Vc t t + E.F1 t * E.V1 t t -
    (E.Psi1 t t + E.Omega1 t t)

end LossAverseAuction.CPERevenue


