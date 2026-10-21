-- Prove2me | Definitions.Def_G2GImport_Sourcing_Model
-- name    : G2GImport_Sourcing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:05.944702+00:00
-- url     : https://prove2.me/theorems/66b33687-a102-49eb-9d87-80e30d28bb50
-- title:
--   Food-importing model: symmetric ad hoc and forward Nash-in-Nash equilibria
-- statement:
--   A buyer needs one unit of a good and has internal yield $Y$ uniform on $[0,1]$. Consumption of $x\in[0,1]$ gives utility $u(x)=2x-x^2$; supply above one is discarded. Each supplier has unit production cost $c>0$. The buyer's bargaining power is $\gamma\in(0,1)$. The positive-production regime used here is $c<1-\gamma$.
--
--   In the **all-ad-hoc game**, each of $l\ge1$ identical suppliers produces $k$ before yield is known. After yield $y$ is observed, supplier $j$ bargains over a purchase and payment while the other $l-1$ agreements remain fixed at their agreed quantities. A symmetric equilibrium requires each bargain to maximize the Nash product and no supplier to gain from a production deviation. Its payoffs are the buyer's expected utility less all payments and each supplier's expected payment less $ck$.
--
--   In the **all-forward game**, each supplier bargains before yield over a quantity and payment, holding the other contracts fixed. Forward suppliers produce exactly their contracted quantities. The model records the resulting buyer and supplier payoffs.
--
--   These definitions make the two pure sourcing regimes of Proposition 3 comparable within one model.
--
--   **Formalization Note** Expectation over $Y$ is the interval integral on $[0,1]$. The ad hoc purchase is capped at remaining need as in (A.2); disagreement holds the other agreed quantities fixed. A production deviation holds those other agreements fixed (passive beliefs). The strict cost bound excludes the zero-production boundary, where the paper's strict monotonicity claim fails.
-- source:
--   Mu, Hu, Reddy & Gavirneni, Negotiating government-to-government food importing contracts: a Nash bargaining framework, accepted manuscript (MSOM, doi:10.1287/msom.2021.1027), PDF pp. 3–8, §§3–4.1; PDF pp. 13–14, (A.2)–(A.4)

import Mathlib
import Definitions.Def_G2GImport_Sourcing_NashBargain

namespace G2GImport.Sourcing

/-- Common cost and bargaining power for the symmetric suppliers. -/
structure Params where
  c : ℝ
  γ : ℝ

/-- The nontrivial positive-production regime of Sections 3 and 4. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.γ ∧ P.γ < 1 ∧ 0 < P.c ∧ P.c < 1 - P.γ

/-- Utility for consumption between zero and the unit demand. -/
def util (x : ℝ) : ℝ := 2 * x - x ^ 2

/-- Excess supply is discarded once demand one is met. -/
def supplyUtil (x : ℝ) : ℝ := util (min 1 x)

/-- Expectation for the internal yield uniformly distributed on the unit interval. -/
noncomputable def EY (f : ℝ → ℝ) : ℝ := ∫ y in (0 : ℝ)..1, f y

/-- The ad hoc bargain after yield realization, holding the other agreed quantities fixed.
The purchase is capped at the remaining need, as in equation (A.2). -/
def AdHocBargain (γ k O y q t : ℝ) : Prop :=
  IsNBS γ (Set.Icc 0 (min k (max 0 (1 - y - O))))
    (fun q' t' => supplyUtil (y + O + q') - supplyUtil (y + O) - t')
    (fun _ t' => t') q t

/-- Symmetric equilibrium of `l` ad hoc suppliers and no forward suppliers. Production
deviations hold other agreements fixed and evaluate every Nash solution of the deviator's
subsequent bargain. -/
def IsAdHocEq (P : Params) (l : ℕ) (k : ℝ) (q t : ℝ → ℝ) : Prop :=
  0 ≤ k ∧
  (∀ y ∈ Set.Icc (0 : ℝ) 1,
    AdHocBargain P.γ k (((l : ℝ) - 1) * q y) y (q y) (t y)) ∧
  ∀ k', 0 ≤ k' → ∀ q' t' : ℝ → ℝ,
    (∀ y ∈ Set.Icc (0 : ℝ) 1,
      AdHocBargain P.γ k' (((l : ℝ) - 1) * q y) y (q' y) (t' y)) →
    EY t' - P.c * k' ≤ EY t - P.c * k

/-- Buyer's expected net utility in a symmetric all-ad-hoc game. -/
noncomputable def adHocBuyer (l : ℕ) (q t : ℝ → ℝ) : ℝ :=
  EY (fun y => supplyUtil (y + (l : ℝ) * q y) - (l : ℝ) * t y)

/-- One ad hoc supplier's expected profit, with production cost paid before yield. -/
noncomputable def adHocSupplier (P : Params) (k : ℝ) (t : ℝ → ℝ) : ℝ :=
  EY t - P.c * k

/-- Symmetric equilibrium of `l` forward suppliers and no ad hoc suppliers. Each
supplier produces exactly its contracted quantity. -/
def IsForwardEq (P : Params) (l : ℕ) (q t : ℝ) : Prop :=
  IsNBS P.γ (Set.Ici 0)
    (fun q' t' => EY (fun y => supplyUtil (y + ((l : ℝ) - 1) * q + q'))
      - EY (fun y => supplyUtil (y + ((l : ℝ) - 1) * q)) - t')
    (fun q' t' => t' - P.c * q') q t

/-- Buyer's expected net utility in a symmetric all-forward game. -/
noncomputable def fwdBuyer (l : ℕ) (q t : ℝ) : ℝ :=
  EY (fun y => supplyUtil (y + (l : ℝ) * q)) - (l : ℝ) * t

/-- One forward supplier's profit when production equals its contracted quantity. -/
def fwdSupplier (P : Params) (q t : ℝ) : ℝ := t - P.c * q

end G2GImport.Sourcing


