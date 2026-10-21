-- Prove2me | Definitions.Def_TurnTables_Reciprocal_Model
-- name    : TurnTables_Reciprocal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:53:41.277572+00:00
-- url     : https://prove2.me/theorems/4fb5fcb8-6927-4a31-b307-3f4ed3f9c90b
-- title:
--   Reciprocal-option offer game with private implementation types
-- statement:
--   In the subgame where both parties acquired the other's capability, each privately has implementation type $\Gamma\in\{\gamma,1\}$, with each type occurring with probability $1/2$. Partial implementation produces value $\gamma V_2$, full implementation produces $V_2$, and joint development pays each party $V_1$. The parameters obey $0<\gamma<1$, $0<V_1$, and $2V_1<V_2$.
--
--   At a nonnegative offer price $B$, an offeree of type $\Gamma_E$ reciprocates precisely when $\Gamma_E V_2-B>B$; equality leads to acceptance. Acceptance pays the offeror $\Gamma_R V_2-B$ and the offeree $B$; reciprocation pays them $B$ and $\Gamma_E V_2-B$, respectively. If neither party offers, each receives $V_1$. When both offer, each becomes offeror with probability $1/2$. A strategy gives each type an offer probability in $[0,1]$, and its equilibrium condition compares every feasible unilateral offer probability.
--
--   The candidate strike price and the mixed offer probability are
--
--   $$
--   B^*=\frac{\gamma V_2}{2},\qquad
--   \pi=\frac{\gamma V_2-2V_1}{V_2-2V_1}.
--   $$
--
--   **Formalization Note** The prior-weighted price payoff uses the offeree's two types with weights $1/2$ each. The assumption $V_1>0$ follows from the paper's value-creation model, where $V_1=3/(8k)$ and $k>0$.
-- source:
--   Taneri & Crama, Turning the Tables in R&D Licensing Contracts, SSRN 3711872 (version of October 15, 2020), pp. 8, 10, 13, 21–22, §3.1, §3.2, §4, §4.4

import Mathlib
import Definitions.Def_TurnTables_Reciprocal_BayesGame

namespace TurnTables.Reciprocal

structure Params where
  γ : ℝ
  V1 : ℝ
  V2 : ℝ

def Params.Standing (P : Params) : Prop :=
  0 < P.γ ∧ P.γ < 1 ∧ 0 < P.V1 ∧ 2 * P.V1 < P.V2

inductive Impl | part | full
  deriving DecidableEq

instance : Fintype Impl :=
  ⟨{.part, .full}, by intro x; cases x <;> simp⟩

def Impl.val (P : Params) : Impl → ℝ
  | .part => P.γ
  | .full => 1

/-- The offeree reciprocates iff this strictly improves its payoff; ties accept. -/
def Reciprocates (P : Params) (E : Impl) (B : ℝ) : Prop :=
  B < E.val P * P.V2 - B

noncomputable def offerorPay (P : Params) (R E : Impl) (B : ℝ) : ℝ :=
  by classical exact if Reciprocates P E B then B else R.val P * P.V2 - B

noncomputable def offereePay (P : Params) (_R E : Impl) (B : ℝ) : ℝ :=
  by classical exact if Reciprocates P E B then E.val P * P.V2 - B else B

/-- Interim payoff when type `T` offers with probability `a`, the other type is
uniformly partial or full, and simultaneous offers get a fair first mover. -/
noncomputable def interimPay (P : Params) (B : ℝ) (σ : Impl → ℝ)
    (T : Impl) (a : ℝ) : ℝ :=
  ∑ o : Impl, (1 / 2 : ℝ) *
    (a * σ o * ((1 / 2 : ℝ) * offerorPay P T o B + (1 / 2 : ℝ) * offereePay P o T B)
    + a * (1 - σ o) * offerorPay P T o B
    + (1 - a) * σ o * offereePay P o T B
    + (1 - a) * (1 - σ o) * P.V1)

noncomputable def offerGame (P : Params) (B : ℝ) : SymmetricBinaryBayesGame Impl :=
  ⟨interimPay P B⟩

def IsSymBNE (P : Params) (B : ℝ) (σ : Impl → ℝ) : Prop :=
  (offerGame P B).IsBNE σ

/-- Price payoff evaluated against the offeree's prior type distribution. -/
noncomputable def offerorPriorPay (P : Params) (R : Impl) (B : ℝ) : ℝ :=
  ∑ E : Impl, (1 / 2 : ℝ) * offerorPay P R E B

noncomputable def strikeB (P : Params) : ℝ := P.γ * P.V2 / 2

noncomputable def offerProb (P : Params) : ℝ :=
  (P.γ * P.V2 - 2 * P.V1) / (P.V2 - 2 * P.V1)

end TurnTables.Reciprocal


