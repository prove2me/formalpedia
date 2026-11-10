-- Prove2me | Definitions.Def_OtterAMM_TwoSided_VCG
-- name    : OtterAMM_TwoSided_VCG
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:46:20.610868+00:00
-- url     : https://prove2.me/theorems/a21ab4cc-d6b5-4c84-8e59-53cec2dc1663
-- title:
--   The one-sided VCG auction of §3.1: welfare $W_F$, max-total welfare-maximizer selection, Clarke compensation; the layer-cake quantities $D_S$, $K_F$
-- statement:
--   Fix a one-sided curve $G$ and a finite set $S$ of sell-Y bids with asks $\tilde v_i$ and budgets $\tilde q_i$. For sales $0\le y_i\le\tilde q_i$ the **social welfare** is
--   $$SW_G(S,\{y_i\})=G\Big(\sum_{i\in S}y_i\Big)-\sum_{i\in S}\tilde v_iy_i,\qquad W_G(S)=\max_{0\le y_i\le\tilde q_i}SW_G(S,\{y_i\})\quad(3).$$
--   The **allocation rule** chooses, among welfare maximizers, one maximizing the total $\sum_i y_i$, then applies an arbitrary exogenous tie-breaking rule: formally a **selection rule** is any map from (curve, bids, asks, budgets) to an allocation, and it is **admissible** if on every one-sided curve and every finite bid set with nonnegative asks and budgets it returns a welfare maximizer whose total is largest among all welfare maximizers. With $y^*$ the selected allocation and $Y^*=\sum_iy^*_i$, the **Clarke pivot compensation** is
--   $$x^*_i=G(Y^*)-\sum_{j\ne i}\tilde v_jy^*_j-W_G(S\setminus\{i\})\qquad(4).$$
--   The one-sided outcome gives identity $i\in S$ the pair $(x^*_i,y^*_i)$.
--
--   For the layer-cake formula (18): $D_S(t)=\sum_{i\in S}\tilde q_i\,\mathbf 1\{\tilde v_i\le t\}$ and $K_G(t)=\sup\{y\ge0:G'_+(y)\ge t\}\in[0,+\infty]$, and the integrand is $\min\{D_S(t),K_G(t)\}$ (finite since $D_S(t)$ is).
--
--   **Formalization Note.** $W_G$ is the supremum (`sSup`) of the welfare over the box; for a one-sided curve it is attained. Allocations are functions on all labels; only their values on $S$ matter. $K_G$ is an `EReal` supremum, so $+\infty$ is allowed; the integrand is converted back to a real number.
-- source:
--   Shi, Zhang, Chung, Li, Otter: A Provably MEV-Resilient Automated Market Maker via Surplus Redistribution, arXiv:2609.03474 (held copy sha256 3a05f18a…), pp. 9–10, §3.1, Eqs. (3)–(5) (PDF 11–12); p. 19, §5 (PDF 21)

import Mathlib
import Definitions.Def_OtterAMM_TwoSided_Curve
import Definitions.Def_OtterAMM_TwoSided_Model

set_option autoImplicit false

namespace OtterAMM.TwoSided

/-- Feasible sales `0 ≤ y_i ≤ q̃_i` for `i ∈ S` (the box of Eq. (3)). -/
def Feas (S : Finset Ident) (q : Ident → ℝ) (y : Ident → ℝ) : Prop :=
  ∀ i ∈ S, 0 ≤ y i ∧ y i ≤ q i

/-- Social welfare `SW_G(S, {y_i}) = G(Σ_{i∈S} y_i) − Σ_{i∈S} ṽ_i y_i` (§3.1). -/
def SW (G : ℝ → ℝ) (S : Finset Ident) (a : Ident → ℝ) (y : Ident → ℝ) : ℝ :=
  G (∑ i ∈ S, y i) - ∑ i ∈ S, a i * y i

/-- Eq. (3): `W_G(S) = max_{0 ≤ y_i ≤ q̃_i} SW_G(S, {y_i})`, written as the supremum of the
welfare over the feasible box (a maximum for a one-sided curve, by continuity on a compact
box). -/
noncomputable def W (G : ℝ → ℝ) (S : Finset Ident) (a q : Ident → ℝ) : ℝ :=
  sSup ((SW G S a) '' {y | Feas S q y})

/-- `y` is a welfare maximizer for the bids `S` with asks `a` and budgets `q`. -/
def IsWelfareMax (G : ℝ → ℝ) (S : Finset Ident) (a q : Ident → ℝ) (y : Ident → ℝ) : Prop :=
  Feas S q y ∧ SW G S a y = W G S a q

/-- `y` is a welfare maximizer whose total `Σ_{i∈S} y_i` is largest among all welfare maximizers
(the first step of the allocation rule of §3.1). -/
def IsMaxTotalWelfareMax (G : ℝ → ℝ) (S : Finset Ident) (a q : Ident → ℝ) (y : Ident → ℝ) :
    Prop :=
  IsWelfareMax G S a q y ∧
    ∀ y' : Ident → ℝ, IsWelfareMax G S a q y' → ∑ i ∈ S, y' i ≤ ∑ i ∈ S, y i

/-- A selection rule: given the curve, the bids and their asks and budgets, it returns an
allocation. -/
abbrev SelRule := (ℝ → ℝ) → Finset Ident → (Ident → ℝ) → (Ident → ℝ) → (Ident → ℝ)

/-- The allocation rule of §3.1 with an arbitrary exogenous tie-breaking rule: on every one-sided
curve and every finite set of bids with nonnegative asks and budgets, the rule returns a welfare
maximizer of largest total. -/
def SelRule.Admissible (sel : SelRule) : Prop :=
  ∀ (G : ℝ → ℝ) (S : Finset Ident) (a q : Ident → ℝ), IsOneSidedCurve G →
    (∀ i ∈ S, 0 ≤ a i ∧ 0 ≤ q i) → IsMaxTotalWelfareMax G S a q (sel G S a q)

/-- The VCG allocation `y*_i`. -/
def vcgAlloc (sel : SelRule) (G : ℝ → ℝ) (S : Finset Ident) (a q : Ident → ℝ) (i : Ident) : ℝ :=
  sel G S a q i

/-- The total `Y* = Σ_{i∈S} y*_i`. -/
def vcgTotal (sel : SelRule) (G : ℝ → ℝ) (S : Finset Ident) (a q : Ident → ℝ) : ℝ :=
  ∑ i ∈ S, vcgAlloc sel G S a q i

/-- Eq. (4), the Clarke pivot compensation
`x*_i = G(Y*) − Σ_{j ≠ i} ṽ_j y*_j − W_G(S ∖ {i})`. -/
noncomputable def vcgComp (sel : SelRule) (G : ℝ → ℝ) (S : Finset Ident) (a q : Ident → ℝ)
    (i : Ident) : ℝ :=
  G (vcgTotal sel G S a q) - ∑ j ∈ S.erase i, a j * vcgAlloc sel G S a q j - W G (S.erase i) a q

/-- The one-sided VCG auction of §3.1 run on the (sell-Y) identities `S` with reports `rep`:
identity `i ∈ S` sells `y*_i` and receives `x*_i`; identities outside `S` get `(0, 0)`. -/
noncomputable def oneSidedOutcome (sel : SelRule) (G : ℝ → ℝ) (S : Finset Ident)
    (rep : Ident → Report) : Outcome :=
  fun i => if i ∈ S then
      (vcgComp sel G S (askOf rep) (budgetOf rep) i, vcgAlloc sel G S (askOf rep) (budgetOf rep) i)
    else (0, 0)

/-- `D_S(t) = Σ_{i∈S} q̃_i 1{ṽ_i ≤ t}` (§5, p. 19). -/
noncomputable def capacityBelow (S : Finset Ident) (a q : Ident → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ S, if a i ≤ t then q i else 0

/-- `K_G(t) = sup {y ≥ 0 : G'₊(y) ≥ t}` (§5, p. 19), in `EReal` so that the value `+∞` is
allowed. -/
noncomputable def thresholdQty (G : ℝ → ℝ) (t : ℝ) : EReal :=
  sSup {z : EReal | ∃ y : ℝ, 0 ≤ y ∧ t ≤ rightDeriv G y ∧ z = (y : EReal)}

/-- The integrand `min{D_S(t), K_G(t)}` of Eq. (18) (a finite value, since `D_S(t)` is
finite). -/
noncomputable def layer (G : ℝ → ℝ) (S : Finset Ident) (a q : Ident → ℝ) (t : ℝ) : ℝ :=
  (min ((capacityBelow S a q t : ℝ) : EReal) (thresholdQty G t)).toReal

end OtterAMM.TwoSided


