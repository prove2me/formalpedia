-- Prove2me | Definitions.Def_OtterAMM_TwoSided_Model
-- name    : OtterAMM_TwoSided_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:45:27.09009+00:00
-- url     : https://prove2.me/theorems/d054da93-7bb8-4dd7-a9c7-fa45fa987099
-- title:
--   Orders, reports, identities, aggregate token flows and the utility of Eq. (2) with $-\infty$; mechanisms on ordered blocks
-- statement:
--   Users trade with the pool through **sell-Y** and **sell-X** orders. A sell-Y report (or true type) is $(\tilde v,\tilde q)\in\mathbb R^2_{\ge0}$: a per-unit ask $\tilde v$ in $X$ per unit of $Y$ and a budget $\tilde q$ of $Y$; a sell-X report is $(\tilde u,\tilde r)\in\mathbb R^2_{\ge0}$ with ask in $Y$ per unit of $X$ and budget of $X$. A sell-Y report is **eligible** iff $\tilde v\le\sigma_0$, a sell-X report iff $\tilde u\le\rho_0$.
--
--   Identities are labels; an **outcome** gives each identity a pair $(x_i,y_i)$: a sell-Y identity receives $x_i$ of $X$ for $y_i$ of $Y$, a sell-X identity receives $y_i$ of $Y$ for $x_i$ of $X$. For a finite set $I$ of identities controlled by one real user (with $\mathcal Y$, $\mathcal X$ the sell-Y and sell-X identities), Eq. (1):
--   $$S_Y=\sum_{i\in I\cap\mathcal Y}y_i,\quad R_X=\sum_{i\in I\cap\mathcal Y}x_i,\quad S_X=\sum_{i\in I\cap\mathcal X}x_i,\quad R_Y=\sum_{i\in I\cap\mathcal X}y_i,$$
--   $\Delta X=R_X-S_X$, $\Delta Y=R_Y-S_Y$. A true sell-Y user of type $(v,q)$ has utility (Eq. (2))
--   $$\mathrm{Util}_Y(I;v,q)=\begin{cases}-\infty,&-\Delta Y>q\ \text{ or }\ (-\Delta Y<0\text{ and }\Delta X<0),\\ \Delta X+v\,\Delta Y,&\text{otherwise,}\end{cases}$$
--   and symmetrically a true sell-X user of type $(u,r)$ has $-\infty$ if $-\Delta X>r$ or ($-\Delta X<0$ and $\Delta Y<0$), and $\Delta Y+u\,\Delta X$ otherwise.
--
--   A deterministic **mechanism** receives the ordered block (a list of identities) and their reports — never their owners — and returns an outcome; an unordered mechanism receives the set of identities. A **prescribed ordering** maps a block to a list containing each of its identities exactly once. The overlay of a deviation set $D$ with reports `dev` on a profile `rep` lets the identities of $D$ report `dev` and every other identity keep its report.
--
--   **Formalization Note.** Identities are natural numbers (an unlimited supply of fresh names); a profile is a function from labels to reports, and only the labels of the block matter. Utilities live in `EReal`, $-\infty$ being `⊥`; no arithmetic is done in `EReal`.
-- source:
--   Shi, Zhang, Chung, Li, Otter: A Provably MEV-Resilient Automated Market Maker via Surplus Redistribution, arXiv:2609.03474 (held copy sha256 3a05f18a…), pp. 5–6, §2 and §2.1, Eqs. (1)–(2) (PDF 7–8); p. 8, §2.3 (3) (PDF 10)

import Mathlib
import Definitions.Def_OtterAMM_TwoSided_Curve

set_option autoImplicit false

namespace OtterAMM.TwoSided

/-- Direction of an order (§2): sell `Y` for `X`, or sell `X` for `Y`. -/
inductive Dir
  | sellY
  | sellX
  deriving DecidableEq

/-- A report (or a true type) `(dir, ask, budget)`: for a sell-Y order the per-unit ask `ṽ`
(in `X` per unit of `Y`) and the budget `q̃` of `Y`; for a sell-X order the ask `ũ` (in `Y`
per unit of `X`) and the budget `r̃` of `X` (§2, p. 5). -/
structure Report where
  dir : Dir
  ask : ℝ
  budget : ℝ

/-- Reports and types live in `ℝ²≥0`. -/
def Report.Valid (r : Report) : Prop := 0 ≤ r.ask ∧ 0 ≤ r.budget

/-- Eligibility (§2.3 (3)): a sell-Y order is eligible iff `ṽ ≤ σ0`, a sell-X order iff
`ũ ≤ ρ0`. -/
def Report.Eligible (C : PricingCurve) (r : Report) : Prop :=
  match r.dir with
  | .sellY => r.ask ≤ C.σ0
  | .sellX => r.ask ≤ C.ρ0

/-- Identities are labelled by natural numbers (an unlimited supply of fresh names). -/
abbrev Ident := ℕ

/-- An outcome assigns to every identity the pair `(x_i, y_i)` of §2: for a sell-Y identity it
receives `x_i` units of `X` for `y_i` units of `Y`; for a sell-X identity it receives `y_i`
units of `Y` for `x_i` units of `X`. -/
abbrev Outcome := Ident → ℝ × ℝ

/-- Every identity of `S` carries a report in `ℝ²≥0`. -/
def ValidOn (S : Finset Ident) (rep : Ident → Report) : Prop := ∀ i ∈ S, (rep i).Valid

def askOf (rep : Ident → Report) (i : Ident) : ℝ := (rep i).ask

def budgetOf (rep : Ident → Report) (i : Ident) : ℝ := (rep i).budget

/-- The sell-Y identities of `S`. -/
def sellYs (S : Finset Ident) (rep : Ident → Report) : Finset Ident :=
  S.filter (fun i => (rep i).dir = Dir.sellY)

/-- The sell-X identities of `S`. -/
def sellXs (S : Finset Ident) (rep : Ident → Report) : Finset Ident :=
  S.filter (fun i => (rep i).dir = Dir.sellX)

/-- Eq. (1): `S_Y(I) = Σ_{i ∈ I ∩ Y} y_i`. -/
def flowSY (rep : Ident → Report) (out : Outcome) (I : Finset Ident) : ℝ :=
  ∑ i ∈ sellYs I rep, (out i).2

/-- Eq. (1): `R_X(I) = Σ_{i ∈ I ∩ Y} x_i`. -/
def flowRX (rep : Ident → Report) (out : Outcome) (I : Finset Ident) : ℝ :=
  ∑ i ∈ sellYs I rep, (out i).1

/-- Eq. (1): `S_X(I) = Σ_{i ∈ I ∩ X} x_i`. -/
def flowSX (rep : Ident → Report) (out : Outcome) (I : Finset Ident) : ℝ :=
  ∑ i ∈ sellXs I rep, (out i).1

/-- Eq. (1): `R_Y(I) = Σ_{i ∈ I ∩ X} y_i`. -/
def flowRY (rep : Ident → Report) (out : Outcome) (I : Finset Ident) : ℝ :=
  ∑ i ∈ sellXs I rep, (out i).2

/-- `ΔX(I) = R_X(I) − S_X(I)`. -/
def deltaX (rep : Ident → Report) (out : Outcome) (I : Finset Ident) : ℝ :=
  flowRX rep out I - flowSX rep out I

/-- `ΔY(I) = R_Y(I) − S_Y(I)`. -/
def deltaY (rep : Ident → Report) (out : Outcome) (I : Finset Ident) : ℝ :=
  flowRY rep out I - flowSY rep out I

/-- Eq. (2): the utility of a real user of true type `t` controlling the identity set `I`
(the directions of the identities are read from the profile `rep`), with values in `EReal`
so that the catastrophic outcome is a genuine `−∞ = ⊥`.
* true sell-Y type `(v, q)`: `−∞` if `−ΔY > q` or (`−ΔY < 0` and `ΔX < 0`), else `ΔX + v·ΔY`;
* true sell-X type `(u, r)`: `−∞` if `−ΔX > r` or (`−ΔX < 0` and `ΔY < 0`), else `ΔY + u·ΔX`. -/
noncomputable def util (t : Report) (rep : Ident → Report) (out : Outcome) (I : Finset Ident) :
    EReal :=
  match t.dir with
  | .sellY =>
      if t.budget < -deltaY rep out I ∨ (-deltaY rep out I < 0 ∧ deltaX rep out I < 0) then ⊥
      else ((deltaX rep out I + t.ask * deltaY rep out I : ℝ) : EReal)
  | .sellX =>
      if t.budget < -deltaX rep out I ∨ (-deltaX rep out I < 0 ∧ deltaY rep out I < 0) then ⊥
      else ((deltaY rep out I + t.ask * deltaX rep out I : ℝ) : EReal)

/-- A deterministic AMM mechanism on ordered blocks: it sees the ordered list of identities in
the block and their reports (never who owns them), and returns an outcome. -/
abbrev Mechanism := List Ident → (Ident → Report) → Outcome

/-- A mechanism that treats the block as an unordered set. -/
abbrev UMechanism := Finset Ident → (Ident → Report) → Outcome

/-- The prescribed ordering of a block (what an honest builder does). -/
abbrev OrderRule := Finset Ident → (Ident → Report) → List Ident

/-- A prescribed ordering lists every identity of the block exactly once. -/
def OrderRule.Admissible (π : OrderRule) : Prop :=
  ∀ (S : Finset Ident) (rep : Ident → Report), (π S rep).Nodup ∧ (π S rep).toFinset = S

/-- The profile in which the identities of `D` report `dev` and every other identity keeps its
report under `rep`. -/
def overlay (D : Finset Ident) (dev rep : Ident → Report) : Ident → Report :=
  fun j => if j ∈ D then dev j else rep j

end OtterAMM.TwoSided


