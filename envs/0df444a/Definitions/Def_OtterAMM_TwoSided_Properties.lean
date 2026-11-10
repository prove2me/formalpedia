-- Prove2me | Definitions.Def_OtterAMM_TwoSided_Properties
-- name    : OtterAMM_TwoSided_Properties
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:46:17.370434+00:00
-- url     : https://prove2.me/theorems/e85a6a6a-bab5-4411-812f-efeea2d43901
-- title:
--   Well-formedness, individual rationality, feasibility (Eq. (41)), UIC, builder(-as-user) strategy-proofness, order-insensitivity, Pareto optimality for eligible users
-- statement:
--   Let $F$ be a pricing curve. All properties quantify over every finite block whose reports lie in $\mathbb R^2_{\ge0}$.
--
--   - **Well-formed**: every sell-Y identity has $0\le y_i\le\tilde q_i$ and $0\le x_i\le\sigma_0y_i$; every sell-X identity has $0\le x_j\le\tilde r_j$ and $0\le y_j\le\rho_0x_j$ (the §2 ranges, nonnegative compensation, and the spot-rate caps of (16) and (7)).
--   - **Individually rational**: under truthful reporting (each identity a distinct real user reporting its type) every user's utility (2) is $\ge0$.
--   - **Feasible** (§2, Eq. (41)): there are a signed residual pool input $p\in(-b,+\infty)$ and burns $B_Y,B_X\ge0$ with
--   $$\sum_{\text{sell-Y}}y_i=\sum_{\text{sell-X}}y_j+p+B_Y,\qquad \sum_{\text{sell-X}}x_j+F(p)=\sum_{\text{sell-Y}}x_i+B_X.$$
--   - **UIC** (for a mechanism on ordered blocks and a prescribed ordering $\pi$): for all other identities $O$ with arbitrary reports, every real user of true type $t$ (either direction), and every finite, possibly empty set $D$ of fresh identities with arbitrary reports in either direction, the user's utility (2) from $D$ (block $D\cup O$ in the prescribed order) is at most its utility from one fresh truthful identity (block $O\cup\{i_0\}$ in the prescribed order).
--   - **Strategy-proof for a builder-as-user**: the same, where the deviating builder also chooses any order of the whole block $D\cup O$ (no censorship: every other bid stays); honest = truthful single identity in the prescribed order.
--   - **Strategy-proof for a builder** (no intrinsic demand): valued as a zero-value zero-budget user of either direction, no injected set $D$ with any order of $D\cup O$ gives it positive utility (honest = no bid, utility $0$).
--   - **Order-insensitive**: the outcome is invariant under permuting the block.
--   - **Pareto optimal for eligible users** (truthful block, final pool input $p_e$): (a) no subset $T$ of eligible users has new positions (sell-Y: receive $x'\ge0$ of $X$ for $0\le y'\le q$ of $Y$; sell-X: receive $y'\ge0$ of $Y$ for $0\le x'\le r$ of $X$) whose total net $X$ and total net $Y$ do not exceed those of $T$ in the outcome, that weakly improve every member and strictly improve one (utility $x'-vy'$, resp. $y'-ux'$); (b) no eligible user has a trade with the pool along $F$ from $p_e$ — sending a signed $\delta$ of $Y$ with $p_e+\delta>-b$ and receiving $F(p_e+\delta)-F(p_e)$ of $X$ — that keeps its position within direction and budget and strictly improves its utility.
--
--   **Formalization Note.** Positions are written as (net $X$, net $Y$) received; within direction and budget neither catastrophic case of (2) applies, so the linear utility is Eq. (2). The reading of "trade" in Pareto optimality is the paper's own in App. C (Eqs. (53)–(54)): any reallocation within direction and budget, including handing back received tokens and unwinding a pool trade.
-- source:
--   Shi, Zhang, Chung, Li, Otter: A Provably MEV-Resilient Automated Market Maker via Surplus Redistribution, arXiv:2609.03474 (held copy sha256 3a05f18a…), p. 5, §2 (PDF 7); pp. 6–8, §2.1 and §2.3 (PDF 8–10); p. 34, App. A (PDF 36); p. 35, Eq. (41) (PDF 37)

import Mathlib
import Definitions.Def_OtterAMM_TwoSided_Curve
import Definitions.Def_OtterAMM_TwoSided_Model

set_option autoImplicit false

namespace OtterAMM.TwoSided

/-- Well-formedness of one identity's outcome `o = (x, y)` (§2 ranges, nonnegative compensation,
and the spot-rate cap of Eqs. (16), (7)): a sell-Y identity has `0 ≤ y ≤ q̃` and
`0 ≤ x ≤ σ0·y`; a sell-X identity has `0 ≤ x ≤ r̃` and `0 ≤ y ≤ ρ0·x`. -/
def WFOutcome (C : PricingCurve) (r : Report) (o : ℝ × ℝ) : Prop :=
  match r.dir with
  | .sellY => 0 ≤ o.2 ∧ o.2 ≤ r.budget ∧ 0 ≤ o.1 ∧ o.1 ≤ C.σ0 * o.2
  | .sellX => 0 ≤ o.1 ∧ o.1 ≤ r.budget ∧ 0 ≤ o.2 ∧ o.2 ≤ C.ρ0 * o.1

/-- The mechanism is well-formed on every finite block with reports in `ℝ²≥0`. -/
def WellFormed (C : PricingCurve) (m : UMechanism) : Prop :=
  ∀ (S : Finset Ident) (rep : Ident → Report), ValidOn S rep →
    ∀ i ∈ S, WFOutcome C (rep i) (m S rep i)

/-- Individual rationality: under truthful reporting (each identity of the block is a distinct
real user whose report is its type) every user's utility (Eq. (2)) is `≥ 0`. -/
def IndividuallyRational (m : UMechanism) : Prop :=
  ∀ (S : Finset Ident) (rep : Ident → Report), ValidOn S rep →
    ∀ i ∈ S, (0 : EReal) ≤ util (rep i) rep (m S rep) {i}

/-- Feasibility of an outcome (§2; Eq. (41)): there are a signed residual pool input
`p ∈ (−b, +∞)` and burns `B_Y, B_X ≥ 0` with
`Σ_{sell-Y} y_i = Σ_{sell-X} y_j + p + B_Y` and `Σ_{sell-X} x_j + F(p) = Σ_{sell-Y} x_i + B_X`. -/
def FeasibleOutcome (C : PricingCurve) (S : Finset Ident) (rep : Ident → Report) (out : Outcome) :
    Prop :=
  ∃ p BY BX : ℝ, -C.b < p ∧ 0 ≤ BY ∧ 0 ≤ BX ∧
    flowSY rep out S = flowRY rep out S + p + BY ∧
    flowSX rep out S + C.F p = flowRX rep out S + BX

/-- The mechanism is feasible on every finite block with reports in `ℝ²≥0`. -/
def Feasible (C : PricingCurve) (m : UMechanism) : Prop :=
  ∀ (S : Finset Ident) (rep : Ident → Report), ValidOn S rep → FeasibleOutcome C S rep (m S rep)

/-- User incentive compatibility (§2.1, §2.3 (1)). Fix the other identities `O` and their reports
`rep` (arbitrary, in `ℝ²≥0`), and a real user of true type `t` (either direction). Truthful
behaviour: one fresh identity `i0` reporting `t`. Deviation: any finite (possibly empty) set `D`
of fresh identities with arbitrary reports `dev` in `ℝ²≥0` and either direction. The block is
ordered by the prescribed rule `π`. The deviation's utility (Eq. (2), from the aggregate flows of
`D`) never exceeds the truthful utility. -/
def UIC (mech : Mechanism) (π : OrderRule) : Prop :=
  ∀ (O : Finset Ident) (rep : Ident → Report) (t : Report) (i0 : Ident) (D : Finset Ident)
    (dev : Ident → Report),
    ValidOn O rep → t.Valid → i0 ∉ O → Disjoint D O → ValidOn D dev →
    util t (overlay D dev rep) (mech (π (D ∪ O) (overlay D dev rep)) (overlay D dev rep)) D ≤
      util t (Function.update rep i0 t)
        (mech (π (insert i0 O) (Function.update rep i0 t)) (Function.update rep i0 t)) {i0}

/-- Strategy-proofness for a builder-as-user (§2.1, §2.3 (2)): as in `UIC`, but the deviating
builder also chooses any order `ℓ` of the whole block `D ∪ O` (it cannot drop another identity's
bid: no censorship); honest behaviour is the truthful single identity in the prescribed order. -/
def BuilderAsUserSP (mech : Mechanism) (π : OrderRule) : Prop :=
  ∀ (O : Finset Ident) (rep : Ident → Report) (t : Report) (i0 : Ident) (D : Finset Ident)
    (dev : Ident → Report) (ℓ : List Ident),
    ValidOn O rep → t.Valid → i0 ∉ O → Disjoint D O → ValidOn D dev →
    ℓ.Nodup → ℓ.toFinset = D ∪ O →
    util t (overlay D dev rep) (mech ℓ (overlay D dev rep)) D ≤
      util t (Function.update rep i0 t)
        (mech (π (insert i0 O) (Function.update rep i0 t)) (Function.update rep i0 t)) {i0}

/-- Strategy-proofness for a builder without intrinsic demand: such a builder is valued as a
zero-budget, zero-value user of either direction (as in Fact 27); honest behaviour (no bid,
prescribed order) gives it utility `0`, and no set `D` of injected identities with any order `ℓ`
of the uncensored block gives it more. -/
def BuilderSP (mech : Mechanism) : Prop :=
  ∀ (d : Dir) (O : Finset Ident) (rep : Ident → Report) (D : Finset Ident)
    (dev : Ident → Report) (ℓ : List Ident),
    ValidOn O rep → Disjoint D O → ValidOn D dev → ℓ.Nodup → ℓ.toFinset = D ∪ O →
    util ⟨d, 0, 0⟩ (overlay D dev rep) (mech ℓ (overlay D dev rep)) D ≤ 0

/-- The mechanism treats the input bids as an unordered set (App. A, Fact 26). -/
def OrderInsensitive (mech : Mechanism) : Prop :=
  ∀ (ℓ ℓ' : List Ident) (rep : Ident → Report), ℓ.Perm ℓ' → mech ℓ rep = mech ℓ' rep

/-- Net `X` received by an identity with outcome `o`. -/
def netX (r : Report) (o : ℝ × ℝ) : ℝ :=
  match r.dir with
  | .sellY => o.1
  | .sellX => -o.1

/-- Net `Y` received by an identity with outcome `o`. -/
def netY (r : Report) (o : ℝ × ℝ) : ℝ :=
  match r.dir with
  | .sellY => -o.2
  | .sellX => o.2

/-- A final position (net `X`, net `Y`) stays in the declared direction and budget:
sell-Y `(v, q)`: receives `x' ≥ 0` of `X` for `0 ≤ y' ≤ q` of `Y`;
sell-X `(u, r)`: receives `y' ≥ 0` of `Y` for `0 ≤ x' ≤ r` of `X`. -/
def PosOK (r : Report) (nx ny : ℝ) : Prop :=
  match r.dir with
  | .sellY => 0 ≤ nx ∧ -r.budget ≤ ny ∧ ny ≤ 0
  | .sellX => 0 ≤ ny ∧ -r.budget ≤ nx ∧ nx ≤ 0

/-- Eq. (2) utility of a position satisfying `PosOK` (where neither catastrophic case applies):
`ΔX + v·ΔY` for sell-Y, `ΔY + u·ΔX` for sell-X. -/
def linUtil (r : Report) (nx ny : ℝ) : ℝ :=
  match r.dir with
  | .sellY => nx + r.ask * ny
  | .sellX => ny + r.ask * nx

/-- Pareto optimality for eligible users (§2.3 (3)) of the outcome `out` of the truthful block
`S` (each identity a distinct user whose report is its type), with final signed pool input `pe`:
(a) no subset `T` of eligible users has a reallocation among themselves (new positions within
direction and budget, the total net `X` and the total net `Y` of `T` not increased) that weakly
improves every member and strictly improves one;
(b) no eligible user has a trade with the pool along `F` from `pe` (sending a signed `δ` of `Y`,
receiving `F(pe + δ) − F(pe)` of `X`, `pe + δ ∈ (−b, +∞)`), staying within direction and budget,
that strictly improves its utility. -/
def ParetoEligibleOutcome (C : PricingCurve) (S : Finset Ident) (rep : Ident → Report)
    (out : Outcome) (pe : ℝ) : Prop :=
  (¬ ∃ (T : Finset Ident) (nx ny : Ident → ℝ),
      (∀ i ∈ T, i ∈ S ∧ (rep i).Eligible C) ∧
      (∀ i ∈ T, PosOK (rep i) (nx i) (ny i)) ∧
      ∑ i ∈ T, nx i ≤ ∑ i ∈ T, netX (rep i) (out i) ∧
      ∑ i ∈ T, ny i ≤ ∑ i ∈ T, netY (rep i) (out i) ∧
      (∀ i ∈ T, linUtil (rep i) (netX (rep i) (out i)) (netY (rep i) (out i)) ≤
        linUtil (rep i) (nx i) (ny i)) ∧
      ∃ i ∈ T, linUtil (rep i) (netX (rep i) (out i)) (netY (rep i) (out i)) <
        linUtil (rep i) (nx i) (ny i)) ∧
  (¬ ∃ i ∈ S, (rep i).Eligible C ∧ ∃ δ : ℝ, -C.b < pe + δ ∧
      PosOK (rep i) (netX (rep i) (out i) + (C.F (pe + δ) - C.F pe)) (netY (rep i) (out i) - δ) ∧
      linUtil (rep i) (netX (rep i) (out i)) (netY (rep i) (out i)) <
        linUtil (rep i) (netX (rep i) (out i) + (C.F (pe + δ) - C.F pe))
          (netY (rep i) (out i) - δ))

/-- Pareto optimality for eligible users on every truthful finite block, `pe S rep` being the
mechanism's final signed pool input. -/
def ParetoEligible (C : PricingCurve) (m : UMechanism)
    (pe : Finset Ident → (Ident → Report) → ℝ) : Prop :=
  ∀ (S : Finset Ident) (rep : Ident → Report), ValidOn S rep →
    ParetoEligibleOutcome C S rep (m S rep) (pe S rep)

end OtterAMM.TwoSided


