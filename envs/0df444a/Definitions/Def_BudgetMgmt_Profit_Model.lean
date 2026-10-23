-- Prove2me | Definitions.Def_BudgetMgmt_Profit_Model
-- name    : BudgetMgmt_Profit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:53:47.999553+00:00
-- url     : https://prove2.me/theorems/6d9aa7c8-7ad2-4d29-9fb5-5a3a522dfc4f
-- title:
--   §2, Table 1, Definition 2.1, Definition A.1, Assumption 1, pp. 5–9, 21, ec 4–9 — symmetric correlated instances, thresholding, reserve pricing, bid shading, system equilibria
-- statement:
--   The model of Balseiro, Kim, Mahdian and Mirrokni, *Budget Management Strategies in Repeated Auctions* (§2, §4), in the **symmetric correlated setting**.
--
--   **Instance.** A seller sells $T>0$ items, one per round, to $n\ge 1$ buyers, at an opportunity cost $c>0$ per item. Each buyer has the same budget $B_1>0$ on his expected total expenditure. In each round the values $x=(x_1,\dots,x_n)$ are drawn from a joint law $F$ with density $f$ on the box $[0,\bar v)^n$ ($\bar v\le\infty$; $X_1=[0,\bar v)$ is each buyer's support), where $c<\bar v$, $f$ is continuous on the box, positive on its interior, zero outside it, integrates to $1$, is **exchangeable** ($f(x_{\sigma(1)},\dots,x_{\sigma(n)})=f(x)$ for every permutation $\sigma$), and $\mathbb E[x_i]<\infty$.
--
--   **Mechanisms (Table 1).** Each buyer $i$ has a parameter $s_i$. With $d_i^{q}=\max_{j\ne i:\,x_j\ge s_j}x_j$ (competitors at or above their own parameter) and $d_i^{S}=\max_{j\ne i}x_j/(1+\mu_j)$:
--   1. **Thresholding** ($\tau_i\ge c$): $i$ wins if $x_i\ge d_i^q\vee\tau_i$ and pays $d_i^q\vee c$.
--   2. **Reserve pricing** ($r_i\ge c$): $i$ wins if $x_i\ge d_i^q\vee r_i$ and pays $d_i^q\vee r_i$.
--   3. **Bid shading** ($\mu_i\ge 0$): $i$ wins if $x_i/(1+\mu_i)\ge d_i^S\vee c$ and pays $d_i^S\vee c$.
--
--   The allocation $Q_i(x;s)\in\{0,1\}$ gives the item to a winner, and the payment is $M_i(x;s)=Q_i(x;s)\cdot$price.
--
--   **Objectives (pp. 6–7).** $G_i(s)=T\,\mathbb E[M_i(x;s)]$ (expenditure), $V_i(s)=T\,\mathbb E[x_iQ_i(x;s)]$, $U_i=V_i-G_i$, $I(s)=T\sum_i\mathbb E[Q_i(x;s)]$ (items sold) and the seller's profit
--   $$P(s)=\sum_{i=1}^n G_i(s)-c\,I(s).$$
--   At a symmetric profile $s_1\vec 1$, $G_1(s_1)$ is buyer 1's expenditure; $F(z)=\mathbb P(x\le z)$ is the joint CDF.
--
--   **Generalized failure rate and Assumption 1 (p. ec 8).** $\xi_i(z_i,z_{-i})=z_if_i(z_i\mid x_{-i}\le z_{-i})/\bar F_i(z_i\mid x_{-i}\le z_{-i})$. Assumption 1: each $\xi_i$ is jointly continuous, and $z_i\mapsto\xi_i(z_i,z_i\vee z_{-i})$ is strictly increasing for every $z_{-i}\in X_{-i}$.
--
--   **System equilibria.** On a rectangular parameter space $[\underline s,\bar s]^n$, $s^*$ is a **system equilibrium** (Definition 2.1) if for each buyer $i$
--   $$s_i^*\in\arg\max_{s_i\in[\underline s,\bar s]}U_i(s_i,s_{-i}^*)\quad\text{s.t. } G_i(s_i,s_{-i}^*)\le B_1 .$$
--   For reserve pricing the space is $S'=\{r: r_i\in[c,\bar r],\ r_i\ge \underline r_i(r_{-i})\}$ with $\underline r_i(r_{-i})$ the solution of $\xi_i(r_i,r_i\vee r_{-i})=1$, and $r^*$ is a **restricted system equilibrium** (Definition A.1) if each $r_i^*$ maximizes $U_i(\cdot,r^*_{-i})$ over $r_i\in[c,\bar r]$ subject to the budget and $r_i\ge\underline r_i(r^*_{-i})$. Symmetric equilibria are those of the form $s_1\vec 1$; $\hat S_1=\{r_1: r_1\vec 1\in S'\}$.
--
--   **Admissible upper ends.** The lower ends are Table 1's ($c$, $c$, $0$). An upper end $\bar\tau$ (resp. $\bar\mu$, $\bar r$) is admissible if it lies in the support ($\bar\tau\le\bar v$, $(1+\bar\mu)c\le\bar v$, $\bar r\le\bar v$) and every buyer meets his budget at the upper end whatever the others' parameters in the space; for reserve pricing also $\bar r\ge\underline r_i(r_{-i})$. These are the conditions the proof of Theorem 3.2 imposes (pp. ec 5, ec 7, ec 9).
--
--   **Formalization Note** The law of the values is Lebesgue measure on $\mathbb R^n$ with density $f$; expectations are Bochner integrals. Every payment lies between $0$ and the winner's value (bid shading: at most $x_i/(1+\mu_i)$) on the profiles of the parameter spaces, so $\mathbb E[x_i]<\infty$ makes all expectations genuine. Ties, which have probability zero, are broken in favour of the lowest index. The empty competing maximum is $0$; it is always combined with $\vee c$, $\vee\tau_i$ or $\vee r_i$ and values are nonnegative, so it is harmless. The constraint $r_i\ge\underline r_i(r_{-i})$ is written $\xi_i(r_i,r_i\vee r_{-i})\ge 1$, as on p. ec 9, and is vacuous at $r_i=\bar v$ (bounded support), where $\xi_i$'s denominator vanishes. $\xi_i$ is written $z_i\,\partial_t\mathbb P(x_i\le t,x_{-i}\le z_{-i})|_{t=z_i}/\mathbb P(x_i\ge z_i,x_{-i}\le z_{-i})$, the page's ratio after cancelling $\mathbb P(x_{-i}\le z_{-i})$. Assumption 1 is read on the interior of the support, where every conditional law is non-degenerate.
-- source:
--   Balseiro, Kim, Mahdian & Mirrokni, Budget management strategies in repeated auctions, SSRN 2858261 (version of July 8, 2020), pp. 5–9 (§2, Table 1 p. 9, Definition 2.1 p. 7), pp. 21–22 (§4), pp. ec 4–9 (parameter spaces, Definition A.1, Assumption 1)

import Mathlib

namespace BudgetMgmt.Profit

open MeasureTheory

/-- The symmetric correlated problem instance (Balseiro–Kim–Mahdian–Mirrokni, §2, p. 5, and §4,
p. 21): `n` buyers, `T > 0` items, opportunity cost `c > 0` per item, a common budget `B > 0`, and
buyers' values `x = (x₁, …, xₙ)` with a joint density `f` supported on the box `[0, v̄)ⁿ`, positive on
its interior and continuous on it, exchangeable (invariant under every permutation of the buyers), and
with finite first moments. `vbar = ⊤` is an unbounded support. The opportunity cost lies in the
interior of the support (`c < v̄`). -/
structure SymInstance (n : ℕ) where
  /-- opportunity cost per item -/
  c : ℝ
  /-- number of items (rounds) -/
  T : ℕ
  /-- common budget `B₁` -/
  B : ℝ
  /-- supremum of each buyer's support `X₁ = [0, v̄)` (`⊤`: unbounded) -/
  vbar : ENNReal
  /-- joint density of the values -/
  f : (Fin n → ℝ) → ℝ
  c_pos : 0 < c
  T_pos : 0 < T
  B_pos : 0 < B
  c_lt_vbar : ENNReal.ofReal c < vbar
  f_nonneg : ∀ x, 0 ≤ f x
  f_measurable : Measurable f
  f_zero_off : ∀ x, ¬ (∀ i, 0 ≤ x i ∧ ENNReal.ofReal (x i) < vbar) → f x = 0
  f_pos : ∀ x, (∀ i, 0 < x i ∧ ENNReal.ofReal (x i) < vbar) → 0 < f x
  f_cont : ContinuousOn f {x | ∀ i, 0 ≤ x i ∧ ENNReal.ofReal (x i) < vbar}
  f_integral : ∫ x, f x = 1
  f_exch : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ), f (x ∘ σ) = f x
  moment : ∀ i, Integrable (fun x : Fin n → ℝ => x i)
    (volume.withDensity (fun x => ENNReal.ofReal (f x)))

variable {n : ℕ}

/-- The law `F` of the value vector: Lebesgue measure on `ℝⁿ` with density `f`. -/
noncomputable def SymInstance.law (P : SymInstance n) : Measure (Fin n → ℝ) :=
  volume.withDensity (fun x => ENNReal.ofReal (P.f x))

/-- A buyer's support `X₁ = [0, v̄)`. -/
def SymInstance.supp (P : SymInstance n) : Set ℝ :=
  {t | 0 ≤ t ∧ ENNReal.ofReal t < P.vbar}

/-- The three budget management mechanisms of Table 1 (p. 9) compared in Theorem 4.2, part 1. -/
inductive Mech
  | thresholding
  | reserve
  | shading
  deriving DecidableEq

/-- The highest competing value among the rivals `j ≠ i` whose value is at least their own parameter,
`max_{j ≠ i : x_j ≥ s_j} x_j` (thresholding and reserve pricing, Table 1); `0` when no rival
qualifies. -/
noncomputable def compQual (s x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (Finset.univ.filter (fun j => j ≠ i ∧ s j ≤ x j)).fold max 0 x

/-- The highest competing shaded bid `max_{j ≠ i} x_j/(1 + μ_j)` (bid shading, Table 1); `0` when there
is no rival. -/
noncomputable def compShaded (s x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (Finset.univ.filter (fun j => j ≠ i)).fold max 0 (fun j => x j / (1 + s j))

/-- Buyer `i`'s winning condition under mechanism `m` with parameter profile `s` and values `x`
(Table 1, p. 9):
* thresholding: `x_i ≥ max_{j≠i: x_j ≥ τ_j} x_j ∨ τ_i`;
* reserve pricing: `x_i ≥ max_{j≠i: x_j ≥ r_j} x_j ∨ r_i`;
* bid shading: `x_i/(1+μ_i) ≥ max_{j≠i} x_j/(1+μ_j) ∨ c`. -/
def wins (c : ℝ) : Mech → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → Prop
  | .thresholding, s, x, i => max (compQual s x i) (s i) ≤ x i
  | .reserve, s, x, i => max (compQual s x i) (s i) ≤ x i
  | .shading, s, x, i => max (compShaded s x i) c ≤ x i / (1 + s i)

/-- Buyer `i`'s price when he wins (Table 1, p. 9):
* thresholding: `max_{j≠i: x_j ≥ τ_j} x_j ∨ c`;
* reserve pricing: `max_{j≠i: x_j ≥ r_j} x_j ∨ r_i`;
* bid shading: `max_{j≠i} x_j/(1+μ_j) ∨ c`. -/
noncomputable def price (c : ℝ) : Mech → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ
  | .thresholding, s, x, i => max (compQual s x i) c
  | .reserve, s, x, i => max (compQual s x i) (s i)
  | .shading, s, x, i => max (compShaded s x i) c

open Classical in
/-- The allocation rule `Q_i(x; s) ∈ {0, 1}`: buyer `i` gets the item if he wins and no buyer of lower
index wins (ties, which have probability zero, are broken by index). -/
noncomputable def alloc (c : ℝ) (m : Mech) (s x : Fin n → ℝ) (i : Fin n) : ℝ :=
  if wins c m s x i ∧ ∀ j, j < i → ¬ wins c m s x j then 1 else 0

/-- The payment rule `M_i(x; s) = Q_i(x; s) · price`. -/
noncomputable def payment (c : ℝ) (m : Mech) (s x : Fin n → ℝ) (i : Fin n) : ℝ :=
  alloc c m s x i * price c m s x i

/-- Expected expenditure of buyer `i` over the horizon, `G_i(s) = T 𝔼[M_i(x; s)]` (p. 6). -/
noncomputable def expend (P : SymInstance n) (m : Mech) (s : Fin n → ℝ) (i : Fin n) : ℝ :=
  P.T * ∫ x, payment P.c m s x i ∂P.law

/-- Gross value of buyer `i`, `V_i(s) = T 𝔼[x_i Q_i(x; s)]` (p. 6). -/
noncomputable def grossValue (P : SymInstance n) (m : Mech) (s : Fin n → ℝ) (i : Fin n) : ℝ :=
  P.T * ∫ x, x i * alloc P.c m s x i ∂P.law

/-- Expected utility of buyer `i`, `U_i(s) = V_i(s) − G_i(s)` (p. 7). -/
noncomputable def utility (P : SymInstance n) (m : Mech) (s : Fin n → ℝ) (i : Fin n) : ℝ :=
  grossValue P m s i - expend P m s i

/-- Expected number of items sold, `I(s) = T ∑ᵢ 𝔼[Q_i(x; s)]` (p. 7). -/
noncomputable def itemsSold (P : SymInstance n) (m : Mech) (s : Fin n → ℝ) : ℝ :=
  P.T * ∑ i, ∫ x, alloc P.c m s x i ∂P.law

/-- The seller's profit, `P(s) = ∑ᵢ G_i(s) − c I(s)` (p. 7). -/
noncomputable def profit (P : SymInstance n) (m : Mech) (s : Fin n → ℝ) : ℝ :=
  (∑ i, expend P m s i) - P.c * itemsSold P m s

/-- The symmetric profile `s₁ 1⃗` (p. 21). -/
def sym (s₁ : ℝ) : Fin n → ℝ := fun _ => s₁

/-- Expected expenditure of one buyer (the reference buyer `0`, the paper's buyer 1) when every buyer
has parameter `s₁`, `G₁(s₁)` (p. 21). -/
noncomputable def G1 (P : SymInstance n) [NeZero n] (m : Mech) (s₁ : ℝ) : ℝ :=
  expend P m (sym s₁) 0

/-- The joint CDF `F(z) = ℙ(x ≤ z)`. -/
noncomputable def cdf (P : SymInstance n) (z : Fin n → ℝ) : ℝ :=
  P.law.real {x | ∀ j, x j ≤ z j}

/-- The generalized failure rate of buyer `i`'s conditional distribution given `x_{−i} ≤ z_{−i}`
(p. ec 8), `ξ_i(z_i, z_{−i}) = z_i f_i(z_i | x_{−i} ≤ z_{−i}) / F̄_i(z_i | x_{−i} ≤ z_{−i})`, written as
`z_i · ∂_t ℙ(x_i ≤ t, x_{−i} ≤ z_{−i})|_{t = z_i} / ℙ(x_i ≥ z_i, x_{−i} ≤ z_{−i})` (the factor
`ℙ(x_{−i} ≤ z_{−i})` cancels). -/
noncomputable def xi (P : SymInstance n) (i : Fin n) (z : Fin n → ℝ) : ℝ :=
  z i * deriv (fun t => P.law.real {x | x i ≤ t ∧ ∀ j, j ≠ i → x j ≤ z j}) (z i) /
    P.law.real {x | z i ≤ x i ∧ ∀ j, j ≠ i → x j ≤ z j}

/-- The point `(t, t ∨ z_{−i})`: coordinate `i` is `t`, every other coordinate `j` is `max t (z j)`. -/
def diagPt (i : Fin n) (t : ℝ) (z : Fin n → ℝ) : Fin n → ℝ :=
  fun j => if j = i then t else max t (z j)

/-- Assumption 1 (p. ec 8–9): (1) each `ξ_i` is jointly continuous in `z` (on the interior of the
support, where every conditional law is non-degenerate); (2) for each `i` and `z_{−i} ∈ X_{−i}`,
`ξ_i(z_i, z_i ∨ z_{−i})` is strictly increasing in `z_i` (on the interior of `X_i`). -/
def Assumption1 (P : SymInstance n) : Prop :=
  (∀ i, ContinuousOn (xi P i) {z | ∀ j, 0 < z j ∧ ENNReal.ofReal (z j) < P.vbar}) ∧
  ∀ i (z : Fin n → ℝ), (∀ j, j ≠ i → z j ∈ P.supp) →
    StrictMonoOn (fun t => xi P i (diagPt i t z)) {t | 0 < t ∧ ENNReal.ofReal t < P.vbar}

/-- Reserve pricing's lower-bound constraint `r_i ≥ r̲_i(r_{−i})` of the restricted space `S'`
(p. ec 9), written through `ξ_i(r_i, r_i ∨ r_{−i}) ≥ 1` ("Note ξ_i(r_i, r_i ∨ r_{−i}) ≥ 1 if
r_i ≥ r̲_i(r_{−i}), and ξ_i(r_i, r_i ∨ r_{−i}) < 1 if r_i < r̲_i(r_{−i})"); at the top of a bounded
support, where `ξ_i`'s denominator vanishes, the constraint holds (`r̲_i(r_{−i})` is interior,
Claim A.4). -/
def ResConstr (P : SymInstance n) (r : Fin n → ℝ) (i : Fin n) : Prop :=
  ENNReal.ofReal (r i) < P.vbar → 1 ≤ xi P i (diagPt i (r i) r)

/-- System equilibrium (Definition 2.1, p. 7) on the rectangular parameter space `[lo, hi]ⁿ`: the
profile lies in the space and each buyer's parameter maximizes his utility over his own parameter
space, others fixed, subject to his budget. -/
def IsSysEq (P : SymInstance n) (m : Mech) (lo hi : ℝ) (s : Fin n → ℝ) : Prop :=
  (∀ j, s j ∈ Set.Icc lo hi) ∧
  ∀ i, expend P m s i ≤ P.B ∧
    ∀ t ∈ Set.Icc lo hi, expend P m (Function.update s i t) i ≤ P.B →
      utility P m (Function.update s i t) i ≤ utility P m s i

/-- Restricted system equilibrium (Definition A.1, p. ec 8) for reserve pricing in the correlated
setting with upper end `r̄` (p. ec 9): parameters in `[c, r̄]`, each buyer's parameter satisfying the
lower-bound constraint `r_i ≥ r̲_i(r_{−i})` and maximizing his utility over the deviations `t ∈ [c, r̄]`
that satisfy the same constraint and his budget, others fixed. -/
def IsRestrictedSysEq (P : SymInstance n) (rbar : ℝ) (r : Fin n → ℝ) : Prop :=
  (∀ j, r j ∈ Set.Icc P.c rbar) ∧
  ∀ i, ResConstr P r i ∧ expend P .reserve r i ≤ P.B ∧
    ∀ t ∈ Set.Icc P.c rbar, ResConstr P (Function.update r i t) i →
      expend P .reserve (Function.update r i t) i ≤ P.B →
      utility P .reserve (Function.update r i t) i ≤ utility P .reserve r i

/-- A symmetric system equilibrium `s₁ 1⃗` (p. 21) of a rectangular-space mechanism. -/
def IsSymSysEq (P : SymInstance n) (m : Mech) (lo hi s₁ : ℝ) : Prop :=
  IsSysEq P m lo hi (sym s₁)

/-- A symmetric restricted system equilibrium `r₁ 1⃗` of reserve pricing. -/
def IsSymRestrictedSysEq (P : SymInstance n) (rbar r₁ : ℝ) : Prop :=
  IsRestrictedSysEq P rbar (sym r₁)

/-- Admissible upper end `τ̄` of thresholding's parameter space `[c, τ̄]` (p. ec 7): inside the support
(`τ̄ = sup X_i` for a bounded support) and every buyer's budget is met at `τ̄` whatever the others'
parameters in `[c, τ̄]`. -/
def AdmissibleT (P : SymInstance n) (taubar : ℝ) : Prop :=
  P.c ≤ taubar ∧ ENNReal.ofReal taubar ≤ P.vbar ∧
  ∀ s : Fin n → ℝ, (∀ j, s j ∈ Set.Icc P.c taubar) →
    ∀ i, expend P .thresholding (Function.update s i taubar) i ≤ P.B

/-- Admissible upper end `μ̄` of bid shading's parameter space `[0, μ̄]` (p. ec 4–5): `(1 + μ̄) c` in the
support (`μ̄ = sup X_i / c − 1` for a bounded support) and every buyer's budget is met at `μ̄` whatever
the others' parameters in `[0, μ̄]`. -/
def AdmissibleS (P : SymInstance n) (mubar : ℝ) : Prop :=
  0 ≤ mubar ∧ ENNReal.ofReal ((1 + mubar) * P.c) ≤ P.vbar ∧
  ∀ s : Fin n → ℝ, (∀ j, s j ∈ Set.Icc 0 mubar) →
    ∀ i, expend P .shading (Function.update s i mubar) i ≤ P.B

/-- Admissible upper end `r̄` of reserve pricing's parameter space (p. ec 9, Claims A.6–A.7): inside
the support (`r̄ = sup X_i` for a bounded support), and for every buyer and every profile of the others
in `[c, r̄]`, the upper end satisfies the lower-bound constraint (`r̄ ≥ r̲_i(r_{−i})`) and meets the
budget. -/
def AdmissibleR (P : SymInstance n) (rbar : ℝ) : Prop :=
  P.c ≤ rbar ∧ ENNReal.ofReal rbar ≤ P.vbar ∧
  ∀ r : Fin n → ℝ, (∀ j, r j ∈ Set.Icc P.c rbar) →
    ∀ i, ResConstr P (Function.update r i rbar) i ∧
      expend P .reserve (Function.update r i rbar) i ≤ P.B

/-- Reserve pricing's symmetric parameter space `Ŝ₁ = {r₁ : r₁ 1⃗ ∈ S'}` (p. 21, p. ec 41). -/
def ShatR (P : SymInstance n) (rbar : ℝ) : Set ℝ :=
  {r | r ∈ Set.Icc P.c rbar ∧ ∀ i, ResConstr P (sym r) i}

end BudgetMgmt.Profit


