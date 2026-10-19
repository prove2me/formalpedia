-- Prove2me | Definitions.Def_CrowdTarget_Separating_Setting
-- name    : CrowdTarget_Separating_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:28.660621+00:00
-- url     : https://prove2.me/theorems/958542bc-5da5-4986-a669-5d17f22ef71d
-- title:
--   Rewards-based crowdfunding with a target and a price: the signaling game
-- statement:
--   A creator runs an all-or-nothing (fixed funding) campaign whose reward is one unit of her product. Her type $i\in\{H,L\}$ (high or low quality) is private. Backers value the two products at $v_H>v_L$, and the type-$i$ creator must pay a fixed startup cost $S_i$, with $S_H\ge S_L$. The number of interested backers is $N\sim U[0,\bar N]$. Throughout, $0<\bar N$, $0<v_L<v_H$, $0<S_L\le S_H$, $S_L<\bar N v_L$ and $S_H<\bar N v_H$.
--
--   The creator chooses a **design** $(C,p)$: a funding target $C$ and a reward price $p$. A design is feasible for type $i$ if $C\ge S_i$ (the funding constraint) and $p>0$.
--
--   A fraction $1-\alpha$ of the backers is **informed**: they know the type and pledge iff $p\le v_i$. The remaining fraction $\alpha\in[0,1]$ is **uninformed**: they see only $(C,p)$, believe the type is $H$ or $L$, and pledge iff $p$ is at most the believed valuation. If a share $k$ of the $N$ backers pledges, the campaign succeeds iff $kpN\ge C$; the creator then collects $kpN$ and pays $S_i$, and otherwise everything is refunded. Her expected profit is (1):
--   $$
--   \Pi=\int_{\{N\in[0,\bar N]\,:\,C\le kpN\}}\frac{kpN-S_i}{\bar N}\,dN .
--   $$
--
--   A **separating equilibrium** is a pair of distinct feasible designs $d_L$, $d_H$ such that, with the uninformed backers believing $H$ exactly at $d_H$ and $L$ at every other design: the L-type earns no more at any other design believed $L$, nor by mimicking $d_H$ (believed $H$), than at $d_L$; and the H-type earns no more at any feasible design $d\ne d_H$ (believed $L$) than at $d_H$. It **survives the intuitive criterion** if there is no off-path design $d$ at which one type is strictly better off when recognized as her true type, while the other type is strictly worse off at $d$ under either belief.
--
--   Finally,
--   $$
--   B=v_L+\frac{S_L^2}{\bar N^2v_L},\qquad \alpha^*=\frac{B+\sqrt{B^2+4\frac{S_H^2-2S_LS_H}{\bar N^2}}}{2v_H},
--   $$
--   $$
--   C^*(\alpha)=\begin{cases}S_H,&\alpha\le\alpha^*,\\ S_L+\sqrt{S_L^2+\bar N^2(\alpha^2v_H^2-\alpha v_HB)},&\text{otherwise},\end{cases}
--   \qquad p_{1,2}(C)=\frac{B\mp\sqrt{B^2+4\frac{C^2-2S_LC}{\bar N^2}}}{2\alpha}.
--   $$
--
--   These objects carry every statement of the mission: Propositions 1 and 3 and the steps of their proofs.
--
--   **Formalization Note** The positivity of $\bar N$, $v_L$, $S_L$ is implicit in the paper (p. 9: "positive fixed costs"). Profit is integrated over the success event, which gives $0$ when the campaign cannot succeed, also when nobody pledges. The pricing constraint $p\le v_i$ is not part of feasibility: prices above every pledging threshold simply get no pledges. $\alpha$ is not a parameter of the structure; statements quantify over $\alpha\in[0,1]$. $C^*$ is the explicit formula (5), not a root.
-- source:
--   Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), pp. 6–15, §3.1–§4, (1), (2), (3), (5); Online Supplement p. 4, (6)–(7)

import Mathlib

/-!
# Signaling to the Crowd: the target-signaling game

Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), pp. 6–15, §3.1–§4
(model, (1), (2), (3), (5)) and Online Supplement pp. 1–5, (6)–(7).

**Formalization Note.**
* `Params.Standing` makes explicit the positivity the paper uses without stating it
  (`0 < N̄`, `0 < v_L`, `0 < S_L`; p. 9 "We model positive ﬁxed costs") together with
  `v_H > v_L` (p. 7), `S_H ≥ S_L` (p. 9) and `S_i < N̄ v_i` (p. 10).
* The uninformed fraction `α` is not a field: statements quantify over `α ∈ [0, 1]`.
* Expected profit (1) is the integral of `(k p N − S)/N̄` over the success event
  `{N ∈ [0, N̄] : C ≤ k p N}`, where `k` is the share of backers who pledge; this is the
  all-or-nothing rule of p. 6 and gives "0 otherwise" automatically, also at `k = 0`.
* `demandFrac` encodes the pledging rules of §3.1 (pp. 7–8): informed backers pledge iff
  `p ≤ v_true`, uninformed backers iff `p ≤ v_believed`; in a separating analysis the
  posterior `b″` is `0` or `1`, so the belief is a type.
* Feasibility is the funding constraint `C ≥ S_i` (p. 12) and a positive price; the pricing
  constraint `p ≤ v_i` is not imposed (p. 12: the L-type "need not satisfy the pricing
  constraint"); a price above every pledging threshold simply gets zero demand.
* Every design other than the H-type's equilibrium design is believed to come from the
  L-type (p. 11, `b″ = 0`).
* The intuitive criterion (p. 11) is tested for both deviating types; "the other type
  strictly worse off no matter what type the uninformed backers perceive her to be" is
  required under both beliefs (a design the other type cannot choose counts as worse).
* `Cstar` is the explicit formula (5), with its `α ≤ α∗` branch; it is not defined as a root.
-/

namespace CrowdTarget.Separating

/-- The primitive parameters of §3: the demand bound `N̄`, valuations `v_H`, `v_L`, and fixed
startup costs `S_H`, `S_L`. -/
structure Params where
  Nbar : ℝ
  vH : ℝ
  vL : ℝ
  SH : ℝ
  SL : ℝ

/-- Standing assumptions of §3.1–3.2 (pp. 7–10), with the implicit positivity made explicit. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.Nbar ∧ 0 < P.vL ∧ P.vL < P.vH ∧ 0 < P.SL ∧ P.SL ≤ P.SH ∧
    P.SL < P.Nbar * P.vL ∧ P.SH < P.Nbar * P.vH

/-- The creator's type: high (`H`) or low (`L`) quality. -/
inductive CType
  | H
  | L
  deriving DecidableEq

/-- Backers' valuation of a type's product: `v_H` or `v_L`. -/
def val (P : Params) : CType → ℝ
  | .H => P.vH
  | .L => P.vL

/-- A type's fixed startup cost: `S_H` or `S_L`. -/
def cost (P : Params) : CType → ℝ
  | .H => P.SH
  | .L => P.SL

/-- A campaign design: funding target `C` and reward price `p` (p. 6). -/
structure Design where
  C : ℝ
  p : ℝ

/-- The share of the `N` interested backers who pledge at price `p` when the creator's true type
is `tru` and the uninformed backers believe the type is `bel`: the informed fraction `1 − α`
pledges iff `p ≤ v_tru`, the uninformed fraction `α` iff `p ≤ v_bel` (pp. 7–8). -/
noncomputable def demandFrac (P : Params) (α : ℝ) (tru bel : CType) (p : ℝ) : ℝ :=
  (if p ≤ val P tru then 1 - α else 0) + (if p ≤ val P bel then α else 0)

/-- Expected profit (1) of a campaign with target `C`, price `p`, startup cost `S`, when a share
`k` of the `N ~ U[0, N̄]` backers pledge: the campaign succeeds iff `C ≤ k p N`, and then the
creator earns `k p N − S`; otherwise all pledges are refunded and she earns `0`. -/
noncomputable def campaignProfit (P : Params) (k S C p : ℝ) : ℝ :=
  ∫ N in Set.Icc 0 P.Nbar ∩ {N : ℝ | C ≤ k * p * N}, (k * p * N - S) / P.Nbar

/-- Expected profit of a creator of true type `tru` choosing design `d` when the uninformed
backers believe her type is `bel`. -/
noncomputable def profit (P : Params) (α : ℝ) (tru bel : CType) (d : Design) : ℝ :=
  campaignProfit P (demandFrac P α tru bel d.p) (cost P tru) d.C d.p

/-- Feasible designs for type `i`: the funding constraint `C ≥ S_i` (p. 12) and a positive price. -/
def Feasible (P : Params) (i : CType) (d : Design) : Prop :=
  cost P i ≤ d.C ∧ 0 < d.p

/-- A separating perfect Bayesian equilibrium (p. 11) in which the L-type plays `dL`, the H-type
plays `dH`, the uninformed backers believe `H` exactly at `dH` and `L` at every other design. -/
def IsSepEq (P : Params) (α : ℝ) (dL dH : Design) : Prop :=
  (Feasible P .L dL ∧ Feasible P .H dH ∧ dL ≠ dH) ∧
  ((∀ d, Feasible P .L d → d ≠ dH → profit P α .L .L d ≤ profit P α .L .L dL) ∧
    profit P α .L .H dH ≤ profit P α .L .L dL) ∧
  (∀ d, Feasible P .H d → d ≠ dH → profit P α .H .L d ≤ profit P α .H .H dH)

/-- The equilibrium `(dL, dH)` survives the intuitive criterion (p. 11): there is no off-path
design `d` such that one type is strictly better off at `d` when recognized as her true type,
while the other type would be strictly worse off at `d` whatever type she is perceived to be. -/
def SurvivesIC (P : Params) (α : ℝ) (dL dH : Design) : Prop :=
  ¬ ∃ d : Design, d ≠ dL ∧ d ≠ dH ∧
    ((Feasible P .H d ∧ profit P α .H .H dH < profit P α .H .H d ∧
        profit P α .L .H d < profit P α .L .L dL ∧
        profit P α .L .L d < profit P α .L .L dL) ∨
      (Feasible P .L d ∧ profit P α .L .L dL < profit P α .L .L d ∧
        (Feasible P .H d →
          profit P α .H .H d < profit P α .H .H dH ∧
            profit P α .H .L d < profit P α .H .H dH)))

/-- `B ≡ v_L + S_L²/(N̄² v_L)`, main text (2), p. 13 (= Online Supplement (1)). -/
noncomputable def B (P : Params) : ℝ :=
  P.vL + P.SL ^ 2 / (P.Nbar ^ 2 * P.vL)

/-- `α∗ ≡ (B + √(B² + 4(S_H² − 2 S_L S_H)/N̄²)) / (2 v_H)`, main text (3), p. 13
(= Online Supplement (3)). -/
noncomputable def alphaStar (P : Params) : ℝ :=
  (B P + Real.sqrt (B P ^ 2 + 4 * ((P.SH ^ 2 - 2 * P.SL * P.SH) / P.Nbar ^ 2))) / (2 * P.vH)

/-- The H-type's equilibrium target (5), p. 15: `S_H` if `α ≤ α∗`, and
`S_L + √(S_L² + N̄²(α² v_H² − α v_H B))` otherwise. -/
noncomputable def Cstar (P : Params) (α : ℝ) : ℝ :=
  if α ≤ alphaStar P then P.SH
  else P.SL + Real.sqrt (P.SL ^ 2 + P.Nbar ^ 2 * (α ^ 2 * P.vH ^ 2 - α * P.vH * B P))

/-- `p₁(C) ≡ (B − √(B² + 4(C² − 2 S_L C)/N̄²)) / (2α)`, Online Supplement (6), p. 4. -/
noncomputable def p1 (P : Params) (α C : ℝ) : ℝ :=
  (B P - Real.sqrt (B P ^ 2 + 4 * ((C ^ 2 - 2 * P.SL * C) / P.Nbar ^ 2))) / (2 * α)

/-- `p₂(C) ≡ (B + √(B² + 4(C² − 2 S_L C)/N̄²)) / (2α)`, Online Supplement (7), p. 4. -/
noncomputable def p2 (P : Params) (α C : ℝ) : ℝ :=
  (B P + Real.sqrt (B P ^ 2 + 4 * ((C ^ 2 - 2 * P.SL * C) / P.Nbar ^ 2))) / (2 * α)

end CrowdTarget.Separating


