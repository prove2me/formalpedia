-- Prove2me | Definitions.Def_AgriChain_LandAlloc_Model
-- name    : AgriChain_LandAlloc_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:18.05649+00:00
-- url     : https://prove2.me/theorems/cbf94e11-7a44-47fe-ba04-6198983efbed
-- title:
--   §2–§3, pp. 9–19 — two-region agri-chain: harvest allocation, processor WTP, second-price final prices, farmers' AON land-allocation game
-- statement:
--   Two farmers, one in each of two regions, plant an export crop (EXP-crop) on part of their land; each region has one processor that buys the harvest. This definition sets up the paper's whole decentralized two-stage model.
--
--   **The chain.** The processed crop sells at the world price $p^e$. Processor $i\in\{1,2\}$ has unit processing cost $c_i$ and capacity $K_i$, and any processor pays at least the minimum guaranteed price $p_o$. The standing assumptions are
--   $$c_1\le c_2,\qquad K_1,K_2>0,\qquad 0\le p_o\le p^e-c_2 .$$
--
--   **Allocation (Theorem 1).** Write $y_i=x_iY^e_i$ for farmer $i$'s realized harvest and $a^+=\max\{a,0\}$. When Processor 1 is preferred (the branch $p_1\ge p_2$),
--   $$s^*_{1,1}=\min\{y_1,K_1\},\quad s^*_{1,2}=\min\{(y_1-K_1)^+,(K_2-y_2)^+\},\quad s^*_{2,1}=\min\{y_2,(K_1-y_1)^+\},\quad s^*_{2,2}=\min\{(y_2-(K_1-y_1)^+)^+,K_2\},$$
--   and symmetrically when Processor 2 is preferred; $s^*_{i,j}$ is farmer $i$'s sale to processor $j$.
--
--   **Processor profits (5)–(6).** With $T=y_1+y_2$, $g_1(p_1,p_2)=(p^e-c_1-p_1)\min\{K_1,T\}$ if $p_1\ge p_2$ and $(p^e-c_1-p_1)\min\{K_1,(T-K_2)^+\}$ otherwise; $g_2$ is the mirror image, with Processor 2 winning only when $p_1<p_2$.
--
--   **Willingness to pay (7)–(8).** $\bar p_1$ is the largest $p\in[p_o,p^e-c_1]$ with $g_1(p,p_o)-g_1(p_o,p_2)\ge0$ for every $p_2>p_o$, and $\bar p_2$ the largest $p\in[p_o,p^e-c_2]$ with $g_2(p_o,p)-g_2(p_1,p_o)\ge0$ for every $p_1\ge p_o$.
--
--   **Final prices (Theorem 3).** If $\bar p_1\ge\bar p_2$, Processor 1 wins and $(p^*_1,p^*_2)=(\bar p_2,p_o)$; otherwise Processor 2 wins and $(p^*_1,p^*_2)=(p_o,\bar p_1)$. Farmer revenues are (11)–(12): $f_1=p^*_1s^*_{1,1}+p^*_2s^*_{1,2}$ and $f_2=p^*_1s^*_{2,1}+p^*_2s^*_{2,2}$, with the allocation taken in the winner's branch.
--
--   **All-or-nothing yields and the game.** Each $Y^e_i\in\{H,0\}$, with joint probabilities $h_{aa},h_{an},h_{na},h_{nn}$; in the IID case $h_{aa}=h^2$, $h_{an}=h_{na}=h(1-h)$, $h_{nn}=(1-h)^2$. Farmer $i$'s expected profit is (13)–(14):
--   $$F_i(x_1,x_2)=E\big[f_i(x_1Y^e_1,x_2Y^e_2)\big]-x_iU_i+A_i ,$$
--   where $U_i$ is the per-unit cost of EXP-crop land (including the forgone alternative crop) and $A_i$ the profit of planting only the alternative crop. An **equilibrium** is a pair $(x_1,x_2)\in[0,L_1]\times[0,L_2]$ in which each $x_i$ maximizes $F_i$ over $[0,L_i]$ given the other farmer's choice. The **symmetric chain** has $c_1=c_2=c$ and $K_1=K_2=K$.
--
--   These objects are shared by every statement of the mission: Theorems 2 and 4 and Lemma 1 are about the WTPs, and Theorem 6 and Lemma 2 are about the equilibria of the land-allocation game.
--
--   **Formalization Note.** All quantities are real numbers. The WTP is defined as the supremum (`sSup`) of the set of admissible prices satisfying (7) or (8), not by the closed forms (9)–(10), which are Theorem 2; the set contains $p_o$ and is bounded by $p^e-c_i$, so the supremum is meaningful. Ties go to Processor 1 (p. 12). The allocation is indexed by the winning processor rather than by the raw comparison of final prices, which coincide only in the asymmetric corner $\bar p_1=p_o<\bar p_2$. The expectation in (13)–(14) is the finite sum over the four AON outcomes, and $U_i$, $A_i$ are real parameters as in the paper from (13) on. The equilibrium is the published generic pure-Nash predicate `CarbonDoubleCount.Planner.IsPureNash` with feasible sets $[0,L_1]$ and $[0,L_2]$.
-- source:
--   Li, Kouvelis & Dada, Agricultural Supply Chains in Emerging Markets: Competition and Cooperation under Correlated Yields, SSRN 3531158 (PDF of 2023-01-03), pp. 9–19, §2, §2.1, §2.2, §3, §3.1, Theorem 1, Theorem 3, (1)–(8), (11)–(14)

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_PureGame

namespace AgriChain.LandAlloc

/-- The data of the two-region agri-chain (§2, pp. 9–12): world price `pe` = p^e of the processed
crop, minimum guaranteed price `po` = p_o, unit processing costs `c1`, `c2` and capacities `K1`,
`K2` of the two processors. -/
structure Chain where
  pe : ℝ
  po : ℝ
  c1 : ℝ
  c2 : ℝ
  K1 : ℝ
  K2 : ℝ

/-- Standing assumptions of §2 (pp. 10–12, Figure 2's domain on p. 20): `c₁ ≤ c₂`, positive
capacities, `0 ≤ p_o`, and `p_o ≤ p^e − c₂` (so that both price ranges `[p_o, p^e − c_i]` are
nonempty). -/
def Chain.Standing (C : Chain) : Prop :=
  C.c1 ≤ C.c2 ∧ 0 < C.K1 ∧ 0 < C.K2 ∧ 0 ≤ C.po ∧ C.po ≤ C.pe - C.c2

/-- Theorem 1, (1): `s∗₁,₁`, farmer 1's sale to processor 1. `one` is "Processor 1 is preferred"
(the branch `p₁ ⩾ p₂`); `y1 = x₁Y₁ᵉ`, `y2 = x₂Y₂ᵉ` are the harvests. -/
def s11 (C : Chain) (one : Prop) [Decidable one] (y1 y2 : ℝ) : ℝ :=
  if one then min y1 C.K1 else min (max (y1 - max (C.K2 - y2) 0) 0) C.K1

/-- Theorem 1, (2): `s∗₁,₂`, farmer 1's sale to processor 2. -/
def s12 (C : Chain) (one : Prop) [Decidable one] (y1 y2 : ℝ) : ℝ :=
  if one then min (max (y1 - C.K1) 0) (max (C.K2 - y2) 0) else min y1 (max (C.K2 - y2) 0)

/-- Theorem 1, (3): `s∗₂,₂`, farmer 2's sale to processor 2. -/
def s22 (C : Chain) (one : Prop) [Decidable one] (y1 y2 : ℝ) : ℝ :=
  if one then min (max (y2 - max (C.K1 - y1) 0) 0) C.K2 else min y2 C.K2

/-- Theorem 1, (4): `s∗₂,₁`, farmer 2's sale to processor 1. -/
def s21 (C : Chain) (one : Prop) [Decidable one] (y1 y2 : ℝ) : ℝ :=
  if one then min y2 (max (C.K1 - y1) 0) else min (max (y2 - C.K2) 0) (max (C.K1 - y1) 0)

/-- (5): processor 1's second-stage profit `g₁(p₁, p₂)` at harvests `y1`, `y2`. -/
noncomputable def g1 (C : Chain) (y1 y2 p1 p2 : ℝ) : ℝ :=
  if p2 ≤ p1 then (C.pe - C.c1 - p1) * min C.K1 (y1 + y2)
  else (C.pe - C.c1 - p1) * min C.K1 (max (y1 + y2 - C.K2) 0)

/-- (6): processor 2's second-stage profit `g₂(p₁, p₂)` at harvests `y1`, `y2`. -/
noncomputable def g2 (C : Chain) (y1 y2 p1 p2 : ℝ) : ℝ :=
  if p2 ≤ p1 then (C.pe - C.c2 - p2) * min C.K2 (max (y1 + y2 - C.K1) 0)
  else (C.pe - C.c2 - p2) * min C.K2 (y1 + y2)

/-- The admissible prices `p ∈ [p_o, p^e − c₁]` satisfying (7):
`g₁(p, p_o) − g₁(p_o, p₂) ⩾ 0` for every `p₂ > p_o`. -/
def wtpSet1 (C : Chain) (y1 y2 : ℝ) : Set ℝ :=
  {p | C.po ≤ p ∧ p ≤ C.pe - C.c1 ∧
    ∀ p2, C.po < p2 → 0 ≤ g1 C y1 y2 p C.po - g1 C y1 y2 C.po p2}

/-- The admissible prices `p ∈ [p_o, p^e − c₂]` satisfying (8):
`g₂(p_o, p) − g₂(p₁, p_o) ⩾ 0` for every `p₁ ⩾ p_o`. -/
def wtpSet2 (C : Chain) (y1 y2 : ℝ) : Set ℝ :=
  {p | C.po ≤ p ∧ p ≤ C.pe - C.c2 ∧
    ∀ p1, C.po ≤ p1 → 0 ≤ g2 C y1 y2 C.po p - g2 C y1 y2 p1 C.po}

/-- Processor 1's willingness to pay `p̄₁`: the highest price satisfying (7) (p. 13). -/
noncomputable def wtp1 (C : Chain) (y1 y2 : ℝ) : ℝ := sSup (wtpSet1 C y1 y2)

/-- Processor 2's willingness to pay `p̄₂`: the highest price satisfying (8) (p. 13). -/
noncomputable def wtp2 (C : Chain) (y1 y2 : ℝ) : ℝ := sSup (wtpSet2 C y1 y2)

/-- Theorem 3: the final prices `(p∗₁, p∗₂)`. Processor 1 wins when `p̄₁ ⩾ p̄₂` and pays `p̄₂`, the
loser pays `p_o`; otherwise Processor 2 wins and pays `p̄₁`. -/
noncomputable def finalPrices (C : Chain) (y1 y2 : ℝ) : ℝ × ℝ :=
  if wtp2 C y1 y2 ≤ wtp1 C y1 y2 then (wtp2 C y1 y2, C.po) else (C.po, wtp1 C y1 y2)

/-- (11), first equality: farmer 1's EXP-crop revenue `f₁ = p∗₁ s∗₁,₁ + p∗₂ s∗₁,₂`, with the
allocation of Theorem 1 taken in the branch of the winning processor. -/
noncomputable def f1 (C : Chain) (y1 y2 : ℝ) : ℝ :=
  (finalPrices C y1 y2).1 * s11 C (wtp2 C y1 y2 ≤ wtp1 C y1 y2) y1 y2 +
    (finalPrices C y1 y2).2 * s12 C (wtp2 C y1 y2 ≤ wtp1 C y1 y2) y1 y2

/-- (12), first equality: farmer 2's EXP-crop revenue `f₂ = p∗₁ s∗₂,₁ + p∗₂ s∗₂,₂`. -/
noncomputable def f2 (C : Chain) (y1 y2 : ℝ) : ℝ :=
  (finalPrices C y1 y2).1 * s21 C (wtp2 C y1 y2 ≤ wtp1 C y1 y2) y1 y2 +
    (finalPrices C y1 y2).2 * s22 C (wtp2 C y1 y2 ≤ wtp1 C y1 y2) y1 y2

/-- §3: all-or-nothing yields. `(Y₁ᵉ, Y₂ᵉ) ∈ {H, 0}²` with probabilities `haa = P(H,H)`,
`han = P(H,0)`, `hna = P(0,H)`, `hnn = P(0,0)`. -/
structure AON where
  H : ℝ
  haa : ℝ
  han : ℝ
  hna : ℝ
  hnn : ℝ

/-- §3, p. 18: `H > 0` and `(h_ij)` is a probability vector. -/
def AON.Standing (Y : AON) : Prop :=
  0 < Y.H ∧ 0 ≤ Y.haa ∧ 0 ≤ Y.han ∧ 0 ≤ Y.hna ∧ 0 ≤ Y.hnn ∧
    Y.haa + Y.han + Y.hna + Y.hnn = 1

/-- §3.1, p. 19: IID AON yields, each equal to `H` with probability `h`:
`haa = h²`, `han = hna = h(1 − h)`, `hnn = (1 − h)²`. -/
def IID (h H : ℝ) : AON := ⟨H, h ^ 2, h * (1 - h), (1 - h) * h, (1 - h) ^ 2⟩

/-- (13): farmer 1's expected profit `F₁(x₁, x₂) = E[f₁(x₁Y₁ᵉ, x₂Y₂ᵉ)] − x₁U₁ + A₁`, the
expectation taken over the four AON outcomes. -/
noncomputable def F1 (C : Chain) (Y : AON) (U1 A1 x1 x2 : ℝ) : ℝ :=
  Y.haa * f1 C (x1 * Y.H) (x2 * Y.H) + Y.han * f1 C (x1 * Y.H) 0 +
    Y.hna * f1 C 0 (x2 * Y.H) + Y.hnn * f1 C 0 0 - x1 * U1 + A1

/-- (14): farmer 2's expected profit `F₂(x₁, x₂) = E[f₂(x₁Y₁ᵉ, x₂Y₂ᵉ)] − x₂U₂ + A₂`. -/
noncomputable def F2 (C : Chain) (Y : AON) (U2 A2 x1 x2 : ℝ) : ℝ :=
  Y.haa * f2 C (x1 * Y.H) (x2 * Y.H) + Y.han * f2 C (x1 * Y.H) 0 +
    Y.hna * f2 C 0 (x2 * Y.H) + Y.hnn * f2 C 0 0 - x2 * U2 + A2

/-- The land-allocation game of §2.2 as a two-player game: player `0` is farmer 1, player `1` is
farmer 2, and the payoff of player `i` at the profile `s = (x₁, x₂)` is `F_{i+1}(x₁, x₂)`. -/
noncomputable def payoff (C : Chain) (Y : AON) (U1 U2 A1 A2 : ℝ) (i : Fin 2) (s : Fin 2 → ℝ) : ℝ :=
  ![F1 C Y U1 A1 (s 0) (s 1), F2 C Y U2 A2 (s 0) (s 1)] i

/-- A (pure) equilibrium `(x₁, x₂)` of the land-allocation game: each farmer `i` plants
`x_i ∈ [0, L_i]`, and `x_i` maximizes `F_i` over `[0, L_i]` given the other's choice. This is the
published generic `IsPureNash` with feasible sets `[0, L₁]`, `[0, L₂]`. -/
def IsEq (C : Chain) (Y : AON) (U1 U2 A1 A2 L1 L2 x1 x2 : ℝ) : Prop :=
  CarbonDoubleCount.Planner.IsPureNash (strategy := fun _ : Fin 2 => ℝ)
    (fun i => Set.Icc 0 (![L1, L2] i)) (payoff C Y U1 U2 A1 A2) ![x1, x2]

/-- §3.1, p. 19: the symmetric chain `c₁ = c₂ = c`, `K₁ = K₂ = K`. -/
def symChain (pe po c K : ℝ) : Chain := ⟨pe, po, c, c, K, K⟩

end AgriChain.LandAlloc


