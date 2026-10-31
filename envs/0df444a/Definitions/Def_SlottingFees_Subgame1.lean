-- Prove2me | Definitions.Def_SlottingFees_Subgame1
-- name    : SlottingFees_Subgame1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:40.930992+00:00
-- url     : https://prove2.me/theorems/bcad5c28-99df-436c-8c98-01f0d1a02289
-- title:
--   The low-variety subgame $|A|=1$: pricing (4), formulation (5)–(8), fee choice
-- statement:
--   The subgame in which the retailer has committed to carry one product (§4.1).
--
--   1. **Stage 3.** For $A=\{i\}$ and wholesale price $w_i$ the retailer solves
--   $$
--   \max_{0\le p_i\le q_i}\ (p_i-w_i)z_i(p_i)+S-K.\qquad(4)
--   $$
--   Let $G_i(w_i)$ be the optimal gross profit. When both manufacturers participate, $\{i\}$ is an optimal assortment if $G_i(w_i)\ge G_j(w_j)$. A pricing strategy is optimal in (4) after every wholesale price $w\ge c_i$; $\tilde z_i(w)$ denotes the resulting demand.
--   2. **Stage 2** (the paper's formulation (5)–(8)). Manufacturer $l$ *can afford* $S$ if some $w\ge c_l$ gives $(w-c_l)\tilde z_l(w)-S\ge 0$. If nobody can, the category is not offered. If exactly one can, it solves the upstream-monopoly problem $\max_{w\ge c_l}(w-c_l)\tilde z_l(w)-S$ (5). If both can, each has a zero-profit price $w^0_l$, the least $w\ge c_l$ with non-negative profit (8); the entrant $i$ is the manufacturer whose zero-profit price gives the retailer the larger $G$ (ties to manufacturer 1), and it maximizes $(w-c_i)\tilde z_i(w)-S$ over $w\ge c_i$ subject to $G_i(w)\ge G_j(w^0_j)$ ((6)–(7)).
--   3. **Stage 1.** With slotting fees, the retailer chooses the fee that maximizes its profit among the fees at which the category is offered, the lowest such fee on a tie; in the benchmark the fee is $0$.
--
--   $\Pi^{|1|}_r$ is the retailer's profit on the path of such a subgame equilibrium. Lemmas 1–2, Corollary 1 and Proposition 1 are stated about these objects.
--
--   **Formalization Note** The entrant rule, the "least root" reading of (8), the fee tie rule and the stage-1 fee range are readings (the paper's range $0\le S\le v_i/8$ is the set of fees at which some manufacturer participates). (7) is stated in its primitive form rather than its Lemma 1 closed form. The constant $S-K$ is dropped from the pricing objective. The outcome `some (i, w)` means product $i$ is carried at wholesale price $w$; `none` means the category is not offered.
-- source:
--   Alan–Kurtuluş–Nakkas, Retail Category Management with Slotting Fees, MSOM (2024), doi:10.1287/msom.2022.0143, §4.1, (4)–(8), pp.10–12

import Mathlib
import Definitions.Def_SlottingFees_Model

namespace SlottingFees

/-- The retailer's gross profit `(p − w) z_i({i}, p)` from carrying product `i` alone at wholesale
price `w` and retail price `p`: the objective of (4), p.10, without the constant `S − K`. -/
noncomputable def gross1 (ω : Params) (i : Fin 2) (w p : ℝ) : ℝ :=
  grossProfit ω {i} (fun _ => w) (fun _ => p)

/-- `p` solves the retailer's stage-3 pricing problem (4), p.10, for `A = {i}`:
`max_{0 ≤ p_i ≤ q_i} (p_i − w_i) z_i(p_i) + S − K`.

**Formalization Note** The constant `S − K` is dropped; it does not change the maximizers. -/
def IsOptPrice1 (ω : Params) (i : Fin 2) (w p : ℝ) : Prop :=
  p ∈ Set.Icc 0 (ω.q i) ∧ ∀ p' ∈ Set.Icc 0 (ω.q i), gross1 ω i w p' ≤ gross1 ω i w p

/-- The retailer's optimal stage-3 gross profit from carrying `i` alone at wholesale price `w`,
the value of (4) minus `S − K` (p.11: `Π̃_r^{{i}}(w_i) − S + K`).

**Formalization Note** A supremum over the compact interval `[0, q_i]`; for `q_i > 0` the
objective is continuous there, so the supremum is attained (Lemma 1 computes it). -/
noncomputable def optGross1 (ω : Params) (i : Fin 2) (w : ℝ) : ℝ :=
  sSup (gross1 ω i w '' Set.Icc 0 (ω.q i))

/-- `{i}` is an optimal stage-3 assortment for the retailer when `|A| = 1`, the participating
manufacturers are `P`, and the wholesale prices are `w`: `i ∈ P` and no participating product
gives a larger optimal gross profit (§4.1, p.10, Lemma 1; the slotting fee and `K` are the same
for every single-product assortment). -/
def IsOptAssortment1 (ω : Params) (P : Finset (Fin 2)) (w : Fin 2 → ℝ) (i : Fin 2) : Prop :=
  i ∈ P ∧ ∀ j ∈ P, optGross1 ω j (w j) ≤ optGross1 ω i (w i)

/-- A retailer pricing strategy for the `|A| = 1` subgame, `σ i w` = the retail price of `i`
when `A = {i}` and the wholesale price is `w`, is optimal in (4) after every wholesale price
`w ≥ c_i` a manufacturer can offer (subgame perfection in stage 3). -/
def IsOptPricing1 (ω : Params) (σ : Fin 2 → ℝ → ℝ) : Prop :=
  ∀ i w, ω.c i ≤ w → IsOptPrice1 ω i w (σ i w)

/-- Manufacturer `l`'s gross profit `(w − c_l) z̃_l(w)` when it is carried alone at wholesale
price `w` and the retailer prices by `σ` (p.11, after (5): `z̃_l(w) = 1 − p̃_l(w)/q_l`). -/
noncomputable def mfrGross1 (ω : Params) (σ : Fin 2 → ℝ → ℝ) (l : Fin 2) (w : ℝ) : ℝ :=
  mfrGross ω {l} (fun _ => w) (fun _ => σ l w) l

/-- Manufacturer `l` can afford the slotting fee `S` (p.9, p.11): some wholesale price `w ≥ c_l`
gives it a non-negative profit `(w − c_l) z̃_l(w) − S ≥ 0`. -/
def CanAfford (ω : Params) (σ : Fin 2 → ℝ → ℝ) (l : Fin 2) (S : ℝ) : Prop :=
  ∃ w, ω.c l ≤ w ∧ 0 ≤ mfrGross1 ω σ l w - S

/-- `w` is manufacturer `l`'s zero-profit wholesale price at fee `S` (p.11, (8)): "the lowest
wholesale price it can offer to the retailer without losing money", i.e. the least `w ≥ c_l`
with `(w − c_l) z̃_l(w) − S ≥ 0`. -/
def IsZeroProfitPrice (ω : Params) (σ : Fin 2 → ℝ → ℝ) (l : Fin 2) (S w : ℝ) : Prop :=
  IsLeast {x | ω.c l ≤ x ∧ 0 ≤ mfrGross1 ω σ l x - S} w

/-- `w` solves the upstream-monopoly problem (5), p.11: `max_{w ≥ c_l} (w − c_l) z̃_l(w) − S`. -/
def IsMonopolyPrice (ω : Params) (σ : Fin 2 → ℝ → ℝ) (l : Fin 2) (S w : ℝ) : Prop :=
  ω.c l ≤ w ∧ ∀ x, ω.c l ≤ x → mfrGross1 ω σ l x - S ≤ mfrGross1 ω σ l w - S

/-- `w` solves the entrant's problem (6)–(7), p.11: manufacturer `i` maximizes
`(w − c_i) z̃_i(w) − S` over `w ≥ c_i` subject to the retailer's incentive-compatibility
constraint (7) that `{i}` is an optimal assortment against the rival's offer `wj`.

**Formalization Note** (7) is printed in its Lemma 1 closed form
`w_i ≤ q_i − (q_j − w_j)√(q_i/q_j)`; here it is the primitive condition it encodes, that the
retailer's optimal gross profit from `i` at `w` is at least that from `j` at `wj` (Lemma 1 proves
the equivalence). -/
def IsCompetitivePrice (ω : Params) (σ : Fin 2 → ℝ → ℝ) (i : Fin 2) (wj S w : ℝ) : Prop :=
  ω.c i ≤ w ∧ optGross1 ω (other i) wj ≤ optGross1 ω i w ∧
    ∀ x, ω.c i ≤ x → optGross1 ω (other i) wj ≤ optGross1 ω i x →
      mfrGross1 ω σ i x - S ≤ mfrGross1 ω σ i w - S

/-- `o` is a stage-2 outcome of the `|A| = 1` subgame at slotting fee `S`, in the paper's
formulation (5)–(8), p.11, with the retailer's stage-3 pricing `σ`. The outcome `some (i, w)`
means that product `i` is carried at wholesale price `w`; `none` means that the category is not
offered.

1. If neither manufacturer can afford `S`, nobody participates and the category is not offered.
2. If exactly one manufacturer `i` can afford `S`, it alone participates, is carried, and solves
   the upstream-monopoly problem (5).
3. If both can afford `S`, both participate; each has a zero-profit price `w⁰_l` (8); the
   entrant `i` is the manufacturer whose zero-profit price gives the retailer the larger optimal
   gross profit (ties to manufacturer 1); it is carried and solves (6)–(7) against the rival's
   zero-profit price.

**Formalization Note** The entrant rule of case 3 is a reading: the paper says only that the
manufacturer "which cannot enter the retailer's assortment, sets its wholesale price on the basis
of its zero-profit condition" (p.11). The rule makes the entrant the more attractive
manufacturer of Lemma 2. Manufacturer 1 is index `0`. -/
def IsStage2Outcome1 (ω : Params) (σ : Fin 2 → ℝ → ℝ) (S : ℝ) (o : Option (Fin 2 × ℝ)) :
    Prop :=
  (¬ CanAfford ω σ 0 S → ¬ CanAfford ω σ 1 S → o = none) ∧
  (∀ i, CanAfford ω σ i S → ¬ CanAfford ω σ (other i) S →
    ∃ w, o = some (i, w) ∧ IsMonopolyPrice ω σ i S w) ∧
  (CanAfford ω σ 0 S → CanAfford ω σ 1 S →
    ∃ w0 : Fin 2 → ℝ, (∀ l, IsZeroProfitPrice ω σ l S (w0 l)) ∧
      ∃ i w, o = some (i, w) ∧
        (i = 0 ↔ optGross1 ω 1 (w0 1) ≤ optGross1 ω 0 (w0 0)) ∧
        IsCompetitivePrice ω σ i (w0 (other i)) S w)

/-- The retailer's profit at slotting fee `S` in the `|A| = 1` subgame, given the stage-2 outcome
`o` and the pricing strategy `σ`: its profit (3) from `A = {i}` at the wholesale price `w` and
retail price `σ i w` when `o = some (i, w)`, and `0` if the category is not offered. -/
noncomputable def payoff1 (ω : Params) (σ : Fin 2 → ℝ → ℝ) (S : ℝ) :
    Option (Fin 2 × ℝ) → ℝ
  | none => 0
  | some (i, w) => retailerProfit ω {i} (fun _ => w) (fun _ => σ i w) S

/-- A strategy profile of the `|A| = 1` subgame: the retailer's stage-3 pricing `price`, the
stage-2 outcome `outcome S` after each announced fee `S`, and the retailer's fee `fee`. -/
structure Play1 where
  price : Fin 2 → ℝ → ℝ
  outcome : ℝ → Option (Fin 2 × ℝ)
  fee : ℝ

/-- At fee `S` the category is offered in the `|A| = 1` subgame: `S ≥ 0` and some manufacturer
is carried. -/
def Play1.Offers (P : Play1) (S : ℝ) : Prop := 0 ≤ S ∧ P.outcome S ≠ none

/-- The retailer's equilibrium profit `Π^{|1|}_r` of the `|A| = 1` subgame under the profile. -/
noncomputable def Play1.value (ω : Params) (P : Play1) : ℝ :=
  payoff1 ω P.price P.fee (P.outcome P.fee)

/-- `P` is an equilibrium of the `|A| = 1` subgame (§4.1, pp.10–12), solved by backward
induction: the pricing is optimal after every wholesale price (stage 3), the outcome after every
fee `S ≥ 0` follows (5)–(8) (stage 2), and in stage 1

* with slotting fees (`fees = true`): the fee maximizes the retailer's profit over the fees at
  which the category is offered, the lowest such maximizer being taken;
* in the benchmark (`fees = false`, §5.2, p.20): the fee is `0`.

**Formalization Note** The paper's stage-1 problem is `max_{0 ≤ S ≤ v_i/8} Π̃_r(S)` (p.12);
`[0, v_i/8]` is exactly the set of fees at which some manufacturer participates (Lemma 2), so the
constraint is stated as "the category is offered". When two fees are optimal the lower one is
taken; this is the choice printed in (10) at `v₁/(v₁+v₂) ∈ {3/7, 4/7}`. -/
def IsEq1 (fees : Bool) (ω : Params) (P : Play1) : Prop :=
  IsOptPricing1 ω P.price ∧
  (∀ S, 0 ≤ S → IsStage2Outcome1 ω P.price S (P.outcome S)) ∧
  if fees then
    IsLeast {S | P.Offers S ∧ ∀ S', P.Offers S' →
      payoff1 ω P.price S' (P.outcome S') ≤ payoff1 ω P.price S (P.outcome S)} P.fee
  else P.fee = 0

end SlottingFees


