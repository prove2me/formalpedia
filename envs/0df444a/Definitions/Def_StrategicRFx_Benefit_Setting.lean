-- Prove2me | Definitions.Def_StrategicRFx_Benefit_Setting
-- name    : StrategicRFx_Benefit_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:27.178339+00:00
-- url     : https://prove2.me/theorems/ed8688bd-e2ed-43fc-8457-1fc20c5d1e35
-- title:
--   §2.1–§3.2, pp. 7–18 — reduced dual-sourcing bargaining model, [Simu-i] equilibria, the RFx programs [RFx-j], [RFx-i] (5)–(12), the buyer's accept-both response
-- statement:
--   This file fixes the reduced model of Chu, Rong and Zheng: a monopoly buyer (player 0) procures from two suppliers (players 1 and 2) of substitutable products and negotiates with them by asymmetric Nash bargaining, possibly after an RFx (request for proposal/quotation) stage in which the suppliers quote offers.
--
--   **Parameters (§2.1, pp. 7–8).** $\Pi$ is the maximum supply chain profit; $\Pi^{-i}$ is the maximum chain profit when supplier $i$ does not participate; $\Pi^{-i}(q_j^o)$ is the chain profit when supplier $i$ does not participate and the other supplier $j$ supplies his first-best quantity $q_j^o$; $\theta_i$ is supplier $i$'s bargaining power. Write $\{i,j\}=\{1,2\}$ and $(x)^+=\max\{x,0\}$.
--
--   **Standing hypotheses (pp. 8, 10).** $\theta_i\in(0,1)$, and the consequences of Assumptions 1–2 printed on p. 10:
--   $$\Pi>\Pi^{-i},\qquad \Pi^{-i}>\Pi^{-i}(q_j^o)>0,\qquad \Pi<\Pi^{-2}(q_1^o)+\Pi^{-1}(q_2^o).$$
--
--   **Nash product.** $N_\theta(a,b)=a^{\theta}b^{1-\theta}$ for $a,b\ge 0$.
--
--   **Follower program (Lemma 1's program, p. 17; [Simu-j], p. 12).** Given supplier $i$'s profit $\pi_i$ and the buyer's single-sourcing profit $\pi'=\pi_0^{-j}$, supplier $j$'s profit $x$ is feasible if $x\ge 0$ and $\Pi-\pi_i-x\ge\pi'$, and it solves the program if it maximizes $N_{\theta_j}(x,\ \Pi-\pi_i-x-\pi')$ over the feasible set. Lemma 1's closed form is $\pi_j(\pi,\pi')=\theta_j(\Pi-\pi-\pi')$.
--
--   **Leader program [RFx-i] (8)–(12), p. 18.** Given offers $(\tilde\pi_1,\tilde\pi_2)$, the buyer first negotiates with supplier $i$ and either accepts or rejects his offer. The reservation utilities are $D_i=\tilde\pi_i$ and
--   $$D_0=\max\{\Pi-\tilde\pi_i-\tilde\pi_j,\ \Pi-\tilde\pi_i-\pi_j(\tilde\pi_i,\Pi^{-j}(q_i^o)-\tilde\pi_i)\}$$
--   if she accepts, and $D_i=0$, $D_0=\max\{(1-\theta_j)\Pi^{-i},\ (1-\theta_j)\Pi^{-i}+\theta_j\Pi^{-i}(q_j^o)-\tilde\pi_j\}$ if she rejects. With the buyer's profit $B(\pi,\pi')=\Pi-\pi-\min\{\tilde\pi_j,\pi_j(\pi,\pi')\}$, a pair $(\pi,\pi')$ is feasible if
--   $$\Pi-\pi-\pi'\ge 0,\qquad \pi'\le\Pi^{-j},\qquad \pi\ge D_i,\qquad B(\pi,\pi')\ge D_0,$$
--   and solves [RFx-i] if it maximizes $N_{\theta_i}(\pi-D_i,\ B(\pi,\pi')-D_0)$ over the feasible set. The buyer accepts $\tilde\pi_j$ at the follower stage when $\tilde\pi_j\le\pi_j(\pi,\pi')$.
--
--   **Accepting both offers (pp. 16, 18).** The buyer accepts both offers if no option (either leader, accept or reject the leader's offer, any solution of [RFx-i]) gives her more than $\Pi-\tilde\pi_1-\tilde\pi_2$. An option is buyer-optimal ("at optimality", Lemmas 4–5) if it solves [RFx-i] and no other option gives her more.
--
--   **Simultaneous bargaining (p. 12).** A profile $(\pi_1,\pi_2,\pi_1^{-2},\pi_2^{-1})$ is a dual-sourcing equilibrium if $\pi_k^{-l}\ge 0$ (Assumption 3) and, for each $i$, $\pi_i$ solves the follower program with $\pi_j$ and $\pi_0^{-i}=\Pi^{-i}-\pi_j^{-i}$.
--
--   **The program [Q] (p. ec21).** Its feasible region is $0\le\pi_i\le\theta_i(\Pi-\pi_j-\Pi^{-i})^+$ for $\{i,j\}=\{1,2\}$.
--
--   These objects carry the paper's whole negotiation analysis; every theorem of the mission is stated in terms of them.
--
--   **Formalization Note** Suppliers are `Fin 2` (supplier 1 is `0`, supplier 2 is `1`), `other i` is the other supplier, offers are `t : Fin 2 → ℝ`. `PiEx i` is $\Pi^{-i}$ and `PiExAt i` is $\Pi^{-i}(q_j^o)$, so $\Pi^{-j}(q_i^o)$ is `PiExAt j`. The primitive profit function $\Pi(q_1,q_2)$, the contracts and Theorems 1–3 are not modelled: the scalars are the paper's derived quantities and `Standing` holds the printed consequences of Assumptions 1–2, not the assumptions themselves. Nash solutions are argmax sets, so every property "at the solution" is required of every maximizer. The free variable $\pi_j^{-i}$ (p. 12) is omitted from the follower program. Ties in the buyer's choice are resolved as on p. 16 (accept).
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), §2.1 pp. 7–8, §2.4 Assumptions 1–3 p. 10, §2.5 (3)–(4) p. 11, §3.1.1 [Simu-i] p. 12, §3.2.1 pp. 15–16, §3.2.2 [RFx-j] (5)–(7) p. 17, [RFx-i] (8)–(12) p. 18, proof of Theorem 5 [Q] p. ec21

import Mathlib

namespace StrategicRFx.Benefit

/-! Chu, Rong & Zheng, *The Strategic Benefit of Request for Proposal/Quotation* (SSRN 3200030),
§2.1–§3.2, pp. 7–18: the reduced dual-sourcing bargaining model.

Suppliers are `Fin 2`: the paper's supplier 1 is `0`, supplier 2 is `1`. All quantities are the
paper's derived scalars (Theorems 2–3 reduce the contract model to profit profiles, p. 11). -/

/-- The scalar data of the reduced model (§2.1, pp. 7–8).
* `θ i` — the bargaining power `θ_i` of supplier `i` when the buyer bargains with him;
* `Pi` — `Π = max_{q_1,q_2 ≥ 0} Π(q_1, q_2)`, the maximum supply chain profit;
* `PiEx i` — `Π^{-i} = max_{q_j} Π^{-i}(q_j)`, the maximum chain profit when supplier `i`
  does not participate;
* `PiExAt i` — `Π^{-i}(q_j^o)`, the chain profit when supplier `i` does not participate and
  the other supplier `j` supplies his first-best quantity `q_j^o`. So `Π^{-j}(q_i^o)` is
  `PiExAt j`. -/
structure Params where
  θ : Fin 2 → ℝ
  Pi : ℝ
  PiEx : Fin 2 → ℝ
  PiExAt : Fin 2 → ℝ

/-- The other supplier: `other 0 = 1`, `other 1 = 0` (`{i, j} = {1, 2}`). -/
def other (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

/-- Standing hypotheses (pp. 8, 10): `θ_i ∈ (0,1)`, and the consequences of Assumptions 1–2
printed on p. 10: `Π > Π^{-i}`, `Π^{-i} > Π^{-i}(q_j^o) > 0`, and
`Π < Π^{-2}(q_1^o) + Π^{-1}(q_2^o)`. Assumption 3 enters through constraint (10) and the
nonnegativity of exclusive-supplier profits in `IsSimuEquilibrium`. -/
structure Standing (P : Params) : Prop where
  θ_pos : ∀ i, 0 < P.θ i
  θ_lt_one : ∀ i, P.θ i < 1
  PiEx_lt : ∀ i, P.PiEx i < P.Pi
  PiExAt_pos : ∀ i, 0 < P.PiExAt i
  PiExAt_lt : ∀ i, P.PiExAt i < P.PiEx i
  submod : P.Pi < P.PiExAt 0 + P.PiExAt 1

/-- The asymmetric Nash product `a^θ b^(1-θ)` (real powers; feasible sets keep `a, b ≥ 0`). -/
noncomputable def nashProduct (θ a b : ℝ) : ℝ := a ^ θ * b ^ (1 - θ)

/-- Feasible set of the follower's program (Lemma 1's program, p. 17: [RFx-j] after the buyer
rejects `j`'s offer, `D_j = 0`, `D_0 = π_0^{-j}`; equally [Simu-j], p. 12): given supplier `i`'s
profit `πi` and the buyer's single-sourcing profit `π' = π_0^{-j}`, supplier `j`'s profit `x`
satisfies `x ≥ 0` and `π_0 = Π - πi - x ≥ π'`. -/
def followerFeasible (P : Params) (_j : Fin 2) (πi π' x : ℝ) : Prop :=
  0 ≤ x ∧ π' ≤ P.Pi - πi - x

/-- `x` maximizes the follower's Nash product `(x - 0)^{θ_j} (Π - πi - x - π')^{1-θ_j}` over the
feasible set (every maximizer, not a chosen one). The free variable `π_j^{-i}` is omitted. -/
def IsFollowerSolution (P : Params) (j : Fin 2) (πi π' x : ℝ) : Prop :=
  followerFeasible P j πi π' x ∧
    ∀ y, followerFeasible P j πi π' y →
      nashProduct (P.θ j) y (P.Pi - πi - y - π') ≤ nashProduct (P.θ j) x (P.Pi - πi - x - π')

/-- Lemma 1's closed form `π_j(π, π') = θ_j (Π - π - π')` (p. 17), used inside (8) and (12). -/
def followerSplit (P : Params) (j : Fin 2) (π π' : ℝ) : ℝ := P.θ j * (P.Pi - π - π')

/-- Supplier `i`'s reservation utility in [RFx-i] (p. 18): `D_i = π̃_i` if the buyer accepts
supplier `i`'s offer (`acc = true`), `D_i = 0` if she rejects it. Offers are `t : Fin 2 → ℝ`. -/
def resSupplier (_P : Params) (i : Fin 2) (acc : Bool) (t : Fin 2 → ℝ) : ℝ :=
  if acc then t i else 0

/-- The buyer's reservation utility in [RFx-i] (p. 18), with `j = other i`:
`D_0 = max{Π - π̃_i - π̃_j, Π - π̃_i - π_j(π̃_i, Π^{-j}(q_i^o) - π̃_i)}` if she accepts `i`'s
offer, and `D_0 = max{(1-θ_j)Π^{-i}, (1-θ_j)Π^{-i} + θ_j Π^{-i}(q_j^o) - π̃_j}` if she rejects it. -/
def resBuyer (P : Params) (i : Fin 2) (acc : Bool) (t : Fin 2 → ℝ) : ℝ :=
  if acc then
    max (P.Pi - t i - t (other i))
      (P.Pi - t i - followerSplit P (other i) (t i) (P.PiExAt (other i) - t i))
  else
    max ((1 - P.θ (other i)) * P.PiEx i)
      ((1 - P.θ (other i)) * P.PiEx i + P.θ (other i) * P.PiExAt i - t (other i))

/-- The buyer's profit in [RFx-i] (8), (12): `Π - π - min{π̃_j, π_j(π, π')}`; the `min` is her
accept/reject choice of `j`'s offer at the follower stage. -/
def leaderBuyer (P : Params) (i : Fin 2) (t : Fin 2 → ℝ) (π π' : ℝ) : ℝ :=
  P.Pi - π - min (t (other i)) (followerSplit P (other i) π π')

/-- Constraints (9)–(12) of [RFx-i] (p. 18), with `j = other i`. -/
def leaderFeasible (P : Params) (i : Fin 2) (acc : Bool) (t : Fin 2 → ℝ) (π π' : ℝ) : Prop :=
  0 ≤ P.Pi - π - π' ∧ π' ≤ P.PiEx (other i) ∧ resSupplier P i acc t ≤ π ∧
    resBuyer P i acc t ≤ leaderBuyer P i t π π'

/-- `(π, π')` solves [RFx-i] (8)–(12) (p. 18): it is feasible and maximizes the Nash product
`(π - D_i)^{θ_i} (Π - π - min{π̃_j, π_j(π, π')} - D_0)^{1-θ_i}` over the feasible set. -/
def IsLeaderSolution (P : Params) (i : Fin 2) (acc : Bool) (t : Fin 2 → ℝ) (π π' : ℝ) : Prop :=
  leaderFeasible P i acc t π π' ∧
    ∀ x y, leaderFeasible P i acc t x y →
      nashProduct (P.θ i) (x - resSupplier P i acc t) (leaderBuyer P i t x y - resBuyer P i acc t) ≤
        nashProduct (P.θ i) (π - resSupplier P i acc t) (leaderBuyer P i t π π' - resBuyer P i acc t)

/-- At the follower stage of [RFx-i] the buyer accepts `π̃_j`, i.e. `π̃_j ≤ π_j(π, π')`
(ties: accept, the paper's tie-break, p. 16). -/
def AcceptsFollower (P : Params) (i : Fin 2) (t : Fin 2 → ℝ) (π π' : ℝ) : Prop :=
  t (other i) ≤ followerSplit P (other i) π π'

/-- The buyer accepts both offers `t = (π̃_1, π̃_2)` (pp. 16, 18): no negotiation option — leader
`i`, accept or reject the leader's offer, any solution of [RFx-i] — gives her more than
`Π - π̃_1 - π̃_2`, the profit of accepting both (ties go to accepting both, p. 16). -/
def AcceptsBoth (P : Params) (t : Fin 2 → ℝ) : Prop :=
  ∀ i acc π π', IsLeaderSolution P i acc t π π' → leaderBuyer P i t π π' ≤ P.Pi - t 0 - t 1

/-- "At optimality" (Lemmas 4–5, p. 24): the buyer first negotiates with `i`, accepting
(`acc = true`) or rejecting its offer, the outcome `(π, π')` solves [RFx-i], and no other
option gives her a higher profit. -/
def IsBuyerOptimal (P : Params) (t : Fin 2 → ℝ) (i : Fin 2) (acc : Bool) (π π' : ℝ) : Prop :=
  IsLeaderSolution P i acc t π π' ∧
    ∀ i' acc' x y, IsLeaderSolution P i' acc' t x y → leaderBuyer P i' t x y ≤ leaderBuyer P i t π π'

/-- A dual-sourcing equilibrium of simultaneous bargaining [Simu-i] (p. 12), as the profile
`π̈ = (π̈_1, π̈_2, π̈_1^{-2}, π̈_2^{-1})`: `π k` is supplier `k`'s profit under dual sourcing and
`πex k` his profit as exclusive supplier (`πex k = π_k^{-other k}`, nonnegative by Assumption 3).
For each `i`, `π i` solves [Simu-i]: maximize `π_i^{θ_i}(π_0 - π_0^{-i})^{1-θ_i}` subject to
`π_i ≥ 0`, `π_0 = Π - π_i - π̈_j ≥ π_0^{-i} = Π^{-i} - π̈_j^{-i}`. -/
def IsSimuEquilibrium (P : Params) (π πex : Fin 2 → ℝ) : Prop :=
  (∀ i, 0 ≤ πex i) ∧
    ∀ i, IsFollowerSolution P i (π (other i)) (P.PiEx i - πex (other i)) (π i)

/-- The feasible region of [Q] (proof of Theorem 5, p. ec21):
`0 ≤ π_i ≤ θ_i (Π - π_j - Π^{-i})^+` for `{i, j} = {1, 2}`. -/
def QFeasible (P : Params) (π : Fin 2 → ℝ) : Prop :=
  ∀ i, 0 ≤ π i ∧ π i ≤ P.θ i * max (P.Pi - π (other i) - P.PiEx i) 0

end StrategicRFx.Benefit


