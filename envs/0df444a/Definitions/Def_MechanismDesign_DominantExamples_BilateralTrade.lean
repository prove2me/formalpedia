-- Prove2me | Definitions.Def_MechanismDesign_DominantExamples_BilateralTrade
-- name    : MechanismDesign_DominantExamples_BilateralTrade
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T01:08:43.361863+00:00
-- url     : https://prove2.me/theorems/c8e3e4c1-c1da-4f9b-bc80-7c9195e00fa3
-- title:
--   Bilateral trade without a prior (Börgers §4.4): deterministic direct mechanisms, dominant strategy IC, ex post IR, exact budget balance, canonical mechanisms
-- statement:
--   This file sets up the bilateral trade model of Börgers, §4.4, in which the designer relies on no assumption about the traders' beliefs.
--
--   **Environment.** A seller $S$ owns one indivisible good and has type $\theta_S \in [\underline\theta_S,\bar\theta_S]$; a buyer $B$ has type $\theta_B \in [\underline\theta_B,\bar\theta_B]$; both intervals are nondegenerate. We write $\theta = (\theta_S,\theta_B)$ and $\Theta = [\underline\theta_S,\bar\theta_S]\times[\underline\theta_B,\bar\theta_B]$. If the good is sold and the seller receives $t_S$ her utility is $t_S$; if it is not sold her utility is $\theta_S + t_S$. The buyer's utility is $\theta_B - t_B$ if he obtains the good and pays $t_B$, and $-t_B$ otherwise.
--
--   **Direct mechanisms** (Definition 3.9). A (deterministic) direct mechanism consists of a trading rule $q : \Theta \to \{0,1\}$ and transfers $t_S, t_B : \Theta \to \mathbb R$ ($t_S$ received by the seller, $t_B$ paid by the buyer). Under truthful reporting the ex post utilities are
--   $$u_S(\theta) = \theta_S\,(1 - q(\theta)) + t_S(\theta), \qquad u_B(\theta) = \theta_B\,q(\theta) - t_B(\theta).$$
--
--   1. **Dominant strategy incentive compatibility**: for all $\theta \in \Theta$, every seller report $\theta_S'$ and every buyer report $\theta_B'$, $\ \theta_S(1 - q(\theta_S',\theta_B)) + t_S(\theta_S',\theta_B) \le u_S(\theta)$ and $\theta_B q(\theta_S,\theta_B') - t_B(\theta_S,\theta_B') \le u_B(\theta)$.
--   2. **Ex post individual rationality**: $u_S(\theta) \ge \theta_S$ (the value of keeping the good) and $u_B(\theta) \ge 0$ for all $\theta \in \Theta$.
--   3. **Ex post exact budget balance** (p.92): $t_B(\theta) = t_S(\theta)$ for all $\theta \in \Theta$.
--   4. **Canonical mechanism** (Definition 4.5): there are strictly increasing and continuous $\psi_S : [\underline\theta_S,\bar\theta_S] \to \mathbb R$ and $\psi_B : [\underline\theta_B,\bar\theta_B] \to \mathbb R$ such that for all $\theta \in \Theta$: $q(\theta) = 1$ if $\psi_B(\theta_B) \ge \psi_S(\theta_S)$ and $0$ otherwise;
--   $$t_S(\theta) = \max\{\hat\theta_S \in [\underline\theta_S,\bar\theta_S] \mid \psi_B(\theta_B) \ge \psi_S(\hat\theta_S)\}, \qquad t_B(\theta) = \min\{\hat\theta_B \in [\underline\theta_B,\bar\theta_B] \mid \psi_B(\hat\theta_B) \ge \psi_S(\theta_S)\}$$
--   if $q(\theta) = 1$, and $t_S(\theta) = t_B(\theta) = 0$ if $q(\theta) = 0$.
--
--   These are the objects every result of §4.4 is stated in terms of.
--
--   **Formalization Note** A type vector is a pair `(θS, θB) : ℝ × ℝ`. The trading rule is real-valued and required to take values in $\{0,1\}$ on $\Theta$. The maximum and minimum in the canonical transfers are written as `sSup` and `sInf`; when trade takes place the sets are nonempty and closed (by continuity of $\psi_S$, $\psi_B$), so they are attained. No sign restriction on the type intervals is imposed, as §3.4.1 imposes none.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.90–92: setup §4.4.1 p.90 and §3.4.1 p.63; Definition 3.9 pp.63–64; seller individual rationality p.64; §4.4.2 p.90; Definition 4.5 and exact budget balance p.92

import Mathlib

namespace MechanismDesign.DominantExamples

/-- The bilateral trade environment of Börgers, *An Introduction to the Theory of Mechanism
Design*, §4.4.1 (p.90), recapitulating §3.4.1 (p.63): a seller `S` owns one indivisible good
and has type `θ_S ∈ [θ̲_S, θ̄_S]`, a buyer `B` has type `θ_B ∈ [θ̲_B, θ̄_B]`; both intervals are
nondegenerate (they are supports of densities in §3.4.1). No prior is assumed in Chapter 4. -/
structure TradeSetting where
  /-- lower end `θ̲_S` of the seller's type interval -/
  loS : ℝ
  /-- upper end `θ̄_S` of the seller's type interval -/
  hiS : ℝ
  /-- lower end `θ̲_B` of the buyer's type interval -/
  loB : ℝ
  /-- upper end `θ̄_B` of the buyer's type interval -/
  hiB : ℝ
  loS_lt_hiS : loS < hiS
  loB_lt_hiB : loB < hiB

namespace TradeSetting

/-- The set of type vectors `Θ = [θ̲_S, θ̄_S] × [θ̲_B, θ̄_B]`; a type vector is the pair
`θ = (θ_S, θ_B)`. -/
def typeSpace (E : TradeSetting) : Set (ℝ × ℝ) :=
  Set.Icc E.loS E.hiS ×ˢ Set.Icc E.loB E.hiB

end TradeSetting

/-- A deterministic direct mechanism for bilateral trade (Definition 3.9, pp.63–64, used in
§4.4.2): a trading rule `q : Θ → {0, 1}`, the transfer `t_S : Θ → ℝ` that the seller receives
and the transfer `t_B : Θ → ℝ` that the buyer makes. `q` takes values in `{0, 1}` on `Θ`;
values outside `Θ` play no role. -/
structure TradeMechanism (E : TradeSetting) where
  /-- trading rule: `q θ = 1` if trade takes place -/
  q : ℝ × ℝ → ℝ
  /-- transfer received by the seller -/
  tS : ℝ × ℝ → ℝ
  /-- transfer made by the buyer -/
  tB : ℝ × ℝ → ℝ
  q_mem : ∀ θ ∈ E.typeSpace, q θ = 0 ∨ q θ = 1

namespace TradeMechanism

variable {E : TradeSetting}

/-- The seller's ex post utility under truthful reporting: `u_S(θ) = θ_S (1 − q(θ)) + t_S(θ)`
(she keeps the good, worth `θ_S`, when there is no trade). -/
def uS (M : TradeMechanism E) (θ : ℝ × ℝ) : ℝ :=
  θ.1 * (1 - M.q θ) + M.tS θ

/-- The buyer's ex post utility under truthful reporting: `u_B(θ) = θ_B q(θ) − t_B(θ)`. -/
def uB (M : TradeMechanism E) (θ : ℝ × ℝ) : ℝ :=
  θ.2 * M.q θ - M.tB θ

/-- Dominant strategy incentive compatibility (§4.4.2): for every `θ = (θ_S, θ_B) ∈ Θ`, no
seller report `θ_S' ∈ [θ̲_S, θ̄_S]` gives the seller more than truth telling, and no buyer
report `θ_B' ∈ [θ̲_B, θ̄_B]` gives the buyer more than truth telling. -/
def IsDSIC (M : TradeMechanism E) : Prop :=
  (∀ θ ∈ E.typeSpace, ∀ x ∈ Set.Icc E.loS E.hiS,
    θ.1 * (1 - M.q (x, θ.2)) + M.tS (x, θ.2) ≤ M.uS θ) ∧
  (∀ θ ∈ E.typeSpace, ∀ y ∈ Set.Icc E.loB E.hiB,
    θ.2 * M.q (θ.1, y) - M.tB (θ.1, y) ≤ M.uB θ)

/-- Ex post individual rationality (§4.4.2 with §3.4.2, p.64): for every `θ ∈ Θ` the seller
obtains at least `θ_S`, the utility of keeping the good, and the buyer at least `0`. -/
def IsEPIR (M : TradeMechanism E) : Prop :=
  ∀ θ ∈ E.typeSpace, θ.1 ≤ M.uS θ ∧ 0 ≤ M.uB θ

/-- Ex post exact budget balance (p.92): `t_B(θ) = t_S(θ)` for all `θ ∈ Θ`. -/
def IsExactlyBudgetBalanced (M : TradeMechanism E) : Prop :=
  ∀ θ ∈ E.typeSpace, M.tB θ = M.tS θ

end TradeMechanism

open Classical in
/-- The trading rule of a canonical mechanism (Definition 4.5, p.92):
`q(θ) = 1` if `ψ_B(θ_B) ≥ ψ_S(θ_S)`, and `q(θ) = 0` otherwise. -/
noncomputable def canonicalTradeQ (ψS ψB : ℝ → ℝ) (θ : ℝ × ℝ) : ℝ :=
  if ψS θ.1 ≤ ψB θ.2 then 1 else 0

open Classical in
/-- The seller's transfer in a canonical mechanism (Definition 4.5, p.92):
`t_S(θ) = max {θ̂_S ∈ [θ̲_S, θ̄_S] | ψ_B(θ_B) ≥ ψ_S(θ̂_S)}` if `q(θ) = 1`, and `0` if
`q(θ) = 0`. The maximum is written as `sSup`; it is attained for continuous `ψ_S`. -/
noncomputable def canonicalTradeTS (E : TradeSetting) (ψS ψB : ℝ → ℝ) (θ : ℝ × ℝ) : ℝ :=
  if canonicalTradeQ ψS ψB θ = 1 then
    sSup {x | x ∈ Set.Icc E.loS E.hiS ∧ ψS x ≤ ψB θ.2}
  else 0

open Classical in
/-- The buyer's transfer in a canonical mechanism (Definition 4.5, p.92):
`t_B(θ) = min {θ̂_B ∈ [θ̲_B, θ̄_B] | ψ_B(θ̂_B) ≥ ψ_S(θ_S)}` if `q(θ) = 1`, and `0` if
`q(θ) = 0`. The minimum is written as `sInf`; it is attained for continuous `ψ_B`. -/
noncomputable def canonicalTradeTB (E : TradeSetting) (ψS ψB : ℝ → ℝ) (θ : ℝ × ℝ) : ℝ :=
  if canonicalTradeQ ψS ψB θ = 1 then
    sInf {y | y ∈ Set.Icc E.loB E.hiB ∧ ψS θ.1 ≤ ψB y}
  else 0

/-- Definition 4.5 (p.92), canonical mechanism for bilateral trade: there are strictly
increasing and continuous functions `ψ_S : [θ̲_S, θ̄_S] → ℝ` and `ψ_B : [θ̲_B, θ̄_B] → ℝ` such
that for all `θ ∈ Θ` the trading rule and the transfers are the ones displayed above. -/
def TradeMechanism.IsCanonical {E : TradeSetting} (M : TradeMechanism E) : Prop :=
  ∃ ψS ψB : ℝ → ℝ,
    StrictMonoOn ψS (Set.Icc E.loS E.hiS) ∧ ContinuousOn ψS (Set.Icc E.loS E.hiS) ∧
    StrictMonoOn ψB (Set.Icc E.loB E.hiB) ∧ ContinuousOn ψB (Set.Icc E.loB E.hiB) ∧
    ∀ θ ∈ E.typeSpace,
      M.q θ = canonicalTradeQ ψS ψB θ ∧ M.tS θ = canonicalTradeTS E ψS ψB θ ∧
        M.tB θ = canonicalTradeTB E ψS ψB θ

end MechanismDesign.DominantExamples


