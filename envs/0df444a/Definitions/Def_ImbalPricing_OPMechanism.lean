-- Prove2me | Definitions.Def_ImbalPricing_OPMechanism
-- name    : ImbalPricing_OPMechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:22.246986+00:00
-- url     : https://prove2.me/theorems/f1dbf762-7916-45df-9d53-bb505c3fe6af
-- title:
--   Optimal imbalance pricing (26), the expected profit $\Pi^i_{op}$ and the offer-game equilibrium
-- statement:
--   In the market of §3.1, at the offer profile $d$ (with $p_1$, $L_1^i$, $L_2^i$, $H_2$ as in the market definition):
--
--   1. **Optimal pricing (OP)** (Definition 4, Eq. (26)). The imbalance price applied to LCG $i$ in Stage 2 is
--   $$p^i_{2,op}=p_1+\alpha_2H_2-\alpha_1L_1^i.$$
--   2. **Expected profit of LCG $i$ under OP** (the form of Eqs. (9), (20)):
--   $$\Pi^i_{op}=\mathbb E\big[p_1L_1^i+p^i_{2,op}L_2^i\big].$$
--   3. **Equilibrium of the offer game.** An offer profile $d$ is an equilibrium if it is a pure Nash equilibrium of the game in which each LCG $i$ chooses $d^i\in[-1,1/\gamma-1]$ to maximize $\Pi^i_{op}$, the other offers being fixed.
--
--   The OP price differs from the single price $p_1+\alpha_2H_2$ (Eq. (8)) by the term $-\alpha_1L_1^i$. Theorem 5 of the paper is about the equilibria of this game.
--
--   **Formalization Note** The profit is the expected profit, since offers are made in Stage 1 before $\epsilon$ and $\nu$ are realized (Eq. (20) prints the expectation, Eq. (9) omits it). The expectation is a Bochner integral. All $\gamma^i$ are common knowledge.
-- source:
--   Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn, Optimal Electricity Imbalance Pricing for the Emerging Penetration of Renewable and Low-Cost Generators, Manufacturing & Service Operations Management, Articles in Advance (2023), doi:10.1287/msom.2021.0555, §7, Definition 4, Eq. (26), p.13 (PDF p.15); Eqs. (9), (20), pp.8, 11 (PDF pp.10, 13); §3.1.4, p.7

import Mathlib
import Definitions.Def_ImbalPricing_IsPureNash
import Definitions.Def_ImbalPricing_Market

open MeasureTheory

namespace ImbalPricing

variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}

namespace Market

/-- **Optimal pricing (OP)**, Definition 4, Eq. (26), Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn,
*Optimal Electricity Imbalance Pricing …*, MSOM Articles in Advance (2023), §7, p.13 (PDF p.15):
the imbalance price applied to LCG `i` is `p^i_{2,op} = p₁ + α₂ H₂ − α₁ L₁ⁱ`. -/
def p2op (M : Market Ω N) (d : Fin N → ℝ) (i : Fin N) (ω : Ω) : ℝ :=
  M.p1 d + M.α₂ * M.H2 d ω - M.α₁ * M.L1i d i

/-- **Expected profit of LCG `i` under OP**, `Πⁱ_op = E[p₁ L₁ⁱ + p^i_{2,op} L₂ⁱ]`; the form of
Eqs. (9) and (20), pp.8 and 11 (PDF pp.10 and 13), with the OP price (26).

**Formalization Note.** The profit is the *expected* profit, since the offer `dⁱ` is chosen in
Stage 1, before `ε` and `ν` are realized (Eq. (20) prints the expectation; Eq. (9) omits it).
The expectation is the Bochner integral against `μ`. -/
noncomputable def profitOP (M : Market Ω N) (d : Fin N → ℝ) (i : Fin N) : ℝ :=
  ∫ ω, (M.p1 d * M.L1i d i + M.p2op d i ω * M.L2i d i ω) ∂M.μ

/-- **Equilibrium of the offer game under OP**: the offer profile `d` is a pure Nash
equilibrium of the game in which LCG `i` chooses `dⁱ ∈ [−1, 1/γ − 1]` (p.7) to maximize its
expected OP profit `Πⁱ_op`, the other offers being fixed.

**Formalization Note.** Complete information over the offers: all `γⁱ` are common knowledge
(they enter the strategy set through `γ = ∑ γⁱ`). -/
def IsNashOP (M : Market Ω N) (d : Fin N → ℝ) : Prop :=
  IsPureNash (fun _ => M.offerBox) (fun i x => M.profitOP x i) d

end Market

end ImbalPricing


