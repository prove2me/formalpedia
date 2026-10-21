-- Prove2me | Definitions.Def_SystemSqueeze_Accommodation_Model
-- name    : SystemSqueeze_Accommodation_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:39.50642+00:00
-- url     : https://prove2.me/theorems/413915cb-e228-4776-b034-9bbb4a7e7a3a
-- title:
--   §3–§4.3.1, pp. 7–14 — complementors A, B and integrated systems: linear demand, price subgames (i)–(iii), Nash equilibria, entry benefits, ΔΠ^X, ΔΠ^Y, ΔΠ^Z
-- statement:
--   This file sets up the model of Reisinger, Schmidt and Stieglitz for two complementors $A$ and $B$, each producing one component of a two-component system, either of which may launch an **integrated system** that substitutes for the two-component system. The de novo entrant of the paper's §5 is absent, so its quantity is zero throughout.
--
--   **Parameters.** $U_C$ is the gross utility of the two-component system, $U_I$ the gross utility of an integrated system, and $\gamma$ the degree of substitution between systems. The **standing assumptions** are
--   $$U_C>0,\qquad U_I>0,\qquad 0<\gamma<1,$$
--   together with the **admissible range** of p. 9: $\gamma\le U_C/(2U_I-U_C)$ if $U_I\ge U_C$, and $\gamma\le \bar\gamma(U_C,U_I):=(\sqrt{U_C^2+3U_I^2}-U_C)/U_I$ if $U_I<U_C$. Production costs are zero; launching an integrated system costs an investment $K$.
--
--   **Demand.** The inverse demand of §3 is $P_{C_A}+P_{C_B}=U_C-Q_C-\gamma\sum_i Q_{I_i}$ and $P_{I_i}=U_I-Q_{I_i}-\gamma(Q_C+Q_{I_{-i}})$, a missing system having quantity zero. The direct demands used in the three price subgames are:
--
--   1. **No entry (i):** $Q_C^{(i)}=U_C-P_{C_A}-P_{C_B}$; profits $\Pi_i^{(i)}=P_{C_i}Q_C^{(i)}$.
--   2. **Accommodation (ii), only $A$ enters:** with $P_C=P_{C_A}+P_{C_B}$,
--   $$Q_C^{(ii)}=\frac{U_C-P_C-\gamma(U_I-P_{I_A})}{(1+\gamma)(1-\gamma)},\qquad Q_{I_A}^{(ii)}=\frac{U_I-P_{I_A}-\gamma(U_C-P_C)}{(1+\gamma)(1-\gamma)},$$
--   and $\Pi_A^{(ii)}=P_{C_A}Q_C^{(ii)}+P_{I_A}Q_{I_A}^{(ii)}$, $\Pi_B^{(ii)}=P_{C_B}Q_C^{(ii)}$.
--   3. **Escalation (iii), both enter:**
--   $$Q_C^{(iii)}=\frac{(U_C-P_C)(1+\gamma)-\gamma(2U_I-P_{I_A}-P_{I_B})}{(1+2\gamma)(1-\gamma)},\qquad Q_{I_i}^{(iii)}=\frac{U_I-P_{I_i}(1+\gamma)+\gamma P_{I_{-i}}-\gamma(U_C-P_C)}{(1+2\gamma)(1-\gamma)},$$
--   and $\Pi_i^{(iii)}=P_{C_i}Q_C^{(iii)}+P_{I_i}Q_{I_i}^{(iii)}$.
--
--   All subgame profits are gross of $K$. A **price equilibrium** of a subgame is a pure Nash equilibrium: no firm can raise its profit by changing the prices it controls, a firm with two products changing both prices at once.
--
--   **Stage 1.** Given equilibrium price profiles of the three subgames, $A$'s benefit of entering when $B$ stays out is $\Pi_A^{(ii)}-K-\Pi_A^{(i)}$ (the paper's (2)), and $B$'s benefit of entering when $A$ is in is $\Pi_B^{(iii)}-K-\Pi_B^{(ii)}$ (the paper's (3)). The **accommodation outcome** at $K$ is: $A$'s benefit is $\ge 0$ and $B$'s benefit is $<0$ (an indifferent firm enters). The **escalation outcome** at $K$ is: each firm's benefit of entering, given the other has entered, is $\ge 0$, staying out yielding the accommodating firm's profit $\Pi_B^{(ii)}$.
--
--   **Incremental profits of $A$** (§4.3.1), for a no-entry profile (i) and an accommodation profile (ii):
--   $$\Delta\Pi_A^Z=(Q_{I_A}^{(ii)}+Q_C^{(ii)}-Q_C^{(i)})P_{I_A}^{(ii)},\quad \Delta\Pi_A^Y=(Q_C^{(i)}-Q_C^{(ii)})(P_{I_A}^{(ii)}-P_{C_A}^{(i)}),\quad \Delta\Pi_A^X=Q_C^{(ii)}(P_{C_A}^{(ii)}-P_{C_A}^{(i)}),$$
--   the profits from market expansion, conversion and squeezing. $A$'s profit from the integrated system in (ii) is $P_{I_A}^{(ii)}Q_{I_A}^{(ii)}$ and from its component $P_{C_A}^{(ii)}Q_C^{(ii)}$.
--
--   These objects are the common vocabulary of every statement in the mission.
--
--   **Formalization Note** Prices range over $\mathbb R$ and the direct demands are the untruncated linear expressions printed in §4.2 (the paper's first-order approach; the equilibrium prices are nonnegative on the admissible range as a consequence). $U_C>0$ and $U_I>0$ are added: the paper uses them as gross utilities without stating positivity. Price profiles are bundled in the structures `NoEntryPrices`, `AccPrices`, `EscPrices`; the entry benefits and incremental profits take equilibrium profiles as arguments rather than closed-form prices. The escalation outcome uses the symmetry of the model: the payoff of the accommodating firm when the *other* firm entered alone is the same function `profitB1` of the accommodation profile.
-- source:
--   Reisinger, Schmidt & Stieglitz, How Complementors Benefit from Taking Competition to the System Level, authors' manuscript (May 2020; Management Science, doi:10.1287/mnsc.2020.3771), pp. 7–14 (PDF 8–15), §3, §4.2 A–C, §4.3.1, and pp. 33–34 (PDF 34–35), (2)–(3)

import Mathlib

namespace SystemSqueeze.Accommodation

/-!
# Reisinger, Schmidt & Stieglitz — complementors and integrated systems (§3, §4.2, §4.3.1)

Two complementors `A` and `B` each sell one component of a two-component system (gross utility
`UC`). Either may launch an integrated system (gross utility `UI`) at investment `K`. Linear
inverse demand with substitution parameter `γ ∈ (0,1)` (pp. 7–8); production costs are zero.
The de novo entrant `E` of §5 is absent, so `Q_{I_E} = 0` throughout.

Prices range over `ℝ` and the direct demands are the linear expressions printed in §4.2,
untruncated (the paper's first-order approach).
-/

/-- The admissible range of `γ` (p. 9): `γ ≤ UC/(2UI − UC)` if `UI ≥ UC`, and
`γ ≤ (√(UC² + 3UI²) − UC)/UI` if `UI < UC`. -/
def Admissible (UC UI γ : ℝ) : Prop :=
  (UC ≤ UI → γ ≤ UC / (2 * UI - UC)) ∧
    (UI < UC → γ ≤ (Real.sqrt (UC ^ 2 + 3 * UI ^ 2) - UC) / UI)

/-- The upper bound `(√(UC² + 3UI²) − UC)/UI` of the admissible range when `UI < UC` (p. 9). -/
noncomputable def gammaMax (UC UI : ℝ) : ℝ :=
  (Real.sqrt (UC ^ 2 + 3 * UI ^ 2) - UC) / UI

/-- Standing assumptions of §3: `UC > 0`, `UI > 0`, `0 < γ < 1` and `γ` admissible. -/
def Standing (UC UI γ : ℝ) : Prop :=
  0 < UC ∧ 0 < UI ∧ 0 < γ ∧ γ < 1 ∧ Admissible UC UI γ

/-! ## Subgame (i): no complementor enters (§4.2 A) -/

/-- Prices `(P_{C_A}^{(i)}, P_{C_B}^{(i)})` of the no-entry subgame. -/
structure NoEntryPrices where
  pCA : ℝ
  pCB : ℝ

/-- Demand for the two-component system when it is the only system:
`Q_C^{(i)} = UC − P_{C_A} − P_{C_B}`. -/
def qC0 (UC : ℝ) (p : NoEntryPrices) : ℝ := UC - (p.pCA + p.pCB)

/-- `Π_A^{(i)} = P_{C_A}^{(i)} Q_C^{(i)}`. -/
def profitA0 (UC : ℝ) (p : NoEntryPrices) : ℝ := p.pCA * qC0 UC p

/-- `Π_B^{(i)} = P_{C_B}^{(i)} Q_C^{(i)}`. -/
def profitB0 (UC : ℝ) (p : NoEntryPrices) : ℝ := p.pCB * qC0 UC p

/-- Pure Nash equilibrium of the no-entry price subgame. -/
def IsNoEntryEq (UC : ℝ) (p : NoEntryPrices) : Prop :=
  (∀ a : ℝ, profitA0 UC { p with pCA := a } ≤ profitA0 UC p) ∧
    (∀ b : ℝ, profitB0 UC { p with pCB := b } ≤ profitB0 UC p)

/-! ## Subgame (ii): only `A` enters (accommodation, §4.2 B) -/

/-- Prices `(P_{C_A}^{(ii)}, P_{I_A}^{(ii)}, P_{C_B}^{(ii)})` of the accommodation subgame. -/
structure AccPrices where
  pCA : ℝ
  pIA : ℝ
  pCB : ℝ

/-- `Q_C^{(ii)} = (UC − P_C − γ(UI − P_{I_A}))/((1+γ)(1−γ))`, `P_C = P_{C_A} + P_{C_B}`. -/
noncomputable def qC1 (UC UI γ : ℝ) (p : AccPrices) : ℝ :=
  (UC - (p.pCA + p.pCB) - γ * (UI - p.pIA)) / ((1 + γ) * (1 - γ))

/-- `Q_{I_A}^{(ii)} = (UI − P_{I_A} − γ(UC − P_C))/((1+γ)(1−γ))`. -/
noncomputable def qIA1 (UC UI γ : ℝ) (p : AccPrices) : ℝ :=
  (UI - p.pIA - γ * (UC - (p.pCA + p.pCB))) / ((1 + γ) * (1 - γ))

/-- `Π_A^{(ii)} = P_{C_A} Q_C^{(ii)} + P_{I_A} Q_{I_A}^{(ii)}`, gross of the investment `K`. -/
noncomputable def profitA1 (UC UI γ : ℝ) (p : AccPrices) : ℝ :=
  p.pCA * qC1 UC UI γ p + p.pIA * qIA1 UC UI γ p

/-- `Π_B^{(ii)} = P_{C_B} Q_C^{(ii)}`. -/
noncomputable def profitB1 (UC UI γ : ℝ) (p : AccPrices) : ℝ :=
  p.pCB * qC1 UC UI γ p

/-- Pure Nash equilibrium of the accommodation subgame; `A` deviates jointly in both its
prices. -/
def IsAccEq (UC UI γ : ℝ) (p : AccPrices) : Prop :=
  (∀ a i : ℝ, profitA1 UC UI γ { p with pCA := a, pIA := i } ≤ profitA1 UC UI γ p) ∧
    (∀ b : ℝ, profitB1 UC UI γ { p with pCB := b } ≤ profitB1 UC UI γ p)

/-! ## Subgame (iii): both enter (escalation, §4.2 C) -/

/-- Prices `(P_{C_A}^{(iii)}, P_{I_A}^{(iii)}, P_{C_B}^{(iii)}, P_{I_B}^{(iii)})` of the
escalation subgame. -/
structure EscPrices where
  pCA : ℝ
  pIA : ℝ
  pCB : ℝ
  pIB : ℝ

/-- `Q_C^{(iii)} = ((UC − P_C)(1+γ) − γ(2UI − P_{I_A} − P_{I_B}))/((1+2γ)(1−γ))`. -/
noncomputable def qC2 (UC UI γ : ℝ) (p : EscPrices) : ℝ :=
  ((UC - (p.pCA + p.pCB)) * (1 + γ) - γ * (2 * UI - p.pIA - p.pIB)) /
    ((1 + 2 * γ) * (1 - γ))

/-- `Q_{I_A}^{(iii)} = (UI − P_{I_A}(1+γ) + γP_{I_B} − γ(UC − P_C))/((1+2γ)(1−γ))`. -/
noncomputable def qIA2 (UC UI γ : ℝ) (p : EscPrices) : ℝ :=
  (UI - p.pIA * (1 + γ) + γ * p.pIB - γ * (UC - (p.pCA + p.pCB))) /
    ((1 + 2 * γ) * (1 - γ))

/-- `Q_{I_B}^{(iii)} = (UI − P_{I_B}(1+γ) + γP_{I_A} − γ(UC − P_C))/((1+2γ)(1−γ))`. -/
noncomputable def qIB2 (UC UI γ : ℝ) (p : EscPrices) : ℝ :=
  (UI - p.pIB * (1 + γ) + γ * p.pIA - γ * (UC - (p.pCA + p.pCB))) /
    ((1 + 2 * γ) * (1 - γ))

/-- `Π_A^{(iii)} = P_{C_A} Q_C^{(iii)} + P_{I_A} Q_{I_A}^{(iii)}`, gross of `K`. -/
noncomputable def profitA2 (UC UI γ : ℝ) (p : EscPrices) : ℝ :=
  p.pCA * qC2 UC UI γ p + p.pIA * qIA2 UC UI γ p

/-- `Π_B^{(iii)} = P_{C_B} Q_C^{(iii)} + P_{I_B} Q_{I_B}^{(iii)}`, gross of `K`. -/
noncomputable def profitB2 (UC UI γ : ℝ) (p : EscPrices) : ℝ :=
  p.pCB * qC2 UC UI γ p + p.pIB * qIB2 UC UI γ p

/-- Pure Nash equilibrium of the escalation subgame; each firm deviates jointly in both its
prices. -/
def IsEscEq (UC UI γ : ℝ) (p : EscPrices) : Prop :=
  (∀ a i : ℝ, profitA2 UC UI γ { p with pCA := a, pIA := i } ≤ profitA2 UC UI γ p) ∧
    (∀ b j : ℝ, profitB2 UC UI γ { p with pCB := b, pIB := j } ≤ profitB2 UC UI γ p)

/-! ## Stage 1: entry benefits (proof of Proposition 1, (2)–(3)) -/

/-- `A`'s benefit of entering when `B` stays out, (2): `Π_A^{(ii)} − K − Π_A^{(i)}`. -/
noncomputable def benefitA (UC UI γ : ℝ) (n : NoEntryPrices) (a : AccPrices) (K : ℝ) : ℝ :=
  profitA1 UC UI γ a - K - profitA0 UC n

/-- `B`'s benefit of entering when `A` is in, (3): `Π_B^{(iii)} − K − Π_B^{(ii)}`. -/
noncomputable def benefitB (UC UI γ : ℝ) (a : AccPrices) (e : EscPrices) (K : ℝ) : ℝ :=
  profitB2 UC UI γ e - K - profitB1 UC UI γ a

/-- Accommodation outcome of stage 1 at `K`: `A` (weakly) prefers entering given `B` stays
out, and `B` strictly prefers staying out given `A` is in (an indifferent firm enters). -/
def AccommodationOutcome (UC UI γ : ℝ) (n : NoEntryPrices) (a : AccPrices) (e : EscPrices)
    (K : ℝ) : Prop :=
  0 ≤ benefitA UC UI γ n a K ∧ benefitB UC UI γ a e K < 0

/-- Escalation outcome of stage 1 at `K`: each firm, given the other has entered, (weakly)
prefers to enter. The payoff from staying out is the accommodating firm's profit `Π_B^{(ii)}`
of the accommodation subgame (the model is symmetric in the two complementors). -/
def EscalationOutcome (UC UI γ : ℝ) (a : AccPrices) (e : EscPrices) (K : ℝ) : Prop :=
  0 ≤ profitA2 UC UI γ e - K - profitB1 UC UI γ a ∧
    0 ≤ profitB2 UC UI γ e - K - profitB1 UC UI γ a

/-! ## Incremental profits of `A` (§4.3.1) -/

/-- Market expansion, `ΔΠ_A^Z = (Q_{I_A}^{(ii)} + Q_C^{(ii)} − Q_C^{(i)}) P_{I_A}^{(ii)}`. -/
noncomputable def dPiZ (UC UI γ : ℝ) (n : NoEntryPrices) (a : AccPrices) : ℝ :=
  (qIA1 UC UI γ a + qC1 UC UI γ a - qC0 UC n) * a.pIA

/-- Conversion, `ΔΠ_A^Y = (Q_C^{(i)} − Q_C^{(ii)})(P_{I_A}^{(ii)} − P_{C_A}^{(i)})`. -/
noncomputable def dPiY (UC UI γ : ℝ) (n : NoEntryPrices) (a : AccPrices) : ℝ :=
  (qC0 UC n - qC1 UC UI γ a) * (a.pIA - n.pCA)

/-- Squeezing, `ΔΠ_A^X = Q_C^{(ii)} (P_{C_A}^{(ii)} − P_{C_A}^{(i)})`. -/
noncomputable def dPiX (UC UI γ : ℝ) (n : NoEntryPrices) (a : AccPrices) : ℝ :=
  qC1 UC UI γ a * (a.pCA - n.pCA)

/-- `A`'s profit from selling the integrated system in subgame (ii), gross of `K`:
`P_{I_A}^{(ii)} Q_{I_A}^{(ii)}`. -/
noncomputable def integratedProfitA (UC UI γ : ℝ) (a : AccPrices) : ℝ :=
  a.pIA * qIA1 UC UI γ a

/-- `A`'s profit from selling its component in subgame (ii): `P_{C_A}^{(ii)} Q_C^{(ii)}`. -/
noncomputable def componentProfitA (UC UI γ : ℝ) (a : AccPrices) : ℝ :=
  a.pCA * qC1 UC UI γ a

end SystemSqueeze.Accommodation


