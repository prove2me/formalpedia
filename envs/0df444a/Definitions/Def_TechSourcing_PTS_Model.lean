-- Prove2me | Definitions.Def_TechSourcing_PTS_Model
-- name    : TechSourcing_PTS_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:46.901986+00:00
-- url     : https://prove2.me/theorems/5ffa394d-e781-4286-b90c-1f9098561141
-- title:
--   §3, pp. 7–13 — new-technology sourcing game: Leontief PTS, equity and loan contracts, existing supplier's cost reduction, Nash equilibrium
-- statement:
--   The model of Zhang and Lee's three-party sourcing game: a manufacturer funds a financially constrained new supplier's R&D for a new component, either by an **equity** investment or by a **loan**, while an existing supplier of a mature component may lower its production cost.
--
--   **Parameters.** $a>0$ and $b>0$ (the new supplier's capability in using investment and effort), $c>0$ (the existing supplier's cost-reduction efficiency), the expected demand $D>0$, the selling price $R>1$ of the end product, and the manufacturer's bargaining power $\beta\in[0,1]$ against the existing supplier.
--
--   **New supplier.** Reaching the probability of technical success (PTS) $\theta\in[0,1]$ requires the verifiable investment $K(\theta)=\theta^2/a$ and the unverifiable effort $G(\theta)=\theta^2/b$. Given a contract with upfront investment $B$, expense cap $B^G$ and expected procurement payment $P$, the supplier chooses $\theta$ and the filed effort expense $S$ subject to (3):
--   $$G(\theta)\le S\le B^G,\qquad S+K(\theta)\le B,\qquad \theta\le\min\{G^{-1}(B^G),\,G^{-1}(aB/(a+b))\},$$
--   with $G^{-1}(x)=\sqrt{bx}$.
--
--   **Equity.** The equity value is $\Pi^N_E=[B-K(\theta)-S]+\theta P$ (1); with the manufacturer's share $\gamma$ the supplier earns $U^N_E(\theta,S)=(1-\gamma)\Pi^N_E+[S-G(\theta)]$ (2). The manufacturer earns
--   $$U_E=-B+\gamma\Pi^N_E(\theta,S)+\theta(DR-P)+(1-\theta)\beta(R-\varphi)D.$$
--   An equity outcome $(B,B^G,\gamma,P,\theta,S)$ is **admissible** if $B,B^G\ge0$, $\gamma\in[0,1]$, $(\theta,S)$ maximizes $U^N_E$ over (3) (IC), the share is the fair valuation $\gamma\,\Pi^N_E(\theta,S)=B$, and $U^N_E(\theta,S)\ge0$ (IR). The manufacturer's best response to $\varphi$ is an admissible outcome maximizing $U_E$ over all admissible outcomes (problem $P_E$).
--
--   **Loan** (interest $r$ normalized to $0$, as on p. 12). The supplier earns (5)
--   $$U^N_L(\theta,S)=[B-K(\theta)-S]+[S-G(\theta)]+\theta(P-B)-(1-\theta)\min\{B-S-K(\theta),B\},$$
--   and the manufacturer $U_L=-B+\theta(DR-P+B)+(1-\theta)\big(\min\{B-K(\theta)-S,B\}+\beta(R-\varphi)D\big)$. Admissibility (IC, IR, $B,B^G\ge0$) and the best response (problem $P_L$) are as for equity, without $\gamma$.
--
--   **Existing supplier.** It chooses its cost $\varphi\le1$ to maximize (4)
--   $$U^O(\varphi\mid\theta)=(1-\theta)(1-\beta)(R-\varphi)D-c(1-\varphi)^2.$$
--
--   **Equilibrium.** An equity (loan) equilibrium is a pure Nash equilibrium $(o,\varphi)$ of the static game between the manufacturer, whose strategies are the admissible outcomes $o$, and the existing supplier, whose strategies are the costs $\varphi\le1$: $o$ is a best response of the manufacturer to $\varphi$, and $\varphi$ is a best response of the existing supplier to the PTS of $o$.
--
--   **Closed forms** used by the milestones: $W(\beta)=[(1-\beta)R+\beta]D$, $L(\beta)=D^2(1-\beta)\beta/(2c)$, $\pi(\varphi)=D[R-\beta(R-\varphi)]$, $\hat\gamma=\big(3(a+b)-\sqrt{9a^2+10ab+b^2}\big)/(4b)$, the best responses $\hat\theta_E(\varphi)$ (A-3), $\hat\theta_L(\varphi)$ (A-4), $\hat\varphi(\theta)=1-D(1-\beta)(1-\theta)/(2c)$ (A-5), the equilibrium values $\theta^*_E$ (6) and $\theta^*_L$ (7), and the comparison function
--   $$F=W(\beta)-\Big[\tfrac13+\tfrac23\hat\gamma\Big]L(\beta)-\tfrac23\sqrt{\tfrac{9}{b^2}+\tfrac{10}{ab}+\tfrac{1}{a^2}}-\tfrac{2}{3a}-\tfrac{2}{3b}$$
--   of the proof of Proposition 1.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** All quantities are real numbers. $D>0$ is added to the page's standing assumptions. The interest $r$ is dropped from the loan contract, following the paper's normalization $r=0$ (p. 12). IC reads "$(\hat\theta,\hat S)=\arg\max$" as "$(\theta,S)$ is a maximizer", chosen jointly with the contract (the standard principal–agent tie-break). Fair valuation is written $\gamma\,\Pi^N_E=B$, never $B/\Pi^N_E$. The Nash equilibrium is the platform's generic `CarbonDoubleCount.Planner.IsPureNash` over the two players `true` (manufacturer) and `false` (existing supplier); the lemmas `isEquityEq_iff` and `isLoanEq_iff` unfold it into the two best-response conditions. $G^{-1}$ is applied only to $B^G\ge0$ and $aB/(a+b)\ge0$.
-- source:
--   Zhang & Lee, Investment Strategies for Sourcing a New Technology in the Presence of a Mature Technology, SSRN 3269249 (version of 23 Mar 2021), pp. 7–13 (PDF 7–13), §3.1–§3.3, (1)–(5); closed forms from Lemma 1 p. 13, Lemma A.1 (A-3)–(A-5) pp. Appendix-11–12 (PDF 37–38), proof of Lemma A.1 p. Appendix-20 (PDF 46), proof of Proposition 1 p. Appendix-13 (PDF 39)

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_PureGame

namespace TechSourcing.PTS

/-- The parameters of the sourcing game (§3.1, pp. 8–10): the new supplier's technological
capabilities `a` (investment) and `b` (effort), the existing supplier's cost-reduction efficiency
`c`, the expected demand `D`, the selling price `R` of the end product, and the manufacturer's
bargaining power `β` against the existing supplier. -/
structure Params where
  a : ℝ
  b : ℝ
  c : ℝ
  D : ℝ
  R : ℝ
  β : ℝ

/-- Standing assumptions: `a > 0`, `b > 0` (p. 8), `c > 0` (p. 9), `R > 1` (p. 9),
`β ∈ [0, 1]` (p. 10), and `D > 0` (added: `D` is the expected demand, p. 9). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.a ∧ 0 < P.b ∧ 0 < P.c ∧ 0 < P.D ∧ 1 < P.R ∧ 0 ≤ P.β ∧ P.β ≤ 1

/-- Required non-labor investment `K(θ) = θ²/a` (p. 8). -/
noncomputable def K (P : Params) (θ : ℝ) : ℝ := θ ^ 2 / P.a

/-- Required effort `G(θ) = θ²/b` (p. 8). -/
noncomputable def G (P : Params) (θ : ℝ) : ℝ := θ ^ 2 / P.b

/-- The inverse `G⁻¹(x) = √(b x)` of `G` on `[0, ∞)`; it is only applied to `x ≥ 0`. -/
noncomputable def Ginv (P : Params) (x : ℝ) : ℝ := Real.sqrt (P.b * x)

/-- `W(β) = [(1 − β)R + β]D` (Lemma 1, p. 13). -/
def Wb (P : Params) : ℝ := ((1 - P.β) * P.R + P.β) * P.D

/-- `L(β) = D²(1 − β)β/(2c)` (Lemma 1, p. 13). -/
noncomputable def Lb (P : Params) : ℝ := P.D ^ 2 * (1 - P.β) * P.β / (2 * P.c)

/-- The new supplier's constraints (3), p. 10, together with `θ ∈ [0, 1]` (p. 8):
`G(θ) ≤ S ≤ B^G`, `S + K(θ) ≤ B` and `θ ≤ min {G⁻¹(B^G), G⁻¹(aB/(a + b))}`. -/
def Feasible (P : Params) (B BG θ S : ℝ) : Prop :=
  0 ≤ θ ∧ θ ≤ 1 ∧ G P θ ≤ S ∧ S ≤ BG ∧ S + K P θ ≤ B ∧
    θ ≤ min (Ginv P BG) (Ginv P (P.a * B / (P.a + P.b)))

/-! ### Equity investment (§3.2, pp. 10–11) -/

/-- The new supplier's expected equity value (1): `Π^N_E = [B − K(θ) − S] + θP`. -/
noncomputable def PiE (P : Params) (B pay θ S : ℝ) : ℝ := (B - K P θ - S) + θ * pay

/-- The new supplier's payoff (2): `U^N_E(θ, S) = (1 − γ)Π^N_E + [S − G(θ)]`. -/
noncomputable def UNE (P : Params) (γ B pay θ S : ℝ) : ℝ :=
  (1 - γ) * PiE P B pay θ S + (S - G P θ)

/-- The manufacturer's payoff in (P_E):
`U_E = −B + γΠ^N_E(θ, S) + θ(DR − P) + (1 − θ)β(R − φ)D`. -/
noncomputable def UE (P : Params) (φ γ B pay θ S : ℝ) : ℝ :=
  -B + γ * PiE P B pay θ S + θ * (P.D * P.R - pay) + (1 - θ) * P.β * (P.R - φ) * P.D

/-- An equity outcome: the contract `(B, B^G, γ, P)` (`pay` is the expected total procurement
payment `P`) and the new supplier's response `(θ, S)`. -/
structure EqOutcome where
  B : ℝ
  BG : ℝ
  γ : ℝ
  pay : ℝ
  θ : ℝ
  S : ℝ

/-- The outcomes the manufacturer can implement under equity: nonnegative `B`, `B^G`; an
equity share `γ ∈ [0, 1]`; `(θ, S)` feasible for (3) and a maximizer of `U^N_E` over (3)
(IC); the fair valuation `γ Π^N_E(θ, S) = B` (p. 11); and `U^N_E(θ, S) ≥ 0` (IR). -/
def EqOutcome.Admissible (P : Params) (o : EqOutcome) : Prop :=
  0 ≤ o.B ∧ 0 ≤ o.BG ∧ 0 ≤ o.γ ∧ o.γ ≤ 1 ∧
    Feasible P o.B o.BG o.θ o.S ∧
    (∀ θ' S', Feasible P o.B o.BG θ' S' →
      UNE P o.γ o.B o.pay θ' S' ≤ UNE P o.γ o.B o.pay o.θ o.S) ∧
    o.γ * PiE P o.B o.pay o.θ o.S = o.B ∧
    0 ≤ UNE P o.γ o.B o.pay o.θ o.S

/-- The manufacturer's best response to `φ` under equity: an admissible outcome maximizing
`U_E` over all admissible outcomes (problem (P_E), p. 11). -/
def IsManufBR_E (P : Params) (φ : ℝ) (o : EqOutcome) : Prop :=
  o.Admissible P ∧ ∀ o' : EqOutcome, o'.Admissible P →
    UE P φ o'.γ o'.B o'.pay o'.θ o'.S ≤ UE P φ o.γ o.B o.pay o.θ o.S

/-! ### Loan investment (§3.3, p. 12), with the interest `r` normalized to zero -/

/-- The new supplier's payoff (5) with `r = 0`:
`U^N_L = [B − K(θ) − S] + [S − G(θ)] + θ(P − B) − (1 − θ) min {B − S − K(θ), B}`. -/
noncomputable def UNL (P : Params) (B pay θ S : ℝ) : ℝ :=
  (B - K P θ - S) + (S - G P θ) + θ * (pay - B) - (1 - θ) * min (B - S - K P θ) B

/-- The manufacturer's payoff in (P_L) with `r = 0`:
`U_L = −B + θ(DR − P + B) + (1 − θ)(min {B − K(θ) − S, B} + β(R − φ)D)`. -/
noncomputable def UL (P : Params) (φ B pay θ S : ℝ) : ℝ :=
  -B + θ * (P.D * P.R - pay + B) + (1 - θ) * (min (B - K P θ - S) B + P.β * (P.R - φ) * P.D)

/-- A loan outcome: the contract `(B, B^G, P)` (`r = 0`) and the response `(θ, S)`. -/
structure LoanOutcome where
  B : ℝ
  BG : ℝ
  pay : ℝ
  θ : ℝ
  S : ℝ

/-- The outcomes the manufacturer can implement under a loan: nonnegative `B`, `B^G`;
`(θ, S)` feasible for (3) and a maximizer of `U^N_L` over (3) (IC); `U^N_L(θ, S) ≥ 0` (IR). -/
def LoanOutcome.Admissible (P : Params) (o : LoanOutcome) : Prop :=
  0 ≤ o.B ∧ 0 ≤ o.BG ∧
    Feasible P o.B o.BG o.θ o.S ∧
    (∀ θ' S', Feasible P o.B o.BG θ' S' →
      UNL P o.B o.pay θ' S' ≤ UNL P o.B o.pay o.θ o.S) ∧
    0 ≤ UNL P o.B o.pay o.θ o.S

/-- The manufacturer's best response to `φ` under a loan (problem (P_L), p. 12). -/
def IsManufBR_L (P : Params) (φ : ℝ) (o : LoanOutcome) : Prop :=
  o.Admissible P ∧ ∀ o' : LoanOutcome, o'.Admissible P →
    UL P φ o'.B o'.pay o'.θ o'.S ≤ UL P φ o.B o.pay o.θ o.S

/-! ### The existing supplier (4) and the equilibrium -/

/-- The existing supplier's payoff (4): `U^O(φ | θ) = (1 − θ)(1 − β)(R − φ)D − c(1 − φ)²`. -/
def UO (P : Params) (θ φ : ℝ) : ℝ :=
  (1 - θ) * (1 - P.β) * (P.R - φ) * P.D - P.c * (1 - φ) ^ 2

/-- `φ` is a best response of the existing supplier to the PTS `θ`: `φ ≤ 1` maximizes (4)
over all `φ' ≤ 1`. -/
def IsExistingBR (P : Params) (θ φ : ℝ) : Prop :=
  φ ≤ 1 ∧ ∀ φ', φ' ≤ 1 → UO P θ φ' ≤ UO P θ φ

/-- Strategy spaces of the static game between the manufacturer (`true`, an equity outcome)
and the existing supplier (`false`, a production cost `φ`). -/
abbrev EqStrat : Bool → Type := fun i => cond i EqOutcome ℝ

/-- Strategy spaces of the loan game: manufacturer `true`, existing supplier `false`. -/
abbrev LoanStrat : Bool → Type := fun i => cond i LoanOutcome ℝ

/-- The strategy profile `(o, φ)` of the equity game. -/
def eqProfile (o : EqOutcome) (φ : ℝ) : (i : Bool) → EqStrat i :=
  fun i => Bool.rec (motive := EqStrat) φ o i

/-- The strategy profile `(o, φ)` of the loan game. -/
def loanProfile (o : LoanOutcome) (φ : ℝ) : (i : Bool) → LoanStrat i :=
  fun i => Bool.rec (motive := LoanStrat) φ o i

/-- Feasible sets of the equity game: admissible outcomes, and `φ ≤ 1`. -/
def eqFeasible (P : Params) : (i : Bool) → Set (EqStrat i) :=
  fun i => Bool.rec (motive := fun i => Set (EqStrat i)) {φ : ℝ | φ ≤ 1}
    {o : EqOutcome | o.Admissible P} i

/-- Feasible sets of the loan game. -/
def loanFeasible (P : Params) : (i : Bool) → Set (LoanStrat i) :=
  fun i => Bool.rec (motive := fun i => Set (LoanStrat i)) {φ : ℝ | φ ≤ 1}
    {o : LoanOutcome | o.Admissible P} i

/-- Payoffs of the equity game: `U_E` for the manufacturer and (4) for the existing supplier. -/
noncomputable def eqPayoff (P : Params) (i : Bool) (s : (i : Bool) → EqStrat i) : ℝ :=
  cond i
    (UE P (s false) (s true).γ (s true).B (s true).pay (s true).θ (s true).S)
    (UO P (s true).θ (s false))

/-- Payoffs of the loan game: `U_L` for the manufacturer and (4) for the existing supplier. -/
noncomputable def loanPayoff (P : Params) (i : Bool) (s : (i : Bool) → LoanStrat i) : ℝ :=
  cond i
    (UL P (s false) (s true).B (s true).pay (s true).θ (s true).S)
    (UO P (s true).θ (s false))

/-- `(o, φ)` is a Nash equilibrium of the equity game (p. 11, "a static game between the
existing supplier and the manufacturer"). -/
def IsEquityEq (P : Params) (o : EqOutcome) (φ : ℝ) : Prop :=
  CarbonDoubleCount.Planner.IsPureNash (strategy := EqStrat) (eqFeasible P) (eqPayoff P)
    (eqProfile o φ)

/-- `(o, φ)` is a Nash equilibrium of the loan game. -/
def IsLoanEq (P : Params) (o : LoanOutcome) (φ : ℝ) : Prop :=
  CarbonDoubleCount.Planner.IsPureNash (strategy := LoanStrat) (loanFeasible P) (loanPayoff P)
    (loanProfile o φ)

/-- The equity equilibrium unfolded into its two best-response conditions. -/
theorem isEquityEq_iff (P : Params) (o : EqOutcome) (φ : ℝ) :
    IsEquityEq P o φ ↔ IsManufBR_E P φ o ∧ IsExistingBR P o.θ φ := by
  constructor
  · rintro ⟨hf, hb⟩
    refine ⟨⟨hf true, fun o' ho' => ?_⟩, ⟨hf false, fun φ' hφ' => ?_⟩⟩
    · simpa [eqPayoff, eqProfile, Function.update] using hb true o' ho'
    · simpa [eqPayoff, eqProfile, Function.update] using hb false φ' hφ'
  · rintro ⟨⟨ho, hbo⟩, hφ, hbφ⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · cases i
      · exact hφ
      · exact ho
    · cases i
      · intro x hx
        simpa [eqPayoff, eqProfile, Function.update] using hbφ x hx
      · intro x hx
        simpa [eqPayoff, eqProfile, Function.update] using hbo x hx

/-- The loan equilibrium unfolded into its two best-response conditions. -/
theorem isLoanEq_iff (P : Params) (o : LoanOutcome) (φ : ℝ) :
    IsLoanEq P o φ ↔ IsManufBR_L P φ o ∧ IsExistingBR P o.θ φ := by
  constructor
  · rintro ⟨hf, hb⟩
    refine ⟨⟨hf true, fun o' ho' => ?_⟩, ⟨hf false, fun φ' hφ' => ?_⟩⟩
    · simpa [loanPayoff, loanProfile, Function.update] using hb true o' ho'
    · simpa [loanPayoff, loanProfile, Function.update] using hb false φ' hφ'
  · rintro ⟨⟨ho, hbo⟩, hφ, hbφ⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · cases i
      · exact hφ
      · exact ho
    · cases i
      · intro x hx
        simpa [loanPayoff, loanProfile, Function.update] using hbφ x hx
      · intro x hx
        simpa [loanPayoff, loanProfile, Function.update] using hbo x hx

/-! ### Closed forms (Lemma 1, Lemma A.1, proof of Proposition 1) -/

/-- `√(9a² + 10ab + b²)`. -/
noncomputable def sq (P : Params) : ℝ := Real.sqrt (9 * P.a ^ 2 + 10 * P.a * P.b + P.b ^ 2)

/-- The equity share `γ̂ = (3(a + b) − √(9a² + 10ab + b²))/(4b)` (proof of Lemma A.1, p. A-20). -/
noncomputable def gammaHat (P : Params) : ℝ := (3 * (P.a + P.b) - sq P) / (4 * P.b)

/-- `π(φ) = D[R − β(R − φ)]` (Lemma A.1). -/
def piPhi (P : Params) (φ : ℝ) : ℝ := P.D * (P.R - P.β * (P.R - φ))

/-- `3/a + 3/b + √(9a² + 10ab + b²)/(ab)`. -/
noncomputable def denE (P : Params) : ℝ := 3 / P.a + 3 / P.b + sq P / (P.a * P.b)

/-- (A-3): `θ̂_E(φ) = π(φ)/(3/a + 3/b + √(9a² + 10ab + b²)/(ab))`. -/
noncomputable def thetaHatE (P : Params) (φ : ℝ) : ℝ := piPhi P φ / denE P

/-- (A-4): `θ̂_L(φ) = π(φ)/[√((1/a + 3/b)² + 6π(φ)/a) + (1/a + 3/b)]`. -/
noncomputable def thetaHatL (P : Params) (φ : ℝ) : ℝ :=
  piPhi P φ / (Real.sqrt ((1 / P.a + 3 / P.b) ^ 2 + 6 * piPhi P φ / P.a) + (1 / P.a + 3 / P.b))

/-- (A-5): `φ̂(θ) = 1 − D(1 − β)(1 − θ)/(2c)`. -/
noncomputable def phiHat (P : Params) (θ : ℝ) : ℝ := 1 - P.D * (1 - P.β) * (1 - θ) / (2 * P.c)

/-- (6): `θ*_E = (W − L)/(3/a + 3/b + √(9a² + 10ab + b²)/(ab) − L)`. -/
noncomputable def thetaEStar (P : Params) : ℝ := (Wb P - Lb P) / (denE P - Lb P)

/-- (7): `θ*_L = [√((1 + 3a/b − (a/2)L)² + 6a(W − L)) − (1 + 3a/b − (a/2)L)]/6`. -/
noncomputable def thetaLStar (P : Params) : ℝ :=
  (Real.sqrt ((1 + 3 * P.a / P.b - P.a / 2 * Lb P) ^ 2 + 6 * P.a * (Wb P - Lb P))
    - (1 + 3 * P.a / P.b - P.a / 2 * Lb P)) / 6

/-- The comparison function of the proof of Proposition 1 (p. A-13):
`W − [1/3 + (2/3)γ̂]L − (2/3)√(9/b² + 10/(ab) + 1/a²) − 2/(3a) − 2/(3b)`. -/
noncomputable def Fcmp (P : Params) : ℝ :=
  Wb P - (1 / 3 + 2 / 3 * gammaHat P) * Lb P
    - 2 / 3 * Real.sqrt (9 / P.b ^ 2 + 10 / (P.a * P.b) + 1 / P.a ^ 2)
    - 2 / (3 * P.a) - 2 / (3 * P.b)

end TechSourcing.PTS


