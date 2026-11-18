-- Prove2me | Definitions.Def_TwoStageRnQ_RuleRand
-- name    : TwoStageRnQ_RuleRand
-- status  : Definition
-- author  : @Ming Hu
-- created : 2026-11-17T00:21:00.215249+00:00
-- url     : https://prove2.me/theorems/bb6a0ebf-dce7-4ac3-8f67-3feb1b6ab97e
-- title:
--   Classical $(R,nQ)$ rules with an outcome-dependent upstream remainder
-- statement:
--   Two classes of shipment policies on the model `TwoStageRnQ_Model`, for fixed integer reorder points $R_1,R_2$ and lot parameters $Q,n\ge1$. Write $IP_i=x_i+U_i-N$, $IL_2(t)=x_2+U_2(t-L_2)-N(t)$, and $W=IL_2-IP_1$ for the physical stock held at Stage 2.
--
--   `FollowsRnQRand S π R₁ R₂ Q n`: there are an upstream remainder $\rho(\omega)\in\{0,\dots,Q-1\}$, measurable with respect to the information at time $0$ (so it may vary with the outcome), and an integer process $\widehat{IP}_1$ such that, almost surely, for every $t\ge0$:
--   1. $IP_2(0)-\rho\equiv\widehat{IP}_1(0)\pmod Q$;
--   2. $\widehat{IP}_1(t)+N(t)\equiv\widehat{IP}_1(0)+N(0)\pmod Q$;
--   3. $nQ$ divides $U_2(t)-U_2(0)$;
--   4. $R_2<IP_2(t)\le R_2+nQ$;
--   5. $R_1<\widehat{IP}_1(t)\le R_1+Q$;
--   6. $IP_1(t)=\min\{\widehat{IP}_1(t),\,IL_2(t)-\rho\}$.
--
--   With a constant $\rho$ this is `Rule.FollowsRnQ` for the controls $(R_1,R_2,Q,n,\rho)$.
--
--   `PaperRnQAll S π R₁ R₂ Q n` transcribes the paper's compatible initialization and operating rule (Appendix A.2) with no condition on the remainder: there is a process $\beta\ge0$ of pending downstream requests such that, almost surely, the initial Stage-2 pipeline consists of complete lots ($nQ$ divides $U_2(0)-U_2(s)$ for $s\in[-L_2,0]$) and, for every $t\ge0$, $R_1<IP_1+Q\beta\le R_1+Q$, $Q$ divides $U_1(t)-U_1(0)$, $nQ$ divides $U_2(t)-U_2(0)$, $R_2<IP_2\le R_2+nQ$, and $\beta>0$ implies $W<Q$.
--
--   **Formalization Note** The remainder $W(0)\bmod Q$ of a `PaperRnQAll` policy may be any time-0 random variable. The companion target `TwoStageRnQ.paper_rule_follows_rand` proves `PaperRnQAll → FollowsRnQRand` and `FollowsRnQ → FollowsRnQRand`. Conditions of the paper that this inclusion does not need (finite moments of the initial state, complete Stage-1 pipeline lots, FIFO order) are left out of `PaperRnQAll`, which only enlarges it. The earlier definition `TwoStageRnQ_Rule` covers a fixed remainder only: its `FollowsRnQ` holds for compatible initializations whose remainder equals the control $\rho$.
-- source:
--   M. Hu, "A 5/3 Guarantee for Echelon Stock (R,nQ) Policies in Two-Stage Stochastic Serial Systems", manuscript rq_167.tex (Sept. 28, 2026 version); posted as arXiv:2609.06318. Section 4.1; Appendices A.2-A.3 (compatible initialization, Lemma A.2).

import Definitions.Def_TwoStageRnQ_Rule

/-!
# Classical `(R,nQ)` rules from compatible initializations with an outcome-dependent remainder

Definitions accompanying "A 5/3 Guarantee for Echelon Stock (R,nQ)
Policies in Two-Stage Stochastic Serial Systems" (manuscript `rq_167.tex`), Section 4.1 and
Appendices A.2-A.3, on the model `TwoStageRnQ_Model`.

The controls `R₁, R₂ ∈ ℤ` and `Q, n ≥ 1` are fixed numbers. With `IP_i = x_i + U_i - N`,
`IL₂(t) = x₂ + U₂(t - L₂) - N(t)` and the Stage-2 physical stock `W = IL₂ - IP₁`:

* `FollowsRnQRand S π R₁ R₂ Q n`: there are an upstream remainder `ρ(ω) ∈ {0, …, Q-1}`, known at time
  `0` and allowed to vary with the outcome, and an integer nominal downstream position `Î₁` such
  that, almost surely, for all `t ≥ 0`: `IP₂(0) - ρ ≡ Î₁(0) (mod Q)`;
  `Î₁(t) + N(t) ≡ Î₁(0) + N(0) (mod Q)`; `nQ` divides `U₂(t) - U₂(0)`; `R₂ < IP₂(t) ≤ R₂ + nQ`;
  `R₁ < Î₁(t) ≤ R₁ + Q`; and `IP₁(t) = min(Î₁(t), IL₂(t) - ρ)`. For a constant `ρ` this is
  `Rule.FollowsRnQ` with controls `(R₁, R₂, Q, n, ρ)`.
* `PaperRnQAll S π R₁ R₂ Q n`: a literal transcription of the paper's compatible initialization and
  operating rule with no condition on the remainder: there is a process `β ≥ 0` of pending
  downstream requests such that, almost surely, the initial Stage-2 pipeline consists of complete
  lots (`nQ ∣ U₂(0) - U₂(s)` for `s ∈ [-L₂, 0]`) and, for all `t ≥ 0`, the nominal position
  `IP₁ + Qβ` lies in `{R₁+1, …, R₁+Q}`, downstream dispatches are complete lots
  (`Q ∣ U₁(t) - U₁(0)`), upstream orders are lots of `nQ` with `IP₂ ∈ {R₂+1, …, R₂+nQ}`, and a
  pending request implies `W < Q`. Its remainder `W(0) mod Q` may be any time-`0` random variable.
-/

open MeasureTheory

noncomputable section

namespace TwoStageRnQ

namespace RuleRand

/-- `π` follows the classical `(R, nQ)` rule with fixed controls `(R₁, R₂, Q, n)` from a compatible
initialization whose upstream remainder `ρ`, known at time `0`, may vary with the outcome. -/
def FollowsRnQRand {P : Params} (S : DemandSpace P) (π : ShipmentPolicy P S) (R1 R2 : ℤ)
    (Q n : ℕ+) : Prop :=
  ∃ ρ : S.Ω → ℕ, Measurable[S.𝓕 0] ρ ∧ (∀ ω, ρ ω < (Q : ℕ)) ∧
    ∃ Ihat : ℝ → S.Ω → ℤ, ∀ᵐ ω ∂S.ν,
      ((Q : ℕ) : ℤ) ∣ (π.x2 ω + π.U2 0 ω - S.N 0 ω) - (ρ ω : ℤ) - Ihat 0 ω ∧
      ∀ t : ℝ, 0 ≤ t →
        ((Q : ℕ) : ℤ) ∣ (Ihat t ω + S.N t ω) - (Ihat 0 ω + S.N 0 ω) ∧
        ((n : ℕ) : ℤ) * ((Q : ℕ) : ℤ) ∣ π.U2 t ω - π.U2 0 ω ∧
        (R2 < π.x2 ω + π.U2 t ω - S.N t ω ∧
          π.x2 ω + π.U2 t ω - S.N t ω ≤ R2 + ((n : ℕ) : ℤ) * ((Q : ℕ) : ℤ)) ∧
        (R1 < Ihat t ω ∧ Ihat t ω ≤ R1 + ((Q : ℕ) : ℤ)) ∧
        π.x1 ω + π.U1 t ω - S.N t ω
          = min (Ihat t ω) (π.x2 ω + π.U2 (t - P.L2) ω - S.N t ω - (ρ ω : ℤ))

/-- Literal transcription of the paper's classical complete-lot rule with controls
`(R₁, R₂, Q, n)` from a compatible initialization, with no condition on the upstream remainder. -/
def PaperRnQAll {P : Params} (S : DemandSpace P) (π : ShipmentPolicy P S) (R1 R2 : ℤ)
    (Q n : ℕ+) : Prop :=
  ∃ β : ℝ → S.Ω → ℤ, ∀ᵐ ω ∂S.ν,
    (∀ s : ℝ, -P.L2 ≤ s → s ≤ 0 → ((n : ℕ) : ℤ) * ((Q : ℕ) : ℤ) ∣ π.U2 0 ω - π.U2 s ω) ∧
    ∀ t : ℝ, 0 ≤ t →
      0 ≤ β t ω ∧
      (R1 < π.x1 ω + π.U1 t ω - S.N t ω + ((Q : ℕ) : ℤ) * β t ω ∧
        π.x1 ω + π.U1 t ω - S.N t ω + ((Q : ℕ) : ℤ) * β t ω ≤ R1 + ((Q : ℕ) : ℤ)) ∧
      ((Q : ℕ) : ℤ) ∣ π.U1 t ω - π.U1 0 ω ∧
      ((n : ℕ) : ℤ) * ((Q : ℕ) : ℤ) ∣ π.U2 t ω - π.U2 0 ω ∧
      (R2 < π.x2 ω + π.U2 t ω - S.N t ω ∧
        π.x2 ω + π.U2 t ω - S.N t ω ≤ R2 + ((n : ℕ) : ℤ) * ((Q : ℕ) : ℤ)) ∧
      (0 < β t ω →
        (π.x2 ω + π.U2 (t - P.L2) ω - S.N t ω) - (π.x1 ω + π.U1 t ω - S.N t ω) < ((Q : ℕ) : ℤ))

end RuleRand

end TwoStageRnQ


