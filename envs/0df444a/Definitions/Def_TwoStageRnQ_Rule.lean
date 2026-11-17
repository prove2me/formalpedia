-- Prove2me | Definitions.Def_TwoStageRnQ_Rule
-- name    : TwoStageRnQ_Rule
-- status  : Definition
-- author  : @beatlesmania
-- created : 2026-11-17T00:20:30.241669+00:00
-- url     : https://prove2.me/theorems/797e6637-a086-43b7-a6ee-2a491e5061c9
-- title:
--   Classical $(R,nQ)$ rules from compatible initializations
-- statement:
--   Integer shorthands for classical controls and the operational class of classical $(R,nQ)$ rules started from a compatible initialization, on the model `TwoStageRnQ_Model`.
--
--   For controls $c=(R_1,R_2,Q,n,\rho)$ with $0\le\rho<Q$ ($\rho$ is the remainder of the Stage-2 stock modulo $Q$), `qZ`, `nZ`, `rZ`, `mZ`, `oZ` are the integers $Q$, $n$, $\rho$, $nQ$ and $\ell-\rho+(n-1)Q$ with $\ell=R_2-R_1$, and `qc c` is the pair of lot sizes $(Q,nQ)$.
--
--   `FollowsRnQ S π c` says that the shipment policy $\pi$ runs the classical rule with complete-lot matching from a compatible initialization: there is an integer process $\widehat{IP}_1$ (the nominal downstream position, that is, the actual position plus pending requests) such that, almost surely, for every $t\ge0$:
--   1. $IP_2(0)-\rho\equiv\widehat{IP}_1(0)\pmod Q$ (complete-lot pipelines and Stage-2 stock congruent to $\rho$);
--   2. $\widehat{IP}_1(t)+N(t)\equiv\widehat{IP}_1(0)+N(0)\pmod Q$ (downstream requests come in lots of $Q$);
--   3. $nQ$ divides $U_2(t)-U_2(0)$ (supplier orders come in lots of $nQ$);
--   4. $R_2<IP_2(t)\le R_2+nQ$;
--   5. $R_1<\widehat{IP}_1(t)\le R_1+Q$;
--   6. $IP_1(t)=\min\{\widehat{IP}_1(t),\,IL_2(t)-\rho\}$ (a request waits only when no complete lot is available).
--
--   Here $IP_i=x_i+U_i-N$ and $IL_2(t)=x_2+U_2(t-L_2)-N(t)$.
--
--   **Formalization Note** The conditions are stated through positions, so they do not depend on the integer origins of the cumulative dispatch counts, and they are required almost surely. Every compatible initialization of Appendix A.2 together with the operating rule of Section 4.1 satisfies them, and so does the counter construction of eq. (A.6).
-- source:
--   M. Hu, "A 5/3 Guarantee for Echelon Stock (R,nQ) Policies in Two-Stage Stochastic Serial Systems", manuscript rq_167.tex (Sept. 28, 2026 version); posted as arXiv:2609.06318. Section 4.1; Appendices A.2-A.3 (compatible initialization, Lemma A.2).

import Definitions.Def_TwoStageRnQ_Model

/-!
# Classical `(R,nQ)` rules from compatible initializations

Definitions accompanying "A 5/3 Guarantee for Echelon Stock (R,nQ)
Policies in Two-Stage Stochastic Serial Systems" (manuscript `rq_167.tex`), Section 4 and
Appendices A.2-A.3, on the model `TwoStageRnQ_Model`.

For classical controls `c = (R₁, R₂, Q, n, ρ)` (`ρ < Q` is the remainder of the Stage-2 stock
modulo `Q`), `qZ, nZ, rZ, mZ, oZ` are the integers `Q, n, ρ, nQ, ℓ - ρ + (n - 1) Q` with
`ℓ = R₂ - R₁`, and `qc c = (Q, nQ)` are the two lot sizes.

`FollowsRnQ S π c` says that the shipment policy `π` operates the classical rule with complete-lot
matching from a compatible initialization. It is stated through positions, so it does not depend
on the integer origins chosen for the cumulative dispatch counts, and it is required almost
surely. There is an integer nominal downstream position `Î₁` (actual position plus pending
requests) such that, almost surely, for all `t ≥ 0`:
* the initial state is residue-compatible: `IP₂(0) - ρ ≡ Î₁(0) (mod Q)` (complete-lot pipelines and
  Stage-2 stock congruent to `ρ`);
* downstream requests come in lots of `Q`: `Î₁(t) + N(t) ≡ Î₁(0) + N(0) (mod Q)`;
* supplier orders come in lots of `nQ`;
* the Stage-2 position stays in `(R₂, R₂ + nQ]`;
* the nominal downstream position stays in `(R₁, R₁ + Q]`;
* complete-lot matching: `IP₁ = min(Î₁, IL₂ - ρ)` (a request waits only if no complete lot is
  available).
-/

open MeasureTheory

noncomputable section

namespace TwoStageRnQ

namespace Rule

/-- Downstream lot size `Q` as an integer. -/
def qZ (c : ClassicalControls) : ℤ := ((c.1.2.2.1 : ℕ) : ℤ)

/-- Upstream multiplier `n` as an integer. -/
def nZ (c : ClassicalControls) : ℤ := ((c.1.2.2.2.1 : ℕ) : ℤ)

/-- Upstream remainder `ρ` as an integer. -/
def rZ (c : ClassicalControls) : ℤ := ((c.1.2.2.2.2 : ℕ) : ℤ)

/-- Upstream lot size `m = nQ`. -/
def mZ (c : ClassicalControls) : ℤ := nZ c * qZ c

/-- Offset of the upstream counter, `ℓ - ρ + (n - 1) Q` with `ℓ = R₂ - R₁`. -/
def oZ (c : ClassicalControls) : ℤ := c.1.2.1 - c.1.1 - rZ c + (nZ c - 1) * qZ c

/-- The lot sizes `(Q, nQ)` of the classical rule. -/
def qc (c : ClassicalControls) : ℕ+ × ℕ+ := (c.1.2.2.1, c.1.2.2.2.1 * c.1.2.2.1)

/-- The shipment policy `π` follows the classical `(R, nQ)` rule with complete-lot matching from a
compatible initialization, for controls `c = (R₁, R₂, Q, n, ρ)` (see the module docstring). -/
def FollowsRnQ {P : Params} (S : DemandSpace P) (π : ShipmentPolicy P S) (c : ClassicalControls) :
    Prop :=
  ∃ Ihat : ℝ → S.Ω → ℤ, ∀ᵐ ω ∂S.ν,
    qZ c ∣ (π.x2 ω + π.U2 0 ω - S.N 0 ω) - rZ c - Ihat 0 ω ∧
    ∀ t : ℝ, 0 ≤ t →
      qZ c ∣ (Ihat t ω + S.N t ω) - (Ihat 0 ω + S.N 0 ω) ∧
      mZ c ∣ π.U2 t ω - π.U2 0 ω ∧
      (c.1.2.1 < π.x2 ω + π.U2 t ω - S.N t ω ∧ π.x2 ω + π.U2 t ω - S.N t ω ≤ c.1.2.1 + mZ c) ∧
      (c.1.1 < Ihat t ω ∧ Ihat t ω ≤ c.1.1 + qZ c) ∧
      π.x1 ω + π.U1 t ω - S.N t ω
        = min (Ihat t ω) (π.x2 ω + π.U2 (t - P.L2) ω - S.N t ω - rZ c)

end Rule

end TwoStageRnQ


