-- Prove2me | Definitions.Def_SparsestCutOracle_Main_Supplement_PrimalDual
-- name    : SparsestCutOracle_Main_Supplement_PrimalDual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:48:25.651887+00:00
-- url     : https://prove2.me/theorems/14a72c08-b489-4351-b00e-30d8306db657
-- title:
--   Algorithm 1 with exact exponential updates and immediate failure
-- statement:
--   For a general normalized SDP, fix $\rho,\alpha>0$, $0<\epsilon<1$, and $\eta=\epsilon\alpha/(2\rho\tau)$. Algorithm 1 starts with $C^{(1)}=C$ and density $P^{(1)}=I/n$. In iteration $t$ it passes $X^{(t)}=\tau\Gamma P^{(t)}\Gamma$ and the current objective to the oracle. A failure terminates immediately with that very certificate. Otherwise it stores the response $y^{(t)}$, replaces the objective by $C_{\rm out}^{(t)}$, sets $M^{(t)}=\Gamma Z^{(t)}\Gamma/\rho$ and computes
--   $$
--   P^{(t+1)}=\frac{\exp(-\eta\sum_{s\le t}M^{(s)})}{\operatorname{Tr}\exp(-\eta\sum_{s\le t}M^{(s)})}.
--   $$
--   After $T\ge1$ successful iterations it returns the final objective and the exact corrected average
--   $$
--   y^*=\frac1T\sum_{t=1}^T y^{(t)}+\frac{\epsilon\alpha}{\tau}e_M.
--   $$
--   The recursive execution retains the cumulative loss, current objective and all responses. Its initial density uses the exponential formula at zero, equal to $I/n$ for $n>0$. Zero-based loop state $T$ contains the source's $C^{(T+1)}$. This is an exact mathematical execution for a correctness theorem; it does not add matrix exponential as a scalar-machine instruction or claim a complexity bound.
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), pp. 14–15, Algorithm 1

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Supplement_GeneralSDP

namespace SparsestCutOracle.Main.Supplement

structure PDState (n m : ℕ) where
  lossSum : Mat n
  objective : Mat n
  answers : List (Fin (m + 1) → ℝ)

noncomputable def pdDensity {n : ℕ} (η : ℝ) (lossSum : Mat n) : Mat n :=
  (Matrix.trace (NormedSpace.exp ((-η) • lossSum)))⁻¹ •
    NormedSpace.exp ((-η) • lossSum)

/-- Algorithm 1's exact execution. A failure is absorbing: no later oracle call is made.
Zero-based loop states hold C^(t+1), all t answers, and the cumulative loss.
The first density is exp(0)/Tr(exp(0)) = I/n for n>0. -/
noncomputable def primalDualRun {n m : ℕ} {Certificate : Type}
    (S : NormalizedSDP n m) (C : Mat n) (ρ α ε : ℝ)
    (O : GeneralOracle n m Certificate) : ℕ → (Certificate × Mat n) ⊕ PDState n m
  | 0 => Sum.inr ⟨0, C, []⟩
  | t + 1 =>
    match primalDualRun S C ρ α ε O t with
    | Sum.inl failure => Sum.inl failure
    | Sum.inr s =>
      let Γ := inverseSqrt S
      let η := ε * α / (2 * ρ * S.τ)
      let X := S.τ • (Γ * pdDensity η s.lossSum * Γ)
      match O t X s.objective α with
      | Sum.inl r => Sum.inl (r, s.objective)
      | Sum.inr r =>
        Sum.inr ⟨s.lossSum + ρ⁻¹ • (Γ * oracleFeedback S r * Γ),
          r.C_out, s.answers ++ [r.y]⟩

noncomputable def averageDual {n m : ℕ} (S : NormalizedSDP n m) (α ε : ℝ)
    (T : ℕ) (ys : List (Fin (m + 1) → ℝ)) : Fin (m + 1) → ℝ :=
  fun j => (T : ℝ)⁻¹ * ys.sum j +
    if j = Fin.last m then ε * α / S.τ else 0

/-- Actual returned value: the first failure certificate, or the corrected average and
FINAL objective. This is an exact mathematical algorithm, with no complexity claim. -/
noncomputable def primalDual {n m : ℕ} {Certificate : Type}
    (S : NormalizedSDP n m) (C : Mat n) (ρ α ε : ℝ)
    (O : GeneralOracle n m Certificate) (T : ℕ) :
    (Certificate × Mat n) ⊕ ((Fin (m + 1) → ℝ) × Mat n) :=
  match primalDualRun S C ρ α ε O T with
  | Sum.inl failure => Sum.inl failure
  | Sum.inr s => Sum.inr (averageDual S α ε T s.answers, s.objective)

end SparsestCutOracle.Main.Supplement


