-- Prove2me | Definitions.Def_QFairEx_Protocol_pAcc
-- name    : QFairEx_Protocol_pAcc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:24:25.507948+00:00
-- url     : https://prove2.me/theorems/def8a09a-0ff7-4a3c-a239-f67ee60f4db1
-- title:
--   The acceptance probability $p_p(t)$ of the stopping execution
-- statement:
--   For $p\in\{0,1\}$ and a cut $t$, the **acceptance probability**
--   $$p_p(t)=\Pr_{\mathrm{Stop}(p,t)}[f_p=\mathrm{acc}]$$
--   averages over the sixteen pairs of independent uniform BB84 challenges $|\phi_1\rangle=H^{\theta_1}X^{x_1}|0\rangle$, $|\phi_2\rangle=H^{\theta_2}X^{x_2}|0\rangle$, with inputs $\psi_0=E_0\phi_1$ and $\psi_1=E_1\phi_2$, of the trace of $P_p$'s accepting output in Stop$(p,t)$.
--
--   The proof of Theorem 4.8 tracks $p_0(t)$ and $p_1(t)$ along the cuts: they start at $0$ (Lemma 4.9), end at $1$, and each moves only in rounds where the other party sends (Lemma 4.10).
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), §4.2.2, "Stopping executions", p.23

import Mathlib
import Definitions.Def_QFairEx_SupportedOn
import Definitions.Def_QFairEx_bb84
import Definitions.Def_QFairEx_encVec
import Definitions.Def_QFairEx_Protocol
import Definitions.Def_QFairEx_Protocol_stopAcc0

namespace QFairEx

open Matrix

/-- **The acceptance probability `p_p(t)`.**
Chung, Lee, Raizes, Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of
2026-11-02, sha256 0099b883…), §4.2.2, "Stopping executions", p.23: "Write (f_p, σ_p) for P_p's
decision and quantum output, and set p_p(t) := Pr_{Stop(p,t)}[f_p = acc]. The probability
averages over the independent BB84 challenges and the execution randomness."

With encodings `e0` (into `ι0`) and `e1` (into `ι1`): for each of the 16 challenge pairs
`|ϕ₁⟩ = H^{θ₁}X^{x₁}|0⟩`, `|ϕ₂⟩ = H^{θ₂}X^{x₂}|0⟩` (uniform), the inputs are `ψ₀ = E₀ϕ₁`,
`ψ₁ = E₁ϕ₂` (p.22), and `p_p(t)` is the average of `Pr[f_p = acc] = Re tr σ_acc` in Stop(p, t).

**Formalization Note.** `p : Fin 2`; `p = 0` uses `stopAcc0` (honest P₀, stopped P₁), `p = 1`
uses `stopAcc1` (honest P₁, stopped P₀). -/
noncomputable def Protocol.pAcc {ι0 ι1 : Type} [Fintype ι0] [Fintype ι1] [DecidableEq ι0]
    [DecidableEq ι1] (P : Protocol ι0 ι1) (e0 : Fin 2 → ι0 → ℂ) (e1 : Fin 2 → ι1 → ℂ)
    (p : Fin 2) (t : ℕ) : ℝ :=
  (1 / 16 : ℝ) * ∑ θ1 : Bool, ∑ x1 : Bool, ∑ θ2 : Bool, ∑ x2 : Bool,
    if p = 0 then
      (P.stopAcc0 (pureDensity (prodVec (encVec e0 (bb84 θ1 x1)) (encVec e1 (bb84 θ2 x2)))) t).trace.re
    else
      (P.stopAcc1 (pureDensity (prodVec (encVec e0 (bb84 θ1 x1)) (encVec e1 (bb84 θ2 x2)))) t).trace.re

end QFairEx


