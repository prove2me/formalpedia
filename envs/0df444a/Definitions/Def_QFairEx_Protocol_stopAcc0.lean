-- Prove2me | Definitions.Def_QFairEx_Protocol_stopAcc0
-- name    : QFairEx_Protocol_stopAcc0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:23:05.548094+00:00
-- url     : https://prove2.me/theorems/4d705078-9407-494d-8b64-76642fee5722
-- title:
--   The stopping executions Stop(p, t) and the honest party's conditional outputs
-- statement:
--   For $p\in\{0,1\}$ and a cut $t\in\{0,\dots,T\}$, **Stop$(p,t)$** is the execution in which $P_{\bar p}$ ($\bar p=1-p$) is controlled by the pre-determined fail-stop adversary with cut $t$, while $P_p$ and the trusted party follow the protocol until termination:
--
--   1. everyone runs honestly through cut $t$;
--   2. in rounds $t+1,\dots,T$, $P_p$ and CTTP continue: in rounds where $P_p$ is the sender its messages to $P_{\bar p}$ are discarded; in rounds where $P_{\bar p}$ is the scheduled sender, $P_p$ and CTTP record `abort`; CTTP's messages to $P_{\bar p}$ are discarded;
--   3. $P_p$ applies its decision instrument.
--
--   The outputs are the subnormalized conditional states $\sigma^{(p)}_{\mathrm{acc}}$ (on $\mathrm{Ver}_{\bar p}$'s register) and $\sigma^{(p)}_{\mathrm{rej}}$ (on $\mathrm{Ver}_p$'s register), with all classical memories summed, so that $\operatorname{tr}\sigma^{(p)}_{\mathrm{acc}}=\Pr[f_p=\mathrm{acc}]$. For $t=T$ this is the completed honest execution with $P_p$'s outputs retained.
--
--   **Formalization Note** The stopped party's registers are traced out at its cut: after the cut it sends nothing, so its remaining processing, which acts only on its own registers, cannot change the joint state of $P_p$ and CTTP (the paper's own argument in the proofs of Lemmas 4.10 and 4.12). Definition 4.2 also allows a randomly sampled cut, a mixture of fixed cuts; only fixed cuts are formalized. The four outputs are `stopAcc0`, `stopRej0` (honest $P_0$) and `stopAcc1`, `stopRej1` (honest $P_1$).
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), Definition 4.2, pp.19–20; §4.2.2, "Stopping executions", p.23

import Mathlib
import Definitions.Def_QFairEx_IsCPInstrument
import Definitions.Def_QFairEx_kronMap
import Definitions.Def_QFairEx_Protocol
import Definitions.Def_QFairEx_Protocol_honestState

namespace QFairEx

open Matrix

variable {ι0 ι1 : Type} [Fintype ι0] [Fintype ι1] [DecidableEq ι0] [DecidableEq ι1]

/-- **One round of P₀ and CTTP after P₁ has stopped**, as a branch map from (P₀'s memory, CTTP's
state) `x` to `y` acting on P₀'s register.
* Odd `r` (P₀ is the sender): P₀ generates with `gen0 r`; its message `(d0, Q0)` to the absent
  P₁ is discarded (`d0` summed, `Q0` traced out); CTTP generates with `ttpGen r`, its message to
  P₁ is discarded; P₀ processes with `send0 r`; CTTP receives `some b0`.
* Even `r` (the stopped P₁ is the scheduled sender): CTTP generates; P₀ records `abort` for the
  omitted quantum slot and processes with `abort0 r`; CTTP records `abort` (`none`). -/
noncomputable def Protocol.stopStep0 (P : Protocol ι0 ι1) (r : ℕ) (x y : P.K0 × P.C)
    (Z : Matrix (ι0 × P.W0) (ι0 × P.W0) ℂ) : Matrix (ι0 × P.W0) (ι0 × P.W0) ℂ :=
  if r % 2 = 1 then
    ∑' z : (P.K0 × P.B0 × P.D0) × (P.C × P.A0 × P.A1),
      ((P.ttpGen r x.2 z.2 * P.ttpRecv0 r (z.2.1, some z.1.2.1) y.2 : ℝ) : ℂ) •
        P.send0 r (z.1.1, z.2.2.1) y.1 (ptraceRight (P.gen0 r x.1 z.1 Z))
  else
    ∑' z : P.C × P.A0 × P.A1,
      ((P.ttpGen r x.2 z * P.ttpRecv1 r (z.1, none) y.2 : ℝ) : ℂ) • P.abort0 r (x.1, z.2.1) y.1 Z

/-- **One round of P₁ and CTTP after P₀ has stopped**: the mirror image of `stopStep0`.
* Odd `r` (the stopped P₀ is the scheduled sender): CTTP generates; P₁ processes with
  `abort1 r`; CTTP receives `none`.
* Even `r` (P₁ is the sender): P₁ generates with `gen1 r`, its message to P₀ is discarded; CTTP
  generates, its message to P₀ is discarded; P₁ processes with `send1 r`; CTTP receives
  `some b1`. -/
noncomputable def Protocol.stopStep1 (P : Protocol ι0 ι1) (r : ℕ) (x y : P.K1 × P.C)
    (Z : Matrix (ι1 × P.W1) (ι1 × P.W1) ℂ) : Matrix (ι1 × P.W1) (ι1 × P.W1) ℂ :=
  if r % 2 = 1 then
    ∑' z : P.C × P.A0 × P.A1,
      ((P.ttpGen r x.2 z * P.ttpRecv0 r (z.1, none) y.2 : ℝ) : ℂ) • P.abort1 r (x.1, z.2.2) y.1 Z
  else
    ∑' z : (P.K1 × P.B1 × P.D1) × (P.C × P.A0 × P.A1),
      ((P.ttpGen r x.2 z.2 * P.ttpRecv1 r (z.2.1, some z.1.2.1) y.2 : ℝ) : ℂ) •
        P.send1 r (z.1.1, z.2.2.2) y.1 (ptraceRight (P.gen1 r x.1 z.1 Z))

/-- **Stop(0, t) at the cut**: the joint honest state at cut `t` with the stopped P₁ discarded
(its memory summed, its register traced out); a cq-state of P₀ and CTTP. -/
noncomputable def Protocol.stopInit0 (P : Protocol ι0 ι1) (X : Matrix (ι0 × ι1) (ι0 × ι1) ℂ)
    (t : ℕ) : P.K0 × P.C → Matrix (ι0 × P.W0) (ι0 × P.W0) ℂ :=
  fun x => ∑' k1 : P.K1, ptraceRight (P.honestState X t (x.1, k1, x.2))

/-- **Stop(1, t) at the cut**: the joint honest state at cut `t` with the stopped P₀ discarded. -/
noncomputable def Protocol.stopInit1 (P : Protocol ι0 ι1) (X : Matrix (ι0 × ι1) (ι0 × ι1) ℂ)
    (t : ℕ) : P.K1 × P.C → Matrix (ι1 × P.W1) (ι1 × P.W1) ℂ :=
  fun x => ∑' k0 : P.K0, ptraceLeft (P.honestState X t (k0, x.1, x.2))

/-- State of P₀ and CTTP in Stop(0, t) at cut `t + n`. -/
noncomputable def Protocol.stopLocal0 (P : Protocol ι0 ι1) (X : Matrix (ι0 × ι1) (ι0 × ι1) ℂ)
    (t : ℕ) : ℕ → P.K0 × P.C → Matrix (ι0 × P.W0) (ι0 × P.W0) ℂ
  | 0 => P.stopInit0 X t
  | n + 1 => applyCQ (P.stopStep0 (t + n + 1)) (P.stopLocal0 X t n)

/-- State of P₁ and CTTP in Stop(1, t) at cut `t + n`. -/
noncomputable def Protocol.stopLocal1 (P : Protocol ι0 ι1) (X : Matrix (ι0 × ι1) (ι0 × ι1) ℂ)
    (t : ℕ) : ℕ → P.K1 × P.C → Matrix (ι1 × P.W1) (ι1 × P.W1) ℂ
  | 0 => P.stopInit1 X t
  | n + 1 => applyCQ (P.stopStep1 (t + n + 1)) (P.stopLocal1 X t n)

/-- **The stopping executions Stop(p, t) and the honest party's conditional outputs.**
Chung, Lee, Raizes, Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of
2026-11-02, sha256 0099b883…), Definition 4.2 (pp.19–20) and §4.2.2, "Stopping executions",
p.23: "define Stop(p, t) as the execution … in which P_p̄ is controlled by the pre-determined
fail-stop adversary of Definition 4.2 with cut t, while P_p and the trusted party follow the
protocol until termination."

For the honest party `P₀` (adversary controlling P₁ with cut `t`), on input operator `X`:
`stopAcc0 X t` is P₀'s subnormalized output conditioned on `acc` (a matrix on Ver₁'s register
`ι1`, trace `= Pr[f₀ = acc]`); `stopRej0 X t` the one on `rej` (on `ι0`). Likewise `stopAcc1`
(on `ι0`), `stopRej1` (on `ι1`) for the honest P₁ against an adversary controlling P₀. The
execution runs honestly through cut `t`, then P₀ and CTTP continue alone through rounds
`t+1, …, T` (`stopStep0`), then P₀ applies its decision instrument; the classical memories are
summed.

**Formalization Note.**
1. *The stopped party is discarded at its cut.* After cut `t` the stopped party sends nothing;
   its remaining processing acts only on its own registers and cannot change the joint state of
   the honest party and CTTP (the paper's own argument, proofs of Lemmas 4.10 and 4.12,
   pp.23–25). So its registers are traced out at cut `t`, `abort` is supplied in each of its
   scheduled slots, and messages addressed to it are discarded.
2. *Fixed cuts.* Definition 4.2 also allows a randomly sampled cut, i.e. a mixture of fixed
   cuts; the security notion quantifies over fixed cuts `t ∈ {0, …, T}`.
3. For `t = T` no round is continued: this is the completed honest execution with P₀'s outputs
   retained. -/
noncomputable def Protocol.stopAcc0 (P : Protocol ι0 ι1) (X : Matrix (ι0 × ι1) (ι0 × ι1) ℂ)
    (t : ℕ) : Matrix ι1 ι1 ℂ :=
  ∑' x : P.K0 × P.C, P.outAcc0 x.1 (P.stopLocal0 X t (P.T - t) x)

/-- P₀'s rejecting conditional output in Stop(0, t) (on Ver₀'s register `ι0`). -/
noncomputable def Protocol.stopRej0 (P : Protocol ι0 ι1) (X : Matrix (ι0 × ι1) (ι0 × ι1) ℂ)
    (t : ℕ) : Matrix ι0 ι0 ℂ :=
  ∑' x : P.K0 × P.C, P.outRej0 x.1 (P.stopLocal0 X t (P.T - t) x)

/-- P₁'s accepting conditional output in Stop(1, t) (on Ver₀'s register `ι0`). -/
noncomputable def Protocol.stopAcc1 (P : Protocol ι0 ι1) (X : Matrix (ι0 × ι1) (ι0 × ι1) ℂ)
    (t : ℕ) : Matrix ι0 ι0 ℂ :=
  ∑' x : P.K1 × P.C, P.outAcc1 x.1 (P.stopLocal1 X t (P.T - t) x)

/-- P₁'s rejecting conditional output in Stop(1, t) (on Ver₁'s register `ι1`). -/
noncomputable def Protocol.stopRej1 (P : Protocol ι0 ι1) (X : Matrix (ι0 × ι1) (ι0 × ι1) ℂ)
    (t : ℕ) : Matrix ι1 ι1 ℂ :=
  ∑' x : P.K1 × P.C, P.outRej1 x.1 (P.stopLocal1 X t (P.T - t) x)

end QFairEx


