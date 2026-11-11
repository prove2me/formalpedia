-- Prove2me | Definitions.Def_QFairEx_Protocol_ralt
-- name    : QFairEx_Protocol_ralt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:25:53.436569+00:00
-- url     : https://prove2.me/theorems/5dcdfe9b-23bf-4ff5-bb37-779f82cfaf9b
-- title:
--   The BB84 basis-guessing reduction $R_{\mathrm{alt}}(t)$ (Algorithm 4.11) and $\delta_t$
-- statement:
--   For a cut $t$, the reduction **$R_{\mathrm{alt}}(t)$** is an adversary of the parallel BB84 game with $n=2$:
--
--   1. initialize $P_0$ with $E_0|\phi_1\rangle$ and $P_1$ with $E_1|\phi_2\rangle$ and run $P_0$, $P_1$, CTTP honestly through cut $t$;
--   2. copy the complete classical state of CTTP into two instances: the joint state $\sum_cq_c\rho^c_{M_0M_1}\otimes|c\rangle\langle c|_{C_0}\otimes|c\rangle\langle c|_{C_1}$;
--   3. for rounds $t+1,\dots,T$ run two separate continuations, $P_p$ with $\mathrm{CTTP}_p$ for $p=0,1$, each supplying `abort` in the absent party's scheduled slots and discarding messages addressed to it, with no message between the continuations; record $(f_0,\sigma_0)$, $(f_1,\sigma_1)$;
--   4. if $f_0=f_1$, output index $1$ and a fresh uniform bit; if $f_0=\mathrm{acc}$, $f_1=\mathrm{rej}$, decode both outputs with $D_1$, run Algorithm 4.6 and output index $2$ with its answer; if $f_0=\mathrm{rej}$, $f_1=\mathrm{acc}$, decode with $D_0$, run Algorithm 4.6 and output index $1$ with its answer.
--
--   The definition gives, for each answer $(j,g)$, the probability of that answer on an arbitrary two-qubit input (extended linearly), and $\delta_t=\Pr_{R_{\mathrm{alt}}(t)}[f_0\ne f_1]$ averaged over the game's challenges.
--
--   **Formalization Note** Indices are 0-based: the paper's index $1$ is `0` and $2$ is `1`. The joint outputs for the four flag pairs are `jointAccAcc`, `jointAccRej`, `jointRejAcc`, `jointRejRej`; decoded registers are ordered ($P_0$'s output, $P_1$'s output).
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), Algorithm 4.11, p.24, with §4.2.2, p.22; Lemma 4.12 (δ_t), p.24

import Mathlib
import Definitions.Def_QFairEx_IsCPInstrument
import Definitions.Def_QFairEx_kronMap
import Definitions.Def_QFairEx_SupportedOn
import Definitions.Def_QFairEx_bb84
import Definitions.Def_QFairEx_clonedPOVM
import Definitions.Def_QFairEx_encVec
import Definitions.Def_QFairEx_Protocol
import Definitions.Def_QFairEx_Protocol_honestState
import Definitions.Def_QFairEx_Protocol_stopAcc0

namespace QFairEx

open Matrix

variable {ι0 ι1 : Type} [Fintype ι0] [Fintype ι1] [DecidableEq ι0] [DecidableEq ι1]

open Classical in
/-- **Algorithm 4.11, steps 1–2: honest run through cut `t`, then the copy of CTTP's state.**
The joint state on (P₀'s memory, CTTP₀'s state) × (P₁'s memory, CTTP₁'s state) and the registers
of P₀ and P₁: `∑_c q_c ρ^c ⊗ |c⟩⟨c|_{C₀} ⊗ |c⟩⟨c|_{C₁}` (p.24), i.e. the block at
`((k0, c0), (k1, c1))` is the honest block at `(k0, k1, c0)` if `c0 = c1` and `0` otherwise. -/
noncomputable def Protocol.forkInit (P : Protocol ι0 ι1) (X : Matrix (ι0 × ι1) (ι0 × ι1) ℂ)
    (t : ℕ) : (P.K0 × P.C) × (P.K1 × P.C) →
      Matrix ((ι0 × P.W0) × (ι1 × P.W1)) ((ι0 × P.W0) × (ι1 × P.W1)) ℂ :=
  fun x => if x.1.2 = x.2.2 then P.honestState X t (x.1.1, x.2.1, x.1.2) else 0

/-- **Algorithm 4.11, step 3: one round `r` of the two separate continuations.** Continuation 0
(P₀ with CTTP₀) takes the step `stopStep0 r` and continuation 1 (P₁ with CTTP₁) the step
`stopStep1 r`, on disjoint registers (`stopStep0 r ⊗ stopStep1 r`); each continuation receives
`abort` in the absent party's scheduled slots and discards messages addressed to it; no message
passes between the continuations. -/
noncomputable def Protocol.forkStep (P : Protocol ι0 ι1) (r : ℕ)
    (F : (P.K0 × P.C) × (P.K1 × P.C) →
      Matrix ((ι0 × P.W0) × (ι1 × P.W1)) ((ι0 × P.W0) × (ι1 × P.W1)) ℂ) :
    (P.K0 × P.C) × (P.K1 × P.C) →
      Matrix ((ι0 × P.W0) × (ι1 × P.W1)) ((ι0 × P.W0) × (ι1 × P.W1)) ℂ :=
  fun y => ∑' x : (P.K0 × P.C) × (P.K1 × P.C),
    kronMap (P.stopStep0 r x.1 y.1) (P.stopStep1 r x.2 y.2) (F x)

/-- Joint state of the two continuations of R_alt(t) at cut `t + n`. -/
noncomputable def Protocol.forkState (P : Protocol ι0 ι1) (X : Matrix (ι0 × ι1) (ι0 × ι1) ℂ)
    (t : ℕ) : ℕ → (P.K0 × P.C) × (P.K1 × P.C) →
      Matrix ((ι0 × P.W0) × (ι1 × P.W1)) ((ι0 × P.W0) × (ι1 × P.W1)) ℂ
  | 0 => P.forkInit X t
  | n + 1 => P.forkStep (t + n + 1) (P.forkState X t n)

/-- Joint output of R_alt(t) before step 4 with `f₀ = acc`, `f₁ = rej`: both quantum outputs on
Ver₁'s register, `σ₀ ⊗ σ₁` on `ι1 × ι1` (subnormalized, trace `Pr[f₀ = acc, f₁ = rej]`). -/
noncomputable def Protocol.jointAccRej (P : Protocol ι0 ι1) (X : Matrix (ι0 × ι1) (ι0 × ι1) ℂ)
    (t : ℕ) : Matrix (ι1 × ι1) (ι1 × ι1) ℂ :=
  ∑' x : (P.K0 × P.C) × (P.K1 × P.C),
    kronMap (P.outAcc0 x.1.1) (P.outRej1 x.2.1) (P.forkState X t (P.T - t) x)

/-- Joint output with `f₀ = rej`, `f₁ = acc`: both outputs on Ver₀'s register (`ι0 × ι0`). -/
noncomputable def Protocol.jointRejAcc (P : Protocol ι0 ι1) (X : Matrix (ι0 × ι1) (ι0 × ι1) ℂ)
    (t : ℕ) : Matrix (ι0 × ι0) (ι0 × ι0) ℂ :=
  ∑' x : (P.K0 × P.C) × (P.K1 × P.C),
    kronMap (P.outRej0 x.1.1) (P.outAcc1 x.2.1) (P.forkState X t (P.T - t) x)

/-- Joint output with `f₀ = f₁ = acc` (on `ι1 × ι0`). -/
noncomputable def Protocol.jointAccAcc (P : Protocol ι0 ι1) (X : Matrix (ι0 × ι1) (ι0 × ι1) ℂ)
    (t : ℕ) : Matrix (ι1 × ι0) (ι1 × ι0) ℂ :=
  ∑' x : (P.K0 × P.C) × (P.K1 × P.C),
    kronMap (P.outAcc0 x.1.1) (P.outAcc1 x.2.1) (P.forkState X t (P.T - t) x)

/-- Joint output with `f₀ = f₁ = rej` (on `ι0 × ι1`). -/
noncomputable def Protocol.jointRejRej (P : Protocol ι0 ι1) (X : Matrix (ι0 × ι1) (ι0 × ι1) ℂ)
    (t : ℕ) : Matrix (ι0 × ι1) (ι0 × ι1) ℂ :=
  ∑' x : (P.K0 × P.C) × (P.K1 × P.C),
    kronMap (P.outRej0 x.1.1) (P.outRej1 x.2.1) (P.forkState X t (P.T - t) x)

/-- **The BB84 basis-guessing reduction `R_alt(t)`** (Algorithm 4.11), as an adversary of the
parallel game with `n = 2`.
Chung, Lee, Raizes, Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of
2026-11-02, sha256 0099b883…), Algorithm 4.11, p.24, with §4.2.2, p.22.

On the game's two-qubit input `Y` (qubit `0` = `|ϕ₁⟩`, qubit `1` = `|ϕ₂⟩`):
1. initialize P₀ with `E₀|ϕ₁⟩`, P₁ with `E₁|ϕ₂⟩` (input `encodeInput e0 e1 Y`) and run everyone
   honestly through cut `t`;
2. copy CTTP's classical state into CTTP₀, CTTP₁ (`forkInit`);
3. run the two continuations through round `T` and record `(f₀, σ₀)`, `(f₁, σ₁)`;
4. if `f₀ = f₁`, output index `0` (the paper's `1`) with a fresh uniform bit; if `f₀ = acc`,
   `f₁ = rej`, decode both outputs with `D₁`, run Algorithm 4.6 and output index `1` (the paper's
   `2`) with its answer; if `f₀ = rej`, `f₁ = acc`, decode with `D₀`, run Algorithm 4.6 and
   output index `0` with its answer.

`ralt P e0 e1 t () (j, g) Y` is the `1 × 1` matrix holding the (complex-linear extension of the)
probability of answering `(j, g)`.

**Formalization Note.** Game indices are `Fin 2` (0-based): the paper's `j = 1` is `0`, `j = 2`
is `1`. Decoded registers are ordered (P₀'s output, P₁'s output). -/
noncomputable def Protocol.ralt (P : Protocol ι0 ι1) (e0 : Fin 2 → ι0 → ℂ) (e1 : Fin 2 → ι1 → ℂ)
    (t : ℕ) : Unit → Fin 2 × Bool → Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ → Matrix Unit Unit ℂ :=
  fun _ o Y _ _ =>
    if o.1 = 0 then
      (1 / 2 : ℂ) * ((P.jointAccAcc (encodeInput e0 e1 Y) t).trace +
          (P.jointRejRej (encodeInput e0 e1 Y) t).trace) +
        (clonedPOVM o.2 * kronMap (decode e0) (decode e0) (P.jointRejAcc (encodeInput e0 e1 Y) t)).trace
    else
      (clonedPOVM o.2 * kronMap (decode e1) (decode e1) (P.jointAccRej (encodeInput e0 e1 Y) t)).trace

/-- **`δ_t := Pr_{R_alt(t)}[f₀ ≠ f₁]`** (Lemma 4.12, p.24), averaged over the challenges of the
game with `n = 2` (`x, θ ∈ {0,1}²` uniform): the mass of the two mismatched flag pairs before
step 4. -/
noncomputable def Protocol.deltaFlags (P : Protocol ι0 ι1) (e0 : Fin 2 → ι0 → ℂ)
    (e1 : Fin 2 → ι1 → ℂ) (t : ℕ) : ℝ :=
  (1 / 16 : ℝ) * ∑ x : Fin 2 → Bool, ∑ θ : Fin 2 → Bool,
    ((P.jointAccRej (encodeInput e0 e1 (pureDensity (bb84Vec θ x))) t).trace +
      (P.jointRejAcc (encodeInput e0 e1 (pureDensity (bb84Vec θ x))) t).trace).re

end QFairEx


