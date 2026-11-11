-- Prove2me | Definitions.Def_QFairEx_Protocol_honestState
-- name    : QFairEx_Protocol_honestState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:16.63754+00:00
-- url     : https://prove2.me/theorems/8f59630a-9a8a-460d-a157-e667760aee47
-- title:
--   Honest execution through a cut and the honest acceptance probability
-- statement:
--   Fix a protocol and an input operator $X$ on $\iota_0\times\iota_1$ (for pure inputs, $X=|\psi_0\rangle\langle\psi_0|\otimes|\psi_1\rangle\langle\psi_1|$). The joint state at a cut is a cq-state: for each value $(k_0,k_1,c)$ of the three classical memories, a block on the registers of $P_0$ and $P_1$ — the state $\sum_c q_c\,\rho^c_{M_0M_1}\otimes|c\rangle\langle c|_C$ of the paper, with the parties' classical memories also written as labels.
--
--   1. At cut $0$ the input registers carry $X$ and the rest carries the auxiliary initialization.
--   2. Round $r$ (odd; even rounds are symmetric): $P_0$ generates its message to $P_1$ and to CTTP and its retained state; CTTP samples its messages to $P_0$ and $P_1$; then $P_0$ processes its retained state with CTTP's message, $P_1$ processes its register together with the delivered quantum message, and CTTP processes the delivered classical message. All intermediate classical values are summed.
--   3. The honest execution through cut $t$ applies rounds $1,\dots,t$.
--
--   The probability that both parties accept, $\Pr[d_0=d_1=\mathrm{acc}]$, applies both accepting branches to the state at cut $T$ and takes the total trace.
--
--   **Formalization Note** A cut $t$ is the end of $t$ completed rounds (Definition 4.2). Sums over classical values are `tsum`s, which converge for a valid protocol.
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), Definition 4.1, p.19; Definition 4.2, p.19; Definition 4.3 (completeness), p.20

import Mathlib
import Definitions.Def_QFairEx_kronMap
import Definitions.Def_QFairEx_Protocol

namespace QFairEx

open Matrix

variable {ι0 ι1 : Type} [Fintype ι0] [Fintype ι1] [DecidableEq ι0] [DecidableEq ι1]

/-- **Joint cq-state of P₀, P₁ and CTTP at a cut**: for each value `(k0, k1, c)` of the three
classical memories, a (subnormalized) block on the registers `(ι0 × W0) × (ι1 × W1)` of P₀ and
P₁. This is the state `∑_c q_c ρ^c_{M0M1} ⊗ |c⟩⟨c|_C` of the proof of Lemma 4.12 (p.24), with
the parties' classical memories also written as classical labels. -/
abbrev Protocol.JState (P : Protocol ι0 ι1) : Type :=
  P.K0 × P.K1 × P.C → Matrix ((ι0 × P.W0) × (ι1 × P.W1)) ((ι0 × P.W0) × (ι1 × P.W1)) ℂ

/-- **Initial joint state** on input operator `X` on `ι0 × ι1` (for pure inputs
`X = |ψ₀⟩⟨ψ₀| ⊗ |ψ₁⟩⟨ψ₁|`): the input registers carry `X`, the work registers and classical
memories carry the auxiliary initialization, `X ⊗ aux`. -/
def Protocol.init (P : Protocol ι0 ι1) (X : Matrix (ι0 × ι1) (ι0 × ι1) ℂ) : P.JState :=
  fun k a b => X (a.1.1, a.2.1) (b.1.1, b.2.1) * P.aux k (a.1.2, a.2.2) (b.1.2, b.2.2)

/-- **Honest odd round `r`** (sender P₀), Definition 4.1, p.19. Generation: P₀ applies
`gen0 r` (producing its retained state, the message `b0` to CTTP and the message `(d0, Q0)` to
P₁) and CTTP samples `(c_g, a0, a1)` from `ttpGen r`. Delivery and processing: P₀ applies
`send0 r` to its retained state with `a0`; P₁ applies `recv1 r` to its register and the
delivered `Q0`, with classical input `(k1, a1, d0)`; CTTP applies `ttpRecv0 r` to
`(c_g, some b0)`. All intermediate classical values are summed over. -/
noncomputable def Protocol.oddRound (P : Protocol ι0 ι1) (r : ℕ) (ρ : P.JState) : P.JState :=
  fun y => ∑' x : (P.K0 × P.K1 × P.C) × (P.K0 × P.B0 × P.D0) × (P.C × P.A0 × P.A1),
    ((P.ttpGen r x.1.2.2 x.2.2 * P.ttpRecv0 r (x.2.2.1, some x.2.1.2.1) y.2.2 : ℝ) : ℂ) •
      kronMap (P.send0 r (x.2.1.1, x.2.2.2.1) y.1) (P.recv1 r (x.1.2.1, x.2.2.2.2, x.2.1.2.2) y.2.1)
        ((kronMap (P.gen0 r x.1.1 x.2.1) id (ρ x.1)).submatrix
          (fun m : (ι0 × P.W0) × ((ι1 × P.W1) × P.Q0) => ((m.1, m.2.2), m.2.1))
          (fun m : (ι0 × P.W0) × ((ι1 × P.W1) × P.Q0) => ((m.1, m.2.2), m.2.1)))

/-- **Honest even round `r`** (sender P₁), Definition 4.1, p.19: the mirror image of
`oddRound`. P₁ applies `gen1 r`, CTTP samples from `ttpGen r`; P₀ applies `recv0 r` to its
register and the delivered `Q1` with classical input `(k0, a0, d1)`, P₁ applies `send1 r`,
CTTP applies `ttpRecv1 r` to `(c_g, some b1)`. -/
noncomputable def Protocol.evenRound (P : Protocol ι0 ι1) (r : ℕ) (ρ : P.JState) : P.JState :=
  fun y => ∑' x : (P.K0 × P.K1 × P.C) × (P.K1 × P.B1 × P.D1) × (P.C × P.A0 × P.A1),
    ((P.ttpGen r x.1.2.2 x.2.2 * P.ttpRecv1 r (x.2.2.1, some x.2.1.2.1) y.2.2 : ℝ) : ℂ) •
      kronMap (P.recv0 r (x.1.1, x.2.2.2.1, x.2.1.2.2) y.1) (P.send1 r (x.2.1.1, x.2.2.2.2) y.2.1)
        ((kronMap id (P.gen1 r x.1.2.1 x.2.1) (ρ x.1)).submatrix
          (fun m : ((ι0 × P.W0) × P.Q1) × (ι1 × P.W1) => (m.1.1, (m.2, m.1.2)))
          (fun m : ((ι0 × P.W0) × P.Q1) × (ι1 × P.W1) => (m.1.1, (m.2, m.1.2))))

/-- **Honest round `r`**: `oddRound r` if `r` is odd, `evenRound r` if `r` is even. -/
noncomputable def Protocol.round (P : Protocol ι0 ι1) (r : ℕ) (ρ : P.JState) : P.JState :=
  if r % 2 = 1 then P.oddRound r ρ else P.evenRound r ρ

/-- **Honest execution through cut `t`.**
Chung, Lee, Raizes, Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of
2026-11-02, sha256 0099b883…), Definition 4.1 (p.19) and Definition 4.2 (p.19: "A cut t is the
end of t completed rounds of Definition 4.1, after all their messages have been delivered and
processed").

`honestState X t` is the joint cq-state of P₀, P₁ and CTTP at cut `t` when every process follows
the protocol on input operator `X`: `honestState X 0 = init X` and
`honestState X (t+1) = round (t+1) (honestState X t)`.

**Formalization Note.** Inputs are an operator `X` on `ι0 × ι1`; the security notion uses
`X = |ψ₀⟩⟨ψ₀| ⊗ |ψ₁⟩⟨ψ₁|`, and the reduction R_alt(t) feeds an encoded two-qubit operator. All
classical sums are `tsum`s; for a valid protocol they converge. -/
noncomputable def Protocol.honestState (P : Protocol ι0 ι1) (X : Matrix (ι0 × ι1) (ι0 × ι1) ℂ) :
    ℕ → P.JState
  | 0 => P.init X
  | t + 1 => P.round (t + 1) (P.honestState X t)

/-- **Probability that both parties accept in the honest execution**, `Pr[d₀ = d₁ = acc]`
(Definition 4.3, completeness, p.20): after round `T`, P₀ applies its accepting branch and P₁
its accepting branch; the trace of the result, summed over the classical memories. -/
noncomputable def Protocol.honestAccAcc (P : Protocol ι0 ι1) (X : Matrix (ι0 × ι1) (ι0 × ι1) ℂ) :
    ℝ :=
  (∑' k : P.K0 × P.K1 × P.C,
    (kronMap (P.outAcc0 k.1) (P.outAcc1 k.2.1) (P.honestState X P.T k)).trace).re

end QFairEx


