-- Prove2me | Definitions.Def_KAQROM_Supplement_BobFirst
-- name    : KAQROM_Supplement_BobFirst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:48:50.374909+00:00
-- url     : https://prove2.me/theorems/258338d6-dd50-4335-b85b-61cc27842ea8
-- title:
--   Bob-first two-message protocols with quantum Bob and passive key recovery (Definition 6.1)
-- statement:
--   A **Bob-first two-message protocol** $\Pi^{qb}=(B_1,A,B_2)$ runs, for $H\leftarrow\mathcal H$:
--
--   1. Bob runs $(M_1,S_B)\leftarrow B_1^H$ with at most $q_{B,1}$ quantum queries, sends the classical message $M_1$ and keeps the register $S_B$;
--   2. Alice runs $(M_2,K_A)\leftarrow A^H(M_1)$ with classical oracle access and at most $q_A$ queries, sends $M_2$ and outputs her key;
--   3. Bob runs $K_B\leftarrow B_2^H(S_B,M_2)$ with at most $q_{B,2}$ quantum queries.
--
--   Keys lie in $K\cup\{\bot\}$, and the parties share no state or correlated randomness. The valid agreement probability is $\alpha=\Pr[K_A=K_B\ne\bot]$. A **passive attacker** $E$ gets the transcript $(M_1,M_2)$ after the honest execution, has access to $H$, and outputs $K^*$. Its advantage is
--   $$
--   \mathrm{Adv}^{\mathrm{KR}}_{\Pi^{qb},E}=\Pr[K^*=K_B\ne\bot].
--   $$
--
--   This is the model of Theorem 6.2 and, through the reduction in its proof, of Theorem 7.2.
--
--   **Formalization Note** Bob's stages are the published `KAQROM.QAlg` with $q_{B,1}$, $q_{B,2}$ query rounds; Alice's stage is a `CStage`. Initial states are arbitrary oracle-independent density operators, which are exactly what all-zero registers followed by local preparation give. $B_2$ is chosen by $(M_1,M_2)$. The advantage is defined here for deterministic classical-query attackers.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 6.1, pp.45–46

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_KAQROM_Instrument
import Definitions.Def_KAQROM_Oracle
import Definitions.Def_KAQROM_QAlg
import Definitions.Def_KAQROM_Supplement_CStage
import Definitions.Def_KAQROM_Supplement_DetAttacker

namespace KAQROM.Supplement

open Matrix
open KAQROM

/-- **Definition 6.1 (Bob-first two-message protocol).** `Π^{qb} = (B₁, A, B₂)` relative to the
random oracle `H : X → {0,1}^ℓ`, with classical messages in `Msg` and non-abort keys in `K` (abort
`⊥` is `none : Option K`):

1. Bob runs `(M₁, S_B) ← B₁^H`, a `q_{B,1}`-query quantum algorithm with classical output `M₁` and
   retained register `S_B`;
2. Alice runs `(M₂, K_A) ← A^H(M₁)` with classical oracle access (at most `q_A` queries), sending
   `M₂` and outputting her key;
3. Bob runs `K_B ← B₂^H(S_B, M₂)`, a `q_{B,2}`-query quantum algorithm.

The parties start in oracle-independent states and share no state or correlated randomness.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 6.1,
pp.45–46.

**Formalization Note.** `q_{B,1}`, `q_{B,2}` are the numbers of query rounds of the published
`KAQROM.QAlg`s (worst-case bounds; idle queries pad). Alice's stage is a `CStage` with input `M₁`
and output `(M₂, K_A)`. The initial states `ρA0`, `ρB0` are arbitrary density operators: the
paper's all-zero registers followed by local state preparation give exactly these. `B₂` is chosen
by `(M₁, M₂)`: Bob knows the message he sent. -/
structure BobFirst (X : Type) [Fintype X] [DecidableEq X] (ℓ : ℕ) (Msg K : Type) [Fintype Msg]
    [DecidableEq Msg] [Fintype K] where
  /-- Alice's register. -/
  RA : Type
  /-- Bob's register. -/
  RB : Type
  /-- Work register of `B₁`. -/
  WB1 : Type
  /-- Work register of `B₂`. -/
  WB2 : Type
  /-- Kraus index type of every instrument of the protocol. -/
  ι : Type
  [fRA : Fintype RA] [dRA : DecidableEq RA]
  [fRB : Fintype RB] [dRB : DecidableEq RB]
  [fWB1 : Fintype WB1] [dWB1 : DecidableEq WB1]
  [fWB2 : Fintype WB2] [dWB2 : DecidableEq WB2]
  [fι : Fintype ι]
  /-- Alice's initial state. -/
  ρA0 : Matrix RA RA ℂ
  /-- Bob's initial state. -/
  ρB0 : Matrix RB RB ℂ
  ρA0_density : WildeQIT.IsDensityOperator ρA0
  ρB0_density : WildeQIT.IsDensityOperator ρB0
  /-- The query bound `q_{B,1}` of `B₁`. -/
  qB1 : ℕ
  /-- The query bound `q_{B,2}` of `B₂`. -/
  qB2 : ℕ
  /-- The number of classical query steps of Alice's stage. -/
  DA : ℕ
  /-- `(M₁, S_B) ← B₁^H`. -/
  B1 : QAlg X ℓ RB WB1 RB Msg ι qB1
  /-- `(M₂, K_A) ← A^H(M₁)`. -/
  A : CStage X ℓ Msg (Msg × Option K) RA ι DA
  /-- `K_B ← B₂^H(S_B, M₂)`, chosen by `(M₁, M₂)`. -/
  B2 : Msg → Msg → QAlg X ℓ RB WB2 Unit (Option K) ι qB2

attribute [instance] BobFirst.fRA BobFirst.dRA BobFirst.fRB BobFirst.dRB BobFirst.fWB1
  BobFirst.dWB1 BobFirst.fWB2 BobFirst.dWB2 BobFirst.fι

namespace BobFirst

variable {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg K : Type} [Fintype Msg]
  [DecidableEq Msg] [Fintype K]

/-- `q_A` bounds Alice's oracle queries: on every oracle, every first message and every branch of
positive probability, her stage makes at most `q` classical queries. -/
def AQueriesLe (P : BobFirst X ℓ Msg K) (q : ℕ) : Prop :=
  P.A.QueriesLe P.ρA0 q

/-- Bob's unnormalized key-`kB` output (a `1 × 1` matrix) on the branch with messages `m₁, m₂`. -/
noncomputable def bobOut (P : BobFirst X ℓ Msg K) (H : Oracle X ℓ) (m1 m2 : Msg)
    (kB : Option K) : Matrix Unit Unit ℂ :=
  (P.B2 m1 m2).run H (P.B1.run H P.ρB0 m1) kB

/-- **The valid agreement probability** `α_{Π^{qb}} = Pr_{Real}[K_A = K_B ≠ ⊥]` (Definition 6.1,
p.46): `H ← ℋ` uniform; `B₁` with outcome `M₁ = m₁`; Alice's stage on `m₁` with query outcomes
`oq` and output `(m₂, K_A)`; `B₂` with outcome `K_B`. -/
noncomputable def alpha (P : BobFirst X ℓ Msg K) : ℝ :=
  (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * ∑ H : Oracle X ℓ, ∑ m1 : Msg, ∑ oq : Fin P.DA → Option X,
    ∑ m2 : Msg, ∑ k : K,
      (P.A.run H m1 oq (m2, some k) P.ρA0).1.trace.re * (P.bobOut H m1 m2 (some k)).trace.re

/-- **`Adv^{KR}_{Π^{qb},E}`** (Definition 6.1, p.46) of a passive deterministic classical-query
attacker `E`: the honest experiment runs to completion, then `E^H(M₁, M₂)` outputs `K∗`; the
experiment outputs `1` iff `K∗ = K_B ≠ ⊥`. The attacker receives no private register or query
record. -/
noncomputable def advKR (P : BobFirst X ℓ Msg K) (E : DetAttacker (Msg × Msg) X ℓ (Option K)) :
    ℝ := by
  classical
  exact (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * ∑ H : Oracle X ℓ, ∑ m1 : Msg, ∑ oq : Fin P.DA → Option X,
    ∑ m2 : Msg, ∑ kA : Option K, ∑ k : K,
      if E.out H (m1, m2) = some k then
        (P.A.run H m1 oq (m2, kA) P.ρA0).1.trace.re * (P.bobOut H m1 m2 (some k)).trace.re
      else 0

end BobFirst

end KAQROM.Supplement


