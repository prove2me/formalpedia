-- Prove2me | Definitions.Def_KAQROM_Supplement_Alternating
-- name    : KAQROM_Supplement_Alternating
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:49:19.604224+00:00
-- url     : https://prove2.me/theorems/801da5b9-30fe-4836-b588-90b1375b678e
-- title:
--   Alternating protocols $B_1,A_1,\dots,A_r,B_{r+1}$ with quantum Bob (Definition 6.10)
-- statement:
--   An **alternating protocol** $\Pi^{qb}$ with $r\ge1$ Alice stages runs the stages $B_1,A_1,B_2,\dots,A_r,B_{r+1}$ with one uniform $H$. Each stage acts on its party's retained register and the honest messages sent so far, keeps an updated register, and sends one classical message; a fixed empty message stands for a stage that sends none. Every $A_i$ has classical oracle access with at most $a_i$ queries, and every $B_i$ is a quantum oracle algorithm with at most $b_i$ queries. After the stages the parties apply local oracle-free output maps to their registers and the transcript $M_{\mathrm{full}}$, which gives $K_A,K_B\in K\cup\{\bot\}$.
--
--   The valid agreement probability is $\alpha=\Pr[K_A=K_B\ne\bot]$. A passive attacker gets $M_{\mathrm{full}}$ after the honest run and outputs $K^*$, with $\mathrm{Adv}^{\mathrm{KR}}_{\Pi^{qb},E}=\Pr[K^*=K_B\ne\bot]$.
--
--   This is the model of Theorem 6.11.
--
--   **Formalization Note** The indexing is 0-based: Bob's stage $i$ sends message $2i$ and Alice's stage $i$ sends message $2i+1$. Alice's stages are the published `KAQROM.PrefixParty`, whose instruments are chosen by the public transcript and her query record. The bounds $a_i$ are a hypothesis (`AQueriesLe`) over every oracle and every branch on which her run has positive probability. Initial states are arbitrary oracle-independent density operators.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 6.10, pp.62–63

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_KAQROM_Instrument
import Definitions.Def_KAQROM_Oracle
import Definitions.Def_KAQROM_QAlg
import Definitions.Def_KAQROM_PrefixParty
import Definitions.Def_KAQROM_Supplement_DetAttacker

namespace KAQROM.Supplement

open Matrix
open KAQROM

/-- **Definition 6.10 (Alternating protocol with quantum Bob).** Stage order
`B₁, A₁, B₂, …, A_r, B_{r+1}` with `r ≥ 1`: each stage acts on its party's retained register and
the honest messages sent so far, retains an updated register and sends one classical message in
`Msg` (a stage that sends none sends a fixed empty message). All `A_i` have classical oracle
access (`alice`, a published `KAQROM.PrefixParty`), all `B_i` are quantum oracle algorithms with
`b_i` queries (`bob i`). After the stages, local oracle-free output maps (`outA`, `outB`) give
`K_A, K_B ∈ K ∪ {⊥}`. One uniform `H` is used throughout.

In 0-based indexing the `2r + 1` messages are `M₀, …, M_{2r}`; Bob's stage `i` (the paper's
`B_{i+1}`) sends `M_{2i}`, Alice's stage `i` (the paper's `A_{i+1}`) sends `M_{2i+1}`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 6.10,
pp.62–63.

**Formalization Note.** Initial states are arbitrary oracle-independent density operators (the
paper's all-zero registers followed by local preparation give exactly these). Alice's stages make
`D` classical query steps each (a step with outcome `none` makes no query); her instruments are
chosen by the public transcript so far and her complete query record, which is part of her
retained register (§3.5, p.18). Bob's stage `i` is chosen by the messages so far. The output maps
are measurements (instruments onto a trivial register) chosen by the full transcript (and, for
Alice, her retained query record). The parameters `a_i`, `Q` of the paper are hypotheses of the
theorem, not fields. -/
structure Alternating (X : Type) [Fintype X] [DecidableEq X] (ℓ : ℕ) (Msg K : Type) [Fintype Msg]
    [DecidableEq Msg] [Fintype K] where
  /-- Alice's register. -/
  RA : Type
  /-- Bob's register. -/
  RB : Type
  /-- Work register of Bob's stages. -/
  WB : Type
  /-- Kraus index type of every instrument of the protocol. -/
  ι : Type
  [fRA : Fintype RA] [dRA : DecidableEq RA]
  [fRB : Fintype RB] [dRB : DecidableEq RB]
  [fWB : Fintype WB] [dWB : DecidableEq WB]
  [fι : Fintype ι]
  /-- The number `r ≥ 1` of Alice stages. -/
  r : ℕ
  one_le_r : 1 ≤ r
  /-- The number of classical query steps of each Alice stage. -/
  D : ℕ
  /-- Alice's initial state. -/
  ρA0 : Matrix RA RA ℂ
  /-- Bob's initial state. -/
  ρB0 : Matrix RB RB ℂ
  ρA0_density : WildeQIT.IsDensityOperator ρA0
  ρB0_density : WildeQIT.IsDensityOperator ρB0
  /-- Alice's stages `A₁, …, A_r` (classical queries, classical messages). -/
  alice : PrefixParty X ℓ Msg RA ι D
  /-- The query bound `b_{i+1}` of Bob's stage `i`. -/
  b : Fin (r + 1) → ℕ
  /-- Bob's stage `i` (the paper's `B_{i+1}`), chosen by the messages so far. -/
  bob : (i : Fin (r + 1)) → List Msg → QAlg X ℓ RB WB RB Msg ι (b i)
  /-- Alice's oracle-free output map. -/
  outA : (Fin (2 * r + 1) → Msg) → Transcript X ℓ → Instrument (Option K) RA Unit ι
  /-- Bob's oracle-free output map. -/
  outB : (Fin (2 * r + 1) → Msg) → Instrument (Option K) RB Unit ι

attribute [instance] Alternating.fRA Alternating.dRA Alternating.fRB Alternating.dRB
  Alternating.fWB Alternating.dWB Alternating.fι

namespace Alternating

variable {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg K : Type} [Fintype Msg]
  [DecidableEq Msg] [Fintype K]

/-- The prefix-party outcome vector of a branch: messages `m`, and Alice's query outcomes `oq i`
in her stage `i` (position `2i + 1`); Bob's positions carry no Alice query outcome. -/
def outcomes (P : Alternating X ℓ Msg K) (m : Fin (2 * P.r + 1) → Msg)
    (oq : Fin P.r → Fin P.D → Option X) : Fin (2 * P.r + 1) → (Fin P.D → Option X) × Msg :=
  fun i => (if h : i.val % 2 = 1 then oq ⟨i.val / 2, by omega⟩ else fun _ => none, m i)

/-- Alice's run on the branch `(m, oq)`: her unnormalized retained state and her complete ordered
query–answer record `T_A`. -/
noncomputable def aliceRun (P : Alternating X ℓ Msg K) (H : Oracle X ℓ)
    (m : Fin (2 * P.r + 1) → Msg) (oq : Fin P.r → Fin P.D → Option X) :
    Matrix P.RA P.RA ℂ × Transcript X ℓ :=
  P.alice.run H (fun i => i % 2 = 1) (2 * P.r + 1) (P.outcomes m oq) P.ρA0

/-- Bob's run on the messages `m`: his unnormalized retained state after his `r + 1` stages,
stage `i` producing message `m (2i)`. -/
noncomputable def bobRun (P : Alternating X ℓ Msg K) (H : Oracle X ℓ)
    (m : Fin (2 * P.r + 1) → Msg) : Matrix P.RB P.RB ℂ :=
  (List.finRange (P.r + 1)).foldl
    (fun σ i => (P.bob i ((List.ofFn m).take (2 * i.val))).run H σ (m ⟨2 * i.val, by omega⟩))
    P.ρB0

/-- `a_i` bounds the queries of Alice's stage `i`: on every oracle and every branch on which her
run has positive probability, her stage `i` makes at most `a i` classical queries. -/
def AQueriesLe (P : Alternating X ℓ Msg K) (a : Fin P.r → ℕ) : Prop :=
  ∀ (H : Oracle X ℓ) (m : Fin (2 * P.r + 1) → Msg) (oq : Fin P.r → Fin P.D → Option X),
    0 < (P.aliceRun H m oq).1.trace.re →
      ∀ i : Fin P.r, (List.ofFn (oq i)).countP (fun o => o.isSome) ≤ a i

/-- **`α_{Π^{qb}} = Pr_{Real}[K_A = K_B ≠ ⊥]`** (Definition 6.10, p.62). -/
noncomputable def alpha (P : Alternating X ℓ Msg K) : ℝ :=
  (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * ∑ H : Oracle X ℓ, ∑ m : Fin (2 * P.r + 1) → Msg,
    ∑ oq : Fin P.r → Fin P.D → Option X, ∑ k : K,
      ((P.outA m (P.aliceRun H m oq).2).apply (some k) (P.aliceRun H m oq).1).trace.re *
        ((P.outB m).apply (some k) (P.bobRun H m)).trace.re

/-- **`Adv^{KR}_{Π^{qb},E}`** (Definition 6.10, pp.62–63) of a passive deterministic
classical-query attacker: after the honest run, `K∗ ← E^H(M_full)`; output `1` iff
`K∗ = K_B ≠ ⊥`. -/
noncomputable def advKR (P : Alternating X ℓ Msg K)
    (E : DetAttacker (Fin (2 * P.r + 1) → Msg) X ℓ (Option K)) : ℝ := by
  classical
  exact (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * ∑ H : Oracle X ℓ, ∑ m : Fin (2 * P.r + 1) → Msg,
    ∑ oq : Fin P.r → Fin P.D → Option X, ∑ k : K,
      if E.out H m = some k then
        (P.aliceRun H m oq).1.trace.re * ((P.outB m).apply (some k) (P.bobRun H m)).trace.re
      else 0

end Alternating

end KAQROM.Supplement


