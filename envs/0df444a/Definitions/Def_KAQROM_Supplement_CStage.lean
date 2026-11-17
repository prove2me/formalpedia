-- Prove2me | Definitions.Def_KAQROM_Supplement_CStage
-- name    : KAQROM_Supplement_CStage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:47:07.749177+00:00
-- url     : https://prove2.me/theorems/7a84e6a4-d086-43dd-84f8-ba80acf7fa53
-- title:
--   Stages with classical oracle access and quantum residual state
-- statement:
--   A **stage with classical oracle access** on a quantum register $R$, with classical input $i\in I$ and classical output $o\in O$, consists of $D$ query steps followed by an output step. Each query step is a quantum instrument with outcome in $X\cup\{\text{none}\}$, chosen by the input, the stage's ordered query–answer transcript so far and the step index; outcome $x$ is a classical query, answered classically by $H(x)$ and appended to the transcript, and outcome none makes no query. The output step is an instrument with outcome in $O$ chosen by the input and the complete transcript.
--
--   Running the stage along a branch gives the unnormalized residual state (its trace is the probability of the branch) and the transcript $T$, whose length is the number of queries made. A worst-case query bound $q$ means $|T|\le q$ on every oracle, every input and every branch of positive probability.
--
--   This is the paper's notion of classical oracle access (Definition 3.1): queries and answers are classical while the residual state may be quantum. It models Alice's stage in Definition 6.1, key generation in Definition 3.12, encryption in Definition 3.13 and the samplers of Theorem 7.3. On a one-dimensional register it is a classical randomized algorithm with classical queries.
--
--   **Formalization Note** It is the one-stage form of the published `KAQROM.PrefixParty` with an arbitrary output type, and reuses its `queryStep`.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 3.1, p.16; Definition 6.1, p.45; Definitions 3.12–3.13, p.23; Theorem 7.3, p.74

import Mathlib
import Definitions.Def_KAQROM_Instrument
import Definitions.Def_KAQROM_Oracle
import Definitions.Def_KAQROM_PrefixParty

namespace KAQROM.Supplement

open Matrix
open KAQROM

/-- A **stage with classical oracle access** (Definition 3.1, p.16, "classical oracle access") on a
quantum register `R`, with classical input `I` and classical output `O`: `D` classical query steps,
each a quantum instrument chosen by the input, the stage's ordered query–answer transcript so far
and the step index (outcome `some x` is a query at `x`, answered classically by `H x`; outcome
`none` makes no query), followed by an output instrument with outcome in `O`, chosen by the input
and the complete transcript of the stage.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 3.1,
p.16; used for Alice in Definition 6.1 (p.45), key generation in Definition 3.12 and encryption in
Definition 3.13 (p.23), and the samplers of Theorem 7.3 (p.74).

**Formalization Note.** This is the one-stage form of the published `KAQROM.PrefixParty` with an
arbitrary output type: the state depends on `H` only through the recorded answers, and the residual
state stays quantum. A stage whose register is one-dimensional is a classical randomized algorithm
with classical queries (each step is then a probability distribution over the next query, given
the input and the answers so far). -/
structure CStage (X : Type) [Fintype X] (ℓ : ℕ) (I O R ι : Type) [Fintype O] [Fintype R]
    [Fintype ι] [DecidableEq R] (D : ℕ) where
  /-- The instrument of query step `k`, given the input and the transcript so far. -/
  query : I → Transcript X ℓ → Fin D → Instrument (Option X) R R ι
  /-- The output instrument, given the input and the complete transcript of the stage. -/
  out : I → Transcript X ℓ → Instrument O R R ι

/-- The run of a classical-query stage with oracle `H` on input `i` and initial (unnormalized)
state `ρ`, along the branch with query outcomes `oq` and output `o`: the unnormalized residual
state (its trace is the probability of the branch, times `Tr ρ`) and the ordered query–answer
transcript (its length is the number of queries made on the branch). -/
noncomputable def CStage.run {X : Type} [Fintype X] {ℓ : ℕ} {I O R ι : Type} [Fintype O]
    [Fintype R] [Fintype ι] [DecidableEq R] {D : ℕ} (S : CStage X ℓ I O R ι D) (H : Oracle X ℓ)
    (i : I) (oq : Fin D → Option X) (o : O) (ρ : Matrix R R ℂ) :
    Matrix R R ℂ × Transcript X ℓ :=
  let s := (List.finRange D).foldl (fun t k => queryStep (S.query i t.2 k) H (oq k) t) (ρ, [])
  ((S.out i s.2).apply o s.1, s.2)

/-- The worst-case query bound of a classical-query stage started in `ρ`: on every oracle, every
input and every branch of positive probability, the stage makes at most `q` queries. -/
def CStage.QueriesLe {X : Type} [Fintype X] {ℓ : ℕ} {I O R ι : Type} [Fintype O] [Fintype R]
    [Fintype ι] [DecidableEq R] {D : ℕ} (S : CStage X ℓ I O R ι D) (ρ : Matrix R R ℂ) (q : ℕ) :
    Prop :=
  ∀ (H : Oracle X ℓ) (i : I) (oq : Fin D → Option X) (o : O),
    0 < (S.run H i oq o ρ).1.trace.re → (S.run H i oq o ρ).2.length ≤ q

end KAQROM.Supplement


