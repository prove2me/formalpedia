-- Prove2me | Definitions.Def_KAQROM_PrefixParty
-- name    : KAQROM_PrefixParty
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:30:42.993198+00:00
-- url     : https://prove2.me/theorems/bc6200e5-69bd-4645-a56b-2607ef203f91
-- title:
--   A party with classical oracle access in a classical-communication prefix
-- statement:
--   A **prefix party** has a quantum register $R$. In each of its stages it performs $D$ query steps and then sends one classical message. Each step is a quantum instrument chosen by the party's classical record: the public transcript so far, its own ordered query–answer transcript so far, and the step index. A query step has outcomes "query $x$" for $x\in X$ or "no query"; after "query $x$" the answer $H(x)$ is appended to the party's transcript. The message step has outcomes in the message set.
--
--   Given the oracle, the outcomes of every stage and an initial state, the run returns the party's unnormalized residual state and its complete ordered query–answer transcript $T$.
--
--   This is the paper's **classical oracle access** (Definition 3.1): each query is made on a classical input, the answer is returned classically, the query–answer list is recorded, and the residual state may be quantum. In particular the state depends on the oracle only through the recorded answers.
--
--   **Formalization Note** All stages of a party use the same number $D$ of query steps and the same register; a step without a query, and a register large enough for every stage, pad any finite adaptive stage to this form.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 3.1, p.16; Definition 3.10, pp.21–22

import Mathlib
import Definitions.Def_KAQROM_Instrument
import Definitions.Def_KAQROM_Oracle

namespace KAQROM

open Matrix

/-- One **classical query step**: apply the instrument `I` with outcome `o : Option X` to the
unnormalized state; outcome `some x` is a classical query at `x`, whose answer `H x` is appended
to the party's ordered query–answer transcript; `none` is a step without a query. -/
noncomputable def queryStep {X : Type} [Fintype X] {ℓ : ℕ} {R ι : Type} [Fintype R] [Fintype ι]
    [DecidableEq R] (I : Instrument (Option X) R R ι) (H : Oracle X ℓ) (o : Option X)
    (s : Matrix R R ℂ × Transcript X ℓ) : Matrix R R ℂ × Transcript X ℓ :=
  (I.apply o s.1, s.2 ++ (o.map (fun x => (x, H x))).toList)

/-- A **party with classical oracle access** in a classical-communication prefix (Definitions 3.1
and 3.10, pp.16 and 21): a party with a quantum register `R` that, in each of its stages, makes
`D` classical query steps and then sends a classical message in `Msg`. Each step is a quantum
instrument chosen by the party's classical record: the public transcript so far, its own ordered
query–answer transcript so far, and (for query steps) the step index.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 3.1
("classical oracle access"), p.16; Definition 3.10, pp.21–22.

**Formalization Note.** Classical oracle access is modelled literally: each query is a classical
outcome `x` of an instrument and the answer `H(x)` is returned classically, by selecting the next
instrument from the record that contains it; the residual state stays quantum. The state therefore
depends on `H` only through the recorded answers. Every stage has the same number `D` of query
steps; a step with outcome `none` makes no query, so any finite adaptive classical-query stage is
of this form. The party's register is one fixed finite type for the whole prefix (a larger
register can hold every residual register). -/
structure PrefixParty (X : Type) [Fintype X] (ℓ : ℕ) (Msg R ι : Type) [Fintype Msg] [Fintype R]
    [Fintype ι] [DecidableEq R] (D : ℕ) where
  /-- The instrument of query step `k` given the public transcript and own transcript so far. -/
  query : List Msg → Transcript X ℓ → Fin D → Instrument (Option X) R R ι
  /-- The instrument producing the message, given the public transcript and own transcript. -/
  send : List Msg → Transcript X ℓ → Instrument Msg R R ι

/-- One stage of a prefix party with oracle `H`, public transcript `pub` so far, and classical
outcomes `o = (query outcomes of the D steps, message sent)`: the unnormalized state and the
transcript after the stage. -/
noncomputable def PrefixParty.stage {X : Type} [Fintype X] {ℓ : ℕ} {Msg R ι : Type} [Fintype Msg]
    [Fintype R] [Fintype ι] [DecidableEq R] {D : ℕ} (P : PrefixParty X ℓ Msg R ι D)
    (H : Oracle X ℓ) (pub : List Msg) (o : (Fin D → Option X) × Msg)
    (s : Matrix R R ℂ × Transcript X ℓ) : Matrix R R ℂ × Transcript X ℓ :=
  let s' := (List.finRange D).foldl (fun t k => queryStep (P.query pub t.2 k) H (o.1 k) t) s
  ((P.send pub s'.2).apply o.2 s'.1, s'.2)

/-- The run of a prefix party over a prefix of `n` messages: the party acts in the stages `i` with
`own i`, reading the first `i` messages as the public transcript; the classical outcomes of every
stage (query outcomes and message) are given by `out`. Returns the party's unnormalized residual
state and its complete ordered query–answer transcript. -/
noncomputable def PrefixParty.run {X : Type} [Fintype X] {ℓ : ℕ} {Msg R ι : Type} [Fintype Msg]
    [Fintype R] [Fintype ι] [DecidableEq R] {D : ℕ} (P : PrefixParty X ℓ Msg R ι D)
    (H : Oracle X ℓ) (own : ℕ → Prop) [DecidablePred own] (n : ℕ)
    (out : Fin n → (Fin D → Option X) × Msg) (ρ0 : Matrix R R ℂ) :
    Matrix R R ℂ × Transcript X ℓ :=
  (List.finRange n).foldl
    (fun s i => if own i.val then
        P.stage H ((List.ofFn (fun j => (out j).2)).take i.val) (out i) s else s)
    (ρ0, [])

end KAQROM


