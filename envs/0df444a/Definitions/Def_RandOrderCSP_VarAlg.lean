-- Prove2me | Definitions.Def_RandOrderCSP_VarAlg
-- name    : RandOrderCSP_VarAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:23.489538+00:00
-- url     : https://prove2.me/theorems/4c8c2669-c0f3-4639-9223-197bf95e7f28
-- title:
--   Streaming algorithms with variable-length states
-- statement:
--   This is the model behind the space bound of Lemma 10.15, whose algorithm does not know the stream length. A deterministic algorithm has states that are bit strings, starts at the empty string, and has an update and an output function. The module also defines a stream update of a colored hypergraph on $[n]$, namely $k$ distinct vertices with a color, and the hypergraph of a list of such updates.
--
--   **Formalization Note** The model of §3.5 fixes the state length, so it cannot express a bound growing with the stream. The theorem bounds the length of every reached state.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), §3.5, p.15; Lemma 10.15, p.55

import Mathlib
import Definitions.Def_RandOrderCSP_Hypergraph

namespace RandOrderCSP

universe u

/-- **A deterministic streaming algorithm with variable-length states**, used for Lemma 10.15 (p.55).

Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating CSPs in random-order streams*,
STOC 2027 submission (manuscript sha256 3aca9d2f…), p.55: the algorithm of Lemma 10.15 "uses
O_{k,R,|Γ|,ε}(log³(n + m + 2)) bits of space", where it does not know `m`.

**Formalization Note.** The fixed-`s` model of §3.5 cannot express a space bound that grows with the
stream, so the state is a bit string, the start state is empty, and the theorem bounds the length of
every reached state. There is no position counter: the update sees only the state and the update. -/
structure VarAlg (U : Type) (Out : Type u) where
  /-- The update function. -/
  update : List Bool → U → List Bool
  /-- The output function. -/
  output : List Bool → Out

/-- The state after the stream `l`, starting from the empty state. -/
def VarAlg.run {U : Type} {Out : Type u} (A : VarAlg U Out) (l : List U) : List Bool :=
  l.foldl A.update []

/-- The output on the stream `l`. -/
def VarAlg.answer {U : Type} {Out : Type u} (A : VarAlg U Out) (l : List U) : Out :=
  A.output (A.run l)

/-- A stream update of a `Col`-colored hypergraph on `[n]` (§3.5, p.15):
`(M_H(j,1), …, M_H(j,k), f(j))`, with `k` distinct vertices. -/
abbrev ColoredEdge (k : ℕ) (Col : Type) (n : ℕ) : Type := (Fin k ↪ Fin n) × Col

/-- The hypergraph on `[n]` with edge set `Fin m` given by a list of colored edges. -/
def edgesHG {k n m : ℕ} {Col : Type} (Φ : Fin m → ColoredEdge k Col n) :
    Hypergraph k (Fin n) (Fin m) where
  M := fun j => (Φ j).1
  row_inj := fun j => (Φ j).1.injective

end RandOrderCSP


