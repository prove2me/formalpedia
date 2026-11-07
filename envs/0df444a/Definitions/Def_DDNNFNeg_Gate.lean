-- Prove2me | Definitions.Def_DDNNFNeg_Gate
-- name    : DDNNFNeg_Gate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:00.59826+00:00
-- url     : https://prove2.me/theorems/1cdbf705-1abb-433a-bf4f-f1792909cc51
-- title:
--   Gate of a negation normal form circuit
-- statement:
--   A **gate** of a negation normal form (NNF) circuit whose gates are numbered $0,\dots,s-1$ is one of:
--
--   1. an input gate labelled by a **literal**: a variable $v \in X$ or its negation $\neg v$;
--   2. a **constant** leaf $0$ or $1$;
--   3. a fan-in-two **$\wedge$-gate** with children $i, j$;
--   4. a fan-in-two **$\vee$-gate** with children $i, j$ (possibly $i = j$).
--
--   This is the vocabulary of the NNF circuits of §3.1.
--
--   **Formalization Note** The paper's NNFs have literal input gates only. Constant leaves are part of this type so that classes "with constants" can be stated; the paper's class is cut out by `NNF.IsConstFree`.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §3.1, p.8

import Mathlib

namespace DDNNFNeg

/-- A gate of a negation normal form circuit whose gates are indexed by `Fin s`
(Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §3.1, p.8): an input gate labelled by a literal (the variable `v` if `pos = true`,
its negation `¬v` if `pos = false`), a constant leaf, or a fan-in-two `∧`/`∨` gate whose
two children are the gates `i` and `j` (possibly `i = j`).

**Formalization Note** The paper's NNFs have literal input gates only; constant leaves exist
in this type so that classes "with constants" can be stated, and the paper's class is cut out
by `NNF.IsConstFree`. -/
inductive Gate (s : ℕ) (X : Type*) where
  /-- the literal `v` (if `pos`) or `¬v` (if `!pos`) -/
  | lit (v : X) (pos : Bool)
  /-- a constant leaf -/
  | const (b : Bool)
  /-- a fan-in-two AND gate with children `i`, `j` -/
  | and (i j : Fin s)
  /-- a fan-in-two OR gate with children `i`, `j` -/
  | or (i j : Fin s)
  deriving DecidableEq

end DDNNFNeg


