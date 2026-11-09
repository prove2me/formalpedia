-- Prove2me | Definitions.Def_HSElemKernel_CardEncoder
-- name    : HSElemKernel_CardEncoder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:25:32.032725+00:00
-- url     : https://prove2.me/theorems/73b38e95-8a3f-4765-9a7f-33aa353c6d0e
-- title:
--   Cardinality encoder and Lemma 3.2's guarantee
-- statement:
--   A **cardinality encoder** $E$ assigns to every $N$, $b$ and $\bowtie \in \{=, \le\}$ a number of auxiliary variables and a CNF formula over the $N$ constrained and the auxiliary variables. It **meets Lemma 3.2's guarantee with constant $C$** if, at every $N$, $b$ and $\bowtie$, its formula is a linear-size encoding of $\sum_{i=1}^N x_i \bowtie b$ with constant $C$ (correct, with at most $C(N+1)$ auxiliary variables and clauses, each of width at most three).
--
--   The formula $\Phi_{\mathcal F}$ of Section 4.3 encodes its two cardinality requirements (5) and (6) with such an encoder.
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 3.2, p.7, used in Section 4.3, p.11

import Mathlib
import Definitions.Def_HSElemKernel_IsCardEncoding

namespace HSElemKernel

/-- A cardinality encoder: for every `N`, bound `b` and comparison `▷◁`, a number of auxiliary
variables and a CNF formula over the `N` constrained and the auxiliary variables (Sheng–Xiao,
arXiv:2609.06512, held version sha256 aca9c70e…, Lemma 3.2, p.7, used in Section 4.3, p.11). -/
structure CardEncoder where
  /-- the number of auxiliary variables of the encoding of `∑_{i ≤ N} xᵢ ▷◁ b` -/
  aux : ℕ → ℕ → CardOp → ℕ
  /-- the encoding of `∑_{i ≤ N} xᵢ ▷◁ b` -/
  enc : (N b : ℕ) → (op : CardOp) → MantriCVQ.CNF (Fin N ⊕ Fin (aux N b op))

/-- The encoder meets the guarantee of Lemma 3.2 with constant `C` at every `N`, `b`, `▷◁`
(Sheng–Xiao, arXiv:2609.06512, held version sha256 aca9c70e…, Lemma 3.2, p.7): correct
encodings with `≤ C(N + 1)` auxiliary variables and clauses, each of width at most three. -/
def CardEncoder.Spec (E : CardEncoder) (C : ℕ) : Prop :=
  ∀ N b op, IsCardEncoding N b op (E.aux N b op) (E.enc N b op) C

end HSElemKernel


