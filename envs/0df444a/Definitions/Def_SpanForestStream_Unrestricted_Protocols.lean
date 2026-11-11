-- Prove2me | Definitions.Def_SpanForestStream_Unrestricted_Protocols
-- name    : SpanForestStream_Unrestricted_Protocols
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:31:50.60421+00:00
-- url     : https://prove2.me/theorems/e79b4af8-1071-4c19-abdf-92101c2ec2a4
-- title:
--   One-way protocols, generalized one-coordinate protocols and the universal relation
-- statement:
--   - **Product law**: $k$ independent copies of a law $p$.
--   - **$k$-fold one-way protocol**: pairs $(X_j,Y_j)_{j\le k}$ independent with common law $D$; a message $M$ drawn from $X^k$ alone (any shared seed is part of $M$); an output $O=(O_1,\dots,O_k)$ drawn from $(M,Y^k)$ with fresh coins. The joint law of $((X_j,Y_j)_j,M,O)$ thus satisfies $M\leftrightarrow X^k\leftrightarrow Y^k$ and $O\leftrightarrow(M,Y^k)\leftrightarrow X^k$.
--   - **Generalized one-way protocol** on an input law $D'$ of $(X,Y)$: the message may depend on both $X$ and $Y$, and the output is drawn from $(M,Y)$, so $O\leftrightarrow(M,Y)\leftrightarrow X$.
--   - **Universal relation** on $[U]$: given $T\subsetneq S\subseteq[U]$, an answer is correct when it is a member of $S\setminus T$; the failure symbol is never correct.
--   - The **uniform law on $m$-subsets** of $[U]$. When $m>U$ there are none, and the definition returns a point mass, which no statement uses.
--
--   Messages and outputs are arbitrary random variables of unrestricted length, with no computational restriction.
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 20 (PDF 23), Lemma 3.4; pp. 30–31 (PDF 33–34), Lemmas 4.5, 4.6, Proposition 4.7; p. 48 (PDF 51), App. B.3

import Mathlib
import Definitions.Def_SpanForestStream_Unrestricted_Info

open scoped ENNReal

namespace SpanForestStream.Unrestricted

noncomputable section

/-!
# One-way protocols and the universal relation

Chao, Cen, Ma, Wang, arXiv:2611.04365: Lemma 3.4, p. 20; Lemmas 4.5, 4.6 and Proposition 4.7,
pp. 30–31; App. B.3, p. 48. Messages and outputs are arbitrary random variables (unbounded
length allowed); there is no computational restriction.
-/

/-- The law of `k` independent copies of `p`. -/
def piLaw {α : Type} : (k : ℕ) → PMF α → PMF (Fin k → α)
  | 0, _ => PMF.pure finZeroElim
  | k + 1, p => p.bind fun a => (piLaw k p).map fun f => Fin.cons a f

/-- The joint law of `((X_j, Y_j)_{j ≤ k}, M, O)` of a `k`-fold one-way protocol: the pairs are
independent with common law `D`, the message `M` is drawn from `X^k` alone (any shared seed is part
of `M`), and the output `O = (O_1, …, O_k)` from `(M, Y^k)` with fresh coins. This encodes the
Markov conditions `M ↔ X^k ↔ Y^k` and `O ↔ (M, Y^k) ↔ X^k`. -/
def oneWayJoint {X Y Msg Out : Type} {k : ℕ} (D : PMF (X × Y))
    (msg : (Fin k → X) → PMF Msg) (out : Msg → (Fin k → Y) → PMF (Fin k → Out)) :
    PMF ((Fin k → X × Y) × Msg × (Fin k → Out)) :=
  (piLaw k D).bind fun xy => (msg fun j => (xy j).1).bind fun m =>
    (out m fun j => (xy j).2).map fun o => (xy, m, o)

/-- The joint law of `((X, Y), M, O)` of a generalized one-way protocol on input law `D'`: the
message may depend on both inputs, and the output is drawn from `(M, Y)` with fresh coins, so
`O ↔ (M, Y) ↔ X`. -/
def genJoint {X Y Msg Out : Type} (D' : PMF (X × Y)) (msg : X → Y → PMF Msg)
    (out : Msg → Y → PMF Out) : PMF ((X × Y) × Msg × Out) :=
  D'.bind fun xy => (msg xy.1 xy.2).bind fun m => (out m xy.2).map fun o => (xy, m, o)

/-- The universal-relation answer `o` is correct for `T ⊊ S`: it is a member of `S \ T`
(`none` is the failure symbol). -/
def URSolves {U : ℕ} (S T : Finset (Fin U)) (o : Option (Fin U)) : Prop :=
  ∃ x, o = some x ∧ x ∈ S ∧ x ∉ T

/-- The uniform law on the `m`-subsets of `[U]`. When `m > U` there are none and the value is a
point mass at `∅` (never used: every statement has `U ≥ m`). -/
def uniformSubsets (U m : ℕ) : PMF (Finset (Fin U)) :=
  if h : m ≤ U then
    PMF.uniformOfFinset ((Finset.univ : Finset (Fin U)).powersetCard m)
      (Finset.powersetCard_nonempty.mpr (by simpa using h))
  else PMF.pure ∅

end

end SpanForestStream.Unrestricted


