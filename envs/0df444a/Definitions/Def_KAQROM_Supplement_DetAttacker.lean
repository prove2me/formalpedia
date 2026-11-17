-- Prove2me | Definitions.Def_KAQROM_Supplement_DetAttacker
-- name    : KAQROM_Supplement_DetAttacker
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:47:33.593202+00:00
-- url     : https://prove2.me/theorems/ade8a584-86aa-4e1a-b0c1-02b20a008dad
-- title:
--   Deterministic and finitely randomized classical-query algorithms with an output
-- statement:
--   A **deterministic classical-query algorithm** with input $m\in M$ and output in $O$ is a decision tree: given $m$ and the query–answer pairs received so far it either queries a point $x\in X$ or stops, and when it stops it computes its output from $m$ and the learned pairs without further queries. Its number of queries on input $m$ under oracle $H$ is the length of the learned list; a worst-case bound $N$ means at most $N$ queries for every $H$ and every $m$.
--
--   A **randomized classical-query algorithm** draws coins $\omega$ from a finite set with probabilities $w(\omega)\ge0$, $\sum_\omega w(\omega)=1$, and then runs a deterministic algorithm depending on $\omega$; its query bound holds for every coin value.
--
--   These are the passive attackers of Theorems 6.2 and 6.11, which compute their key guess deterministically from the learners' recorded view, the verification predicate and the predictor of Theorem 7.5, and the classical distinguishers of Theorem 7.3.
--
--   **Formalization Note** The tree is the published `KAQROM.QueryTree`. Finitely many coin values restrict the class of randomized algorithms; the class is only used in statements of the form "there is a classical algorithm".
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Theorems 6.2 and 6.11, pp.46, 63; §7.2, p.74; §7.4, pp.76–78

import Mathlib
import Definitions.Def_KAQROM_Oracle
import Definitions.Def_KAQROM_QueryTree

namespace KAQROM.Supplement

open KAQROM

/-- A **deterministic classical-query algorithm with an output**: a published `KAQROM.QueryTree`
(each next query, or the decision to stop, is a function of the input and the answers received
so far) together with an output map that computes the result from the input and the learned
query–answer pairs without further queries.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Theorems 6.2 and
6.11 (pp.46, 63: the passive attacker "obtains all its oracle information through two learners,
after which it computes K∗ deterministically from their recorded view without further oracle
queries"); the predictor `E_ξ` in the proof of Theorem 7.5 (p.78); the verification predicate
`V^H_Ver` of p.76.

**Formalization Note.** A computationally unbounded deterministic algorithm with classical oracle
access is exactly such a tree. Its number of queries on input `m` is the length of the learned
list. -/
structure DetAttacker (M X : Type) (ℓ : ℕ) (O : Type) extends QueryTree M X ℓ where
  /-- The output, computed from the input and the learned pairs. -/
  guess : M → Transcript X ℓ → O

/-- The output of a deterministic classical-query algorithm on input `m` with oracle `H`. -/
def DetAttacker.out {M X : Type} {ℓ : ℕ} {O : Type} (E : DetAttacker M X ℓ O) (H : Oracle X ℓ)
    (m : M) : O :=
  E.guess m (E.learned H m)

/-- Worst-case query bound: on every oracle and every input the algorithm makes at most `N`
classical queries. -/
def DetAttacker.QueriesLe {M X : Type} {ℓ : ℕ} {O : Type} (E : DetAttacker M X ℓ O) (N : ℕ) :
    Prop :=
  ∀ (H : Oracle X ℓ) (m : M), (E.learned H m).length ≤ N

/-- A **classical randomized classical-query algorithm** with finitely many coin values: coins
`ω ∈ Ω` drawn with probabilities `w ω` (nonnegative, summing to `1`), then the deterministic
algorithm `alg ω`.

**Formalization Note.** Used only under an existential quantifier ("there is a classical
attacker"): finitely many coin values restrict the class, so existence of such an attacker is at
least as strong as existence of a general randomized classical attacker. -/
structure RandDet (M X : Type) (ℓ : ℕ) (O : Type) where
  /-- The coin space. -/
  Ω : Type
  [fΩ : Fintype Ω]
  /-- The coin distribution. -/
  w : Ω → ℝ
  w_nonneg : ∀ ω, 0 ≤ w ω
  w_sum : ∑ ω, w ω = 1
  /-- The deterministic algorithm run on coins `ω`. -/
  alg : Ω → DetAttacker M X ℓ O

attribute [instance] RandDet.fΩ

/-- Worst-case query bound of a randomized classical algorithm: for every coin value, oracle and
input, at most `N` queries. -/
def RandDet.QueriesLe {M X : Type} {ℓ : ℕ} {O : Type} (C : RandDet M X ℓ O) (N : ℕ) : Prop :=
  ∀ ω, (C.alg ω).QueriesLe N

/-- The probability that a randomized classical algorithm outputs `o` on input `m` with oracle
`H`. -/
noncomputable def RandDet.prob {M X : Type} {ℓ : ℕ} {O : Type} [DecidableEq O]
    (C : RandDet M X ℓ O) (H : Oracle X ℓ) (m : M) (o : O) : ℝ :=
  ∑ ω, if (C.alg ω).out H m = o then C.w ω else 0

end KAQROM.Supplement


