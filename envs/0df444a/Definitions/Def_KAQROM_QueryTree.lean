-- Prove2me | Definitions.Def_KAQROM_QueryTree
-- name    : KAQROM_QueryTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:30:53.106454+00:00
-- url     : https://prove2.me/theorems/bcb1986e-8037-43d6-925d-9d98b3dd8ec6
-- title:
--   Deterministic classical-query algorithms on a transcript, and prefix learners that may abort
-- statement:
--   A **deterministic classical-query algorithm** on an input $m$ (a complete public transcript) is a decision tree: given $m$ and the query–answer pairs learned so far, it either queries a new point or stops. Run with oracle $H$, it produces the ordered list of learned pairs (its length is the number of queries) and outputs the partial oracle $h$ they form.
--
--   A **prefix learner** additionally decides, after its queries and without further queries, whether to output $h$ or to abort.
--
--   Lemma 5.10's learner $L^H_{\varepsilon_1,\varepsilon_2}(m)$ is of the first kind; Lemma 5.11's $\mathsf{Learn}^{\mathsf{BM},H}_\eta$, which "outputs a partial oracle $h$ or aborts", is of the second.
--
--   **Formalization Note** A deterministic algorithm with classical oracle access and unbounded computation is exactly such a tree. A step budget makes the run total; a tree that has stopped keeps stopping.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Lemma 5.10, p.34; Lemma 5.11, p.35

import Mathlib
import Definitions.Def_KAQROM_Oracle

namespace KAQROM

/-- A **deterministic classical-query algorithm** on an input `m : M` (a complete public
transcript): a decision tree that, given `m` and the query–answer pairs learned so far, either
queries a point `x` (`some x`) or stops (`none`), for at most `depth` steps. Its output is the
partial oracle formed by the learned pairs.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Lemma 5.10
("a deterministic classical-query algorithm `L^H_{ε₁,ε₂}(m)` that takes a complete public
transcript `m` as input and outputs a partial oracle `h`"), p.34.

**Formalization Note.** A deterministic algorithm with classical oracle access and unbounded
computation is exactly such a tree: each next query is a function of the input and the answers
so far. The step budget `depth` only makes the run a total function; a tree that has stopped keeps
returning `none`. -/
structure QueryTree (M X : Type) (ℓ : ℕ) where
  /-- The step budget. -/
  depth : ℕ
  /-- The next query (or `none` to stop) given the input and the pairs learned so far. -/
  next : M → Transcript X ℓ → Option X

/-- The ordered list of query–answer pairs learned by the tree on input `m` with oracle `H`; its
length is the number of oracle queries made. -/
def QueryTree.learned {M X : Type} {ℓ : ℕ} (L : QueryTree M X ℓ) (H : Oracle X ℓ) (m : M) :
    Transcript X ℓ :=
  (List.range L.depth).foldl
    (fun t _ => match L.next m t with
      | some x => t ++ [(x, H x)]
      | none => t) []

/-- The partial oracle output by the tree: the learned pairs. -/
def QueryTree.output {M X : Type} [DecidableEq X] {ℓ : ℕ} (L : QueryTree M X ℓ)
    (H : Oracle X ℓ) (m : M) : PartialOracle X ℓ :=
  (L.learned H m).toPartial

/-- A **prefix learner**: a deterministic classical-query algorithm on a complete public prefix
transcript that outputs a partial oracle `h` or aborts (Lemma 5.11, p.35). After its queries it
decides, from the input and the learned pairs and without further queries, whether to output the
learned partial oracle or to abort. -/
structure PrefixLearner (M X : Type) (ℓ : ℕ) extends QueryTree M X ℓ where
  /-- `true`: output the learned partial oracle; `false`: abort. -/
  accept : M → Transcript X ℓ → Bool

/-- The output of a prefix learner: `some h` (the learned partial oracle) or `none` (abort). -/
def PrefixLearner.result {M X : Type} [DecidableEq X] {ℓ : ℕ} (L : PrefixLearner M X ℓ)
    (H : Oracle X ℓ) (m : M) : Option (PartialOracle X ℓ) :=
  if L.accept m (L.learned H m) then some (L.output H m) else none

end KAQROM


