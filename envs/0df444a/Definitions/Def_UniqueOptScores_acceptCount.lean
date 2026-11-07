-- Prove2me | Definitions.Def_UniqueOptScores_acceptCount
-- name    : UniqueOptScores_acceptCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:16.560587+00:00
-- url     : https://prove2.me/theorems/c19a0767-7726-4e90-b530-d63b454df215
-- title:
--   Number of accepting computations of a verifier
-- statement:
--   A nondeterministic verifier with a finite set of choice sequences $\Pi$ is the family $(V_\pi)_{\pi \in \Pi}$ of deterministic query algorithms with Boolean output, one per choice sequence. Its **accepting count** under an oracle $O$ is
--   $$
--   c(O) = \#\{\pi \in \Pi : \mathrm{eval}(V_\pi, O) = 1\}.
--   $$
--   Distinct computations count separately even when they query the same points.
--
--   **Formalization Note** A choice sequence determines one deterministic computation, so this is the paper's count of accepting computations.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 7.2, p.26 ("If cj counts the accepting paths of test j"); proof of Lemma 2.3, p.27

import Mathlib
import Definitions.Def_UniqueOptScores_QTree

namespace UniqueOptScores

/-- **The number of accepting computations of a verifier.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §7.2, p.26: "If c_j counts the accepting paths of test j"; proof of Lemma 2.3, p.27:
"Distinct computations contribute separately".

A nondeterministic verifier with finitely many choice sequences `π : κ` is the family of
deterministic query algorithms `V π`; `acceptCount V O` is the number of choice sequences whose
computation accepts under the oracle `O`.

**Formalization Note.** A choice sequence determines one deterministic computation, so this is the
paper's count of accepting computations. -/
def acceptCount {κ α : Type*} [Fintype κ] (V : κ → QTree α Bool) (O : α → Bool) : ℕ :=
  (Finset.univ.filter fun π => (V π).eval O = true).card

end UniqueOptScores


