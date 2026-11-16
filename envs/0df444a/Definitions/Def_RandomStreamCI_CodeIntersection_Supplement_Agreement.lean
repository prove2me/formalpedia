-- Prove2me | Definitions.Def_RandomStreamCI_CodeIntersection_Supplement_Agreement
-- name    : RandomStreamCI_CodeIntersection_Supplement_Agreement
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:45:30.393444+00:00
-- url     : https://prove2.me/theorems/d4df0142-782f-405e-be17-59fcd65d1d40
-- title:
--   Pairwise code agreement and high-value events
-- statement:
--   For a finite code $C\subseteq\Sigma^n$, pairwise agreement at most $d-1$ means that distinct codewords coincide on at most $d-1$ coordinate indices. For $A\subseteq[n]\times\Sigma$ and a normalized Boolean law $X$ on $\{0,1\}^A$, put $k_c=|T_c\cap A|$ and define
--   $$E_c=\left\{\sum_{u\in T_c\cap A}X_u\ge k_c/2+s\right\}.$$
--   The corresponding probability sums the full PMF over this event. The surplus $s$ is real, and the event uses exactly the coordinates in $A$. No independence or density-restoring condition on $X$ is part of the definition. These notions apply to arbitrary finite codes, independently of polynomial structure.
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, release papers-1/71.pdf, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Lemma 25, pp. 19--20; Lemma 26, p. 20

import Definitions.Def_RandomStreamCI_CodeIntersection_Stream

noncomputable section

namespace RandomStreamCI.CodeIntersection.Supplement

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Lemmas 25 and 26: pairwise coordinate agreement, for arbitrary finite codes. -/
def PairwiseAgreement {n : ℕ} {Alphabet : Type*} [DecidableEq Alphabet]
    (C : Finset (Word n Alphabet)) (d : ℕ) : Prop :=
  ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' →
    (Finset.univ.filter (fun i => c i = c' i)).card ≤ d - 1

/-- Lemma 25's observed Hamming weight on exactly T_c intersect A, under any Boolean law on A. -/
def HighValue {n : ℕ} {Alphabet : Type*} [DecidableEq Alphabet]
    (A : Finset (Address n Alphabet)) (c : Word n Alphabet) (s : ℝ) (x : A → Bool) : Prop :=
  (observedCount c A : ℝ) / 2 + s ≤
    ((Finset.univ.filter (fun u : A => (u : Address n Alphabet) ∈ wordAddresses c ∧ x u = true)).card : ℝ)

/-- Event probability under the whole normalized law, without any partition or density hypothesis. -/
def highValueProbability {n : ℕ} {Alphabet : Type*} [DecidableEq Alphabet]
    (A : Finset (Address n Alphabet)) (X : PMF (A → Bool)) (c : Word n Alphabet) (s : ℝ) : ℝ :=
  eventMass (weights X) (HighValue A c s)

end RandomStreamCI.CodeIntersection.Supplement


