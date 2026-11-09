-- Prove2me | Definitions.Def_ExactLearningSeparation678_Randomized_Observations
-- name    : ExactLearningSeparation678_Randomized_Observations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:28.157773+00:00
-- url     : https://prove2.me/theorems/4ec34241-5302-4fe3-8fca-b7105bd9fb21
-- title:
--   Finite adaptive transcripts and equality-query laws
-- statement:
--   A deterministic Boolean query learner is the published decision tree: an internal node queries a coordinate and chooses its next node from the answer, while a leaf returns an output. Record the sequence of actual query-answer pairs and the final output. For a query bound $D$, use $D$ optional slots, with empty slots after termination, so repeated queries and early stopping are retained.
--
--   For finite probability mass functions $p,q$ on a finite set $Y$, use the published total variation convention
--   $$d_{\rm TV}(p,q)=\frac12\sum_{y\in Y}|p(y)-q(y)|,$$
--   and define the probability of an event $E$ by $\Pr_p(E)=\sum_{y\in E}p(y)$.
--
--   For finite sets $X,Z$, with $Z$ nonempty, a law of functions $F:X\to Z$ is $k$-wise uniform when, for every $r\le k$ and every $r$ distinct inputs, their evaluation vector is uniform on $Z^r$. Its equality oracle returns $\mathbf1[F(x)=z]$ at coordinate $(x,z)$. The equality transcript law is the pushforward of the function law through the same fixed decision tree.
--
--   This layer separates computed transcript distributions from the inequalities asserted about them. Probability laws are genuine PMFs; no distance estimate is included in an algorithm or law definition.
--
--   **Formalization Note** Finite output carriers cover the finite range of any bounded decision tree. The reading of $k$-wise uniformity for sets of at most $k$ inputs is disclosed on Lemma 3.9.
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), §3.4 preamble and Eq. (12), p.23; Lemma 3.9 and its proof, pp.24–25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_PureDPQR_tvDist

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized

/-- Record all actual queries and answers, stopping at the leaf. The decision rule is the
published general decision-tree object, total on every Boolean history. -/
def queryTrace {X O : Type} : QAlgorithms.DecisionTree X Bool O → (X → Bool) → List (X × Bool) × O
  | .leaf o, _ => ([], o)
  | .node x next, f =>
    let r := queryTrace (next (f x)) f
    ((x, f x) :: r.1, r.2)

/-- Finite transcript carrier: at most D observations, padded by none after stopping, plus
final output. Every theorem imposing budget D retains the whole trace. -/
abbrev Transcript (X O : Type) (D : ℕ) := (Fin D → Option (X × Bool)) × O

def record {X O : Type} (D : ℕ) (A : QAlgorithms.DecisionTree X Bool O) (f : X → Bool) :
    Transcript X O D :=
  (fun i => (queryTrace A f).1[i.val]?, (queryTrace A f).2)

/-- Probability of an event in a genuine finite PMF. -/
noncomputable def probability {Y : Type} [Fintype Y] (p : PMF Y) (E : Y → Prop) : ℝ :=
  ∑ y, if E y then (p y).toReal else 0

/-- Reuse the published half-L1 total variation, applied to PMF masses. -/
noncomputable def tv {Y : Type} [Fintype Y] (p q : PMF Y) : ℝ :=
  PureDPQR.tvDist (fun y => (p y).toReal) (fun y => (q y).toReal)

/-- Standard k-wise independence, including every r ≤ k, even when k > |X|. -/
def KWiseUniform {X Z : Type} [Fintype X] [Fintype Z] [Nonempty Z]
    (k : ℕ) (law : PMF (X → Z)) : Prop :=
  ∀ r : ℕ, r ≤ k → ∀ ys : Fin r → X, Function.Injective ys →
    law.map (fun f i => f (ys i)) = PMF.uniformOfFintype (Fin r → Z)

noncomputable def equalityOracle {X Z : Type} [DecidableEq Z] (f : X → Z) : X × Z → Bool :=
  fun q => decide (f q.1 = q.2)

noncomputable def equalityLaw {X Z O : Type} [Fintype X] [Fintype Z] [DecidableEq Z]
    (D : ℕ) (A : QAlgorithms.DecisionTree (X × Z) Bool O) (law : PMF (X → Z)) :
    PMF (Transcript (X × Z) O D) :=
  law.map (fun f => record D A (equalityOracle f))

end ExactLearningSeparation678.Randomized


