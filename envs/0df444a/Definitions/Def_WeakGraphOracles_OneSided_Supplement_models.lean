-- Prove2me | Definitions.Def_WeakGraphOracles_OneSided_Supplement_models
-- name    : WeakGraphOracles_OneSided_Supplement_models
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:24:18.977881+00:00
-- url     : https://prove2.me/theorems/929f34f8-1ef0-4252-a11e-dd9853972ef7
-- title:
--   Edit distance $\mathrm{dist}_\oplus$, induced freeness, two-sided and one-sided testers, GEN2/GEN3 oracles and views
-- statement:
--   This module extends the published GEN1 oracle layer to arbitrary graph properties, two-sided error, the stronger models GEN2 and GEN3, and the views used in the lower bounds.
--
--   For graphs $G,G'$ on the same $n$ labels, $|E(G)\oplus E(G')|$ is the number of vertex pairs that are an edge of exactly one of them, and
--
--   $$\mathrm{dist}_\oplus(G,G')=\frac{|E(G)\oplus E(G')|}{|E(G)|+|E(G')|},$$
--
--   with value $0$ for two identical edgeless graphs (the only case of a zero denominator). A graph $G$ is $\epsilon$-far from a property $P$ when $\mathrm{dist}_\oplus(G,G')\ge\epsilon$ for every $G'\in P$ on the same labels; if $P$ has no member, every graph is far. A graph is induced $F$-free when no member $H\in F$ has an induced embedding, that is an injective map $V(H)\to V(G)$ under which $(\phi(a),\phi(b))$ is an edge exactly when $(a,b)$ is.
--
--   A randomized policy is correct with two-sided error on a property with a farness notion when it accepts every member with probability at least $2/3$ and rejects every far input with probability at least $2/3$; it is one-sided when members are accepted with probability $1$. Two-sided testability in GEN1 means: for every $\epsilon>0$ there is a query bound $q$, fixed before $n$, and for every $n$ one GEN1 policy of depth at most $q$ correct on all $n$-vertex graphs.
--
--   GEN2 adds an exact degree query $\deg_G(v)$ at any label to the published GEN1 queries, which keep their fresh uniform random-neighbour and random-edge replies with isolation and no-edge answers. In GEN3 the value $|E(G)|$ is public, like $n$: a GEN3 tester is a family of GEN2 policies indexed by the edge count, and the one indexed by $|E(G)|$ is run on $G$.
--
--   The total variation distance of two discrete laws is $\tfrac12\sum_x|\mu(x)-\nu(x)|$. A uniformly random relabeling of $G$ is its image under a uniformly random permutation of the $n$ labels. The view of a randomized policy on an input drawn from a law $\mu$ is the joint law of its coins (the chosen deterministic plan) and its complete run (decision and query/reply transcript), the input being drawn independently of the coins.
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 1 (PDF p. 2), §1 (dist⊕, farness); p. 5 (PDF p. 6), §3, GEN1–GEN3 and Definition 1 with footnote 1; pp. 5–6 (PDF pp. 6–7), Remark 2; p. 10 (PDF p. 11), §5; p. 19 (PDF p. 20), §7.6 (induced embeddings); p. 19 (PDF p. 20), Lemma 7.2 (views)

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_protocol
import Definitions.Def_WeakGraphOracles_OneSided_graphs
import Definitions.Def_WeakGraphOracles_OneSided_oracle

set_option autoImplicit false

namespace WeakGraphOracles.OneSided.Supplement

/-- `|E(G) ⊕ E(G')|`: the number of vertex pairs on which two graphs on the
same labels differ (edges of one that are non-edges of the other). -/
noncomputable def symmDiffCard {n : ℕ} (G G' : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact ((edges G \ edges G') ∪ (edges G' \ edges G)).card

/-- `dist⊕(G,G') = |E(G) ⊕ E(G')| / (|E(G)| + |E(G')|)`. The denominator is zero
only when both graphs are edgeless, and then the numerator is zero too, so the
value `0` is the source's distance between identical edgeless graphs. -/
noncomputable def distPlus {n : ℕ} (G G' : SimpleGraph (Fin n)) : ℝ :=
  (symmDiffCard G G' : ℝ) / ((edges G).card + (edges G').card)

/-- `G` is `ε`-far from the property `P` (on its own label set): its `dist⊕`
distance to every member of `P` is at least `ε` (Section 1). The closest graph
exists since there are finitely many graphs; an empty `P` makes every graph far
(distance `+∞`). -/
def DistFar {n : ℕ} (P : SimpleGraph (Fin n) → Prop) (ε : ℝ) (G : SimpleGraph (Fin n)) :
    Prop :=
  ∀ G' : SimpleGraph (Fin n), P G' → ε ≤ distPlus G G'

/-- Induced appearances: `H.graph ↪g G` is an injective map that preserves and
reflects adjacency. Induced `F`-freeness excludes them for every member. -/
def InducedFree {n : ℕ} (F : Finset Pattern) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ H ∈ F, IsEmpty (H.graph ↪g G)

/-- Acceptance probability of a randomized policy run against a response kernel. -/
noncomputable def acceptProb {Q R : Type} {q : ℕ} (kernel : Q → PMF R)
    (A : RandomPolicy Q R q) : ℝ :=
  eventProbability (executePolicy kernel A) (fun out => out.1 = true)

/-- Two-sided correctness of one fixed policy on every input: members of the
property are accepted with probability at least `2/3`, far inputs are rejected
with probability at least `2/3`. The input is seen only through `kernel`. -/
def TwoSidedCorrect {X Q R : Type} {q : ℕ} (kernel : X → Q → PMF R)
    (yes far : X → Prop) (A : RandomPolicy Q R q) : Prop :=
  ∀ G : X, (yes G → (2 : ℝ) / 3 ≤ acceptProb (kernel G) A) ∧
    (far G → (2 : ℝ) / 3 ≤ 1 - acceptProb (kernel G) A)

/-- One-sided correctness: members are accepted with probability `1`. -/
def OneSidedCorrect {X Q R : Type} {q : ℕ} (kernel : X → Q → PMF R)
    (yes far : X → Prop) (A : RandomPolicy Q R q) : Prop :=
  ∀ G : X, (yes G → acceptProb (kernel G) A = 1) ∧
    (far G → (2 : ℝ) / 3 ≤ 1 - acceptProb (kernel G) A)

/-- Two-sided testability in GEN1: for every `ε > 0` one query bound `q`, fixed
before `n`, and for every `n` one GEN1 policy correct on all `n`-vertex graphs.
`far ε n` is the farness notion of the property. -/
def GEN1TwoSidedTestable (P : (n : ℕ) → SimpleGraph (Fin n) → Prop)
    (far : ℝ → (n : ℕ) → SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ q : ℕ, ∀ n : ℕ, ∃ A : Policy n q,
    TwoSidedCorrect (fun G : SimpleGraph (Fin n) => oracle G) (P n) (far ε n) A

/-- GEN2 queries: the GEN1 queries plus an exact degree query at any label. -/
inductive Query2 (n : ℕ) where
  | base (a : Query n) : Query2 n
  | degree (v : Fin n) : Query2 n

inductive Reply2 (n : ℕ) where
  | base (r : Reply n) : Reply2 n
  | degree (d : ℕ) : Reply2 n

/-- The GEN2 oracle: GEN1 queries are answered by the published GEN1 kernel
(fresh uniform neighbor / oriented edge, isolation and no-edge replies); a
degree query returns `deg_G(v)` exactly. No adjacency query exists. -/
noncomputable def oracle2 {n : ℕ} (G : SimpleGraph (Fin n)) : Query2 n → PMF (Reply2 n)
  | .base a => (oracle G a).map Reply2.base
  | .degree v => PMF.pure (Reply2.degree (G.neighborSet v).ncard)

abbrev GEN2Policy (n q : ℕ) := RandomPolicy (Query2 n) (Reply2 n) q

/-- GEN3: the policy may depend on the public value `|E(G)|` (like `n`), and
then queries the GEN2 oracle. Correct on every `n`-vertex graph. -/
def GEN3TwoSidedCorrect {n q : ℕ} (yes far : SimpleGraph (Fin n) → Prop)
    (A : ℕ → GEN2Policy n q) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (yes G → (2 : ℝ) / 3 ≤ acceptProb (oracle2 G) (A (edges G).card)) ∧
    (far G → (2 : ℝ) / 3 ≤ 1 - acceptProb (oracle2 G) (A (edges G).card))

/-- Total variation distance of two discrete laws, `½ Σ_x |μ(x) − ν(x)|`
(computed in `ℝ≥0∞`, where `(a - b) + (b - a) = |a - b|`). -/
noncomputable def tvDist {X : Type} (μ ν : PMF X) : ℝ :=
  ((∑' x, ((μ x - ν x) + (ν x - μ x))) / 2).toReal

/-- A uniformly random relabeling of `G`: the image of `G` under a uniformly
random permutation of its `n` labels. -/
noncomputable def relabelLaw {n : ℕ} (G : SimpleGraph (Fin n)) : PMF (SimpleGraph (Fin n)) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin n))).map fun σ => G.map σ.toEmbedding

/-- The view of a randomized policy on a random input drawn from `μ`: the joint
law of its internal coins (the chosen deterministic plan) and its full run
(decision and transcript of queries and replies). The input is drawn
independently of the coins and stays fixed during the run. -/
noncomputable def view {X Q R : Type} {q : ℕ} (kernel : X → Q → PMF R)
    (A : RandomPolicy Q R q) (μ : PMF X) :
    PMF (QueryTree Q R q × (Bool × List (Q × R))) :=
  A.bind fun T => μ.bind fun G => (executeTree (kernel G) T).map fun out => (T, out)

end WeakGraphOracles.OneSided.Supplement


