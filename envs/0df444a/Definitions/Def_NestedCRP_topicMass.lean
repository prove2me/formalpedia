-- Prove2me | Definitions.Def_NestedCRP_topicMass
-- name    : NestedCRP_topicMass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:28:46.427092+00:00
-- url     : https://prove2.me/theorems/0a1b2ad6-9512-4409-af14-beca90aa2759
-- title:
--   Topic prior and the word mass with the topics integrated out
-- statement:
--   Nodes of the infinite tree are pairs (level, block of tourists). The topic prior draws one independent topic $\beta_{\mathsf n}\sim\mathrm{Dir}(\eta,\dots,\eta)$ on the $V$-simplex for each node $\mathsf n$. Given a tree and level allocations, the node of site $s=(d,n)$ is the node of $d$ at level $z_{d,n}$, and for a set $A$ of sites the word mass is
--
--   $$
--   \mathbb E\Bigl[\prod_{s\in A}\beta_{\mathrm{node}(s)}(w_s)\Bigr],
--   $$
--
--   the probability of the words on $A$ once the topics are integrated out. Taking $A$ to be all sites gives the probability of the corpus given the tree and the levels.
--
--   **Formalization Note** The paper attaches a topic to each table of the infinite tree. Here topics are indexed by (level, block), so they exist independently of the tree. The map from the nodes of a given tree to these indices is injective, so the topics a tree visits are i.i.d. Dirichlet and independent of the tree, which gives the same law of $(T,z,w)$. The mass is a genuine Bochner integral of a measurable integrand with values in $[0,1]$ almost surely.
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, §4, p.7:11; §5, p.7:14

import Mathlib
import Definitions.Def_NestedCRP_dirichletMeasure
import Definitions.Def_NestedCRP_Corpus
open MeasureTheory

namespace NestedCRP

/-- A node of the infinite tree: a level and the block of tourists at it. -/
abbrev Node (D : ℕ) : Type := ℕ × Finset (Fin D)

/-- The topic prior: one independent symmetric Dirichlet(η) topic on the `V`-simplex per node.
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §4, step (1), p.7:11.

**Formalization Note** The paper attaches a topic to each table of the infinite tree. Here topics are
indexed by `(ℓ, block)`, so they exist independently of the tree. Since the map from the nodes of a
given tree to `Node D` is injective, the topics a tree visits are i.i.d. Dirichlet(η) and independent
of the tree, which gives the same law of `(T, z, w)`. -/
noncomputable def topicLaw (η : ℝ) (V D : ℕ) : Measure (Node D → Fin V → ℝ) :=
  Measure.infinitePi fun _ : Node D => dirichletMeasure fun _ : Fin V => η

variable {V D : ℕ}

/-- The node of the topic of site `s`: `β_{c_d[z_{d,n}]}` of §4, step (2)(c)ii, p.7:11. -/
noncomputable def nodeOf (C : Corpus V D) (T : Tree D) (z : C.Levels) (s : C.Site) : Node D :=
  (z s.1 s.2, T.block (z s.1 s.2) s.1)

/-- The probability of the words on the sites of `A` given the tree and the levels, with the topics
integrated out: `E[∏_{s ∈ A} β_{node s}(w s)]`.
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §4, p.7:11, and §5, p.7:14 (the `β_i` are marginalized).

**Formalization Note** This is a genuine Bochner integral, not a collapsed formula. The integrand is
measurable and takes values in `[0, 1]` almost surely, so it is integrable. -/
noncomputable def topicMassOn (η : ℝ) (C : Corpus V D) (T : Tree D) (z : C.Levels)
    (A : Finset C.Site) : ℝ :=
  ∫ β, ∏ s ∈ A, β (nodeOf C T z s) (C.word s) ∂topicLaw η V D

/-- The probability of the whole corpus given the tree and the levels. -/
noncomputable def topicMass (η : ℝ) (C : Corpus V D) (T : Tree D) (z : C.Levels) : ℝ :=
  topicMassOn η C T z Finset.univ

end NestedCRP


