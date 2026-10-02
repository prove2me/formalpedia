-- Prove2me | Definitions.Def_AppliedComb_ManyFaces_IndepOutside
-- name    : AppliedComb_ManyFaces_IndepOutside
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:45:16.377993+00:00
-- url     : https://prove2.me/theorems/df4aff0f-31c5-48a0-b0b6-4792f6b2d2ed
-- title:
--   Joint failure of a subfamily, and "E is independent of any event not in 𝓝" (Section 16.7)
-- statement:
--   Let $(\Omega, P)$ be a probability space and let $\mathcal F = (A_i)_{i \in \iota}$ be a family of events indexed by a finite set $\iota$. For a subfamily $G \subseteq \iota$ write $\overline{A}$ for the complement of an event $A$ and
--   $$\prod_{j \in G} \overline{A_j} \;=\; \bigcap_{j \in G} \overline{A_j},$$
--   the event that every event of the subfamily fails (concatenation is intersection, as in the book). For $G = \emptyset$ this is the whole sample space.
--
--   Fix $i \in \iota$ and a subfamily $N(i) \subseteq \iota$. We say that **$A_i$ is independent of any event not in $N(i)$** if for every subfamily $G \subseteq \iota$ with $i \notin G$ and $G \cap N(i) = \emptyset$,
--   $$P\Big(A_i \cap \prod_{j \in G} \overline{A_j}\Big) = P(A_i)\, P\Big(\prod_{j \in G} \overline{A_j}\Big).$$
--
--   This is the book's condition $P(E \mid \prod_{F \in \mathcal G} \overline{F}) = P(E)$ whenever $\mathcal G \cap \mathcal N = \emptyset$, the hypothesis of both forms of the Lovász Local Lemma (Lemmas 16.14 and 16.15). It conditions on intersections of complements of events outside $N(i)$; it is neither pairwise independence nor mutual independence of the whole family.
--
--   **Formalization Note.** `allFail A G` is $\bigcap_{j \in G} (A_j)^c$. `IndepOutside μ A N i` uses the multiplicative form of the conditional probability with `μ.real` (probabilities as real numbers). When $P(\prod_{j\in G}\overline{A_j}) > 0$ it is exactly the book's equation $P(A_i \mid \cdot) = P(A_i)$; when that probability is $0$ the book's conditional probability is undefined (p. 216) and the multiplicative equation holds automatically, so nothing is added or lost.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 326, Section 16.7 (notation ∏ Ē and "independent of any event not in 𝓝"); conditional probability p. 216

import Mathlib

namespace AppliedComb.ManyFaces

open MeasureTheory

/-- The event `∏_{F ∈ 𝓖} F̄` of Keller & Trotter, *Applied Combinatorics* (2017 Edition), p. 326:
the intersection of the complements of the events `A j`, `j ∈ G`, i.e. the event that every event
of the subfamily `G` fails. For `G = ∅` it is the whole sample space. -/
def allFail {Ω ι : Type*} (A : ι → Set Ω) (G : Finset ι) : Set Ω :=
  ⋂ j ∈ G, (A j)ᶜ

/-- "`E` is independent of any event not in `𝓝`" (Keller & Trotter, p. 326), for `E = A i` and
`𝓝 = N i`: for every subfamily `G` of the family with `i ∉ G` and `G ∩ N i = ∅`,
`P(A i | ∏_{j ∈ G} Ā_j) = P(A i)`. The conditional probability is written in multiplicative form,
`P(A i ∩ ∏_{j ∈ G} Ā_j) = P(A i) · P(∏_{j ∈ G} Ā_j)`, which is the book's equation whenever the
conditioning event has positive probability (where the book's conditional probability is defined,
p. 216) and holds automatically when it has probability zero. -/
def IndepOutside {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : ι → Set Ω)
    (N : ι → Finset ι) (i : ι) : Prop :=
  ∀ G : Finset ι, i ∉ G → Disjoint G (N i) →
    μ.real (A i ∩ allFail A G) = μ.real (A i) * μ.real (allFail A G)

end AppliedComb.ManyFaces


