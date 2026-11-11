-- Prove2me | Definitions.Def_FOMCMonDep_ConstructionSeq
-- name    : FOMCMonDep_ConstructionSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:24:24.135162+00:00
-- url     : https://prove2.me/theorems/afe10fb8-ff52-4c78-89ce-1a1fad8b8e9d
-- title:
--   Construction sequences, radius-$r$ width and radius-$r$ depth-$q$ width (Definition 4.1)
-- statement:
--   A **construction sequence** of a graph $G=(V,E)$ is a sequence $G_1,\dots,G_\lambda$ of partial graphs on $V$ such that $G_1$ has no resolved pairs and only singleton parts, every $G_{t+1}$ is obtained from $G_t$ by one merge of two distinct parts or one resolve of two parts (positive or negative), and $G_\lambda$ has a single part, $E(G_\lambda)=E$ and $N(G_\lambda)=\binom V2-E$. Its **length** is $\lambda$.
--
--   1. The **radius-$r$ width** is the maximum over $t\in[\lambda]$ and $v\in V$ of the number of parts of $G_t$ meeting $\mathrm{Ball}^{G_t}_r(v)$.
--   2. (**Definition 4.1**) The **radius-$r$ depth-$q$ width** is
--   $$\max_{t\in[\lambda-1]}\ \max_{v\in V}\ \bigl|\mathrm{Types}^{G_t}_{q,q}\bigl(\mathrm{Ball}^{G_{t+1}}_r(v)\bigr)\bigr|,$$
--   the number of quantifier-rank-$q$ types of $q$-tuples in $G_t$ realized in a ball of the next partial graph.
--   3. A construction sequence is input as the number $\lambda-1$ of steps followed by the steps, each coded $[0,P,Q]$ (merge), $[1,P,Q]$ (positive resolve) or $[2,P,Q]$ (negative resolve).
--
--   The depth-$q$ width is the quantity connecting the two halves of the proof: Theorem 4.2 produces sequences of small depth-$q$ width, and Theorem 4.3 runs in time polynomial in it.
--
--   **Formalization Note** A sequence is the list of its $\lambda-1$ steps on named colors, starting from vertex $v$ having color $v$; each step must act on parts (nonempty colors). "A single part" is written "all vertices have the same color", vacuous for the empty graph. The maximum over an empty range ($\lambda=1$) is $0$. On $n$ vertices there are at most $n^q$ types of $q$-tuples, so the counts are finite.
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), §2, p.6 (PDF 8); §4, p.12 (PDF 14); Part III, p.38 (PDF 40)

import Mathlib
import Definitions.Def_FOMCMonDep_PartialGraph
import Definitions.Def_FOMCMonDep_tp

set_option autoImplicit false

namespace FOMCMonDep

/-- One step of a construction sequence: `merge P Q`, or `resolve pos P Q` (`pos = true`: positive resolve). -/
inductive Step
  | merge (P Q : ℕ)
  | resolve (pos : Bool) (P Q : ℕ)

namespace Step

/-- The partial graph after the step. -/
def apply {n : ℕ} (G : PartialGraph n) : Step → PartialGraph n
  | merge P Q => G.merge P Q
  | resolve pos P Q => G.resolve pos P Q

/-- The step is an operation on parts of `G` (§2, p.5–6): "For two distinct parts P, Q of H, the merge of P and Q
replaces them by the single part P ∪ Q. For two parts P, Q of H (possibly P = Q), the positive resolve …". Parts are
nonempty color classes. -/
def Valid {n : ℕ} (G : PartialGraph n) : Step → Prop
  | merge P Q => P ≠ Q ∧ (∃ v, G.color v = P) ∧ (∃ v, G.color v = Q)
  | resolve _ P Q => (∃ v, G.color v = P) ∧ (∃ v, G.color v = Q)

/-- A step as an input: `[0, P, Q]` (merge), `[1, P, Q]` (positive resolve), `[2, P, Q]` (negative resolve). -/
def code : Step → List ℤ
  | merge P Q => [0, (P : ℤ), (Q : ℤ)]
  | resolve true P Q => [1, (P : ℤ), (Q : ℤ)]
  | resolve false P Q => [2, (P : ℤ), (Q : ℤ)]

end Step

/-- `G_t` (`t ≥ 1`): the initial partial graph after the first `t − 1` steps. A list of `λ − 1` steps describes the
sequence `G₁, …, G_λ` of partial graphs; `G₁ = PartialGraph.initial n`. -/
def stage {n : ℕ} (seq : List Step) (t : ℕ) : PartialGraph n :=
  (seq.take (t - 1)).foldl Step.apply (PartialGraph.initial n)

/-- The length `λ` of the sequence `G₁, …, G_λ` (the number of partial graphs). -/
def seqLength (seq : List Step) : ℕ := seq.length + 1

/-- **Construction sequences.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §2, p.6 (PDF 8): "A construction sequence of a graph
G = (V, E) is a sequence G1, . . . , Gλ of partial graphs with vertex set V, such that G1 has no resolved pairs and only
singleton parts, every Gt+1 is obtained from Gt by one merge or one resolve, and, finally, Gλ has a single part,
E(Gλ) = E, and N(Gλ) = (V choose 2) − E." Part III, p.38 (PDF 40): "every step of a construction sequence G1, . . . ,
Gλ (Section 2) has the form Gt+1 = merge_{P,Q}(Gt), resolve⁺_{P,Q}(Gt), or resolve⁻_{P,Q}(Gt) for some colors P, Q."

**Formalization Note.** The sequence is the list of its `λ − 1` steps on named colors, from `G₁` with `color v = v`
(any naming of the singleton parts is equivalent); every step acts on parts (`Step.Valid`). "Gλ has a single part" is
written "all vertices of Gλ have the same color", which for `n = 0` (no vertices, hence no parts) holds vacuously.
`N(Gλ) = (V choose 2) − E` is `Gᶜ`, the complement graph. -/
def IsConstructionSeq {n : ℕ} (G : SimpleGraph (Fin n)) (seq : List Step) : Prop :=
  (∀ (t : ℕ) (h : t < seq.length), (seq[t]'h).Valid (stage (n := n) seq (t + 1))) ∧
    (∀ u v : Fin n, (stage (n := n) seq (seqLength seq)).color u = (stage (n := n) seq (seqLength seq)).color v) ∧
    (stage seq (seqLength seq)).E = G ∧ (stage seq (seqLength seq)).N = Gᶜ

/-- **The radius-`r` width of a construction sequence.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §2, p.6 (PDF 8): "The radius-r
width of the sequence is the maximum, over all t ∈ [λ] and v ∈ V, of the number of parts of Gt that intersect
Ball^{Gt}_r(v)." The parts meeting the ball are the colors of its vertices. -/
noncomputable def radiusWidth {n : ℕ} (seq : List Step) (r : ℕ) : ℕ :=
  ((Finset.Icc 1 (seqLength seq)) ×ˢ (Finset.univ : Finset (Fin n))).sup fun p =>
    ((stage (n := n) seq p.1).color '' (stage (n := n) seq p.1).ball r p.2).ncard

/-- **The radius-`r` depth-`q` width (Definition 4.1).** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §4, p.12 (PDF 14):
"For r, q ∈ N, the radius-r depth-q width of a construction sequence G1, . . . , Gλ is defined as:
max_{t∈[λ−1]} max_{v∈V(G)} |Types^{Gt}_{q,q}(Ball^{Gt+1}_r(v))|." The types are first-order types over the signature
`PGLang` of partial graphs, without parameters.

**Formalization Note.** The maximum over an empty range (`λ = 1`, or `n = 0`) is `0`. On `Fin n` there are at most
`n^q` types of `q`-tuples, so the `ℕ∞`-valued count is finite and `toNat` is exact. The color names do not affect the
number of types (renaming colors renames formulas, and an unused color is defined by `⊥`). -/
noncomputable def depthWidth {n : ℕ} (seq : List Step) (r q : ℕ) : ℕ :=
  ((Finset.Icc 1 (seqLength seq - 1)) ×ˢ (Finset.univ : Finset (Fin n))).sup fun p =>
    (typeCount (stage (n := n) seq p.1).toStructure q q ((stage (n := n) seq (p.1 + 1)).ball r p.2) ∅).toNat

/-- **A construction sequence as an input or output**: the number `λ − 1` of steps, then the step codes. -/
def seqCode (seq : List Step) : List ℤ :=
  (seq.length : ℤ) :: seq.flatMap Step.code

end FOMCMonDep


