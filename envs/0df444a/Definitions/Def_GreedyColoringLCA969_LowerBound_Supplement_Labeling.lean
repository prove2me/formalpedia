-- Prove2me | Definitions.Def_GreedyColoringLCA969_LowerBound_Supplement_Labeling
-- name    : GreedyColoringLCA969_LowerBound_Supplement_Labeling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:32:15.889708+00:00
-- url     : https://prove2.me/theorems/b45ab3e2-0655-4e50-9da2-1c6b1a5590a5
-- title:
--   Extendable and radius-one locally verifiable labeling problems
-- statement:
--   An $L$-labeling problem specifies which labelings $l:V\to L$ are correct on each finite simple undirected graph $G=(V,E)$. The label set is arbitrary. For a vertex $v$, its neighbor-label multiset retains the multiplicity of each label.
--
--   Given $F:\operatorname{Mult}(L)\to L$ and a permutation of the vertices, sequential labeling assigns each vertex $F(S)$, where $S$ contains exactly the labels already assigned to its neighbors. The predicate that $F$ is an extension rule requires every completed labeling obtained in every ordering on every graph to be correct. A local verifier is a single set $C\subseteq L\times\operatorname{Mult}(L)$ such that
--
--   $$P(G,l)\iff\forall v\in V,\ (l(v),\{\!\{l(u):u\in N_G(v)\}\!\})\in C.$$
--
--   A label is realizable when some sequential labeling produces it at a vertex. The spawning relation $\alpha\rightsquigarrow\beta$ means $\alpha\in S$ and $F(S)=\beta$ for some finite multiset $S$. These definitions place no degree or size restriction on the graphs and no finiteness restriction on $L$.
--
--   **Formalization Note** Vertices use $\operatorname{Fin}(n)$, shifting the source's identifiers down by one. Sequential states initialize unused entries to $F(\varnothing)$; the strict earlier-position filter excludes every unused entry from the argument of $F$.
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), pp.7–8 (PDF 8–9), Definitions 2.1–2.4; p.17 (PDF 18), Definition 4.6 and Lemma 4.7 hypothesis

import Definitions.Def_GreedyColoringLCA969_LowerBound_GraphBasics

open scoped ENNReal BigOperators
open MeasureTheory Classical
set_option autoImplicit false

namespace GreedyColoringLCA969.LowerBound.Supplement

/-- A correctness predicate on all finite simple graphs, not on a degree-restricted class. -/
abbrev LabelProblem (L : Type) := ∀ {n : ℕ}, SimpleGraph (Fin n) → (Fin n → L) → Prop

noncomputable def neighborLabels {L : Type} {n : ℕ} (G : SimpleGraph (Fin n))
    (l : Fin n → L) (v : Fin n) : Multiset L :=
  (G.neighborFinset v).val.map l

/-- The state after i sequential assignments. Unprocessed entries are initialized to F(∅)
but are excluded from every multiset by the strict ordering test. -/
noncomputable def sequentialState {L : Type} {n : ℕ} (F : Multiset L → L)
    (G : SimpleGraph (Fin n)) (order : Equiv.Perm (Fin n)) : ℕ → (Fin n → L)
  | 0 => fun _ => F 0
  | i + 1 => if h : i < n then
      let v := order ⟨i, h⟩
      let old := sequentialState F G order i
      Function.update old v (F (((G.neighborFinset v).filter
        (fun u => (order.symm u).val < i)).val.map old))
    else sequentialState F G order i

noncomputable def sequentialLabeling {L : Type} {n : ℕ} (F : Multiset L → L)
    (G : SimpleGraph (Fin n)) (order : Equiv.Perm (Fin n)) : Fin n → L :=
  sequentialState F G order n

def IsExtensionRule {L : Type} (P : LabelProblem L) (F : Multiset L → L) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (order : Equiv.Perm (Fin n)),
    P G (sequentialLabeling F G order)

def IsLocalVerifier {L : Type} (P : LabelProblem L) (C : Set (L × Multiset L)) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (l : Fin n → L),
    P G l ↔ ∀ v, (l v, neighborLabels G l v) ∈ C

def AllLabelsRealizable {L : Type} (F : Multiset L → L) : Prop :=
  ∀ α, ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (order : Equiv.Perm (Fin n)) (v : Fin n),
    sequentialLabeling F G order v = α

/-- Definition 4.6, with multiplicity and with no bound on the multiset. -/
def Spawns {L : Type} (F : Multiset L → L) (α β : L) : Prop :=
  ∃ S : Multiset L, α ∈ S ∧ F S = β

end GreedyColoringLCA969.LowerBound.Supplement


