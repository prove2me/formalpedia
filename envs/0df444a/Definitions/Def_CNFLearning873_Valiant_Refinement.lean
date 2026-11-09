-- Prove2me | Definitions.Def_CNFLearning873_Valiant_Refinement
-- name    : CNFLearning873_Valiant_Refinement
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T05:09:26.00198+00:00
-- url     : https://prove2.me/theorems/c9ef4425-8b1d-45bf-9b08-6bdb4c017a4d
-- title:
--   Finite refinement derivations with arbitrary maximal representatives
-- statement:
--   At a node with subclause $s'$ and assigned candidate family $A$, stop if its width is $k$, or if its width is below $k$ and $q_{s'}\le\lambda$. Otherwise choose any inclusion-maximal subfamily $R\subseteq A$ whose residual supports outside $s'$ are pairwise disjoint. Let $H$ be the union of those residual supports.
--
--   $$H=\bigcup_{c\in R}(\operatorname{vbl}(c)\setminus\operatorname{vbl}(s')).$$
--
--   Each assigned candidate goes to the child extending $s'$ by its first variable in $H$ outside the current support and the corresponding sign. Create only nonempty children. A finite inductive derivation records exactly these rules; all maximal choices are admitted. The internal representative list and the subclause/partition invariant predicate are defined separately. Their validity and bounds remain conclusions, never fields of a supposedly good tree.
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf, §4.3, pp.16–17 (PDF pp.16–17)

import Definitions.Def_CNFLearning873_Valiant_LargeSharing

namespace CNFLearning873.Valiant

def DisjointOutside {n : ℕ} (s : Clause n) (R : CNF n) : Prop :=
  ∀ c ∈ R, ∀ c' ∈ R, c ≠ c' →
    Disjoint (support c \ support s) (support c' \ support s)

/-- Maximal by inclusion, with no size bound or probability conclusion. -/
def MaximalRepresentatives {n : ℕ} (s : Clause n) (A R : CNF n) : Prop :=
  R ⊆ A ∧ DisjointOutside s R ∧
    ∀ R', R ⊆ R' → R' ⊆ A → DisjointOutside s R' → R' = R

noncomputable def hitVariables {n : ℕ} (s : Clause n) (R : CNF n) : Finset (Fin n) :=
  R.biUnion fun c => support c \ support s

/-- A fixed arbitrary variable ordering; first intersection variable, as on p.17. -/
noncomputable def firstHit {n : ℕ} (order : List (Fin n)) (s : Clause n) (R : CNF n)
    (c : Clause n) : Option (Fin n) :=
  order.find? fun v => decide (v ∈ (support c \ support s) ∩ hitVariables s R)

noncomputable def childFamily {n : ℕ} (order : List (Fin n)) (s : Clause n)
    (A R : CNF n) (vb : Fin n × Bool) : CNF n := by
  classical
  exact A.filter fun c => firstHit order s R c = some vb.1 ∧ c vb.1 = some vb.2

/-- Only nonempty child families create nodes. Boolean labels here are literal signs,
so they negate the source's forbidden-value labels and describe the same extension. -/
noncomputable def childSeeds {n : ℕ} (order : List (Fin n)) (s : Clause n)
    (A R : CNF n) : List (Clause n × CNF n) := by
  classical
  exact ((Finset.univ : Finset (Fin n × Bool)).toList.filter fun vb =>
    (childFamily order s A R vb).Nonempty).map fun vb =>
      (Function.update s vb.1 (some vb.2), childFamily order s A R vb)

inductive RefinementTree (n : ℕ) where
  | leaf (s : Clause n) (A : CNF n)
  | branch (s : Clause n) (A R : CNF n) (children : List (RefinementTree n))

/-- A finite derivation of precisely the top-down rules on pp.16--17. Every maximal
choice is admitted. No branching, representative, rarity, or depth bound is a field. -/
inductive Builds {n : ℕ} (F : CNF n) (h : (solutions F).Nonempty)
    (k : ℕ) (lam : ℝ) (order : List (Fin n)) :
    Clause n → CNF n → RefinementTree n → Prop where
  | leaf (s A) (stop : width s = k ∨ (width s < k ∧ q F h s ≤ lam)) :
      Builds F h k lam order s A (.leaf s A)
  | branch (s A R) (hw : width s < k) (hq : lam < q F h s)
      (hm : MaximalRepresentatives s A R)
      (children : Fin (childSeeds order s A R).length → RefinementTree n)
      (sub : ∀ i, Builds F h k lam order
        ((childSeeds order s A R).get i).1 ((childSeeds order s A R).get i).2 (children i)) :
      Builds F h k lam order s A (.branch s A R (List.ofFn children))

/-- Representatives at every internal node, including all descendants. -/
def internalFamilies {n : ℕ} : RefinementTree n → List (CNF n)
  | .leaf _ _ => []
  | .branch _ _ R children => R :: children.flatMap internalFamilies

/-- Local well-formedness of a constructed tree, with the source's partition and
subclause invariants. These are conclusions of the construction, not its inputs. -/
def TreeWellFormed {n : ℕ} : RefinementTree n → Prop
  | .leaf s A => ∀ c ∈ A, Subclause s c
  | .branch s A _ children =>
      (∀ c ∈ A, Subclause s c) ∧
      (∀ c, c ∈ A ↔ ∃! i : Fin children.length,
        match children.get i with
        | .leaf _ B => c ∈ B
        | .branch _ B _ _ => c ∈ B) ∧
      ∀ child ∈ children, TreeWellFormed child

end CNFLearning873.Valiant


