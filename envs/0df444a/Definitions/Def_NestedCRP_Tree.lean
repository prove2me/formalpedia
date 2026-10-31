-- Prove2me | Definitions.Def_NestedCRP_Tree
-- name    : NestedCRP_Tree
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:26:42.188821+00:00
-- url     : https://prove2.me/theorems/043f5bf0-6606-4c46-9153-c4a67867282a
-- title:
--   Trees as nested partitions of the documents
-- statement:
--   A tree on $D$ tourists is a sequence of partitions $(\mathcal P_\ell)_{\ell\ge0}$ of $\{0,\dots,D-1\}$, where $\mathcal P_\ell$ groups the tourists by their node at level $\ell$, such that
--
--   1. all tourists are together at the root, $\mathcal P_0$ being the trivial partition;
--   2. partitions get finer with depth;
--   3. at some finite level all tourists are separated.
--
--   The module also gives the relation "$e$ and $d$ share a node at level $\ell$", the first level of full separation, the block of $d$ at level $\ell$, the relation "same restriction to the tourists other than $d$", relabelling of tourists by a permutation, and the countability of the set of trees.
--
--   This implements the paper's remark "A tree can be viewed as a nested sequence of partitions". It is the latent tree of the model, with no bound on depth or branching.
--
--   **Formalization Note** Levels are 0-based. The tree is the nested partition rather than labelled tables, since conditioning on labelled paths of the other documents would reveal the position of the document left out. Clause 3 costs nothing: two tourists stay together for $L$ levels with probability $(1+\gamma)^{-L}$, so it holds almost surely, and `NestedCRP.ncrp_hasSum_one` proves the law has total mass one on these trees.
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, §3, p.7:9 and p.7:10; §5.2, p.7:17

import Mathlib

namespace NestedCRP

/-- A tree on `D` tourists, as a nested sequence of partitions ("A tree can be viewed as a nested
sequence of partitions", Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §3, p.7:9):
`part ℓ` is the partition of the tourists by their node at level `ℓ`. All tourists sit at the root,
partitions get finer with depth, and at some finite level all tourists are separated.

**Formalization Note** Levels are 0-based: `part ℓ` is the paper's level `ℓ + 1`. The tree is the
nested partition rather than labelled tables, because conditioning on labelled paths of the others
would reveal the position of the document left out. The separation clause carries no loss: under
the nCRP two tourists stay together for `L` levels with probability `(1 + γ)^{-L}`, so it holds
almost surely, and `ncrp_hasSum_one` proves the law has total mass 1 on these trees. -/
@[ext]
structure Tree (D : ℕ) where
  part : ℕ → Setoid (Fin D)
  root : part 0 = ⊤
  antitone : Antitone part
  separated : ∃ L, part L = ⊥

/-- `Tree.Rel T ℓ e d`: tourists `e` and `d` sit at the same node of level `ℓ`. -/
def Tree.Rel {D : ℕ} (T : Tree D) (ℓ : ℕ) (e d : Fin D) : Prop :=
  (T.part ℓ).r e d

open Classical in
/-- The first level at which all tourists are separated. -/
noncomputable def Tree.sepLevel {D : ℕ} (T : Tree D) : ℕ :=
  Nat.find T.separated

open Classical in
/-- The block of tourist `d` at level `ℓ`, as a set of tourists. Together with `ℓ` this gives a
node an identity independent of the tree. -/
noncomputable def Tree.block {D : ℕ} (T : Tree D) (ℓ : ℕ) (d : Fin D) : Finset (Fin D) :=
  Finset.univ.filter fun e => T.Rel ℓ e d

/-- `T` and `T'` have the same restriction to the tourists other than `d`. This is the paper's
conditioning on `c_{-d}`, §5.2, p.7:17. -/
def Tree.AgreesOff {D : ℕ} (d : Fin D) (T T' : Tree D) : Prop :=
  ∀ (ℓ : ℕ) (e e' : Fin D), e ≠ d → e' ≠ d → (T.Rel ℓ e e' ↔ T'.Rel ℓ e e')

/-- Relabel the tourists of a tree by a permutation (the arrival order of §3, p.7:10). -/
def Tree.relabel {D : ℕ} (σ : Equiv.Perm (Fin D)) (T : Tree D) : Tree D where
  part ℓ := (T.part ℓ).comap σ
  root := top_unique fun a b _ => by
    change (T.part 0).r (σ a) (σ b)
    rw [T.root]
    trivial
  antitone := fun _ _ h _ _ hab => T.antitone h hab
  separated := by
    obtain ⟨L, hL⟩ := T.separated
    refine ⟨L, le_bot_iff.mp fun a b hab => ?_⟩
    have h : (T.part L).r (σ a) (σ b) := hab
    rw [hL] at h
    exact σ.injective h

instance {D : ℕ} : Countable (Tree D) := by
  classical
  have : Finite (Setoid (Fin D)) :=
    Finite.of_injective (fun s : Setoid (Fin D) => s.r) fun a b h => Setoid.ext (by
      intro x y
      exact iff_of_eq (congrFun (congrFun h x) y))
  let f : Tree D → List (Setoid (Fin D)) :=
    fun T => (List.range (Nat.find T.separated)).map T.part
  have hbot : ∀ (T : Tree D) (ℓ : ℕ), Nat.find T.separated ≤ ℓ → T.part ℓ = ⊥ := fun T ℓ h =>
    le_bot_iff.mp ((T.antitone h).trans (Nat.find_spec T.separated).le)
  refine Function.Injective.countable (f := f) ?_
  intro T T' h
  have hlen : Nat.find T.separated = Nat.find T'.separated := by
    simpa [f] using congrArg List.length h
  refine Tree.ext (funext fun ℓ => ?_)
  by_cases hℓ : ℓ < Nat.find T.separated
  · have := List.ext_getElem_iff.mp h
    have h2 := this.2 ℓ (by simpa [f] using hℓ) (by simpa [f, ← hlen] using hℓ)
    simpa [f] using h2
  · push Not at hℓ
    rw [hbot T ℓ hℓ, hbot T' ℓ (hlen ▸ hℓ)]

noncomputable instance {D : ℕ} : DecidableEq (Tree D) := Classical.decEq _

end NestedCRP


