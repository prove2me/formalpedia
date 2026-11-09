-- Prove2me | Definitions.Def_PhyloCSP_IsTreeRel
-- name    : PhyloCSP_IsTreeRel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:22:09.17584+00:00
-- url     : https://prove2.me/theorems/80ec2bad-13c5-4a15-980b-08b0e8fb2281
-- title:
--   Binary tree structures: the rooted-triplet axioms
-- statement:
--   A ternary relation $C$ on a set $X$, written $C(x;y,z)$ or $x\mid yz$ ("$x$ splits off first, then $y$ and $z$ split"), is a **binary tree structure** when it satisfies the four axioms of Section 7.1:
--
--   1. **Symmetry.** For distinct $x,y,z$: $C(x;y,z)\iff C(x;z,y)$.
--   2. **Unique outgroup.** For distinct $x,y,z$, exactly one of $C(x;y,z)$, $C(y;x,z)$, $C(z;x,y)$ holds.
--   3. **Compatibility.** For pairwise distinct $x,y,z,w$: $C(x;y,z)$ implies $C(x;w,z)$ or $C(w;y,z)$.
--   4. **Distinctness.** $C(x;y,z)$ is false whenever two of its arguments are equal.
--
--   By the paper, these axioms characterize the rooted-triplet relations of rooted binary trees with leaf set $X$, on finite or infinite nonempty domains.
--
--   This predicate is the basis of every object in the mission: finite trees (patterns), the Fraïssé limit, and the random output relations of tree transformations.
--
--   **Formalization Note** The relation is Boolean-valued, $C : X\to X\to X\to\mathrm{Bool}$, so that relations form the product space used for random relations. The predicate is stated on any type, the empty one included; the pull-back of a tree relation along an injection is again a tree relation.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Definition 7.1 and axioms (1)–(4), Section 7.1, p.18 (PDF p.20)

import Mathlib

set_option autoImplicit false

namespace PhyloCSP

/-- **Binary tree structures (rooted-triplet relations).**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Definition 7.1 and the axioms (1)–(4) of Section 7.1,
p.18 (PDF p.20). `C x y z = true` is the rooted triplet relation `C(x; y, z)`, i.e. `x | yz`:
`x` splits off first and `y, z` split afterwards.

1. Symmetry: for distinct `x, y, z`, `C(x; y, z) ↔ C(x; z, y)`.
2. Unique outgroup: for distinct `x, y, z`, exactly one of `C(x; y, z)`, `C(y; x, z)`,
   `C(z; x, y)` holds.
3. Compatibility: for pairwise distinct `x, y, z, w`, `C(x; y, z)` implies `C(x; w, z)` or
   `C(w; y, z)`.
4. Distinctness: `C(x; y, z)` is false whenever two arguments are equal.

The paper (p.18): "Together, these axioms characterize binary tree structures on finite or
infinite nonempty domains."

**Formalization Note.** The relation is `Bool`-valued, so that a relation is a point of the
product space `X → X → X → Bool`. The predicate is stated on any type, including the empty one
(where it holds trivially); every statement of the mission says where nonemptiness matters. -/
def IsTreeRel {X : Type} (C : X → X → X → Bool) : Prop :=
  (∀ x y z : X, (x ≠ y ∧ x ≠ z ∧ y ≠ z) → (C x y z = true ↔ C x z y = true)) ∧
  (∀ x y z : X, (x ≠ y ∧ x ≠ z ∧ y ≠ z) →
      (C x y z = true ∨ C y x z = true ∨ C z x y = true) ∧
      ¬ (C x y z = true ∧ C y x z = true) ∧ ¬ (C x y z = true ∧ C z x y = true) ∧
      ¬ (C y x z = true ∧ C z x y = true)) ∧
  (∀ x y z w : X, (x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w) →
      C x y z = true → C x w z = true ∨ C w y z = true) ∧
  (∀ x y z : X, (x = y ∨ x = z ∨ y = z) → C x y z = false)

instance {X : Type} [Fintype X] [DecidableEq X] (C : X → X → X → Bool) :
    Decidable (IsTreeRel C) := by
  unfold IsTreeRel
  exact @instDecidableAnd _ _ inferInstance
    (@instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance inferInstance))

/-- Pulling a tree relation back along an injection gives a tree relation (the axioms only
mention distinctness, which an injection preserves). -/
theorem IsTreeRel.comap {X Y : Type} {C : X → X → X → Bool} (h : IsTreeRel C) (f : Y ↪ X) :
    IsTreeRel (fun a b c => C (f a) (f b) (f c)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun x y z ⟨hxy, hxz, hyz⟩ => h1 _ _ _ ⟨f.injective.ne hxy, f.injective.ne hxz,
      f.injective.ne hyz⟩,
    fun x y z ⟨hxy, hxz, hyz⟩ => h2 _ _ _ ⟨f.injective.ne hxy, f.injective.ne hxz,
      f.injective.ne hyz⟩,
    fun x y z w ⟨hxy, hxz, hxw, hyz, hyw, hzw⟩ => h3 _ _ _ _ ⟨f.injective.ne hxy,
      f.injective.ne hxz, f.injective.ne hxw, f.injective.ne hyz, f.injective.ne hyw,
      f.injective.ne hzw⟩,
    fun x y z h => h4 _ _ _ ?_⟩
  rcases h with h | h | h <;> simp [h]

end PhyloCSP


