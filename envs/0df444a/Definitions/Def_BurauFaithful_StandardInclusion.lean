-- Prove2me | Definitions.Def_BurauFaithful_StandardInclusion
-- name    : BurauFaithful_StandardInclusion
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T20:09:52.235123+00:00
-- url     : https://prove2.me/theorems/54492467-701a-48cc-9cc3-6d2022e93afa
-- title:
--   The standard inclusion $B_n \hookrightarrow B_{n+1}$
-- statement:
--   The standard inclusion of braid groups.
--
--   The embedding of the $n$-punctured disk $D_n$ into the $(n+1)$-punctured disk $D_{n+1}$ induces a group homomorphism
--
--   $$\iota : B_n \longrightarrow B_{n+1}, \qquad \sigma_{i+1} \longmapsto \sigma_{i+1},$$
--
--   which in pictures adds one extra strand on the right that is not braided with the others. On Artin's presentations this is the map determined by sending the generator with index $i \in \mathrm{Fin}(n-1)$ to the generator with the same index in $\mathrm{Fin}(n)$; the defining relations of $B_n$ map to defining relations of $B_{n+1}$, which is what makes the assignment well defined.
--
--   This map is the one used in the source paper to transfer a four-strand braid into the five-strand braid group.
-- source:
--   Vasudha Bharathram, Joan S. Birman, Tara E. Brendle, *The Burau representation is faithful for n = 4*, arXiv:2607.05283v1 (6 July 2026), https://arxiv.org/abs/2607.05283, Observation 2.1 (the inclusion $f : B_n \to B_{n+1}$ from the standard embedding of $D_n$ into $D_{n+1}$)

import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

/-!
# The standard inclusion of braid groups `B_n → B_{n+1}`

The embedding of the `n`-punctured disk into the `(n+1)`-punctured disk induces the
homomorphism `B_n → B_{n+1}` that sends the Artin generator `σ_{i+1}` of `B_n` to the Artin
generator of the same index in `B_{n+1}`; in pictures, it adds one extra, unbraided strand on
the right.
-/

namespace BurauFaithful

open BraidsLinksMCG

/-- An Artin generator index for `n` strands, read as an index for `n + 1` strands. -/
def strandIdx {n : ℕ} (i : Fin (n - 1)) : Fin (n + 1 - 1) := ⟨i, by have := i.isLt; omega⟩

lemma sigma_relations_map (n : ℕ) :
    ∀ r ∈ braidRels n,
      (FreeGroup.lift fun i : Fin (n - 1) =>
        PresentedGroup.of (rels := braidRels (n + 1)) (strandIdx i)) r = 1 := by
  have key : ∀ w : FreeGroup (Fin (n - 1)),
      (FreeGroup.lift fun i : Fin (n - 1) =>
          PresentedGroup.of (rels := braidRels (n + 1)) (strandIdx i)) w =
        PresentedGroup.mk (braidRels (n + 1)) (FreeGroup.map strandIdx w) := by
    intro w
    induction w using FreeGroup.induction_on with
    | C1 => simp
    | of x => simp [PresentedGroup.of]
    | inv_of x _ => simp [PresentedGroup.of]
    | mul x y hx hy => simp [hx, hy]
  intro r hr
  simp only [braidRels, Set.mem_union] at hr
  rcases hr with ⟨i, j, h, rfl⟩ | ⟨i, j, h, rfl⟩ <;> rw [key] <;>
      refine PresentedGroup.one_of_mem ?_
  · exact Or.inl ⟨strandIdx i, strandIdx j, by simpa [strandIdx] using h, by simp⟩
  · exact Or.inr ⟨strandIdx i, strandIdx j, by simpa [strandIdx] using h, by simp⟩

/-- The standard inclusion `B_n → B_{n+1}`, sending `σ_{i+1}` to `σ_{i+1}`. -/
def standardInclusion (n : ℕ) : ArtinBraidGroup n →* ArtinBraidGroup (n + 1) :=
  PresentedGroup.toGroup (sigma_relations_map n)

end BurauFaithful


