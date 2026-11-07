-- Prove2me | Definitions.Def_MonDepMW_oneType
-- name    : MonDepMW_oneType
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:41.776528+00:00
-- url     : https://prove2.me/theorems/9ecf2a38-e622-4e87-a438-bdaae776fa9e
-- title:
--   1-types $\mathcal T_1(G,S)$ and the shatter function $\pi_G$
-- statement:
--   Two vertices $a,b$ of $G$ have the same **1-type over $S$** if either $a=b\in S$, or $a,b\notin S$ and $N_G(a)\cap S=N_G(b)\cap S$. The corresponding partition of $V(G)$ is $\mathcal T_1(G,S)$. The **shatter function** $\pi_G$ maps $k$ to the maximum of $|\mathcal T_1(G,A)|$ among vertex subsets $A$ of cardinality $k$.
--
--   The almost linear growth of $\mathcal T_1$ on monadically dependent classes (Theorem 3.3) is the combinatorial input of the whole proof.
--
--   **Formalization Note** $\pi_G(k)$ is $0$ when no subset has cardinality $k$, i.e. for $k>n$.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, pp.12–13

import Mathlib
import Definitions.Def_MonDepMW_partsHit

set_option autoImplicit false

namespace MonDepMW

/-- **The partition `𝒯₁(G, S)` into 1-types.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.12: "two vertices a, b ∈ V (G) have the same 1-type over S if
either a = b ∈ S, or a, b ∉ S and N_G(a) ∩ S = N_G(b) ∩ S". -/
def oneType {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Setoid (Fin n) where
  r a b := (a = b ∧ a ∈ S) ∨ (a ∉ S ∧ b ∉ S ∧ ∀ s ∈ S, (G.Adj a s ↔ G.Adj b s))
  iseqv :=
    { refl := fun a => by
        by_cases h : a ∈ S
        · exact Or.inl ⟨rfl, h⟩
        · exact Or.inr ⟨h, h, fun _ _ => Iff.rfl⟩
      symm := by
        rintro a b (⟨rfl, h⟩ | ⟨ha, hb, h⟩)
        · exact Or.inl ⟨rfl, h⟩
        · exact Or.inr ⟨hb, ha, fun s hs => (h s hs).symm⟩
      trans := by
        rintro a b c (⟨rfl, h⟩ | ⟨ha, hb, h⟩) (⟨rfl, h'⟩ | ⟨hb', hc, h'⟩)
        · exact Or.inl ⟨rfl, h⟩
        · exact absurd h hb'
        · exact absurd h' hb
        · exact Or.inr ⟨ha, hc, fun s hs => (h s hs).trans (h' s hs)⟩ }

/-- **The shatter function `π_G`.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.13: "the function π_G : N → N that maps every k ∈ N to the maximum of
|𝒯1(G, A)| among vertex subsets A of cardinality k."

**Formalization Note.** The value is `0` if no subset has cardinality `k`, i.e. for `k > n`. Theorem 3.5 evaluates it
at the exact width, which is at most `n`. -/
noncomputable def shatterFn {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : ℕ :=
  (Finset.powersetCard k (Finset.univ : Finset (Fin n))).sup fun A => numParts (oneType G A)

end MonDepMW


