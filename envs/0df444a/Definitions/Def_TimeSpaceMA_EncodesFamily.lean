-- Prove2me | Definitions.Def_TimeSpaceMA_EncodesFamily
-- name    : TimeSpaceMA_EncodesFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:56:08.36085+00:00
-- url     : https://prove2.me/theorems/565eb92d-cf91-4bba-847f-e59d1d66c2ea
-- title:
--   Output layout for a family of sets and its key map
-- statement:
--   For a family $F_1,\dots,F_N$ of subsets of $[n]$, $\mathrm{rep}(i)$ is the least $i'$ with $F_{i'}=F_i$, and the *distinct size* is the total size of the distinct sets.
--
--   A memory **encodes** the family if $M[0]=N$, $M[1+i]=\mathrm{rep}(i)$, and for each $i$ with $\mathrm{rep}(i)=i$ the pointer $p=M[1+N+i]$ leads to $M[p]=|F_i|$ followed by the elements of $F_i$. This is the output of the computations in Lemmas A.3 and 3.10; the paper gives no layout.
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), p.12; Lemma A.3(a), p.33

import Mathlib

namespace TimeSpaceMA

/-- `rep(i)`: the least index `i′` with `F i′ = F i`; p.12. -/
noncomputable def familyRep {N : ℕ} {α : Type*} (F : Fin N → α) (i : Fin N) : ℕ :=
  sInf {i' : ℕ | ∃ h : i' < N, F ⟨i', h⟩ = F i}

/-- The total size of the distinct sets of a family (an empty set contributes `0`). -/
def distinctSize {N n : ℕ} (F : Fin N → Finset (Fin n)) : ℕ :=
  ∑ T ∈ Finset.univ.image F, T.card

/-- The output layout for "the list of the distinct sets and the map to them" in Lemmas A.3(a), p.33,
and 3.10, p.12: `M[0] = N`; `M[1+i] = rep(i)`; and at each `i` with `rep(i) = i`, the pointer
`p = M[1+N+i]` leads to `M[p] = |F i|` followed by the elements of `F i` in cells `p+1, …`.

**Formalization Note** The page gives no layout. This one determines the family and has size `N` plus
the total size of the distinct sets. -/
def EncodesFamily {N n : ℕ} (mem : ℕ → ℕ) (F : Fin N → Finset (Fin n)) : Prop :=
  mem 0 = N ∧ ∀ i : Fin N,
    mem (1 + i.val) = familyRep F i ∧
    (familyRep F i = i.val →
      mem (mem (1 + N + i.val)) = (F i).card ∧
      ∀ v : Fin n, v ∈ F i ↔
        ∃ e < (F i).card, mem (mem (1 + N + i.val) + 1 + e) = v.val)

end TimeSpaceMA


