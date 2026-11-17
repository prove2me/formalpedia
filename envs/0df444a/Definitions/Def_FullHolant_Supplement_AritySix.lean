-- Prove2me | Definitions.Def_FullHolant_Supplement_AritySix
-- name    : FullHolant_Supplement_AritySix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:58:50.13593+00:00
-- url     : https://prove2.me/theorems/0fddfb44-3e21-4d90-96a4-4d04535fc222
-- title:
--   The support $S_\star$, partition cosets, and bit-flip/variable-permutation images
-- statement:
--   1. $S_\star=\{000000,000011,001100,110011,111100,111111\}\subseteq\mathbb F_2^6$ (F.25).
--   2. A set $S\subseteq\mathbb F_2^n$ is a **partition coset** when $S=a+L_\pi$, $L_\pi=\mathrm{span}_{\mathbb F_2}\{\mathbf 1_C:C\in\pi\}$, for a partition $\pi$ of the variables into even blocks and an offset $a$: the strings obtained from $a$ by toggling each block as one unit. On six variables the possible types are $(6)$, $(4+2)$ and $(2+2+2)$.
--   3. $S$ is a **bit-flip/variable-permutation image** of $S_\star$ when $S=\{s\circ\tau\oplus b: s\in S_\star\}$ for a permutation $\tau$ of the six variables and a flip $b\in\mathbb F_2^6$.
--
--   These are the support types that survive the arity-six classification of Theorem F.A.2.
--
--   **Formalization Note** The first character of a string is variable $1$ (`Fin 6` index $0$).
-- source:
--   Liu–Meng–Wang, A Full Complexity Dichotomy for Complex-Valued Boolean Holant Problems, arXiv:2610.00081 (held version, sha256 d67958c6…), Eq. (F.25), p.F-43 (PDF p.61); §F.6.5.1, p.F-40 (PDF p.58); §F.2.5, p.F-7 (PDF p.25)

import Mathlib

set_option autoImplicit false

namespace FullHolant.Supplement

/-- The six strings of `S⋆ = {000000, 000011, 001100, 110011, 111100, 111111}` (F.25), the first
character being variable `1` (`Fin 6` index `0`). Liu–Meng–Wang, *A Full Complexity Dichotomy for
Complex-Valued Boolean Holant Problems*, arXiv:2610.00081 (held version, sha256 d67958c6…),
Eq. (F.25), p.F-43 (PDF p.61). -/
def sStar : Set (Fin 6 → Bool) :=
  {![false, false, false, false, false, false], ![false, false, false, false, true, true],
    ![false, false, true, true, false, false], ![true, true, false, false, true, true],
    ![true, true, true, true, false, false], ![true, true, true, true, true, true]}

/-- `S` is a **partition coset** `a + L_π`, `L_π = span_{𝔽₂}{1_C : C ∈ π}`, for a partition `π` of
the variables into even blocks: the strings obtained from `a` by toggling each block as one unit.
Liu–Meng–Wang, arXiv:2610.00081, §F.6.5.1, p.F-40 (PDF p.58): "Its cosets are precisely the sets
obtained by toggling each block as one unit."

**Formalization Note.** On six variables the even-block partitions are exactly the types `(6)`,
`(4 + 2)` and `(2 + 2 + 2)`. -/
def IsPartitionCoset {n : ℕ} (S : Set (Fin n → Bool)) : Prop :=
  ∃ (π : Finpartition (Finset.univ : Finset (Fin n))) (a : Fin n → Bool),
    (∀ C ∈ π.parts, Even C.card) ∧
      S = {x | ∀ C ∈ π.parts, (∀ k ∈ C, x k = a k) ∨ (∀ k ∈ C, x k = !a k)}

/-- `S` is a **bit-flip/variable-permutation image** of `S⋆`: `S = {x : x ∘ τ ⊕ b ∈ S⋆}`-type
images, i.e. `{k ↦ s(τ k) ⊕ b_k : s ∈ S⋆}` for a permutation `τ` and a flip `b`. Liu–Meng–Wang,
arXiv:2610.00081, §F.2.5, p.F-7 (PDF p.25): "Bit-flip/variable-permutation orbits use these flips
and permutations of argument positions." -/
def IsSStarImage (S : Set (Fin 6 → Bool)) : Prop :=
  ∃ (τ : Equiv.Perm (Fin 6)) (b : Fin 6 → Bool),
    S = {x | ∃ s ∈ sStar, x = fun k => xor (s (τ k)) (b k)}

end FullHolant.Supplement


