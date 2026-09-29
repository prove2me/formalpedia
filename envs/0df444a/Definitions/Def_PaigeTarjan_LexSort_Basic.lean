-- Prove2me | Definitions.Def_PaigeTarjan_LexSort_Basic
-- name    : PaigeTarjan_LexSort_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:40:24.797477+00:00
-- url     : https://prove2.me/theorems/1636fe00-edcc-4d5d-8761-e55384af3833
-- title:
--   Strings with end marker, labeled blocks $B_\alpha$, distinguishing prefixes $x'_i$ and $m'$
-- statement:
--   This file fixes the objects of the lexicographic sorting problem of Paige and Tarjan (§2).
--
--   Let $\Sigma = \{1, \dots, k\}$ and let $0$ be an end marker, so strings are finite sequences over $\Sigma \cup \{0\} = \{0, 1, \dots, k\}$. The input is a multiset $U = \{x_1, \dots, x_n\}$ of strings in $\Sigma^*0$: each $x_i$ is a string over $\Sigma$ followed by a single $0$. Repeated strings are allowed and are told apart by their index.
--
--   1. A string $\alpha$ is a **prefix** of $y$ if $y = \alpha z$ for some string $z$; every string is a prefix of itself.
--   2. The **labeled block** $B_\alpha$ is the multiset of strings of $U$ having $\alpha$ as a prefix; $\alpha$ is its **associated prefix**, and $B_\lambda = U$ for the empty string $\lambda$.
--   3. The **distinguishing prefix** $x'_i$ of $x_i$ in $U$ is (i) the shortest prefix of $x_i$ that is not a prefix of any other string of $U$, if $x_i$ occurs uniquely in $U$; or (ii) $x_i$ itself, if $x_i$ has multiple occurrences in $U$.
--   4. The total length of the distinguishing prefixes is
--   $$m' = \sum_{i=1}^n |x'_i|.$$
--   5. Block $B_\alpha$ is **finished** iff $\alpha = x'_i$ for some $i$; the set of finished labels is $F = \{x'_1, \dots, x'_n\}$.
--
--   These are the objects on which the refinement algorithm of §2 operates: finding all finished blocks is the same as finding all distinguishing prefixes.
--
--   **Formalization Note.** Strings are `List (Fin (k + 1))` with `0` the end marker, and $U$ is a family `x : Fin n → List (Fin (k + 1))`. `EndMarked x` is the standing hypothesis $U \subseteq \Sigma^*0$. A block is referred to by its label and `blk x α` is its set of indices, so two labels with the same member strings remain different blocks. In case (i) the shortest length is found by `Nat.find` over the predicate "$\ell = |x_i|$ or the length-$\ell$ prefix of $x_i$ is a prefix of no other string"; the first disjunct only makes the definition total and never changes the value when a qualifying prefix exists, which is always the case under `EndMarked`. The shortest prefix can be the empty string $\lambda$ (when $n = 1$), exactly as in the literal definition.
-- source:
--   Paige, Tarjan, Three Partition Refinement Algorithms, SIAM J. Comput. 16 (1987), pp. 974–975, §2 (definitions of prefix, Σ*0, distinguishing prefix x′_i, m′; labeled block B_α, associated prefix, finished block)

import Mathlib

namespace PaigeTarjan.LexSort

/-- The input of the lexicographic sorting problem (Paige–Tarjan 1987, §2, p. 974).
The alphabet with end marker is `Σ ∪ {0} = {0, 1, …, k}`, encoded as `Fin (k + 1)`; the symbol
`0` is the end marker. The multiset `U = {x₁, …, xₙ}` is an indexed family `x : Fin n → List (Fin (k + 1))`
(repeated strings are allowed and are told apart by their index).

`EndMarked x` says `U ⊆ Σ*0`: every string is a string over `Σ = {1, …, k}` followed by a
single `0`. -/
def EndMarked {k n : ℕ} (x : Fin n → List (Fin (k + 1))) : Prop :=
  ∀ i, ∃ w : List (Fin (k + 1)), x i = w ++ [0] ∧ (0 : Fin (k + 1)) ∉ w

/-- The labeled block `B_α`: the (indices of the) strings of `U` that have `α` as a prefix
(p. 975). Two different labels may have the same block; a block is always referred to by its
label. -/
def blk {k n : ℕ} (x : Fin n → List (Fin (k + 1))) (α : List (Fin (k + 1))) : Finset (Fin n) :=
  Finset.univ.filter (fun i => α <+: x i)

open Classical in
/-- The length of the distinguishing prefix of `x i` in case (i) of p. 974: the least `ℓ` such
that the length-`ℓ` prefix of `x i` is a prefix of no other string `x j`, `j ≠ i`. The disjunct
`ℓ = (x i).length` only makes the search total; whenever some prefix of `x i` (including `x i`
itself) is a prefix of no other string, the least such length is at most `(x i).length`, so the
disjunct never changes the value. -/
noncomputable def dpLength {k n : ℕ} (x : Fin n → List (Fin (k + 1))) (i : Fin n) : ℕ :=
  Nat.find (p := fun ℓ => ℓ = (x i).length ∨ ∀ j, j ≠ i → ¬ ((x i).take ℓ <+: x j))
    ⟨(x i).length, Or.inl rfl⟩

open Classical in
/-- The distinguishing prefix `x′ᵢ` of `xᵢ` in `U` (p. 974):
(i) if `xᵢ` occurs uniquely in `U`, the shortest prefix of `xᵢ` that is not a prefix of any
other string in `U`; (ii) `xᵢ` itself if `xᵢ` has multiple occurrences in `U`. -/
noncomputable def dp {k n : ℕ} (x : Fin n → List (Fin (k + 1))) (i : Fin n) :
    List (Fin (k + 1)) :=
  if ∃ j, j ≠ i ∧ x j = x i then x i else (x i).take (dpLength x i)

/-- `m′ = ∑ᵢ |x′ᵢ|`, the total length of the distinguishing prefixes (p. 974). -/
noncomputable def mPrime {k n : ℕ} (x : Fin n → List (Fin (k + 1))) : ℕ :=
  ∑ i, (dp x i).length

/-- Block `B_α` is finished iff `α = x′` for some string `x ∈ U` (p. 975). -/
def IsFinished {k n : ℕ} (x : Fin n → List (Fin (k + 1))) (α : List (Fin (k + 1))) : Prop :=
  ∃ i, α = dp x i

/-- The set `F` of (labels of) finished blocks: the distinguishing prefixes (p. 975). -/
noncomputable def finishedLabels {k n : ℕ} (x : Fin n → List (Fin (k + 1))) :
    Finset (List (Fin (k + 1))) :=
  Finset.univ.image (dp x)

end PaigeTarjan.LexSort


