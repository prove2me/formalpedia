-- Prove2me | Definitions.Def_ReadOnceParityBP_LowerBound_CanonicalMatching
-- name    : ReadOnceParityBP_LowerBound_CanonicalMatching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:26:09.154257+00:00
-- url     : https://prove2.me/theorems/2d14e49b-e709-4590-82f3-541e995cca79
-- title:
--   Canonical cyclic matching, polynomial, validity, and leader
-- statement:
--   Place positions 0,…,n−1 clockwise. For a half-subset B, scan the surviving positions from the smallest representative, take the first j∈B whose next surviving cyclic neighbour k lies outside B, record j↦k, delete both, and repeat. greedyPairs carries out this finite deletion process with n steps of fuel; matchPairs uses the whole cycle, and σ_B reads the resulting list. The default σ_B(j)=j is only an extension off the legitimate matched domain. Bijectivity is a theorem obligation.
--
--   With x-variables in the first block and y-variables in the second block, over any field F define
--
--   $$f_B=\prod_{j\in B}(x_j+x_{\sigma_B(j)}),\qquad f=\sum_{|B|=n/2}\Bigl(\prod_{j\in B}y_j\Bigr)f_B.$$
--
--   fBool is its Boolean evaluation over F₂. B is x-valid when every matched pair has distinct x-bits, and y-eligible when all y-bits indexed by B are one. validEligibleCount is the exact natural cardinality of the half-subsets satisfying both predicates. The leader is the least j∈B with σ_B(j)<j, or zero if there is none; cutPos and cwDist are the corresponding cyclic position and clockwise distance. These are computed from B, not selected to satisfy geometry.
--
--   The finite empty-cycle extension uses Fin 0, with polynomial and count one and leader zero. Odd n and non-half-subsets have total helper values but are not used as source instances. Multilinearity, bijectivity, geometry, and polynomial-time computation are not fields in these definitions.
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Definition 2.3 p.4; validity and eligibility p.6; leader p.7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_AlgebraicProgram

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

open MvPolynomial

/-- The greedy deletion process of Definition 2.3 on a cyclically ordered list `l` of
distinct elements of `ℤ_n`, for a set `B` (the elements of `B` play the role of the
elements to be matched). Scanning `l` from its first element, pick the first `j ∈ B` whose
next element on the cycle (the following list entry, the first entry after the last one) is
some `k ∉ B`; record the pair `(j, k)`, erase `j` and `k`, and continue in the same manner on
the remaining cycle. `fuel` bounds the number of steps (`n` steps always suffice since each
step erases two elements). -/
def greedyPairs {n : ℕ} (B : Finset (Fin n)) : ℕ → List (Fin n) → List (Fin n × Fin n)
  | 0, _ => []
  | fuel + 1, l =>
    match (l.zip (l.rotate 1)).find? (fun q => decide (q.1 ∈ B ∧ q.2 ∉ B)) with
    | none => []
    | some q => q :: greedyPairs B fuel (l.filter fun v => v != q.1 && v != q.2)

/-- Volk, Definition 2.3 (p. 4): the pairs `(j, σ_B(j))` produced by the canonical clockwise
deletion process on the whole cycle `0, 1, …, n-1` of `ℤ_n`. -/
def matchPairs {n : ℕ} (B : Finset (Fin n)) : List (Fin n × Fin n) :=
  greedyPairs B n (List.finRange n)

/-- Volk, Definition 2.3 (p. 4): the canonical map `σ_B : B → ℤ_n ∖ B`, read off from
`matchPairs B`. (For `|B| = n/2` every `j ∈ B` is matched by the process; the fallback value
`j` is only used outside `B`.) -/
def sigma {n : ℕ} (B : Finset (Fin n)) (j : Fin n) : Fin n :=
  ((matchPairs B).lookup j).getD j

/-- `f_B(x) = ∏_{j ∈ B} (x_j + x_{σ_B(j)})` (Definition 2.3). Variables are indexed by
`Fin n ⊕ Fin n`: `Sum.inl j` is `x_j` and `Sum.inr j` is `y_j`. -/
noncomputable def fB (F : Type) [Field F] {n : ℕ} (B : Finset (Fin n)) :
    MvPolynomial (Fin n ⊕ Fin n) F :=
  ∏ j ∈ B, (X (Sum.inl j) + X (Sum.inl (sigma B j)))

/-- Volk, Definition 2.3 (p. 4), the Raz–Shpilka–Yehudayoff polynomial in the `2n` variables
`x_0, …, x_{n-1}, y_0, …, y_{n-1}` over a field `F`:
`f(x, y) = ∑_{B ⊆ ℤ_n, |B| = n/2} (∏_{j ∈ B} y_j) · f_B(x)`. -/
noncomputable def rsyPoly (F : Type) [Field F] (n : ℕ) : MvPolynomial (Fin n ⊕ Fin n) F :=
  ∑ B ∈ (Finset.univ : Finset (Fin n)).powersetCard (n / 2),
    (∏ j ∈ B, X (Sum.inr j)) * fB F B

/-- The Boolean function `f_bool : {0,1}^{2n} → {0,1}` represented by `f` over `𝔽₂`
(§2.1, p. 5); an input assigns a bit to each `x_j` (`Sum.inl j`) and `y_j` (`Sum.inr j`). -/
noncomputable def fBool (n : ℕ) : (Fin n ⊕ Fin n → Bool) → Bool :=
  boolOf (rsyPoly (ZMod 2) n)

/-- §3, p. 6: `B` is `x`-valid if `x_j ≠ x_{σ_B(j)}` for every `j ∈ B`. -/
def XValid {n : ℕ} (x : Fin n → Bool) (B : Finset (Fin n)) : Prop :=
  ∀ j ∈ B, x j ≠ x (sigma B j)

/-- §3, p. 6: `B` is `y`-eligible if `y_j = 1` for every `j ∈ B`. -/
def YEligible {n : ℕ} (y : Fin n → Bool) (B : Finset (Fin n)) : Prop :=
  ∀ j ∈ B, y j = true

open Classical in
/-- Theorem 3.2 (p. 9): the number of `x`-valid and `y`-eligible sets `B ⊆ ℤ_n` with
`|B| = n/2`. -/
noncomputable def validEligibleCount (n : ℕ) (x y : Fin n → Bool) : ℕ :=
  (((Finset.univ : Finset (Fin n)).powersetCard (n / 2)).filter
    fun B => XValid x B ∧ YEligible y B).card

open Classical in
/-- §3, p. 7: the leader `ℓ` of the matching `σ_B`: the smallest `j ∈ ℤ_n` (here: `j ∈ B`,
the domain of `σ_B`) with `σ_B(j) < j` as integers, and `0` if there is no such element. -/
noncomputable def leader {n : ℕ} (B : Finset (Fin n)) : ℕ :=
  if h : (B.filter fun j => sigma B j < j).Nonempty then
    ((B.filter fun j => sigma B j < j).min' h).val
  else 0

/-- Position of `v ∈ ℤ_n` in the interval `ℓ, ℓ+1, …, n-1, 0, 1, …, ℓ-1` obtained by cutting
the cycle at `ℓ` (Lemma 3.1): `(v - ℓ) mod n`. -/
def cutPos (n ℓ : ℕ) (v : Fin n) : ℕ := (v.val + n - ℓ) % n

/-- Clockwise distance from `j` to `v` on the cycle `ℤ_n`: `(v - j) mod n`. -/
def cwDist {n : ℕ} (j v : Fin n) : ℕ := (v.val + n - j.val) % n

end ReadOnceParityBP.LowerBound


