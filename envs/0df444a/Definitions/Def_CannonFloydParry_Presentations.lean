-- Prove2me | Definitions.Def_CannonFloydParry_Presentations
-- name    : CannonFloydParry_Presentations
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-17T20:39:13.432194+00:00
-- url     : https://prove2.me/theorems/7f07b7a6-3279-44d3-b7d2-20fea3fd009f
-- title:
--   Cannon–Floyd–Parry §3: the presented groups $F_1$ and $F_2$
-- statement:
--   The formal side of §3, on top of the published bundles for $F$ (§1) and for tree
--   diagrams and words (§2).
--
--   Throughout, $[x, y] = x y x^{-1} y^{-1}$ is the source's convention; relators are written out in
--   that form rather than with a bracket.
--
--   - `FormalAB`: a two-element type, the formal symbols $A$ and $B$.
--   - `relsF1`: the two relators $[AB^{-1}, A^{-1}BA]$ and $[AB^{-1}, A^{-2}BA^{2}]$ in the free group on
--     `FormalAB`; `F1` is the presented group $F_1 = \langle A, B : [AB^{-1}, A^{-1}BA],\ [AB^{-1},
--     A^{-2}BA^{2}]\rangle$, i.e. the free group modulo the normal closure of `relsF1`.
--   - `relsF2`: the words $X_k^{-1} X_n X_k X_{n+1}^{-1}$ for all $k < n$ in the free group on
--     $\mathbb{N}$; `F2` is $F_2 = \langle X_0, X_1, \dots : X_k^{-1} X_n X_k = X_{n+1} \text{ for } k < n \rangle$.
--   - `symF2 : FormalAB → F2` sends $A \mapsto X_0$, $B \mapsto X_1$; `symF` sends $A$, $B$ to the
--     functions `mapA`, `mapB` of the §1 bundle.
--   - `Y : ℕ → F1`: $Y_0 = A$ and $Y_{n} = A^{-(n-1)} B A^{n-1}$ for $n \ge 1$, the source's elements of
--     $F_1$ intended as images of the $X_n$.
--   - `wordFromF2`, `wordF2`: the positive word $X_0^{c_0} X_1^{c_1} \cdots X_n^{c_n}$ in $F_2$
--     determined by a list of exponents, mirroring `wordFrom` and `word` of the §2 bundle.
--
--   No theorem is stated here; in particular nothing in the bundle asserts that $F_1$ or $F_2$ is
--   isomorphic to anything.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 3, p. 225 (the definitions of F₁ and F₂, and of Y₀, Y₁, …)

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib

/-!
# Cannon–Floyd–Parry §3: the two presentations of Thompson's group `F`

Cannon, Floyd, Parry, *Introductory notes on Richard Thompson's groups*, L'Enseignement Math.
(2) 42 (1996), §3, p. 225:

  F₁ = ⟨A, B : [AB⁻¹, A⁻¹BA], [AB⁻¹, A⁻²BA²]⟩
  F₂ = ⟨X₀, X₁, X₂, … : Xₖ⁻¹ Xₙ Xₖ = Xₙ₊₁ for k < n⟩

with `[x, y] = x y x⁻¹ y⁻¹`.  The generators are *formal symbols*, as opposed to the functions
`mapA`, `mapB`, `X n` of the earlier bundles.  Both groups are Mathlib `PresentedGroup`s: the
quotient of the free group on the symbols by the normal closure of the relators.  `F1`, `F2`
below are the source's `F₁`, `F₂`.  The elements `Yₙ` of `F₁` (p. 225) and the words
`X₀^{c₀} X₁^{c₁} ⋯` in `F₂` are the auxiliary objects the section's proofs manipulate; `symF2`
and `symF` send the two formal symbols to their intended images in `F₂` and in the interval
maps.
-/

namespace CannonFloydParry

/-- The two formal symbols `A`, `B` of the finite presentation. -/
inductive FormalAB
  | A
  | B
  deriving DecidableEq

/-- The relators of `F₁`: the commutators `[AB⁻¹, A⁻¹BA]` and `[AB⁻¹, A⁻²BA²]`, written out
with the source's convention `[x, y] = x y x⁻¹ y⁻¹`. -/
def relsF1 : Set (FreeGroup FormalAB) :=
  let a := FreeGroup.of FormalAB.A
  let b := FreeGroup.of FormalAB.B
  { (a * b⁻¹) * (a⁻¹ * b * a) * (a * b⁻¹)⁻¹ * (a⁻¹ * b * a)⁻¹,
    (a * b⁻¹) * (a⁻¹ ^ 2 * b * a ^ 2) * (a * b⁻¹)⁻¹ * (a⁻¹ ^ 2 * b * a ^ 2)⁻¹ }

/-- `F₁ = ⟨A, B : [AB⁻¹, A⁻¹BA], [AB⁻¹, A⁻²BA²]⟩`. -/
abbrev F1 := PresentedGroup relsF1

/-- The relators of `F₂`: for `k < n`, the word `Xₖ⁻¹ Xₙ Xₖ Xₙ₊₁⁻¹`, i.e. the relation
`Xₖ⁻¹ Xₙ Xₖ = Xₙ₊₁`. -/
def relsF2 : Set (FreeGroup ℕ) :=
  { r | ∃ k n : ℕ, k < n ∧
      r = (FreeGroup.of k)⁻¹ * FreeGroup.of n * FreeGroup.of k * (FreeGroup.of (n + 1))⁻¹ }

/-- `F₂ = ⟨X₀, X₁, X₂, … : Xₖ⁻¹ Xₙ Xₖ = Xₙ₊₁ for k < n⟩`. -/
abbrev F2 := PresentedGroup relsF2

/-- The intended images of the formal symbols in `F₂`: `A ↦ X₀`, `B ↦ X₁`. -/
def symF2 : FormalAB → F2
  | FormalAB.A => PresentedGroup.of 0
  | FormalAB.B => PresentedGroup.of 1

/-- The intended images of the formal symbols among the interval maps: `A ↦ mapA`,
`B ↦ mapB`. -/
noncomputable def symF : FormalAB → (UI ≃o UI)
  | FormalAB.A => mapA
  | FormalAB.B => mapB

/-- The elements `Y₀ = A` and `Yₙ = A^{-(n-1)} B A^{n-1}` (`n ≥ 1`) of `F₁` (p. 225), the
images intended for the formal symbols `Xₙ`. -/
def Y : ℕ → F1
  | 0 => PresentedGroup.of FormalAB.A
  | n + 1 => (PresentedGroup.of FormalAB.A ^ n)⁻¹ * PresentedGroup.of FormalAB.B
      * PresentedGroup.of FormalAB.A ^ n

/-- The word `Xᵢ^{c₀} Xᵢ₊₁^{c₁} ⋯` in `F₂` determined by a list of nonnegative exponents,
smallest index leftmost — the formal counterpart of `wordFrom` in the tree-diagram bundle. -/
def wordFromF2 (i : ℕ) : List ℕ → F2
  | [] => 1
  | c :: cs => PresentedGroup.of i ^ c * wordFromF2 (i + 1) cs

/-- The positive word `X₀^{c₀} X₁^{c₁} ⋯ Xₙ^{cₙ}` in `F₂`. -/
def wordF2 (cs : List ℕ) : F2 := wordFromF2 0 cs

end CannonFloydParry


