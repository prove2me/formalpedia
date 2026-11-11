-- Prove2me | Definitions.Def_PolySwap_KMS_Unip
-- name    : PolySwap_KMS_Unip
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:40:40.981737+00:00
-- url     : https://prove2.me/theorems/d4ca71f1-bc26-4f97-8193-8746b41faaee
-- title:
--   $\mathrm{Unip}_n(R)$, the 5-block form, block generators $E_{i,j}(A)$ and the presentation $\langle S_{\mathrm{Elm}}\mid R_{\mathrm{Elm}}\rangle$
-- statement:
--   Let $R$ be a commutative unital ring. $\mathrm{Unip}_n(R)$ is the group of upper unitriangular $n\times n$ matrices over $R$. For $n\ge5$ put $k_0=\lfloor n/5\rfloor$, $k_1=n-4k_0$ and cut matrices into $5\times5$ blocks of sizes $k_0,k_0,k_1,k_0,k_0$. For $1\le i<j\le5$, $E_{i,j}(A)$ is the block matrix with identity diagonal blocks, $A$ in block position $(i,j)$ and $0$ elsewhere; for $1\le i\le5$, $E_{i,i}(A)$ has the upper unitriangular block $A$ in position $(i,i)$ and identity blocks elsewhere. $A$ is **$(i,j)$-admissible** if $E_{i,j}(A)$ is defined. The generators are
--   $$S_{\mathrm{Elm}}=\{E_{i,j}(A):1\le i\le j\le5,\ (i,j)\ne(1,5),\ A\ (i,j)\text{-admissible}\}$$
--   and $R_{\mathrm{Elm}}$ consists of: (Elm1) $E_{i,j}(A_1)E_{i,j}(A_2)=E_{i,j}(A_1+A_2)$ for $i<j$ and $=E_{i,j}(A_1A_2)$ for $i=j$; (Elm2) for $1\le i<j\le4,1\le k<l\le4$, or $2\le i<j\le5,2\le k<l\le5$, or $\{(i,j),(k,l)\}=\{(1,2),(4,5)\}$: $[E_{i,j}(A_1),E_{k,l}(A_2)]=E_{i,l}(A_1A_2)$ if $j=k$, $E_{k,j}(-A_2A_1)$ if $i=l$, and $e$ otherwise, with $[g,h]=g^{-1}h^{-1}gh$; (Elm3) for $1\le i\le j\le4,1\le l\le4$, or $2\le i\le j\le5,2\le l\le5$, or $1\le i\le j\le2,l=5$, or $4\le i\le j\le5,l=1$: $E_{l,l}(B)^{-1}E_{i,j}(A)E_{l,l}(B)$ equals $E_{i,j}(A)$ ($i\ne l\ne j$), $E_{i,j}(B^{-1}A)$ ($i=l\ne j$), $E_{i,j}(AB)$ ($j=l\ne i$), $E_{l,l}(B^{-1}AB)$ ($i=j=l$).
--
--   **Formalization Note.** `Unip n R` is the subgroup of `SL (Fin n) R` of upper unitriangular matrices (every such matrix has determinant 1). Blocks are numbered 1–5 (`blockOf`). An admissible block matrix is stored embedded in an $n\times n$ matrix: for $i<j$ the matrix carrying $A$ in block $(i,j)$ and $0$ elsewhere, with `E i j A = 1 + A`; for $i=j$ the matrix $E_{i,i}(A)$ itself. Block sums, products and inverses are then the $n\times n$ operations. $S_{\mathrm{Elm}}$ is a set of group elements and $R_{\mathrm{Elm}}$ a set of words in `FreeGroup (SElm n R)`, each relation written as a word equal to 1 (e.g. $x\,y\,z^{-1}$ for $xy=z$). In (Elm2) the case $j=k$ uses $E_{i,l}(A_1A_2)$, the block form of the commutator $[E_{i,j}(A_1),E_{j,l}(A_2)]$; the page prints $E_{i,k}(A_1A_2)$, a typo (INSIGHTS I3).
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), §5 (pp. 35–38: Unip_n(R), the 5-block form, E_{i,j}(A), admissibility, S_Elm, R_Elm)

import Mathlib
import Definitions.Def_PolySwap_KMS_Dehn

open Classical Matrix

noncomputable section

namespace PolySwap.KMS

/-!
# `Unip_n(R)`, its 5-block form, the block generators `E_{i,j}(A)` and `⟨S_Elm | R_Elm⟩`

Dikstein, Oppenheim, Valentiner-Branth, *Polynomial Swap Coboundary Expansion with Applications
to LTCs and PCPs*, STOC 2027 submission (manuscript sha256 b9cb2095…), §5 (pp. 35–38).

`R` is a commutative unital ring. Blocks are numbered `1, …, 5` as in the paper; matrix
coordinates are `Fin n` (0-based). An `(i, j)`-admissible block matrix `A` is stored embedded in
an `n × n` matrix: for `i < j` it is the `n × n` matrix that carries `A` in block position `(i, j)`
and `0` elsewhere, and `E_{i,j}(A) = 1 + A`; for `i = j` it is the `n × n` matrix
`E_{i,i}(A)` itself (the identity outside the diagonal block `(i, i)`, `A` inside it). With this
encoding block sums, block products and block inverses are the corresponding `n × n` operations.
-/

variable (n : ℕ) (R : Type*) [CommRing R]

/-- `M` is upper unitriangular: zero below the diagonal and `1` on it. -/
def IsUnitriangular (M : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ i j : Fin n, j < i → M i j = 0) ∧ ∀ i : Fin n, M i i = 1

/-- `Unip_n(R)` (p. 35): the group of upper unitriangular `n × n` matrices over `R`, as a
subgroup of `SL_n(R)` (every upper unitriangular matrix has determinant `1`). -/
def Unip : Subgroup (Matrix.SpecialLinearGroup (Fin n) R) where
  carrier := {M | IsUnitriangular n R (M : Matrix (Fin n) (Fin n) R)}
  one_mem' := by
    refine ⟨fun i j h => ?_, fun i => ?_⟩
    · simp [(ne_of_lt h).symm]
    · simp
  mul_mem' := by
    intro A B hA hB
    have hA' : IsUnitriangular n R (A : Matrix (Fin n) (Fin n) R) := hA
    have hB' : IsUnitriangular n R (B : Matrix (Fin n) (Fin n) R) := hB
    show IsUnitriangular n R ((A * B : Matrix.SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)
    rw [Matrix.SpecialLinearGroup.coe_mul]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero (fun k _ => ?_)
      rcases lt_or_ge k i with hk | hk
      · simp [hA'.1 i k hk]
      · simp [hB'.1 k j (lt_of_lt_of_le hij hk)]
    · rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · simp [hA'.2 i, hB'.2 i]
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with hk | hk
        · simp [hA'.1 i k hk]
        · simp [hB'.1 k i hk]
      · simp
  inv_mem' := by
    intro A hA
    have hA' : IsUnitriangular n R (A : Matrix (Fin n) (Fin n) R) := hA
    show IsUnitriangular n R ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)
    have hbt : (A : Matrix (Fin n) (Fin n) R).BlockTriangular id := fun i j h => hA'.1 i j h
    have hdet : (A : Matrix (Fin n) (Fin n) R).det = 1 := A.2
    let _ : Invertible (A : Matrix (Fin n) (Fin n) R) :=
      Matrix.invertibleOfIsUnitDet _ (by rw [hdet]; exact isUnit_one)
    have hinv : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) =
        (A : Matrix (Fin n) (Fin n) R)⁻¹ := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.inv_def, hdet]; simp
    have hbt' := Matrix.blockTriangular_inv_of_blockTriangular hbt
    rw [hinv]
    refine ⟨fun i j h => hbt' h, fun i => ?_⟩
    have h1 : ((A : Matrix (Fin n) (Fin n) R) * (A : Matrix (Fin n) (Fin n) R)⁻¹) i i = 1 := by
      rw [Matrix.mul_inv_of_invertible]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
    · simpa [hA'.2 i] using h1
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · simp [hA'.1 i k hk]
      · simp [hbt' hk]
    · simp

/-- The block number `1, …, 5` of the coordinate `a` in the 5-block form (p. 37): with
`k₀ = ⌊n/5⌋` and `k₁ = n - 4k₀`, the blocks have sizes `k₀, k₀, k₁, k₀, k₀`. -/
def blockOf (a : Fin n) : ℕ :=
  if (a : ℕ) < n / 5 then 1
  else if (a : ℕ) < 2 * (n / 5) then 2
  else if (a : ℕ) < 2 * (n / 5) + (n - 4 * (n / 5)) then 3
  else if (a : ℕ) < 3 * (n / 5) + (n - 4 * (n / 5)) then 4
  else 5

/-- `A` is `(i, j)`-admissible (p. 38), in the embedded encoding: for `i < j`, `A` is supported in
block position `(i, j)`; for `i = j`, `A` is upper unitriangular and equal to the identity outside
the diagonal block `(i, i)`. -/
def Admissible (i j : ℕ) (A : Matrix (Fin n) (Fin n) R) : Prop :=
  (i < j ∧ ∀ a b, ¬ (blockOf n a = i ∧ blockOf n b = j) → A a b = 0) ∨
  (i = j ∧ IsUnitriangular n R A ∧
    ∀ a b, ¬ (blockOf n a = i ∧ blockOf n b = i) → A a b = if a = b then 1 else 0)

/-- `E_{i,j}(A)` (p. 37): for `i < j` the block matrix with identity diagonal blocks, `A` in
position `(i, j)` and `0` elsewhere; for `i = j` the block-diagonal matrix with `A` in position
`(i, i)` and identity blocks elsewhere. -/
def E (i j : ℕ) (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  if i < j then 1 + A else A

/-- The matrix of an element of `Unip_n(R)`. -/
def umat (g : Unip n R) : Matrix (Fin n) (Fin n) R :=
  ((g : Matrix.SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)

/-- `S_Elm = {E_{i,j}(A) : 1 ≤ i ≤ j ≤ 5, (i, j) ≠ (1, 5), A (i, j)-admissible}` (p. 38), a subset
of `Unip_n(R)`. -/
def SElm : Set (Unip n R) :=
  {g | ∃ i j A, 1 ≤ i ∧ i ≤ j ∧ j ≤ 5 ∧ (i, j) ≠ (1, 5) ∧ Admissible n R i j A ∧
    umat n R g = E n R i j A}

/-- The relations `R_Elm` (p. 38) on the alphabet `S_Elm`, as words of `Free(S_Elm)`:
(Elm1) `E_{i,j}(A₁)E_{i,j}(A₂) = E_{i,j}(A₁ + A₂)` (`i < j`), `= E_{i,j}(A₁A₂)` (`i = j`);
(Elm2) `[E_{i,j}(A₁), E_{k,l}(A₂)] = E_{i,l}(A₁A₂)` if `j = k`, `= E_{k,j}(-A₂A₁)` if `i = l`,
`= e` otherwise, for `1 ≤ i < j ≤ 4, 1 ≤ k < l ≤ 4`, or `2 ≤ i < j ≤ 5, 2 ≤ k < l ≤ 5`, or
`{(i,j),(k,l)} = {(1,2),(4,5)}`, with `[g, h] = g⁻¹h⁻¹gh`;
(Elm3) `E_{l,l}(B)⁻¹E_{i,j}(A)E_{l,l}(B) = E_{i,j}(A)` (`i ≠ l ≠ j`), `= E_{i,j}(B⁻¹A)`
(`i = l ≠ j`), `= E_{i,j}(AB)` (`j = l ≠ i`), `= E_{l,l}(B⁻¹AB)` (`i = j = l`), for
`1 ≤ i ≤ j ≤ 4, 1 ≤ l ≤ 4`, or `2 ≤ i ≤ j ≤ 5, 2 ≤ l ≤ 5`, or `1 ≤ i ≤ j ≤ 2, l = 5`, or
`4 ≤ i ≤ j ≤ 5, l = 1`. -/
def RElm : Set (FreeGroup (SElm n R)) :=
  -- (Elm1)
  {w | ∃ (i j : ℕ) (A₁ A₂ : Matrix (Fin n) (Fin n) R) (x y z : SElm n R),
      1 ≤ i ∧ i ≤ j ∧ j ≤ 5 ∧ (i, j) ≠ (1, 5) ∧ Admissible n R i j A₁ ∧ Admissible n R i j A₂ ∧
      umat n R x.1 = E n R i j A₁ ∧ umat n R y.1 = E n R i j A₂ ∧
      umat n R z.1 = E n R i j (if i < j then A₁ + A₂ else A₁ * A₂) ∧
      w = FreeGroup.of x * FreeGroup.of y * (FreeGroup.of z)⁻¹} ∪
  -- (Elm2)
  {w | ∃ (i j k l : ℕ) (A₁ A₂ : Matrix (Fin n) (Fin n) R) (x y : SElm n R),
      ((1 ≤ i ∧ i < j ∧ j ≤ 4 ∧ 1 ≤ k ∧ k < l ∧ l ≤ 4) ∨
        (2 ≤ i ∧ i < j ∧ j ≤ 5 ∧ 2 ≤ k ∧ k < l ∧ l ≤ 5) ∨
        ((i, j) = (1, 2) ∧ (k, l) = (4, 5)) ∨ ((i, j) = (4, 5) ∧ (k, l) = (1, 2))) ∧
      Admissible n R i j A₁ ∧ Admissible n R k l A₂ ∧
      umat n R x.1 = E n R i j A₁ ∧ umat n R y.1 = E n R k l A₂ ∧
      ((j = k ∧ ∃ z : SElm n R, umat n R z.1 = E n R i l (A₁ * A₂) ∧
          w = (FreeGroup.of x)⁻¹ * (FreeGroup.of y)⁻¹ * FreeGroup.of x * FreeGroup.of y *
            (FreeGroup.of z)⁻¹) ∨
        (i = l ∧ ∃ z : SElm n R, umat n R z.1 = E n R k j (-(A₂ * A₁)) ∧
          w = (FreeGroup.of x)⁻¹ * (FreeGroup.of y)⁻¹ * FreeGroup.of x * FreeGroup.of y *
            (FreeGroup.of z)⁻¹) ∨
        (j ≠ k ∧ i ≠ l ∧
          w = (FreeGroup.of x)⁻¹ * (FreeGroup.of y)⁻¹ * FreeGroup.of x * FreeGroup.of y))} ∪
  -- (Elm3)
  {w | ∃ (i j l : ℕ) (A B : Matrix (Fin n) (Fin n) R) (x b z : SElm n R),
      i ≤ j ∧
      ((1 ≤ i ∧ j ≤ 4 ∧ 1 ≤ l ∧ l ≤ 4) ∨ (2 ≤ i ∧ j ≤ 5 ∧ 2 ≤ l ∧ l ≤ 5) ∨
        (1 ≤ i ∧ j ≤ 2 ∧ l = 5) ∨ (4 ≤ i ∧ j ≤ 5 ∧ l = 1)) ∧
      Admissible n R i j A ∧ Admissible n R l l B ∧
      umat n R x.1 = E n R i j A ∧ umat n R b.1 = E n R l l B ∧
      umat n R z.1 =
        (if i ≠ l ∧ j ≠ l then E n R i j A
         else if i = l ∧ j ≠ l then E n R i j (B⁻¹ * A)
         else if j = l ∧ i ≠ l then E n R i j (A * B)
         else E n R l l (B⁻¹ * A * B)) ∧
      w = (FreeGroup.of b)⁻¹ * FreeGroup.of x * FreeGroup.of b * (FreeGroup.of z)⁻¹}

/-- The inclusion `S_Elm → Unip_n(R)`. -/
def sElmIncl : SElm n R → Unip n R := Subtype.val

end PolySwap.KMS


