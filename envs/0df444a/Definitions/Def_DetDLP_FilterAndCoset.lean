-- Prove2me | Definitions.Def_DetDLP_FilterAndCoset
-- name    : DetDLP_FilterAndCoset
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T09:09:57.055585+00:00
-- url     : https://prove2.me/theorems/4f1202c0-cf14-4ecc-bd19-a69bda2e4b94
-- title:
--   Fixed-Shift Tuples, Newton–Binomial Filter $\mathcal{Q}(X)$, and Column-HNF Affine Cosets
-- statement:
--   This definition module supplies the algebraic and lattice structures for Stage II of the deterministic discrete logarithm algorithm.
--
--   For an indexed factor base $F_1, \dots, F_m$ concatenated with dedicated coordinates for the generator $P$ and target $Q$ ($N = N_0 + 2$), it defines block-respecting $2m$-term tuples $\mathbf{X} \in \prod_{i=1}^m (F_i \times F_i)$, their incidence vectors $\mathrm{cnt}(\mathbf{X})$, group sums $\mathrm{val}(\mathbf{X})$, canonical lifted label sums $\Lambda_y(\mathbf{X}) \in \mathbb{Z}$, and the initial consistency congruences (4.1). For counterexample separation, it defines the nonnegative integer filter polynomial
--
--   $$\mathcal{Q}(X) = \prod_{j=-w}^{w} (X - 1 - j M_{\mathrm{lab}})^2 \in \mathbb{Z}[X]$$
--
--   of degree $d_{\mathrm{filt}} = 4w + 2$, its Newton forward-difference coefficients $c_j$, and the generalized integer binomial coefficient $\binom{d}{j}$ (`Ring.choose`). Finally, it defines lower-triangular column Hermite normal form (HNF) bases $B \in \mathbb{Z}^{N \times N}$, full-rank modular lattices $M_{\mathrm{lab}}\mathbb{Z}^N \subseteq B\mathbb{Z}^N$, affine solution cosets $\mathcal{A} = (x_0 + B\mathbb{Z}^N) / M_{\mathrm{lab}}\mathbb{Z}^N$, and their canonical binary encodings.
--
--   **Formalization Note** All lattice coordinates and residues are encoded in binary so coset representations have bit-length $\mathrm{poly}(N, \log M_{\mathrm{lab}})$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 4 (eqs. 4.1–4.4 and Lemma 4.4, pp. 14–17)

import Mathlib
import Definitions.Def_DetDLP_Machine

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- A block-indexed factor base of `m` blocks `F₁, ..., Fₘ` in an additive group `G`,
concatenated into `N₀ = ∑ᵢ |Fᵢ|` coordinates followed by two dedicated coordinates
`N₀` (holding generator `P`) and `N₀ + 1` (holding target `Q`), with `N = N₀ + 2`. -/
structure IndexedFactorBase (G : Type*) (m : ℕ) where
  blocks : Fin m → List G

namespace IndexedFactorBase

variable {G : Type*} {m : ℕ} (FB : IndexedFactorBase G m)

/-- Total factor-base size `N₀ = ∑_{i=1}^m |Fᵢ|`. -/
def totalBaseSize : ℕ :=
  ∑ i : Fin m, (FB.blocks i).length

/-- Total coordinate count `N = N₀ + 2`. -/
def totalCoords : ℕ :=
  FB.totalBaseSize + 2

/-- Prefix sum of block lengths strictly before block `i`. -/
def blockOffset (i : Fin m) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin m => j < i), (FB.blocks j).length

lemma blockOffset_add_lt (i : Fin m) (r : Fin (FB.blocks i).length) :
    FB.blockOffset i + r.val < FB.totalBaseSize := by
  have hdisj : i ∉ Finset.univ.filter (fun j : Fin m => j < i) := by
    simp
  have hsum :
      (FB.blocks i).length + FB.blockOffset i ≤ FB.totalBaseSize := by
    have h1 : (FB.blocks i).length +
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => j < i), (FB.blocks j).length =
      ∑ j ∈ insert i (Finset.univ.filter (fun j : Fin m => j < i)), (FB.blocks j).length :=
      (Finset.sum_insert (f := fun j : Fin m => (FB.blocks j).length) hdisj).symm
    calc (FB.blocks i).length + FB.blockOffset i
        = ∑ j ∈ insert i (Finset.univ.filter (fun j : Fin m => j < i)), (FB.blocks j).length := h1
      _ ≤ ∑ j : Fin m, (FB.blocks j).length :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  omega

/-- Coordinate index in `Fin (N₀ + 2)` of the `r`-th element of block `i`. -/
def coordOf (i : Fin m) (r : Fin (FB.blocks i).length) : Fin FB.totalCoords :=
  ⟨FB.blockOffset i + r.val, Nat.lt_trans (FB.blockOffset_add_lt i r) (by unfold totalCoords; omega)⟩

/-- Dedicated coordinate `N₀` holding the generator `P`. -/
def genCoord : Fin FB.totalCoords :=
  ⟨FB.totalBaseSize, by unfold totalCoords; omega⟩

/-- Dedicated coordinate `N₀ + 1` holding the target `Q`. -/
def targetCoord : Fin FB.totalCoords :=
  ⟨FB.totalBaseSize + 1, by unfold totalCoords; omega⟩

/-- The indexed list `A₁, ..., A_N` (`N = N₀ + 2`): concatenated block entries followed by `P` and `Q`. -/
def elem (P Q : G) (j : Fin FB.totalCoords) : G :=
  if h : j.val < FB.totalBaseSize then
    ((List.finRange m).flatMap FB.blocks).get ⟨j.val, by
      rw [List.length_flatMap, ← Fin.sum_univ_def]
      exact h⟩
  else if j.val = FB.totalBaseSize then P
  else Q

/-- A block-respecting `2m`-term tuple `X = (X_{1,1}, X_{1,2}, ..., X_{m,1}, X_{m,2}) ∈ ∏ᵢ (Fᵢ × Fᵢ)`. -/
abbrev BlockTuple : Type :=
  (i : Fin m) → Fin 2 → Fin (FB.blocks i).length

/-- Incidence vector `cnt(X) ∈ ℕ^N` supported on `{0, ..., N₀ - 1}` with `‖cnt(X)‖₁ = 2m`. -/
def tupleCnt (X : FB.BlockTuple) (j : Fin FB.totalCoords) : ℕ :=
  ∑ i : Fin m, ∑ s : Fin 2, if FB.coordOf i (X i s) = j then 1 else 0

/-- Group sum `val(X) = ∑_{i=1}^m (X_{i,1} + X_{i,2}) ∈ G`. -/
def tupleVal [AddCommGroup G] (X : FB.BlockTuple) : G :=
  ∑ i : Fin m, ((FB.blocks i).get (X i 0) + (FB.blocks i).get (X i 1))

/-- Canonical lifted integer label sum `Λ_y(X) = ∑_{j=1}^N cnt(X)_j · lift(y_j) ∈ ℤ`,
lifting each `y_j ∈ ZMod Mlab` canonically to `{0, ..., Mlab - 1}`. -/
def tupleLabelSum (Mlab : ℕ) [NeZero Mlab] (y : Fin FB.totalCoords → ZMod Mlab)
    (X : FB.BlockTuple) : ℤ :=
  ∑ j : Fin FB.totalCoords, (FB.tupleCnt X j : ℤ) * ((y j).val : ℤ)

/-- Initial consistency congruences (4.1):
`y_{N₀+1} ≡ 1 (mod Mlab)` and `y_j - Λ_y(U^{(j)}) ≡ 0 (mod Mlab)` for all `1 ≤ j ≤ N`. -/
def SatisfiesInitialCongruences (Mlab : ℕ) [NeZero Mlab]
    (U : Fin FB.totalCoords → FB.BlockTuple) (y : Fin FB.totalCoords → ZMod Mlab) : Prop :=
  y FB.genCoord = 1 ∧
  ∀ j : Fin FB.totalCoords, y j = ((FB.tupleLabelSum Mlab y (U j) : ℤ) : ZMod Mlab)

end IndexedFactorBase

/-- Nonnegative integer filter polynomial (eq. 4.3):
`Q(X) = ∏_{j = -w}^w (X - 1 - j · Mlab)² ∈ ℤ[X]` of degree `4w + 2`. -/
noncomputable def filterPoly (w Mlab : ℕ) : Polynomial ℤ :=
  ∏ j ∈ Finset.Icc (-(w : ℤ)) (w : ℤ),
    (Polynomial.X - Polynomial.C (1 + j * (Mlab : ℤ))) ^ 2

/-- Filter degree `d_filt = 4w + 2`. -/
def dFilt (w : ℕ) : ℕ := 4 * w + 2

/-- Newton forward-difference coefficient `c_j = ∑_{t=0}^j (-1)^{j-t} C(j, t) Q(t) ∈ ℤ` (eq. 4.4). -/
noncomputable def newtonCoeff (w Mlab j : ℕ) : ℤ :=
  ∑ t ∈ Finset.range (j + 1),
    (-1 : ℤ) ^ (j - t) * (Nat.choose j t : ℤ) * (filterPoly w Mlab).eval (t : ℤ)

/-- Integer generalized binomial coefficient `C(d, j) ∈ ℤ` for arbitrary integer `d ∈ ℤ` and `j ∈ ℕ`. -/
def intBinom (d : ℤ) (j : ℕ) : ℤ :=
  Ring.choose d j

/-- Lower-triangular column Hermite normal form (HNF) predicate for an integer matrix
`B ∈ ℤ^{N × N}` (columns `b₁, ..., b_N` form the HNF basis):
lower-triangular (`B i j = 0` for `i < j`), positive diagonal (`0 < B i i`),
and column-reduced left of the diagonal (`0 ≤ B i j < B i i` for `j < i`). -/
def IsColumnHNF {N : ℕ} (B : Matrix (Fin N) (Fin N) ℤ) : Prop :=
  (∀ i j : Fin N, i < j → B i j = 0) ∧
  (∀ i : Fin N, 0 < B i i) ∧
  (∀ i j : Fin N, j < i → 0 ≤ B i j ∧ B i j < B i i)

/-- The integer lattice `Λ_lat = B · ℤ^N ⊆ ℤ^N` generated by the columns of `B`. -/
def latticeSpan {N : ℕ} (B : Matrix (Fin N) (Fin N) ℤ) : Set (Fin N → ℤ) :=
  {v | ∃ t : Fin N → ℤ, v = Matrix.mulVec B t}

/-- Full-rank modular lattice condition `Mlab · ℤ^N ⊆ Λ_lat ⊆ ℤ^N` and `det B ∣ Mlab^N`. -/
def IsModularLatticeBasis (Mlab : ℕ) {N : ℕ} (B : Matrix (Fin N) (Fin N) ℤ) : Prop :=
  IsColumnHNF B ∧
  (∀ v : Fin N → ℤ, (fun i => (Mlab : ℤ) * v i) ∈ latticeSpan B) ∧
  (B.det ∣ ((Mlab : ℤ) ^ N))

/-- The affine solution coset `A = (x₀ + Λ_lat) / Mlab ℤ^N ⊆ (ZMod Mlab)^N`. -/
def affineCoset (Mlab : ℕ) [NeZero Mlab] {N : ℕ}
    (x0 : Fin N → ZMod Mlab) (B : Matrix (Fin N) (Fin N) ℤ) : Set (Fin N → ZMod Mlab) :=
  {x | ∃ t : Fin N → ℤ, ∀ i : Fin N, x i = x0 i + ((Matrix.mulVec B t i : ℤ) : ZMod Mlab)}

/-- Canonical binary encoding of a coset representation `(x₀, B)` where `x₀ : Fin N → ℕ`
and `B : Matrix (Fin N) (Fin N) ℤ`. -/
def encodeCosetRep {N : ℕ} (x0 : Fin N → ℕ) (B : Matrix (Fin N) (Fin N) ℤ) : List Bool :=
  Encoding.encodeList id
    [ encodeNatListBin (List.ofFn x0),
      Encoding.encodeList encodeIntBin
        ((List.finRange N).flatMap fun i => (List.finRange N).map fun j => B i j) ]

/-- Canonical binary input encoding for the coset update of Lemma 4.4:
`(Mlab, N, x₀, B, a, c₀)`. -/
def encodeCosetUpdateInput (Mlab : ℕ) {N : ℕ}
    (x0 : Fin N → ℕ) (B : Matrix (Fin N) (Fin N) ℤ) (a : Fin N → ℕ) (c0 : ℕ) : List Bool :=
  Encoding.encodeList id
    [ countWord Mlab,
      countWord N,
      encodeCosetRep x0 B,
      encodeNatListBin (List.ofFn a),
      countWord c0 ]

end DetDLP


