-- Prove2me | Definitions.Def_RealAPSP_Supplement_BSG
-- name    : RealAPSP_Supplement_BSG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:03:20.790696+00:00
-- url     : https://prove2.me/theorems/57216d5a-2d6e-41e7-bf8f-e7acc8002fd2
-- title:
--   $\Delta$-spaced sets, approximate solution pairs, and the output layout of BSG covering
-- statement:
--   For $\delta\ge0$, a finite set $X\subseteq\mathbb R$ is **$\delta$-spaced** if $|x-x'|\ge\delta$ for all distinct $x,x'\in X$.
--
--   For $\Delta\ge0$ and finite $X,Y,Z\subseteq\mathbb R$, the **approximate solution pairs** are
--
--   $$\{(x,y)\in X\times Y:\ \exists z\in Z,\ |x+y-z|\le\Delta\},$$
--
--   and for families $X_1,\dots,X_L$ and $Y_1,\dots,Y_L$ the set $R$ of Theorem 7.6 is this set with the union of the boxes $X_\ell\times Y_\ell$ removed:
--
--   $$R=\{(x,y)\in X\times Y:\ \exists z\in Z:\ x+y=z\pm\Delta\}\setminus\bigcup_{\ell=1}^{L}(X_\ell\times Y_\ell).$$
--
--   The module also fixes how the algorithm of Theorem 7.6 reports its output when $X=\{x_0,\dots,x_{n-1}\}$ and $Y=\{y_0,\dots,y_{n-1}\}$ are given as lists. Integer output cell $0$ holds a number $p$. For $\ell<p$, the next $2n$ cells are membership bits: bit $i$ says whether $x_i\in X_\ell$, bit $n+j$ whether $y_j\in Y_\ell$. The sets with $\ell\ge p$ are empty, so the output need not have $L\cdot n$ cells when $L$ is large. After these blocks come a count $r$ and then $r$ pairs of indices $(i,j)$, each standing for the pair $(x_i,y_j)\in R$.
--
--   These objects state Theorem 7.6, the Balog–Szemerédi–Gowers covering for approximate reals.
--
--   **Formalization Note** The boxes are indexed by $\ell\in\{0,\dots,L-1\}$, i.e. `Fin L`. Memory starts at $0$, so a zero cell means "absent".
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), §4.1, ∆-spaced and x = y ± ∆, p.11 (PDF p.13); Theorem 7.6, the set R, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_RealAPSP_Cover

namespace RealAPSP

namespace Supplement

/-!
# Spaced sets, approximate solution pairs, and the output layout of BSG covering

Fischer, Polak, Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*, arXiv:2611.04847 (held file
sha256 a3dc0096…), §4.1, p.11 (PDF p.13): "For ∆ ≥ 0, a set X ⊆ R is ∆-spaced if |x − x′| ≥ ∆ for every pair of
distinct x, x′ ∈ X"; Theorem 7.6, p.34 (PDF p.36): "R := {(x, y) ∈ X × Y : ∃z ∈ Z : x + y = z ± ∆} \ ⋃_{ℓ=1}^{L}
(X_ℓ × Y_ℓ)", where `x = y ± ∆` means `|x − y| ≤ ∆` (p.11).

**Formalization Note.**
* `approxPairs Δ X Y Z` is `{(x, y) ∈ X × Y : ∃ z ∈ Z, |x + y − z| ≤ ∆}`, and `bsgRemainder` removes the union of the
  `L` boxes `X_ℓ × Y_ℓ`, indexed by `Fin L` (0-based; the page's `ℓ ∈ [L]`).
* **Output layout of the algorithm of Theorem 7.6.** The inputs are injective lists `x, y : Fin n → ℝ`,
  `z : Fin m → ℝ`, and the sets are identified by input indices. Integer output cell `0` holds a number `p`; for
  `ℓ < p` the cells `1 + 2nℓ + i` (`i < n`) are the membership bits of `x i` in `X_ℓ` and the cells
  `1 + 2nℓ + n + j` those of `y j` in `Y_ℓ` (nonzero = member); the sets with `ℓ ≥ p` are empty, so the output need
  not have `L·n` cells when `L` is large. From `b = 1 + 2np` the cell `b` holds a count `r`, and for `t < r` the cells
  `b + 1 + 2t`, `b + 2 + 2t` hold the indices `i, j` of the `t`-th pair `(x i, y j)` of `R`. Memory starts at `0`, so
  a zero cell means "absent".
-/

/-- `X` is `δ`-spaced: distinct elements are at distance at least `δ` (§4.1, p.11). -/
def IsSpaced (δ : ℝ) (X : Finset ℝ) : Prop :=
  ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → δ ≤ |x - x'|

open Classical in
/-- The pairs `(x, y) ∈ X × Y` with `x + y = z ± ∆` for some `z ∈ Z`. -/
noncomputable def approxPairs (Δ : ℝ) (X Y Z : Finset ℝ) : Finset (ℝ × ℝ) :=
  (X ×ˢ Y).filter fun p => ∃ z ∈ Z, |p.1 + p.2 - z| ≤ Δ

open Classical in
/-- The set `R` of Theorem 7.6: approximate solution pairs outside every box `X_ℓ × Y_ℓ`. -/
noncomputable def bsgRemainder {L : ℕ} (Δ : ℝ) (X Y Z : Finset ℝ) (Xs Ys : Fin L → Finset ℝ) :
    Finset (ℝ × ℝ) :=
  approxPairs Δ X Y Z \ Finset.univ.biUnion fun ℓ => Xs ℓ ×ˢ Ys ℓ

/-- The number `p` of output pairs that may be nonempty (output cell `0`). -/
noncomputable def bsgPairCount (σ : State) : ℕ := (σ.imem (outCell 0)).toNat

open Classical in
/-- The output set `X_ℓ`: the `x i` whose bit is nonzero, and `∅` for `ℓ ≥ p`. -/
noncomputable def bsgOutX {n : ℕ} (x : Fin n → ℝ) (L : ℕ) (σ : State) (ℓ : Fin L) : Finset ℝ :=
  if (ℓ : ℕ) < bsgPairCount σ then
    (Finset.univ.filter fun i : Fin n => σ.imem (outCell (1 + 2 * n * ℓ + i)) ≠ 0).image x
  else ∅

open Classical in
/-- The output set `Y_ℓ`: the `y j` whose bit is nonzero, and `∅` for `ℓ ≥ p`. -/
noncomputable def bsgOutY {n : ℕ} (y : Fin n → ℝ) (L : ℕ) (σ : State) (ℓ : Fin L) : Finset ℝ :=
  if (ℓ : ℕ) < bsgPairCount σ then
    (Finset.univ.filter fun j : Fin n => σ.imem (outCell (1 + 2 * n * ℓ + n + j)) ≠ 0).image y
  else ∅

/-- The cell `b = 1 + 2np` that holds the count of the listed pairs of `R`. -/
noncomputable def bsgRBase (n : ℕ) (σ : State) : ℕ := 1 + 2 * n * bsgPairCount σ

open Classical in
/-- The output set `R`: the pairs `(x i, y j)` listed by index after cell `b`. -/
noncomputable def bsgOutR {n : ℕ} (x y : Fin n → ℝ) (σ : State) : Finset (ℝ × ℝ) :=
  (Finset.univ.filter fun ij : Fin n × Fin n =>
      ∃ t < (σ.imem (outCell (bsgRBase n σ))).toNat,
        σ.imem (outCell (bsgRBase n σ + 1 + 2 * t)) = ((ij.1 : ℕ) : ℤ) ∧
        σ.imem (outCell (bsgRBase n σ + 2 + 2 * t)) = ((ij.2 : ℕ) : ℤ)).image
    fun ij => (x ij.1, y ij.2)

end Supplement

end RealAPSP


