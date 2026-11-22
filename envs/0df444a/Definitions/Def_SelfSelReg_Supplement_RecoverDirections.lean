-- Prove2me | Definitions.Def_SelfSelReg_Supplement_RecoverDirections
-- name    : SelfSelReg_Supplement_RecoverDirections
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T05:17:23.094124+00:00
-- url     : https://prove2.me/theorems/85c3feca-de88-429c-b6e5-81db2a5acc22
-- title:
--   Algorithm 6.3 (RECOVERDIRECTIONS) as an input–output relation, with $\mathrm{Unif}(\mathbb S^{n-1})$ and $L=\lceil\log_2(1/\delta)\rceil$
-- statement:
--   Algorithm 6.3 takes symmetric matrices $\widehat D_1,\dots,\widehat D_n\in\mathbb R^{p\times p}$, $p\ge2$, and a confidence parameter $\delta$, and returns unit vectors $\widehat u_1,\dots,\widehat u_p\in\mathbb R^n$:
--
--   1. put $L=\log_2(1/\delta)$ and draw independent $b_1,\dots,b_L\sim\mathrm{Unif}(\mathbb S^{n-1})$;
--   2. for each trial $\iota\in[L]$ form $\widehat D(b_\iota)=\sum_{j=1}^n(b_\iota)_j\widehat D_j$ and compute its eigenvalues $\widehat\nu^{(\iota)}_1\ge\dots\ge\widehat\nu^{(\iota)}_p$ with corresponding orthonormal eigenvectors $\widehat z^{(\iota)}_1,\dots,\widehat z^{(\iota)}_p$;
--   3. let $\iota_\star\in\arg\max_{\iota}\min_{1\le i<p}\bigl(\widehat\nu^{(\iota)}_i-\widehat\nu^{(\iota)}_{i+1}\bigr)$;
--   4. set $(\widehat a_i)_j=(\widehat z^{(\iota_\star)}_i)^\top\widehat D_j\,\widehat z^{(\iota_\star)}_i$ for $i\in[p]$, $j\in[n]$, and return $\widehat u_i=\widehat a_i/\|\widehat a_i\|_2$.
--
--   The bundle defines
--
--   - the uniform distribution on the unit sphere of $\mathbb R^n$, as the law of $G/\|G\|_2$ for $G\sim N(0,I_n)$;
--   - the number of trials $L=\lceil\log_2(1/\delta)\rceil$;
--   - the relation "$(\widehat u_i)_{i\in[p]}$ is an output of the routine on $(\widehat D,\delta)$ for the drawn directions $b_1,\dots,b_L$": there are eigendecompositions of all $\widehat D(b_\iota)$ and a maximizing trial $\iota_\star$ for which step 4 holds.
--
--   Theorem 6.6 is a statement about every output of this relation, with the directions drawn independently and uniformly from the sphere.
--
--   **Formalization Note** The page writes $L\leftarrow\log_2(1/\delta)$; $L$ counts trials and the proof uses $2^{-L}\le\delta$, so $L$ is the ceiling. The directions are an explicit argument, so that "with probability at least $1-\delta$" is a statement about their law. The routine is a relation because the eigenvectors and the maximizing trial are not fixed by the pseudocode. When $\widehat a_i=0$ the quotient in step 4 is undefined; since the routine is declared to return unit vectors, $\widehat u_i$ may then be any unit vector.
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Algorithm 6.3, p.43 (PDF p.46)

import Mathlib
import Definitions.Def_SelfSelReg_Supplement_EigDecomp

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

namespace Supplement

/-- The uniform distribution `Unif(S^{n−1})` on the unit sphere of `ℝⁿ` (Algorithm 6.3, line 2), as a
measure on `ℝⁿ`: the law of `G/‖G‖₂` for `G ∼ N(0, I_n)`.

**Formalization Note.** For `n ≥ 1` the standard Gaussian is rotation invariant and `G ≠ 0` almost
surely, so `G/‖G‖₂` is uniform on the sphere. -/
noncomputable def sphereLaw (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (stdGaussian (EuclideanSpace ℝ (Fin n))).map fun x => ‖x‖⁻¹ • x

/-- The number of trials `L` of Algorithm 6.3, line 1: "L ← log₂(1/δ)".

**Formalization Note.** The page's `log₂(1/δ)` is not an integer; `L` counts trials, and the proof
uses `2^{−L} ≤ δ` (p.44, PDF p.47), so `L = ⌈log₂(1/δ)⌉`. -/
noncomputable def numTrials (δ : ℝ) : ℕ := ⌈Real.logb 2 (1 / δ)⌉₊

/-- The coordinate quadratic forms of Algorithm 6.3, line 7: the vector `â ∈ ℝⁿ` with
`(â)_j = zᵀ D̂_j z`. -/
noncomputable def quadCoords {n p : ℕ} (D : Fin n → Matrix (Fin p) (Fin p) ℝ) (z : Fin p → ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j => z ⬝ᵥ (D j).mulVec z

/-- **Algorithm 6.3** (RECOVERDIRECTIONS) as an input–output relation.

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Algorithm 6.3, p.43 (PDF p.46): "Input: Symmetric matrices
(D̂_j)_{j∈[n]} of common dimension p ≥ 2, and confidence parameter δ. Output: Unit vectors û_1, …, û_p.
1 L ← log₂(1/δ); 2 Draw independent b_1, …, b_L ∼ Unif(S^{n−1}); 3 for ι = 1, …, L do
4 D̂(b_ι) ← Σ_{j=1}^n (b_ι)_j D̂_j; 5 Compute the eigenvalues ν̂_1^{(ι)} ≥ ⋯ ≥ ν̂_p^{(ι)} and corresponding
orthonormal eigenvectors ẑ_1^{(ι)}, …, ẑ_p^{(ι)} of D̂(b_ι); 6 ι⋆ ← arg max_{1≤ι≤L} min_{1≤i<p}
(ν̂_i^{(ι)} − ν̂_{i+1}^{(ι)}); 7 For i ∈ [p] and j ∈ [n], set (â_i)_j ← (ẑ_i^{(ι⋆)})ᵀ D̂_j ẑ_i^{(ι⋆)};
8 û_i ← â_i/‖â_i‖₂ for i ∈ [p]; 9 return (û_i)_{i∈[p]}."

`IsRecoverOutput D δ b u` says that `u` is an output of the routine on `(D, δ)` when the drawn
directions are `b 0, …, b (L − 1)`: for some eigendecompositions `(vals ι, Z ι)` of the `D̂(b_ι)`
(line 5), some trial `ι⋆` maximizes the minimum consecutive gap (line 6), and `u_i = â_i/‖â_i‖₂`
with `â_i = quadCoords D ẑ_i`, `(â_i)_j = ẑ_iᵀ D̂_j ẑ_i`, for the rows `ẑ_i` of `Z ι⋆` (lines 7–8).

**Formalization Note.**
* The directions are an explicit argument (a stream, of which the first `L` entries are read), so
  that "with probability at least `1 − δ`" is a statement about their law.
* The routine is a relation because line 5 does not fix the eigenvectors and line 6 does not fix the
  maximizer among ties; a statement about every output covers every choice.
* "`ι⋆` maximizes `min_{1≤i<p}`" is written without the minimum: for every trial `ι` some gap of `ι` is
  at most every gap of `ι⋆`. For `p ≥ 2` this is the same condition.
* Line 8 divides by `‖â_i‖₂`. When `â_i = 0` the quotient is undefined, and the routine is declared to
  "return unit vectors": in that case `u_i` may be any unit vector. -/
def IsRecoverOutput {n p : ℕ} (D : Fin n → Matrix (Fin p) (Fin p) ℝ) (δ : ℝ)
    (b : ℕ → EuclideanSpace ℝ (Fin n)) (u : Fin p → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ (vals : Fin (numTrials δ) → Fin p → ℝ) (Z : Fin (numTrials δ) → Matrix (Fin p) (Fin p) ℝ),
    (∀ ι : Fin (numTrials δ), IsEigDecomp (∑ j, b (ι : ℕ) j • D j) (vals ι) (Z ι)) ∧
    ∃ ιs : Fin (numTrials δ),
      (∀ ι, ∃ (i : Fin p) (hi : (i : ℕ) + 1 < p), ∀ (i' : Fin p) (hi' : (i' : ℕ) + 1 < p),
        vals ι i - vals ι ⟨i + 1, hi⟩ ≤ vals ιs i' - vals ιs ⟨i' + 1, hi'⟩) ∧
      ∀ i : Fin p,
        (quadCoords D (Z ιs i) ≠ 0 → u i = ‖quadCoords D (Z ιs i)‖⁻¹ • quadCoords D (Z ιs i)) ∧
        (quadCoords D (Z ιs i) = 0 → ‖u i‖ = 1)

end Supplement

end SelfSelReg


