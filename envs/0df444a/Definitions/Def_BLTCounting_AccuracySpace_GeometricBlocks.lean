-- Prove2me | Definitions.Def_BLTCounting_AccuracySpace_GeometricBlocks
-- name    : BLTCounting_AccuracySpace_GeometricBlocks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:02.287139+00:00
-- url     : https://prove2.me/theorems/523a805b-a2f4-43ea-950f-15f1265e38c5
-- title:
--   Geometric blocks, harmonic masses, the compression matrix $Q$, and the parameters of Section 4
-- statement:
--   Fix an integer $R$ and a width $h$. Section 4 of the paper partitions an integer range into blocks of equal logarithmic width.
--
--   1. The **block endpoints** are $t_i=e^{\xi_i}$ with $\xi_i=\log R+ih$.
--   2. The **blocks** are $S_i=\{r\in\mathbb Z:t_i\le r<t_{i+1}\}$, and $S=\bigcup_{i<K}S_i$. Since $t_i>0$, every $r\in S_i$ is a positive integer.
--   3. The **harmonic mass** of a block is $w_i=\sum_{r\in S_i}1/r$.
--   4. The **matrix $Q$** has rows indexed by $S$ and columns by $i<K$, with $Q[r,i]=(rw_i)^{-1/2}$ for $r\in S_i$ and $Q[r,i]=0$ otherwise.
--   5. The **compression** of a sequence $a$ is $F(a)=Q^*\widehat H_S(a)Q$.
--   6. Section 4 computes its parameters from $m$ and $\eta$ by
--   $$L=\log m,\quad h=\frac{\eta}{L},\quad R=\Bigl\lceil\frac{L^4}{\eta^2}\Bigr\rceil,\quad \ell=\log\frac mR,\quad K=\Bigl\lfloor\frac{\ell}{h}\Bigr\rfloor.$$
--
--   The compression turns the weighted Hankel matrix into one that is close to the Toeplitz matrix $V_h$.
--
--   **Formalization Note.** The identity $Q^*Q=I$ is not built into the definition. The verification file proves it sorry-free when $h>0$ and all block masses are positive.
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, equation (28), printed p. 23 (PDF p. 24); equation (32) and Claim 4.4 preamble, printed p. 26 (PDF p. 27); equation (33), printed p. 27 (PDF p. 28)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_Sequences

open Matrix

namespace BLTCounting.AccuracySpace

/-- The block endpoint `t_i = e^{ξ_i}`, `ξ_i = log R + ih` (§4, PDF p. 27). -/
noncomputable def blockPoint (R : ℕ) (h : ℝ) (i : ℕ) : ℝ :=
  Real.exp (Real.log R + i * h)

/-- The geometric block `S_i = {r ∈ ℤ : t_i ≤ r < t_{i+1}}`, equation (32), PDF p. 27. Since `t_i > 0`,
every such `r` is a positive integer, and `t_i ≤ r < t_{i+1}` is exactly
`⌈t_i⌉ ≤ r < ⌈t_{i+1}⌉`. -/
noncomputable def block (R : ℕ) (h : ℝ) (i : ℕ) : Finset ℕ :=
  Finset.Ico ⌈blockPoint R h i⌉₊ ⌈blockPoint R h (i + 1)⌉₊

/-- The harmonic block mass `w_i = ∑_{r ∈ S_i} 1/r` (PDF p. 27). -/
noncomputable def blockMass (R : ℕ) (h : ℝ) (i : ℕ) : ℝ :=
  ∑ r ∈ block R h i, ((r : ℝ))⁻¹

/-- The index set `S = ⋃_{i < K} S_i`, equation (32), PDF p. 27. -/
noncomputable def blockUnion (R : ℕ) (h : ℝ) (K : ℕ) : Finset ℕ :=
  (Finset.range K).biUnion (block R h)

/-- The matrix `Q ∈ ℝ^{|S|×K}` of equation (33), PDF p. 28: `Q[r, i] = (r w_i)^{-1/2}` for `r ∈ S_i`,
and `0` otherwise, embedded in `ℂ`. That `Q* Q = I` is not built in. -/
noncomputable def blockIsometry (R : ℕ) (h : ℝ) (K : ℕ) : Matrix (blockUnion R h K) (Fin K) ℂ :=
  Matrix.of fun r i =>
    if (r : ℕ) ∈ block R h (i : ℕ) then
      (((Real.sqrt (((r : ℕ) : ℝ) * blockMass R h (i : ℕ)))⁻¹ : ℝ) : ℂ)
    else 0

/-- The compressed matrix `F(a) = Q* Ĥ_S(a) Q` for the block construction (PDF pp. 27–28). -/
noncomputable def blockCompression (R : ℕ) (h : ℝ) (K : ℕ) (a : ℕ → ℂ) : Matrix (Fin K) (Fin K) ℂ :=
  (blockIsometry R h K)ᴴ * weightedHankel (blockUnion R h K) a * blockIsometry R h K

/-- Section 4's width `h = η / L`, `L = log m`, equation (28), PDF p. 24. -/
noncomputable def sectionH (m : ℕ) (η : ℝ) : ℝ :=
  η / Real.log m

/-- Section 4's offset `R = ⌈L⁴ / η²⌉`, `L = log m`, equation (28), PDF p. 24. -/
noncomputable def sectionR (m : ℕ) (η : ℝ) : ℕ :=
  ⌈Real.log m ^ 4 / η ^ 2⌉₊

/-- Section 4's block count `K = ⌊ℓ / h⌋`, `ℓ = log(m / R)` (PDF p. 27). -/
noncomputable def sectionK (m : ℕ) (η : ℝ) : ℕ :=
  ⌊Real.log ((m : ℝ) / sectionR m η) / sectionH m η⌋₊

end BLTCounting.AccuracySpace


