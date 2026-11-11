-- Prove2me | Definitions.Def_SpectralFeedback_pairAtom
-- name    : SpectralFeedback_pairAtom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:27:19.387342+00:00
-- url     : https://prove2.me/theorems/8740c1d0-1e49-40bc-92c7-50edfa5b6f51
-- title:
--   Spectral basis, active matrix $R_{[q]}$, tail, paired spectrum $c$ and reverse-paired atoms $T_\pm$
-- statement:
--   Let $R\in\mathbb C^{d\times d}$ be Hermitian with decreasing eigenvalues $\lambda_1\ge\dots\ge\lambda_d$ (padded by zeros), and fix $s\ge1$.
--
--   1. A **decreasing spectral basis** of $R$ is a unitary $U$ with $R=U\,\mathrm{diag}(\lambda_1,\dots,\lambda_d)\,U^*$; its columns $e_1,\dots,e_d$ are orthonormal eigenvectors, $Re_j=\lambda_je_j$.
--   2. The **active matrix** keeps the first $q$ eigenvalues with their original mass: $R_{[q]}=\sum_{j\le q}\lambda_je_je_j^*$. The **tail beyond $2s$** is $\sum_{j>2s}\lambda_je_je_j^*$.
--   3. The **paired spectrum** is $c\in\mathbb R^s$,
--   $$
--   c_i=\lambda_i+\lambda_{2s+1-i},\qquad 1\le i\le s .
--   $$
--   It need not be decreasing.
--   4. The **reverse-paired atoms** are
--   $$
--   T_\pm=\sum_{i=1}^s v_{i,\pm}v_{i,\pm}^*,\qquad v_{i,\pm}=\frac{\sqrt{\lambda_i}\,e_i\pm\sqrt{\lambda_{2s+1-i}}\,e_{2s+1-i}}{\sqrt2},
--   $$
--   where coordinates beyond dimension $d$ are omitted.
--
--   These are the explicit common optimizer of Theorem H.2 and the objects of Lemma H.1.
--
--   **Formalization Note** Indices are 0-based: entry $i$ of $c$ (`pairedVec R s i`) is $\lambda_{i+1}+\lambda_{2s-i}$, and $v_i$ pairs coordinate $i$ with coordinate $2s-1-i$; the natural-number subtraction never truncates because $i<s$. The atoms are written $T=U\bigl(\sum_i v_iv_i^*\bigr)U^*$ with $v_i$ given by its coordinates in the basis $U$; coordinates $\ge d$ do not exist in `Fin d`, which is the paper's omission. The sign is a real parameter $\sigma$ (`pairAtom R U s 1` is $T_+$, `pairAtom R U s (-1)` is $T_-$). Under repeated eigenvalues the basis is not unique, and statements quantify over every such $U$.
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), Lemma H.1, p.108 (PDF p.110); Theorem H.2, p.109 (PDF p.111); Theorem F.4, (F.5), p.94 (PDF p.96)

import Mathlib
import Definitions.Def_SpectralFeedback_eigDesc

namespace SpectralFeedback

/-- **A decreasing spectral basis** of a Hermitian `R ∈ ℂ^{d×d}` (Qi, *Spectral Structure and Exact
Arithmetic of Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), Theorem 4.2, p.6
(PDF p.8): "in a spectral basis"; Theorem F.4, p.94: "In a decreasing spectral basis"; Theorem H.2,
p.109): a unitary `U` with `R = U · diag(λ₁(R), …, λ_d(R)) · U*`.

The `j`-th column of `U` (0-based) is the unit eigenvector `e_{j+1}` of `λ_{j+1}(R)`. Under repeated
eigenvalues the basis is not unique; statements quantify over every such `U`. -/
def IsSortedEigenbasis {d : ℕ} (R U : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
    R = U * Matrix.diagonal (fun j : Fin d => ((eigDesc R (j : ℕ) : ℝ) : ℂ)) * star U

/-- **The active matrix `R_{[q]}`** (Qi, manuscript (Nov. 2026), Lemma H.1, p.108 (PDF p.110): "let
`R_{[q]}` retain its first `q` eigenvalues with their original mass"): in the decreasing spectral
basis `U`, `R_{[q]} = ∑_{j ≤ q} λ_j(R) e_j e_j*`. -/
noncomputable def activePart {d : ℕ} (R U : Matrix (Fin d) (Fin d) ℂ) (q : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  U * Matrix.diagonal (fun j : Fin d => if (j : ℕ) < q then ((eigDesc R (j : ℕ) : ℝ) : ℂ) else 0) *
    star U

/-- **The tail beyond `2s`** (Qi, manuscript (Nov. 2026), Theorem H.2, p.109 (PDF p.111): "Add the
tail beyond `2s` to `T₊` for the full problem"; Theorem F.4, (F.5), p.94: `∑_{i>2s} λ_i e_i e_i*`):
in the decreasing spectral basis `U`, `∑_{j > 2s} λ_j(R) e_j e_j*` (zero when `d ≤ 2s`). -/
noncomputable def tailPart {d : ℕ} (R U : Matrix (Fin d) (Fin d) ℂ) (s : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  U * Matrix.diagonal
      (fun j : Fin d => if 2 * s ≤ (j : ℕ) then ((eigDesc R (j : ℕ) : ℝ) : ℂ) else 0) * star U

/-- **The paired spectrum `c`** (Qi, *Spectral Structure and Exact Arithmetic of Finite-Feedback
Measurement Discrimination*, manuscript (Nov. 2026), Theorem H.2, p.109 (PDF p.111)):
`c_i = λ_i + λ_{2s+1−i}`, `1 ≤ i ≤ s`, where `λ₁ ≥ ⋯ ≥ λ_{2s} ≥ 0` are the first `2s`
eigenvalues of `R`, padded by zeros.

**Formalization Note** 0-based: entry `i : Fin s` is `λ_{i+1} + λ_{2s−i}`, i.e.
`eigDesc R i + eigDesc R (2s − 1 − i)`; the natural-number subtraction never truncates since
`i < s`. The vector need not be decreasing. -/
noncomputable def pairedVec {d : ℕ} (R : Matrix (Fin d) (Fin d) ℂ) (s : ℕ) : Fin s → ℝ :=
  fun i => eigDesc R (i : ℕ) + eigDesc R (2 * s - 1 - (i : ℕ))

/-- The coordinates of the paired vector `v_{i,σ}` in the spectral basis (Qi, manuscript
(Nov. 2026), Theorem H.2, p.109 (PDF p.111)):
`v_{i,±} = (√λ_i e_i ± √λ_{2s+1−i} e_{2s+1−i}) / √2`, with sign `σ = ±1`; coordinates beyond
dimension `d` are omitted (they do not occur in `Fin d`). 0-based: `i : Fin s` pairs coordinate `i`
with coordinate `2s − 1 − i`. -/
noncomputable def pairVec {d : ℕ} (R : Matrix (Fin d) (Fin d) ℂ) (s : ℕ) (σ : ℝ) (i : Fin s) :
    Fin d → ℂ :=
  fun j => ((((if (j : ℕ) = (i : ℕ) then Real.sqrt (eigDesc R (i : ℕ)) else 0) +
      σ * (if (j : ℕ) = 2 * s - 1 - (i : ℕ) then Real.sqrt (eigDesc R (2 * s - 1 - (i : ℕ)))
        else 0)) / Real.sqrt 2 : ℝ) : ℂ)

/-- **The reverse-paired atoms `T_±`** (Qi, *Spectral Structure and Exact Arithmetic of
Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), Theorem H.2, p.109 (PDF p.111);
Theorem 4.2, p.6; (F.5), p.94):
`T_± = ∑_{i=1}^s v_{i,±} v_{i,±}*`, `v_{i,±} = (√λ_i e_i ± √λ_{2s+1−i} e_{2s+1−i})/√2`,
written in the decreasing spectral basis `U` (columns `e_j`). `pairAtom R U s 1` is `T₊` and
`pairAtom R U s (-1)` is `T₋`.

**Formalization Note** `U * (∑ᵢ vᵢ vᵢ*) * U*` is `∑ᵢ (U vᵢ)(U vᵢ)*`, i.e. the paper's vectors
expressed in the basis `e_j = U e_j^{std}`. The sign is a real parameter; the mission uses `±1`. -/
noncomputable def pairAtom {d : ℕ} (R U : Matrix (Fin d) (Fin d) ℂ) (s : ℕ) (σ : ℝ) :
    Matrix (Fin d) (Fin d) ℂ :=
  U * (∑ i : Fin s, Matrix.vecMulVec (pairVec R s σ i) (star (pairVec R s σ i))) * star U

end SpectralFeedback


