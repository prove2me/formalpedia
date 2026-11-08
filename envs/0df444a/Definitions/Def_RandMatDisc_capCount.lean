-- Prove2me | Definitions.Def_RandMatDisc_capCount
-- name    : RandMatDisc_capCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:40:58.672296+00:00
-- url     : https://prove2.me/theorems/3c2f8c42-fec6-4cd4-ad5f-0ac80df40b70
-- title:
--   Cap counts, $K_q(v)$, the parameters $t,p$ and the norm event $\mathcal E_{\mathrm{norm}}$
-- statement:
--   Fix vectors $v_1,\dots,v_N\in\mathbb R^D$.
--
--   1. The **cap count** of a direction $u$ at level $t$ is $\#\{i\in[N]:\langle u,v_i\rangle\ge t\}$.
--   2. For $q\ge0$, the set of vectors produced with $q$ units of fractional coefficients is
--   $$K_q(v)=\Big\{\sum_i a_iv_i:\ 0\le a_i\le1,\ \sum_i a_i\le q\Big\}.$$
--   3. With $\alpha_d=N/D$, the section's parameters are
--   $$t=\tfrac12\sqrt{\log\alpha_d},\qquad p=\mathbb P(Z\ge t),\quad Z\sim\mathcal N(0,1).$$
--   4. For a $D\times N$ matrix $G=[g_1\cdots g_N]$ and constants $C_0,C_\alpha$, the **norm event** is
--   $$\mathcal E_{\mathrm{norm}}=\Big\{\|G\|_{\mathrm{op}}^2\le C_\alpha D,\ \max_{i\le N}\|g_i\|_2^2\le C_0D\Big\}.$$
--
--   These objects carry the geometric part of the analysis of the recenter-and-round algorithm: a uniform lower bound on cap counts lets a residual be cancelled by a fractional combination in $K_q$, and $\mathcal E_{\mathrm{norm}}$ controls the rounding noise.
--
--   **Formalization Note** $\log$ is the natural logarithm; $t>0$ exactly when $\alpha_d>1$. For $q<0$ the set $K_q(v)$ is empty; the paper only uses $q\ge0$. $\|G\|_{\mathrm{op}}$ is the $\ell_2$ operator norm of the matrix with columns $g_i$ (`Matrix.Norms.L2Operator`), and the maximum over columns is written as a bound for every column.
-- source:
--   Kızıldağ, Li, Stable and Online Algorithms for Random Matrix Discrepancy, arXiv:2610.01591 (held file sha256 889af7fc…), §3.1, p.16 (PDF p.18), eq. (13), (14); p.17 (PDF p.19), eq. (18); Lemma 3.5, p.18 (PDF p.20), eq. (20)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace RandMatDisc

/-- The cap count `#{i ∈ [N] : ⟨u, vᵢ⟩ ≥ t}`: the number of the vectors `v₁, …, v_N ∈ ℝ^ι` whose
projection on `u` is at least `t` (Kızıldağ, Li, arXiv:2610.01591, held file sha256 889af7fc…,
(14) and (17), pp.16–17, and Lemma 3.4, p.17). -/
noncomputable def capCount {ι : Type} [Fintype ι] {N : ℕ} (u : EuclideanSpace ℝ ι)
    (v : Fin N → EuclideanSpace ℝ ι) (t : ℝ) : ℕ :=
  (Finset.univ.filter fun i => t ≤ inner ℝ u (v i)).card

/-- The set `K_q(v) = {Σᵢ aᵢ vᵢ : 0 ≤ aᵢ ≤ 1, Σᵢ aᵢ ≤ q}` of vectors produced with `q` units of
fractional coefficients, eq. (18), p.17 (arXiv:2610.01591, sha256 889af7fc…). The paper defines it
for `q ≥ 0`; for `q < 0` the set is empty. -/
def Kq {ι : Type} [Fintype ι] {N : ℕ} (v : Fin N → EuclideanSpace ℝ ι) (q : ℝ) :
    Set (EuclideanSpace ℝ ι) :=
  {y | ∃ a : Fin N → ℝ, (∀ i, 0 ≤ a i ∧ a i ≤ 1) ∧ ∑ i, a i ≤ q ∧ ∑ i, a i • v i = y}

/-- The threshold `t = ½ √(log α_d)` of eq. (13), p.16 (arXiv:2610.01591), with `α_d = N/D`.

**Formalization Note.** `Real.log` and `Real.sqrt`; `t > 0` exactly when `α_d > 1`, which holds
for all large `D` whenever `N/D → α ≥ 2`. -/
noncomputable def tPar (N D : ℕ) : ℝ := (1 / 2) * Real.sqrt (Real.log ((N : ℝ) / D))

/-- The cap probability `p = P(Z ≥ t)` for `Z ∼ N(0, 1)`, eq. (13), p.16 (arXiv:2610.01591),
as a real number. -/
noncomputable def pPar (N D : ℕ) : ℝ := (gaussianReal 0 1).real (Set.Ici (tPar N D))

/-- The `D × N` matrix `G = [g₁ ⋯ g_N]` with columns `gᵢ ∈ ℝ^ι`. Its norm (with
`open scoped Matrix.Norms.L2Operator`) is the operator norm `‖G‖_op`. -/
def colMat {ι : Type} [Fintype ι] {N : ℕ} (G : Fin N → EuclideanSpace ℝ ι) :
    Matrix ι (Fin N) ℝ :=
  Matrix.of fun a i => G i a

/-- The norm event of Lemma 3.5, eq. (20), p.18 (arXiv:2610.01591, sha256 889af7fc…), with
constants `C₀` and `Cα`:
`E_norm = {‖G‖²_op ≤ Cα D, max_{i ≤ N} ‖gᵢ‖₂² ≤ C₀ D}`, `D = card ι`.

**Formalization Note.** `‖G‖_op` is the `L²` operator norm of `colMat G`
(`Matrix.Norms.L2Operator`); the maximum over the columns is written as a bound for every
column. -/
def normEvent {ι : Type} [Fintype ι] {N : ℕ} (C₀ Cα : ℝ) (G : Fin N → EuclideanSpace ℝ ι) :
    Prop :=
  ‖colMat G‖ ^ 2 ≤ Cα * Fintype.card ι ∧ ∀ i, ‖G i‖ ^ 2 ≤ C₀ * Fintype.card ι

end RandMatDisc


