-- Prove2me | Definitions.Def_DegenNRM_kappa1
-- name    : DegenNRM_kappa1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:39.637142+00:00
-- url     : https://prove2.me/theorems/a0bb3942-ef70-4942-8496-799070b50b37
-- title:
--   The constants $\bar a$, $\kappa_1$ of (15) and $r_{\max}$
-- statement:
--   Let
--   $$\bar a=\max_{j\in[n]}\big(\|a_j\|_2^2+2\big)^{1/2},\qquad \kappa_1=\max_{j\in[n]}\Big\{\frac1{p_j}\Big\}\cdot(m+2n)\cdot\bar a^{\,n},\qquad r_{\max}=\max_{j\in[n]}u_j.$$
--   $\kappa_1$ is the Lipschitz constant of Lemma 4 and the constant in the thresholds $2\kappa_1\sqrt{\log s/s}$ of Algorithm 2; $r_{\max}$ bounds the rewards.
--
--   **Formalization Note** The paper uses $\bar a$ in (15) and in the proof of Lemma 4 (p.43) but does not define it. $\bar a$ is read as the largest Euclidean norm of a column of the stacked matrix $[A;I_n;-I_n]$, the smallest number bounding every column of every square submatrix the proof ranges over; the alternative $\max_j\|a_j\|_2$ makes Lemma 4 false. Maxima over the finite type set are written as suprema.
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, (15), p.15; proof of Lemma 4, p.43; Theorem 1, p.15

import Mathlib
import Definitions.Def_DegenNRM_Instance

namespace DegenNRM

/-- **The constant `ā` of (15)** (Jiang, Ma & Zhang, arXiv:2210.07996v5, (15), p.15, and proof
of Lemma 4, p.43): `ā = max_j (‖a_j‖₂² + 2)^{1/2}`, the largest Euclidean norm of a column of
the stacked matrix `[A; I_n; -I_n]`.

**Formalization Note.** The paper uses `ā` in (15) and on p.43 ("|det(A′)| = Π‖a′_i‖₂ ≤ ā^{n′}
≤ āⁿ") but never defines it. This is the reading of the mission (R1): the smallest number that
bounds the column norms of every square submatrix of `[A; I_n; -I_n]` that the proof ranges
over. The alternative `max_j ‖a_j‖₂` makes Lemma 4 false. The maximum over the finite type set
is `⨆ j`. -/
noncomputable def abar {m n : ℕ} (inst : Instance m n) : ℝ :=
  ⨆ j : Fin n, Real.sqrt (∑ i, inst.a j i ^ 2 + 2)

/-- **The constant `κ₁` of (15)** (arXiv:2210.07996v5, (15), p.15):
`κ₁ = max_{j∈[n]} {1/p_j} · (m + 2n) · āⁿ`. It enters Algorithm 2 (its thresholds
`2κ₁ √(log s / s)`), Lemma 4 and Theorem 1. -/
noncomputable def kappa1 {m n : ℕ} (inst : Instance m n) : ℝ :=
  (⨆ j : Fin n, 1 / inst.p j) * ((m : ℝ) + 2 * n) * abar inst ^ n

/-- **`r_max = max_{j∈[n]} u_j`**, the upper bound of the reward (arXiv:2210.07996v5,
Theorem 1, p.15). -/
noncomputable def rmax {m n : ℕ} (inst : Instance m n) : ℝ :=
  ⨆ j : Fin n, inst.u j

end DegenNRM


