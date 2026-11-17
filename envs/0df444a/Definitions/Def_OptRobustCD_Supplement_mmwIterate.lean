-- Prove2me | Definitions.Def_OptRobustCD_Supplement_mmwIterate
-- name    : OptRobustCD_Supplement_mmwIterate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:51:32.256645+00:00
-- url     : https://prove2.me/theorems/956991c6-7923-4f03-8285-d7ce280f1046
-- title:
--   Matrix multiplicative weights iterate $X_t=e^{S_t}/\operatorname{Tr}e^{S_t}$, $S_t=-\eta\sum_{s<t}H_s$
-- statement:
--   Let $\eta\in\mathbb R$ and let $H_1,H_2,\dots$ be real $n\times n$ matrices. For an integer $t\ge 1$ put
--   $$
--   S_t=-\eta\sum_{1\le s<t}H_s,\qquad X_t=\frac{e^{S_t}}{\operatorname{Tr}e^{S_t}},
--   $$
--   where $e^{S}=\sum_{k\ge0}S^k/k!$ is the matrix exponential. In particular $S_1=0$ and $X_1=I/n$.
--
--   When the $H_s$ are symmetric, $S_t$ is symmetric, $\operatorname{Tr}e^{S_t}$ is the sum of the exponentials of its eigenvalues (so positive), and $X_t$ is a density matrix: the Gibbs state of $S_t$. These are the iterates of the matrix multiplicative weights method with step size $\eta$ and loss matrices $H_s$; Theorem 8.3 compares them with the points $\widetilde X_t$ at which subgradients are actually computed.
--
--   **Formalization Note** The sequence $H$ is indexed by $\mathbb N$ with the paper's 1-based indices; $H_0$ never enters. The exponential is Mathlib's `NormedSpace.exp`, the sum of the exponential series. Division by the trace is multiplication by its inverse; the paper uses $X_t$ only for symmetric $H_s$, where the trace is positive.
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Theorem 8.3, p.40 (pdf p.42)

import Mathlib

namespace OptRobustCD

namespace Supplement

open Finset

/-- **The exponent `S_t = −η ∑_{s<t} H_s`** of Theorem 8.3. Hopkins, Hua, Mohanty, Rajaraman,
Steurer, *Optimal Robust Community Detection*, STOC 2027 submission (manuscript of November 3, 2026,
sha256 3d287d54…), Theorem 8.3, p.40 (pdf p.42).

**Formalization Note.** The matrices are indexed by `ℕ` with the paper's 1-based indices: the sum
runs over `s ∈ {1, …, t − 1}` (`Finset.Ico 1 t`), so `S_1 = 0`. Values `H s` with `s = 0` never
enter. -/
def mmwExponent {n : ℕ} (η : ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (t : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  -η • ∑ s ∈ Ico 1 t, H s

/-- **The matrix-multiplicative-weights iterate `X_t = e^{S_t} / Tr e^{S_t}`** of Theorem 8.3.
Hopkins, Hua, Mohanty, Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027
submission (manuscript of November 3, 2026, sha256 3d287d54…), Theorem 8.3, p.40 (pdf p.42):
"For `1 ⩽ t ⩽ T`, define `S_t = −η ∑_{s<t} H_s`, `X_t = e^{S_t} / Tr e^{S_t}`."

**Formalization Note.** `e^{·}` is the matrix exponential `NormedSpace.exp` (the sum of the
exponential series, which does not depend on a choice of matrix norm). When every `H_s` is
symmetric, `S_t` is symmetric, `Tr e^{S_t}` is the sum of the exponentials of its eigenvalues, hence
positive, and `X_t` is a density matrix; the paper uses `X_t` only in that case. Division is
multiplication by the inverse trace. -/
noncomputable def mmwIterate {n : ℕ} (η : ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (t : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (NormedSpace.exp (mmwExponent η H t)).trace⁻¹ • NormedSpace.exp (mmwExponent η H t)

end Supplement

end OptRobustCD


