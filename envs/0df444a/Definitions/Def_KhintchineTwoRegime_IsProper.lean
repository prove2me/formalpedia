-- Prove2me | Definitions.Def_KhintchineTwoRegime_IsProper
-- name    : KhintchineTwoRegime_IsProper
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:39.586898+00:00
-- url     : https://prove2.me/theorems/d1052c24-6511-4508-a76b-4fff0cf61088
-- title:
--   Proper vectors: the chamber $\mathfrak C=\{\omega_1\ge\cdots\ge\omega_n\ge0,\ \|\omega\|_2=1\}$
-- statement:
--   A vector $\omega\in\mathbb R^n$ is **proper** if it lies in the chamber
--   $$
--   \mathfrak C=\{\omega:\ \omega_1\ge\omega_2\ge\cdots\ge\omega_n\ge0,\ \|\omega\|_2=1\}.
--   $$
--   Since $K_n$ is invariant under sign changes and permutations of the coordinates, every unit vector can be brought into $\mathfrak C$ without changing $K_n$; the paper works in this chamber throughout §2.
--
--   **Formalization Note** The ordering is `Antitone ω` on `Fin n` (0-based), and the norm is the Euclidean norm $\sqrt{\sum_i\omega_i^2}$ (the published definition `HighDimProb.SparseRecovery.l2Norm`).
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §2, p.4 (also §1.1, p.2)

import Mathlib
import Definitions.Def_HighDimProb_SparseRecovery_L2Norm
open HighDimProb.SparseRecovery (l2Norm)

namespace KhintchineTwoRegime

/-- `ω` is *proper*: it lies in the chamber
`C = {ω : ω₁ ≥ ω₂ ≥ ⋯ ≥ ωₙ ≥ 0, ‖ω‖₂ = 1}` (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §2, p.4).

**Formalization Note** `Antitone ω` on `Fin n` is `ω₁ ≥ ω₂ ≥ ⋯ ≥ ωₙ` (0-based indices);
the norm is the Euclidean norm `l2Norm`. -/
def IsProper {n : ℕ} (ω : Fin n → ℝ) : Prop :=
  Antitone ω ∧ (∀ i, 0 ≤ ω i) ∧ l2Norm ω = 1

end KhintchineTwoRegime


