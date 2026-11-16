-- Prove2me | Definitions.Def_GaussProcSparsify_Optimal_Supplement_Junta
-- name    : GaussProcSparsify_Optimal_Supplement_Junta
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:19:45.711198+00:00
-- url     : https://prove2.me/theorems/ee7ae494-f781-47a1-a26f-cc6641ba8d8e
-- title:
--   Norms on arbitrary subspaces and their pullbacks
-- statement:
--   A $k$-junta norm on $\mathbb R^n$ is a function $\varphi$ for which there is a linear subspace $E\subseteq\mathbb R^n$ of dimension at most $k$ and a genuine norm $\nu$ on $E$ such that
--   $$\varphi(x)=\nu(\pi_E x).$$
--   Here $\pi_E$ is orthogonal projection in the fixed Euclidean inner product. The norm $\nu$ is represented by a real seminorm with trivial kernel; absolute homogeneity and subadditivity are the standard seminorm axioms. Neither the ambient Euclidean norm nor the Gaussian measure is changed. The pullback may vanish on $E^\perp$. This definition includes arbitrary subspaces rather than only coordinate subspaces.
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), §1.1.1, PDF p. 4 (printed p. 3), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Definitions.Def_GaussProcSparsify_Optimal_Gaussian

open MeasureTheory ProbabilityTheory

namespace GaussProcSparsify.Optimal.Supplement

/-- A norm pulled back from an arbitrary subspace of dimension at most k.
The ambient Euclidean structure and Gaussian law are unchanged. PDF p. 4. -/
def IsJuntaNorm {n : ℕ} (k : ℕ) (φ : Vec n → ℝ) : Prop :=
  ∃ E : Submodule ℝ (Vec n), Module.finrank ℝ E ≤ k ∧
    ∃ ν : Seminorm ℝ E, (∀ x : E, ν x = 0 → x = 0) ∧
      ∀ x, φ x = ν (E.orthogonalProjectionOnto x)

end GaussProcSparsify.Optimal.Supplement


