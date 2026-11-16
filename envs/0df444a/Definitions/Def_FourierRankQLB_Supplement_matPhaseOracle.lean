-- Prove2me | Definitions.Def_FourierRankQLB_Supplement_matPhaseOracle
-- name    : FourierRankQLB_Supplement_matPhaseOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:13:15.15809+00:00
-- url     : https://prove2.me/theorems/cc8579f9-2ee2-4279-8af5-271dff95256f
-- title:
--   Matrix phase oracle $(P_M\psi)(v,u) = e^{i u^\top M v}\psi(v,u)$ (Eq. (11))
-- statement:
--   Let $M$ be a real $n\times n$ matrix. On the register $L^2(Y,\nu)\otimes W$ whose labels $y$ represent query pairs $\iota(y) = (v,u) \in \mathbb R^n\times\mathbb R^n$, with $\iota$ measurable, the **matrix phase oracle** of $M$ is
--
--   $$
--   (P_M\psi)(y) = e^{i\,u^\top M v}\,\psi(y), \qquad (v,u) = \iota(y).
--   $$
--
--   The paper's register is $L^2(\mathbb R^n\times\mathbb R^n;\mathbb C)$ (that is, $Y = \mathbb R^n\times\mathbb R^n$ with Lebesgue measure and $\iota$ the identity), and Remark 3.6 extends every result to any σ-finite label space, for example a finite set of labels with counting measure. The phase $u^\top M v = \operatorname{Tr}((uv^\top)^\top M)$ has a rank-one frequency matrix, which is what the Fourier-rank method exploits.
--
--   **Formalization Note** $M$ is an arbitrary real matrix, so the same definition gives the oracle of $Q \in O(n)$ (Theorem 3.5) and of $S_Q = (Q+Q^\top)/2$ (Theorem 3.9). It is the phase multiplication with $\theta(y) = u^\top M v$.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §2.4, Eq. (11), p.15; Remark 3.6, p.20

import Mathlib
import Definitions.Def_FourierRankQLB_Supplement_phaseMul

open MeasureTheory Matrix

namespace FourierRankQLB

namespace Supplement

/-- The matrix phase oracle `(P_M ψ)(v, u) = e^{i uᵀ M v} ψ(v, u)` of Eq. (11), for a real `n × n`
matrix `M`, on the register `L²(Y, ν) ⊗ W` whose labels `y` represent the query pairs
`ι y = (v, u) ∈ ℝⁿ × ℝⁿ`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (11), p. 15 and Remark 3.6, p. 20.

**Formalization Note.** The paper's register is `L²(ℝⁿ × ℝⁿ)` (`Y = ℝⁿ × ℝⁿ`, Lebesgue measure,
`ι = id`); Remark 3.6 allows any σ-finite label space, for example a finite set of labels with
counting measure. The workspace `W` is untouched. `M` is a general real matrix, so the same
definition serves `M = Q ∈ O(n)` (Theorem 3.5) and `M = S_Q` (Theorem 3.9). -/
noncomputable def matPhaseOracle {n : ℕ} {Y : Type} [MeasurableSpace Y] (ν : Measure Y)
    (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ι : Y → (Fin n → ℝ) × (Fin n → ℝ)) (hι : Measurable ι) (M : Matrix (Fin n) (Fin n) ℝ) :
    Lp W 2 ν ≃ₗᵢ[ℂ] Lp W 2 ν :=
  phaseMul ν W (fun y => (ι y).2 ⬝ᵥ (M *ᵥ (ι y).1))
    ((continuous_snd.dotProduct (continuous_const.matrix_mulVec continuous_fst)).measurable.comp hι)

end Supplement

end FourierRankQLB


