-- Prove2me | Definitions.Def_RandomGateDesign_MasterBound_Moments
-- name    : RandomGateDesign_MasterBound_Moments
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:21.621439+00:00
-- url     : https://prove2.me/theorems/e85dd610-f4d0-4413-8dc1-27949e8a6ff9
-- title:
--   Mixed tensor moments, exact unitary designs, highest-weight indices and Weyl dimensions
-- statement:
--   For a unitary matrix $U\in U(d)$, let $U^{t,t}=U^{\otimes t}\otimes\overline U^{\otimes t}$, with all ordinary tensor factors preceding the conjugate factors. The moment operator of a measure $\nu$ is
--
--   $$T_{\nu,t}=\int_{U(d)} U^{t,t}\,d\nu(U).$$
--
--   For $S$ sampled gates $U_1,\ldots,U_S$, the empirical moment is $S^{-1}\sum_{k=1}^{S}U_k^{t,t}$; when $S=0$ the Lean definition returns zero. The design distance is the operator norm $\delta(\nu,t)=\|T_{\nu,t}-T_{\mu,t}\|$. A Haar probability measure is bi-invariant, and an exact $t$-design is a probability measure whose $t$th mixed moment equals the Haar moment.
--
--   The finite set $\Lambda_t$ consists of nonzero decreasing integer $d$-tuples $\lambda$ with $\sum_i\lambda_i=0$ and $\sum_i\max(\lambda_i,0)\le t$. Each coordinate is bounded by $t$ under these conditions. The Weyl factor is
--
--   $$d_\lambda=\prod_{1\le i<j\le d}\frac{\lambda_i-\lambda_j+j-i}{j-i}.$$
--
--   These definitions fix the objects appearing in Theorem 1 and in the representation decomposition.
-- source:
--   Dulian & Sawicki, Matrix concentration inequalities and efficiency of random universal sets of quantum gates, arXiv:2202.05371v3, pp. 2, 10–12, 19; eqs. (17), (20), (23)

import Mathlib
import Definitions.Def_TroppMatrixConcentration_probability

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace RandomGateDesign.MasterBound

abbrev U (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ

abbrev MIdx (d t : ℕ) := (Fin t → Fin d) × (Fin t → Fin d)

def tensorMoment {d : ℕ} (t : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (MIdx d t) (MIdx d t) ℂ :=
  fun p q => (∏ a : Fin t, A (p.1 a) (q.1 a)) *
    (∏ b : Fin t, star (A (p.2 b) (q.2 b)))

def momentOp {d : ℕ} (ν : Measure (U d)) (t : ℕ) :
    Matrix (MIdx d t) (MIdx d t) ℂ :=
  ∫ g, tensorMoment t (g : Matrix (Fin d) (Fin d) ℂ) ∂ν

def empiricalMoment {d S : ℕ} (Us : Fin S → U d) (t : ℕ) :
    Matrix (MIdx d t) (MIdx d t) ℂ :=
  (S : ℂ)⁻¹ • ∑ k : Fin S, tensorMoment t (Us k : Matrix (Fin d) (Fin d) ℂ)

def designDist {d : ℕ} (μ ν : Measure (U d)) (t : ℕ) : ℝ :=
  TroppMatrixConcentration.spectralNorm (momentOp ν t - momentOp μ t)

def IsHaarProb {d : ℕ} (μ : Measure (U d)) : Prop :=
  IsProbabilityMeasure μ ∧ μ.IsMulLeftInvariant ∧ μ.IsMulRightInvariant

def IsExactDesign {d : ℕ} (μ ν : Measure (U d)) (t : ℕ) : Prop :=
  IsProbabilityMeasure ν ∧ momentOp ν t = momentOp μ t

def Lambda (d t : ℕ) : Finset (Fin d → ℤ) :=
  (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(t : ℤ)) (t : ℤ))).filter
    (fun l => l ≠ 0 ∧ Antitone l ∧ (∑ i, l i) = 0 ∧
      (∑ i, max (l i) 0) ≤ (t : ℤ))

def weylDim {d : ℕ} (l : Fin d → ℤ) : ℝ :=
  ∏ i : Fin d, ∏ j : Fin d,
    if i < j then
      (((l i - l j : ℤ) : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) /
        (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ))
    else 1

end RandomGateDesign.MasterBound


