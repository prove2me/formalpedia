-- Prove2me | Definitions.Def_CommutativeRankNC_Approximation_Scaling
-- name    : CommutativeRankNC_Approximation_Scaling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:27.660276+00:00
-- url     : https://prove2.me/theorems/1a4c4992-0b0f-4cd4-8e60-39825052904f
-- title:
--   Operator scaling and finite fourth moments
-- statement:
--   For a complex matrix tuple $A=(A_i)$ set $M=\sum_iA_iA_i^*$, $N=\sum_iA_i^*A_i$, and
--
--   $$\operatorname{ds}(A)=\|M-I\|_F^2+\|N-I\|_F^2.$$
--
--   Dimension non-decreasing means $\dim\operatorname{span}\bigcup_iD_i(U)\ge\dim U$ for every complex subspace $U$. Scalable means that invertible complex left and right maps make $\operatorname{ds}$ arbitrarily small. The separate full-rank-span predicate expresses the standing assumption of subsection 3.1. For signs $\epsilon$, define $S=\sum_i\epsilon_iA_i$ and $Y=\operatorname{Re}\operatorname{Tr}((S^*S)^2)$. All probability sums are finite. The shared constant is $c_0=3/25$, as fixed on p.14.
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), §3.1, pp.12–14; Appendix p.31; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_Signs

noncomputable section

namespace CommutativeRankNC.Approximation

abbrev CMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def leftMoment {n m : ℕ} (A : Fin m → CMatrix n) : CMatrix n :=
  ∑ i, A i * (A i).conjTranspose

def rightMoment {n m : ℕ} (A : Fin m → CMatrix n) : CMatrix n :=
  ∑ i, (A i).conjTranspose * A i

def frobeniusSquared {n : ℕ} (M : CMatrix n) : ℝ := ∑ i, ∑ j, Complex.normSq (M i j)

def doublyStochasticDistance {n m : ℕ} (A : Fin m → CMatrix n) : ℝ :=
  frobeniusSquared (leftMoment A - 1) + frobeniusSquared (rightMoment A - 1)

def DimensionNondecreasing {n m : ℕ} (D : Fin m → CMatrix n) : Prop :=
  ∀ U : Submodule ℂ (Fin n → ℂ), Module.finrank ℂ U ≤
    Module.finrank ℂ (Submodule.span ℂ
      {v | ∃ i : Fin m, ∃ u ∈ U, (D i).mulVec u = v})

def Scalable {n m : ℕ} (D : Fin m → CMatrix n) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ L R : (CMatrix n)ˣ,
    doublyStochasticDistance (fun i => (L : CMatrix n) * D i * (R : CMatrix n)) ≤ η

/-- The standing full-rank assumption in subsection 3.1 only. -/
def HasFullRankSpan {n m : ℕ} (A : Fin m → CMatrix n) : Prop :=
  ∃ a : Fin m → ℂ, IsUnit (∑ i, a i • A i)

def signedMatrix {n m : ℕ} (A : Fin m → CMatrix n) (e : SignVector m) : CMatrix n :=
  ∑ i, (signValue (e i) : ℂ) • A i

def fourthMoment {n m : ℕ} (A : Fin m → CMatrix n) (e : SignVector m) : ℝ :=
  let S := signedMatrix A e
  (Matrix.trace ((S.conjTranspose * S) ^ 2)).re

def cZero : ℝ := 3 / 25

end CommutativeRankNC.Approximation


