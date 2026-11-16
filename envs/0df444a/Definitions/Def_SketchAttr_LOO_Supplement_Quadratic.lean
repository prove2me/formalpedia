-- Prove2me | Definitions.Def_SketchAttr_LOO_Supplement_Quadratic
-- name    : SketchAttr_LOO_Supplement_Quadratic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:50:08.648221+00:00
-- url     : https://prove2.me/theorems/87db1bec-a93c-404c-8d7f-d330718033bf
-- title:
--   Real Gaussian Gram matrices and the quadratic oracle
-- statement:
--   For a real matrix $G\in\mathbb R^{r\times n}$, let $\operatorname{Gram}(G)=G^\top G$, with independent standard $N(0,1)$ entries under the matrix law. For a real square matrix $A$, its Frobenius norm is the published order-two tensor norm after embedding its entries into $\mathbb C$. Define
--
--   $$\phi_A(w)=\sum_{i,j}A_{ij}w_iw_j,\qquad \alpha(B)=B^2/16.$$
--
--   The real matrix-vector oracle returns $Ax$. The quadratic oracle accepts every $w,g\in\mathbb C^n$ and every integer $N\ge1$ and returns $\phi_A(w)$ together with $D_g^r\nabla\phi_A(w)$ for $0\le r\le N$. A sequence stores these vector responses, with zero padding beyond the requested degree. The free value and gradient at zero are the fixed pair $(0,0)$, so they carry no hidden input information. Query and terminal maps receive no matrix or circuit encoding. The two oracle specializations instantiate the unrestricted adaptive interface, and squared diagonal error means $\sum_i|\widehat L_i-A_{ii}|^2$.
--
--   This fixes the real Gaussian normalization and preserves the transpose convention; no complex conjugation occurs in the quadratic polynomial.
-- source:
--   Chris Liaw, Aranyak Mehta, Grigoris Velegkas, Felix Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (October 2026), PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2, Section 5.3, pp. 19–20; Proposition C.1 and Lemma C.2, p. 29

import Mathlib
import Definitions.Def_SketchAttr_LOO_Taylor
import Definitions.Def_SketchAttr_LOO_Stability
import Definitions.Def_SketchAttr_LOO_Supplement_Adaptive

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SketchAttr.LOO.Supplement

instance realMatrixMeasurableSpace (r n : ℕ) :
    MeasurableSpace (Matrix (Fin r) (Fin n) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin r → Fin n → ℝ))

abbrev RealMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev RealVector (n : ℕ) := Fin n → ℝ

noncomputable def matrixTensor {n : ℕ} (A : RealMatrix n) : Tensor n 2 :=
  fun j => (A (j 0) (j 1) : ℂ)

/-- The published order-two tensor norm, with the real matrix embedded in C. -/
noncomputable def matrixFrobNorm {n : ℕ} (A : RealMatrix n) : ℝ :=
  frobNorm (matrixTensor A)

noncomputable def realGaussianMatrix (r n : ℕ) :
    Measure (Matrix (Fin r) (Fin n) ℝ) :=
  Measure.pi fun _ : Fin r => Measure.pi fun _ : Fin n => gaussianReal 0 1

noncomputable def gram {r n : ℕ} (G : Matrix (Fin r) (Fin n) ℝ) : RealMatrix n :=
  fun i j => ∑ a, G a i * G a j

/-- No conjugation: the source uses transpose, not conjugate transpose. -/
noncomputable def quadratic {n : ℕ} (A : RealMatrix n) (w : Vec n) : ℂ :=
  ∑ i, ∑ j, (A i j : ℂ) * w i * w j

noncomputable def quadraticProfile : StabilityProfile :=
  fun B => ENNReal.ofReal (B.val ^ 2 / 16)

abbrev MatrixProcedure (Seed : Type*) [MeasurableSpace Seed] (n q : ℕ) :=
  AdaptiveProcedure Seed (RealVector n) (RealVector n) (RealVector n) q

noncomputable def matrixEstimate {Seed : Type*} [MeasurableSpace Seed] {n q : ℕ}
    (P : MatrixProcedure Seed n q) (A : RealMatrix n) (seed : Seed) : RealVector n :=
  adaptiveOutput P (fun x => A.mulVec x) seed

noncomputable def squaredDiagonalError {n : ℕ} (v : RealVector n) (A : RealMatrix n) : ℝ :=
  ∑ i, |v i - A i i| ^ 2

/-- All positive query degrees are permitted, with no fixed cap. -/
abbrev QuadraticQuery (n : ℕ) := Vec n × Vec n × {N : ℕ // 1 ≤ N}

/-- The sequence represents degrees 0 through the chosen N; all later
coordinates are set to zero and reveal no additional information. -/
abbrev QuadraticAnswer (n : ℕ) := ℂ × (ℕ → Vec n)

/-- Exactly the oracle of Section 5.3, evaluated on the quadratic polynomial.
Degree zero of the vector sequence is the gradient itself. -/
noncomputable def quadraticOracle {n : ℕ} (A : RealMatrix n)
    (Q : QuadraticQuery n) : QuadraticAnswer n :=
  (quadratic A Q.1, fun r => if r ≤ Q.2.2.val then
    iteratedFDeriv ℂ r (gradient (quadratic A)) Q.1 (fun _ => Q.2.1) else 0)

abbrev QuadraticProcedure (Seed : Type*) [MeasurableSpace Seed] (n q : ℕ) :=
  AdaptiveProcedure Seed (QuadraticQuery n) (QuadraticAnswer n) (Vec n) q

/-- The free value and gradient at zero are identically (0,0) on this family.
They are public constants, so omitting a redundant argument gives every
procedure exactly the same access. No circuit encoding is passed to P. -/
noncomputable def quadraticEstimate {Seed : Type*} [MeasurableSpace Seed] {n q : ℕ}
    (P : QuadraticProcedure Seed n q) (A : RealMatrix n) (seed : Seed) : Vec n :=
  adaptiveOutput P (quadraticOracle A) seed

end SketchAttr.LOO.Supplement


