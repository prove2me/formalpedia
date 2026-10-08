-- Prove2me | Definitions.Def_AMPUniversality_StateEvol_Converging
-- name    : AMPUniversality_StateEvol_Converging
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T05:30:08.985123+00:00
-- url     : https://prove2.me/theorems/e219c504-1d11-4551-af55-1adf3fe10934
-- title:
--   Polynomial and converging AMP sequences, Definition 5 and (1.9)
-- statement:
--   A converging sequence adds $k$ coordinate classes to a regular AMP sequence. Class $a$ has asymptotic fraction $c_a\in(0,1)$, the symmetric nonnegative matrix $W$ sets entry variances $W_{ab}/N$, and independent labels $Y(i)$ have class law $P_a$, a finite mixture of possibly degenerate Gaussian laws. The label vector is also independent of the matrix and initial vectors. The polynomial map at coordinate $i$ is $g(x,Y(i),a,t)$. Its coefficients are uniformly bounded and measurable as functions of the label.
--
--   The initial second-moment condition is
--
--   $$\frac1{|C_a^N|}\sum_{i\in C_a^N}g(x_i^0,Y(i),a,0)g(x_i^0,Y(i),a,0)^\mathsf T\longrightarrow\widehat\Sigma_a^0$$
--
--   in probability, entry by entry. This supplies the initial covariance for state evolution.
--
--   **Formalization Note** Classes are fibers of a class-label function on `Fin N`; their cardinality at $N=0$ is immaterial to the limit. Coefficient measurability makes the label-dependent maps genuine random variables. Independence of the full label vector from the matrix and initial vectors is made explicit because independence of the induced coefficients alone does not imply it when $g$ omits label information; Theorem 4 requires an independent Gaussian-label limit.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, pp. 8–9, Definition 5, (1.9)

import Definitions.Def_AMPUniversality_StateEvol_Regular
import Definitions.Def_AMPUniversality_StateEvol_GaussianMixture

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace AMPUniversality.StateEvol

/-- Data of a polynomial, class-structured AMP instance. -/
structure Model (Ω : Type*) [MeasurableSpace Ω]
    (q h k d : ℕ) where
  C : ℝ
  A : ∀ N : ℕ, Ω → Matrix (Fin N) (Fin N) ℝ
  x0 : ∀ N : ℕ, Ω → Fin N → Fin q → ℝ
  Y : ∀ N : ℕ, Ω → Fin N → EuclideanSpace ℝ (Fin h)
  cls : ∀ N : ℕ, Fin N → Fin k
  gc : EuclideanSpace ℝ (Fin h) → Fin k → ℕ → Fin q →
    (Fin q → Fin (d + 1)) → ℝ
  W : Matrix (Fin k) (Fin k) ℝ
  ca : Fin k → ℝ
  Pa : Fin k → Measure (EuclideanSpace ℝ (Fin h))
  hat0 : Fin k → Matrix (Fin q) (Fin q) ℝ

/-- The random coefficient array induced by the labels. -/
def Model.coeff {Ω : Type*} [MeasurableSpace Ω] {q h k d : ℕ}
    (M : Model Ω q h k d) (N : ℕ) (ω : Ω) (i : Fin N) (t : ℕ) :=
  M.gc (M.Y N ω i) (M.cls N i) t

/-- Polynomial map `g` in coordinate form. -/
def Model.gvec {Ω : Type*} [MeasurableSpace Ω] {q h k d : ℕ}
    (M : Model Ω q h k d) (x : Fin q → ℝ)
    (y : EuclideanSpace ℝ (Fin h)) (a : Fin k) (t : ℕ) : Fin q → ℝ :=
  fun r => polyEval (M.gc y a t) x r

/-- The AMP orbit associated to the model. -/
def Model.orbit {Ω : Type*} [MeasurableSpace Ω] {q h k d : ℕ}
    (M : Model Ω q h k d) (N : ℕ) (ω : Ω) (t : ℕ) :
    Fin N → Fin q → ℝ :=
  AMPUniversality.Universal.ampOrbit (M.A N ω) (M.coeff N ω) (M.x0 N ω) t

/-- The class of an index and its cardinality. -/
def Model.class {Ω : Type*} [MeasurableSpace Ω] {q h k d : ℕ}
    (M : Model Ω q h k d) (N : ℕ) (a : Fin k) : Finset (Fin N) :=
  Finset.univ.filter (fun i => M.cls N i = a)

/-- Definition 5, including (1.9), with explicit measurability of label coefficients. -/
def IsConverging {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {q h k d : ℕ}
    (M : Model Ω q h k d) : Prop :=
  IsRegular P M.C d q M.A M.coeff M.x0 ∧
  M.W.IsSymm ∧ (∀ a b, 0 ≤ M.W a b) ∧
  (∀ N (i j : Fin N), i < j →
    (∫ ω, (M.A N ω i j) ^ 2 ∂P) =
      M.W (M.cls N i) (M.cls N j) / (N : ℝ)) ∧
  (∀ a, (M.hat0 a).PosSemidef) ∧
  (∀ a, IsGaussianMixture (M.Pa a)) ∧
  (∀ a, 0 < M.ca a ∧ M.ca a < 1 ∧
    Tendsto (fun N => ((M.class N a).card : ℝ) / (N : ℝ))
      atTop (𝓝 (M.ca a))) ∧
  (∀ N, iIndepFun (fun i : Fin N => fun ω => M.Y N ω i) P) ∧
  (∀ N, IndepFun (M.Y N)
    (fun ω => (fun (i j : Fin N) => M.A N ω i j, M.x0 N ω)) P) ∧
  (∀ N (i : Fin N), Measurable (fun ω => M.Y N ω i) ∧
    Measure.map (fun ω => M.Y N ω i) P = M.Pa (M.cls N i)) ∧
  (∀ y a t r m, |M.gc y a t r m| ≤ M.C) ∧
  (∀ a t r m, Measurable (fun y => M.gc y a t r m)) ∧
  (∀ a r s,
    TendstoInMeasure P
      (fun N ω => (((M.class N a).card : ℝ)⁻¹) *
        ∑ i ∈ M.class N a,
          M.gvec (M.x0 N ω i) (M.Y N ω i) a 0 r *
          M.gvec (M.x0 N ω i) (M.Y N ω i) a 0 s)
      atTop (fun _ => M.hat0 a r s))

end AMPUniversality.StateEvol


