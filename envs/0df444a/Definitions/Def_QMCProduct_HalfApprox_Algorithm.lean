-- Prove2me | Definitions.Def_QMCProduct_HalfApprox_Algorithm
-- name    : QMCProduct_HalfApprox_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:05.552978+00:00
-- url     : https://prove2.me/theorems/c8c799c6-584e-4dab-a5d8-c9ff7046aac1
-- title:
--   Algorithms 2 and 4, eqs. (3), (5), pp. 11–14, 18 — F(k, t), Lemma 6's h(v, γ), Gaussian rounding and the output state
-- statement:
--   The rounding function uses a $k\times d$ matrix $R$ of independent standard normal variables. For unit vectors $u,v\in\mathbb R^d$, its correlation function is
--   $$F(k,t)=\frac{2}{k}\left(\frac{\Gamma((k+1)/2)}{\Gamma(k/2)}\right)^2t\,{}_2F_1\left(\tfrac12,\tfrac12;\tfrac{k}{2}+1;t^2\right).$$
--   Lemma 6 uses the auxiliary function
--   $$h(v,\gamma)=\frac{8(3\gamma+1)\gamma^2\,{}_2F_1\left(\tfrac32,\tfrac32;\tfrac72;\gamma^2\right)+40\,{}_2F_1\left(\tfrac12,\tfrac12;\tfrac52;\gamma^2\right)-45\pi}{15\pi(3v+1)^2}.$$
--
--   The vectors $W_i\in\mathbb R^d$ supplied by the level-2 relaxation have norm one and satisfy $W_i\cdot W_j=-v_{ij}$ for distinct vertices. Three Gaussian rows project each $W_i$ to a three-vector, which is normalized to the Bloch vector $\theta_i$. Algorithm 2 forms the tensor product of the associated one-qubit states $(I+\theta_i^X X+\theta_i^Y Y+\theta_i^Z Z)/2$.
--
--   For a threshold $\gamma$, Algorithm 4 takes the **large edges** $L=\{\{i,j\}\in E:v_{ij}>\gamma\}$ and the vertices $B$ incident to no edge in $L$. It outputs the matrix
--   $$\rho=\prod_{\{i,j\}\in L}\frac{I-Z_iZ_j}{4}\prod_{k\in B}\frac{I+\theta_k^X X_k+\theta_k^Y Y_k+\theta_k^Z Z_k}{2}.$$
--   The formula defines an operator before the matching property of $L$ is proved; that property makes it a state at the selected threshold.
--
--   **Formalization Note** Gaussian rows are one flattened standard Gaussian vector, reusing the published vector definition. `Unit(0)=0`, so a zero projection gives the maximally mixed one-qubit state. The first product has a fixed finite order; its factors commute. All energies are computed from this full matrix, never supplied as edge values.
-- source:
--   Parekh & Thompson, An Optimal Product-State Approximation for 2-Local Quantum Hamiltonians with Positive Terms, arXiv:2206.08342v2, pp. 11–14, 18, Algorithm 2, Lemma 4, equation (3), Algorithm 4, equation (5), Lemma 6

import Definitions.Def_QMCProduct_HalfApprox_Basic
import Definitions.Def_HighDimProb_RandomVectors_IsStandardGaussianVector
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric

set_option autoImplicit false

namespace QMCProduct.HalfApprox

open MeasureTheory ProbabilityTheory

/-- Equation (3), p. 12. The parameter k is positive in every stated use. -/
noncomputable def F (k : ℕ) (t : ℝ) : ℝ :=
  (2 / (k : ℝ)) *
    (Real.Gamma (((k : ℝ) + 1) / 2) / Real.Gamma ((k : ℝ) / 2)) ^ 2 * t *
    ordinaryHypergeometric (1 / 2 : ℝ) (1 / 2 : ℝ) ((k : ℝ) / 2 + 1) (t ^ 2)

/-- The function `h(v, γ)` of Lemma 6, p. 18. -/
noncomputable def hLemma6 (v γ : ℝ) : ℝ :=
  (8 * (3 * γ + 1) * γ ^ 2 *
      ordinaryHypergeometric (3 / 2 : ℝ) (3 / 2 : ℝ) (7 / 2 : ℝ) (γ ^ 2) +
    40 * ordinaryHypergeometric (1 / 2 : ℝ) (1 / 2 : ℝ) (5 / 2 : ℝ) (γ ^ 2) - 45 * Real.pi) /
    (15 * Real.pi * (3 * v + 1) ^ 2)

/-- The `k` by `d` array of independent N(0,1) entries, p. 12. -/
def IsStdGaussianMatrix {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {k d : ℕ} (R : Fin k → Fin d → Ω → ℝ) : Prop :=
  HighDimProb.RandomVectors.IsStandardGaussianVector P
    (fun z : Fin (k * d) => R (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2)

/-- Step 4 of Algorithm 4: the Gram data of the Lasserre rounding vectors. -/
def IsRoundingInput {n d : ℕ} (ρt : Op n) (W : Fin n → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ i, inner ℝ (W i) (W i) = 1) ∧
    ∀ i j, i ≠ j → inner ℝ (W i) (W j) = -v ρt i j

/-- Algorithm 2's `Unit` map, with Unit(0) = 0. -/
noncomputable def unitVec {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) := ‖x‖⁻¹ • x

/-- Multiplication of a real Gaussian matrix by a vector, p. 12. -/
noncomputable def gaussianProject {k d : ℕ} {Ω : Type}
    (R : Fin k → Fin d → Ω → ℝ) (ω : Ω)
    (u : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun a : Fin k => ∑ c : Fin d, R a c ω * u c)

/-- The normalized three-dimensional Gaussian projection of a rounding vector. -/
noncomputable def bloch {n d : ℕ} {Ω : Type} (W : Fin n → EuclideanSpace ℝ (Fin d))
    (R : Fin 3 → Fin d → Ω → ℝ) (ω : Ω) (i : Fin n) :
    EuclideanSpace ℝ (Fin 3) :=
  unitVec (gaussianProject R ω (W i))

/-- The one-qubit factor of equation (5). -/
noncomputable def blochState (θ : EuclideanSpace ℝ (Fin 3)) : Matrix Bool Bool ℂ :=
  (1 / 2 : ℂ) •
    (1 + (θ 0 : ℂ) • QAlgorithms.pauliX +
      (θ 1 : ℂ) • QAlgorithms.pauliY + (θ 2 : ℂ) • QAlgorithms.pauliZ)

/-- The product state of Algorithm 2, p. 11. -/
noncomputable def alg2State {n d : ℕ} {Ω : Type}
    (W : Fin n → EuclideanSpace ℝ (Fin d))
    (R : Fin 3 → Fin d → Ω → ℝ) (ω : Ω) : Op n :=
  QAlgorithms.kronAll (fun i => blochState (bloch W R ω i))

/-- Step 3 of Algorithm 4: large edges, counted once. -/
noncomputable def large {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ρt : Op n) (γ : ℝ) : Finset (Fin n × Fin n) :=
  (edges G).filter (fun e => γ < v ρt e.1 e.2)

/-- The undirected edge `{i,k}` is a member of the large-edge set. -/
def inLarge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ρt : Op n) (γ : ℝ) (i k : Fin n) : Prop :=
  ∃ e ∈ large G ρt γ,
    (e.1 = i ∧ e.2 = k) ∨ (e.1 = k ∧ e.2 = i)

/-- The set B of vertices not incident to a large edge, Algorithm 4, p. 14. -/
def inB {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ρt : Op n) (γ : ℝ) (i : Fin n) : Prop :=
  ∀ j, G.Adj i j → v ρt i j ≤ γ

/-- The first product in equation (5), in a fixed finite order. -/
noncomputable def largeState {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ρt : Op n) (γ : ℝ) : Op n :=
  ((large G ρt γ).toList.map (fun e =>
    (1 / 4 : ℂ) • (1 - Z e.1 * Z e.2))).prod

/-- Equation (5), p. 14, for every Gaussian outcome. -/
noncomputable def alg4State {n d : ℕ} {Ω : Type} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (ρt : Op n) (γ : ℝ)
    (W : Fin n → EuclideanSpace ℝ (Fin d))
    (R : Fin 3 → Fin d → Ω → ℝ) (ω : Ω) : Op n := by
  classical
  exact largeState G ρt γ * QAlgorithms.kronAll
    (fun i => if inB G ρt γ i then blochState (bloch W R ω i) else 1)

end QMCProduct.HalfApprox


