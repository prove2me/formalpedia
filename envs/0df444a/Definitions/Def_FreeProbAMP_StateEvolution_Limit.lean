-- Prove2me | Definitions.Def_FreeProbAMP_StateEvolution_Limit
-- name    : FreeProbAMP_StateEvolution_Limit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:25:40.736733+00:00
-- url     : https://prove2.me/theorems/dfed018c-98f7-4cdc-a488-d9e72fe5b74d
-- title:
--   Gaussian–semicircular state law and AMP assumptions
-- statement:
--   Let $U^0$ have the limiting initialization law. Let $(U^1,\ldots,U^{T+1})$ be centered jointly Gaussian, independent of $U^0$, and let $(S^0,\ldots,S^T)$ be jointly centered semicircular in a faithful tracial C*-probability space. Put
--
--   $$G^t=g_t(U^0,\ldots,U^t),\qquad W^t=\sum_{s=0}^t a_{t,s}S^s.$$
--
--   The state law requires exactly
--
--   $$\mathbb E[U^{r+1}U^{s+1}]=\alpha\tau(W^rW^s),\qquad
--   \tau(S^rS^s)=\mathbb E[G^rG^s]\quad(0\le r,s\le T).$$
--
--   All linear combinations of the Gaussian tuple have centered normal laws; zero variance is permitted in this definition. Finite data satisfy the AMP assumptions when $\alpha_d\to\alpha>0$, the input matrices have independent normalized GOE laws, initialization is independent of the Gaussian operators and has the almost-sure all-moment empirical limit, and the coefficient and map assumptions hold.
--
--   Joint vector and matrix tuples are formed from these actual trajectories and their limiting coordinates. The induction predicate $H_t$ is empirical convergence through $(u^t,m^t)$ together with strong convergence through $(V^{t-1},M^{t-1})$. It is an assumption only for Lemma 6.6, rather than an assumption of state evolution. Positive definiteness is strict positivity of the associated quadratic form on every nonzero real coefficient vector.
--
--   **Formalization Note** Results hold for arbitrary realizations of this recursively determined law. Such realizations exist by finite Gaussian covariance constructions and the semicircular Fock-space construction; their trace moments and faithful C*-norms agree. The law predicate contains no convergence assumption. All moments used in its expectations are finite under the source initialization and map assumptions.
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), pp. 3–4, Assumptions 2.1–2.5 and (2.4)–(2.5); p. 30, Assumption 6.3

import Mathlib
import Definitions.Def_FreeProbAMP_StateEvolution_Iteration
import Definitions.Def_FreeProbAMP_StateEvolution_FreeLaw

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution

variable {E B Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω] [CStarAlgebra B]

/-- All real linear combinations have centered Gaussian laws, permitting zero variance. -/
def CenteredGaussian {k : ℕ} (ν : Measure E) (X : E → Fin k → ℝ) : Prop :=
  Measurable X ∧ ∀ c : Fin k → ℝ, ∃ v : ℝ≥0,
    ν.map (fun ξ => ∑ j, c j * X ξ j) = gaussianReal 0 v

structure LimitData (E B : Type*) [MeasurableSpace E] [CStarAlgebra B] where
  ν : Measure E
  probability : IsProbabilityMeasure ν
  τ : FaithfulTrace B
  U : ℕ → E → ℝ
  S : ℕ → B

namespace LimitData

def inputs (L : LimitData E B) (t : ℕ) (ξ : E) : Fin (t+1) → ℝ := fun r => L.U r ξ
def G (L : LimitData E B) (g : ScalarMaps) (t : ℕ) (ξ : E) : ℝ := g t (L.inputs t ξ)
def W (L : LimitData E B) (a : ℕ → ℕ → ℝ) (t : ℕ) : B :=
  ∑ s : Fin (t+1), (a t s : ℂ) • L.S s

end LimitData

/-- The recursive Gaussian/semicircular law (2.4)–(2.5); no convergence is assumed. -/
def StateLaw (L : LimitData E B) (T : ℕ) (α : ℝ) (a : ℕ → ℕ → ℝ) (g : ScalarMaps) : Prop :=
  CenteredGaussian L.ν (fun ξ (t : Fin (T+1)) => L.U (t.val+1) ξ) ∧
  IndepFun (L.U 0) (fun ξ (t : Fin (T+1)) => L.U (t.val+1) ξ) L.ν ∧
  JointSemicircular L.τ (fun t : Fin (T+1) => L.S t) ∧
  ∀ r s : Fin (T+1),
    (∫ ξ, L.U (r.val+1) ξ * L.U (s.val+1) ξ ∂L.ν) =
      α * (L.τ.value (L.W a r * L.W a s)).re ∧
    L.τ.value (L.S r * L.S s) = ((∫ ξ, L.G g r ξ * L.G g s ξ ∂L.ν) : ℂ)

/-- All source assumptions 2.1–2.5, with the independent initialization law. -/
def AMPAssumptions (D : FiniteData Ω) (L : LimitData E B) (T : ℕ) (α : ℝ) : Prop :=
  0 < α ∧ Tendsto D.α atTop (𝓝 α) ∧
  (∀ d, GOEArray D.μ (D.A d)) ∧
  IndepFun (fun ω d => D.u₀ d ω) (fun ω d => D.A d ω) D.μ ∧
  InitialLimit D.μ L.ν D.n D.u₀ (L.U 0) ∧
  Coefficients T D.a ∧ RegularMaps T D.g ∧ LastLinear T D.g

def concat {k l : ℕ} (x : Fin k → ℝ) (y : Fin l → ℝ) : Fin (k+l) → ℝ :=
  Fin.addCases x y

def vectorTuple (D : FiniteData Ω) (p q d : ℕ) (ω : Ω) (i : Fin (D.n d)) : Fin (p+q) → ℝ :=
  concat (fun r : Fin p => D.u r d ω i) (fun s : Fin q => D.m s d ω i)

def limitTuple (D : FiniteData Ω) (L : LimitData E B) (p q : ℕ) (ξ : E) : Fin (p+q) → ℝ :=
  concat (fun r : Fin p => L.U r ξ) (fun s : Fin q => L.G D.g s ξ)

def matrixTuple (D : FiniteData Ω) (p d : ℕ) (ω : Ω) : Fin p ⊕ Fin p → RMat (d+1) :=
  Sum.elim (fun r => D.V r d ω) (fun s => D.M s d ω)

def matrixLimit (D : FiniteData Ω) (L : LimitData E B) (p : ℕ) : Fin p ⊕ Fin p → B :=
  Sum.elim (fun r => L.S r) (fun s => L.W D.a s)

/-- Precisely Assumption 6.3, only for the cancellation lemma. -/
def InductionHypothesis (D : FiniteData Ω) (L : LimitData E B) (t : ℕ) : Prop :=
  Empirical D.μ L.ν D.n (vectorTuple D (t+1) (t+1)) (limitTuple D L (t+1) (t+1)) ∧
  Strong D.μ L.τ (matrixTuple D t) (matrixLimit D L t)

/-- Positive definiteness on every nonzero real coefficient vector. -/
def PositiveDefinite {p : ℕ} (G : RMat p) : Prop :=
  ∀ c : Fin p → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * G i j * c j

end FreeProbAMP.StateEvolution


