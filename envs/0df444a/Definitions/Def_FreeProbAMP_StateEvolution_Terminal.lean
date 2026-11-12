-- Prove2me | Definitions.Def_FreeProbAMP_StateEvolution_Terminal
-- name    : FreeProbAMP_StateEvolution_Terminal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:27:44.937612+00:00
-- url     : https://prove2.me/theorems/30a8d791-6359-4c20-a0ec-418584e89802
-- title:
--   Trace-preserving extensions and the smooth extra half-step
-- statement:
--   A trace-preserving C*-extension consists of a unital C*-algebra $\mathcal N'$, a faithful tracial state $\tau'$, and an isometric unital star-algebra embedding $j:\mathcal N\to\mathcal N'$ with $\tau'(j(a))=\tau(a)$. This permits adjoining semicircular variables without assuming the initial ambient algebra already contains them.
--
--   After the trajectory through time $T-1$, let $k:\mathbb R^{T+1}\to\mathbb R$ be an arbitrary $C^1$ map whose value and first derivatives are pseudo-Lipschitz of finite order. Define
--
--   $$\widehat z_i=k(u_i^0,\ldots,u_i^T),\quad K=k(U^0,\ldots,U^T),$$
--   $$d_{k,r}=\frac1n\sum_i\partial_r k(u_i^0,\ldots,u_i^T),\qquad
--   c_{k,r}=\mathbb E[\partial_r k(U^0,\ldots,U^T)]\quad(1\le r\le T),$$
--   $$\widehat V=A\widehat z-\alpha_d\sum_{r=1}^T d_{k,r}M^{r-1}.$$
--
--   The extra map need not be affine in its last input or have a positive slope. These definitions support the extra-half-step limit while keeping the existence of a semicircular extension in the theorem's conclusion.
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), p. 38, (7.3)–(7.4) and Lemma 7.3; p. 29, Proposition 6.2

import Mathlib
import Definitions.Def_FreeProbAMP_StateEvolution_History

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal Matrix
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution

universe u

/-- An extension of the ambient probability algebra; adjoining a new semicircular variable
must not require the old algebra already to contain it. -/
structure TraceExtension (B : Type u) [CStarAlgebra B] (τ : FaithfulTrace B) where
  carrier : Type u
  [cstar : CStarAlgebra carrier]
  trace : FaithfulTrace carrier
  embed : B →⋆ₐ[ℂ] carrier
  isometric : ∀ b, ‖embed b‖ = ‖b‖
  preserves : ∀ b, trace.value (embed b) = τ.value b

attribute [instance] TraceExtension.cstar

variable {Ω E B : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [CStarAlgebra B]

def extraMessage (D : FiniteData Ω) (T : ℕ) (k : (Fin (T+1) → ℝ) → ℝ) (d : ℕ) (ω : Ω) :=
  fun i => k (D.inputs T d ω i)

def extraDeriv (D : FiniteData Ω) (T : ℕ) (k : (Fin (T+1) → ℝ) → ℝ)
    (r : Fin T) (d : ℕ) (ω : Ω) : ℝ :=
  avg (D.n d) (fun i => derivCoord k ⟨r.val+1, by omega⟩ (D.inputs T d ω i))

def extraV (D : FiniteData Ω) (T : ℕ) (k : (Fin (T+1) → ℝ) → ℝ) (d : ℕ) (ω : Ω) : RMat (d+1) :=
  applyA (D.A d ω) (extraMessage D T k d ω) -
    D.α d • ∑ r : Fin T, extraDeriv D T k r d ω • D.M r d ω

def extraCovDerivative (L : LimitData E B) (T : ℕ) (k : (Fin (T+1) → ℝ) → ℝ) (r : Fin T) : ℝ :=
  ∫ ξ, derivCoord k ⟨r.val+1, by omega⟩ (L.inputs T ξ) ∂L.ν

end FreeProbAMP.StateEvolution


