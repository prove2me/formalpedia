-- Prove2me | Definitions.Def_HamLocality237_Testing_Dynamics
-- name    : HamLocality237_Testing_Dynamics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:36:01.35559+00:00
-- url     : https://prove2.me/theorems/5e868489-3c46-4ea8-860f-399dbd2b0439
-- title:
--   Dyson evolution and the continuous-time Hamiltonian access model
-- statement:
--   For an integrable operator-valued function $F$, define $D_0(t)=I$ and
--
--   $$D_{m+1}(t)=-i\int_0^t F(s)D_m(s)\,ds,\qquad U_F(t)=\sum_{m=0}^\infty D_m(t).$$
--
--   The recursively nested integrals are the ordered simplices of the Dyson expansion. The propagator predicate requires absolute continuity, integrability of the integrand, and the complete integral equation.
--
--   A continuous-time algorithm consists of a nonnegative final time, a finite nonempty workspace, a unit initial vector, an integrable a.e. self-adjoint driver, an integrable a.e. nonnegative query intensity, measurable orthogonal query projections whose sum is at most the identity, and a binary orthogonal final measurement. On a real diagonal input table $h$, its generator is $K(t)+\lambda(t)\sum_x h_xP_x(t)$, its state is the Dyson evolution of the initial vector, and its cost is $\int_0^{t_f}\lambda(t)\,dt$. These are input-independent data; no success, progress, or lower-bound property is a structure field.
--
--   Every unit vector is a basis vector in some orthonormal basis. Binary final measurements encode coarse-graining and postprocessing of the source's final projective measurement. Data are taken modulo null sets on the finite time interval; extension outside that interval changes no evolution.
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), §2.2 Eqs. (2)–(3), p.9; §2.3.1 Eq. (6), p.11. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Definitions.Def_HamLocality237_Testing_Protocol

open QAlgorithms
open MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section

namespace HamLocality237.Testing

/-- Ordered simplex integrals, recursively integrating the latest time first. -/
def dysonTerm {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (F : ℝ → E →L[ℂ] E) : ℕ → ℝ → E →L[ℂ] E
  | 0, _ => 1
  | m + 1, t => (-Complex.I) • ∫ s in (0 : ℝ)..t, F s * dysonTerm F m s

/-- Eq. (2), including the zeroth (identity) term. -/
def dysonEvolution {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (F : ℝ → E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E := ∑' m, dysonTerm F m t

/-- The integral equation, including AC and genuine integrability. -/
def IsPropagator {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (F U : ℝ → E →L[ℂ] E) (tf : ℝ) : Prop :=
  AbsolutelyContinuousOnInterval U 0 tf ∧
  IntegrableOn (fun s => F s * U s) (Set.Icc 0 tf) ∧
  ∀ t ∈ Set.Icc 0 tf, U t = 1 + (-Complex.I) • ∫ s in (0 : ℝ)..t, F s * U s

abbrev AlgorithmSpace (n w : ℕ) := EuclideanSpace ℂ (Fin w × Qubits n)

/-- Orthogonal projection in the Hilbert-space sense. -/
def IsProjection {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (P : E →L[ℂ] E) : Prop := IsSelfAdjoint P ∧ P * P = P

/-- §2.3.1: data independent of H. A binary final projection encodes postprocessing. -/
structure ContinuousAlgorithm (n : ℕ) where
  workspaceSize : ℕ
  workspaceNonempty : 0 < workspaceSize
  finalTime : ℝ
  finalTime_nonneg : 0 ≤ finalTime
  initial : AlgorithmSpace n workspaceSize
  initial_unit : ‖initial‖ = 1
  driver : ℝ → AlgorithmSpace n workspaceSize →L[ℂ] AlgorithmSpace n workspaceSize
  driver_integrable : IntegrableOn driver (Set.Icc 0 finalTime)
  driver_selfAdjoint : ∀ᵐ t ∂volume.restrict (Set.Icc 0 finalTime), IsSelfAdjoint (driver t)
  intensity : ℝ → ℝ
  intensity_integrable : IntegrableOn intensity (Set.Icc 0 finalTime)
  intensity_nonneg : ∀ᵐ t ∂volume.restrict (Set.Icc 0 finalTime), 0 ≤ intensity t
  query : Qubits n → ℝ → AlgorithmSpace n workspaceSize →L[ℂ] AlgorithmSpace n workspaceSize
  query_measurable : ∀ x, AEStronglyMeasurable (query x) (volume.restrict (Set.Icc 0 finalTime))
  query_projection : ∀ᵐ t ∂volume.restrict (Set.Icc 0 finalTime), ∀ x, IsProjection (query x t)
  query_orthogonal : ∀ᵐ t ∂volume.restrict (Set.Icc 0 finalTime), ∀ x y, x ≠ y → query x t * query y t = 0
  query_subidentity : ∀ᵐ t ∂volume.restrict (Set.Icc 0 finalTime), ∀ v,
    (inner ℂ v ((∑ x, query x t) v)).re ≤ ‖v‖ ^ 2
  accept : AlgorithmSpace n workspaceSize →L[ℂ] AlgorithmSpace n workspaceSize
  accept_projection : IsProjection accept

abbrev ContinuousAlgorithm.Space {n : ℕ} (A : ContinuousAlgorithm n) := AlgorithmSpace n A.workspaceSize

def ContinuousAlgorithm.hamiltonian {n : ℕ} (A : ContinuousAlgorithm n)
    (h : Qubits n → ℝ) (t : ℝ) : A.Space →L[ℂ] A.Space :=
  A.driver t + (A.intensity t : ℂ) • ∑ x, (h x : ℂ) • A.query x t

def ContinuousAlgorithm.state {n : ℕ} (A : ContinuousAlgorithm n)
    (h : Qubits n → ℝ) (t : ℝ) : A.Space :=
  dysonEvolution (A.hamiltonian h) t A.initial

def ContinuousAlgorithm.acceptProbability {n : ℕ} (A : ContinuousAlgorithm n)
    (h : Qubits n → ℝ) : ℝ :=
  ‖A.accept (A.state h A.finalTime)‖ ^ 2

def ContinuousAlgorithm.time {n : ℕ} (A : ContinuousAlgorithm n) : ℝ :=
  ∫ t in (0 : ℝ)..A.finalTime, A.intensity t

end HamLocality237.Testing


