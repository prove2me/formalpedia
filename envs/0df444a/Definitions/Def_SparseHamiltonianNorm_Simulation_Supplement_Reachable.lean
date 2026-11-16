-- Prove2me | Definitions.Def_SparseHamiltonianNorm_Simulation_Supplement_Reachable
-- name    : SparseHamiltonianNorm_Simulation_Supplement_Reachable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:28:24.155315+00:00
-- url     : https://prove2.me/theorems/84f9d1e6-3e2b-4e5c-91e4-cfcdf6857189
-- title:
--   Scalar reachable histories and their coordinatewise grid representation
-- statement:
--   Let $\tau$ be a real interval length and let $m$ be a nonnegative integer. In the published space $L^2([0,\tau];\mathbb C)$, represented with a one-coordinate complex Euclidean fiber, define
--   $$\mathcal F_{m-1}^{\rm sc}(\tau)=\operatorname{span}_{\mathbb C}\{x\mapsto e^{-x}x^j:0\le j<m\}.$$
--   The empty span is zero, so $m=0$ means $\mathcal F_{-1}^{\rm sc}$. For a fiber $E=\mathbb C^e$, membership is tested on each scalar coordinate; this is exactly the tensor product with $E$. Its norm is the inherited $L^2$ norm, with Lebesgue measure and no probability normalization. The endpoints have measure zero.
--
--   For a complex linear isometry $E_\Delta$ from this scalar subspace to $\mathbb C^G$, its fiber extension applies that same map to every coordinate. The grid has the Euclidean norm on $\mathbb C^{G\times e}$, and a matrix on $E$ acts at each grid address. Finally,
--   $$L_R(\tau)=1+\frac{R^2}{\min\{\tau,1\}}.$$
--   These objects describe the reachable domain of the finite-coupling comparison. Uses of the derivative factor assume $\tau>0$. The coordinate encoder is totalized by zero outside its stated domain; Lemma 16 asserts all needed output membership.
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), Eq. (104)–(105), and the tensor extension in Lemma 16, p.28 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_Coupling

noncomputable section

namespace SparseHamiltonianNorm.Simulation.Supplement
open MeasureTheory QAlgorithms
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Number-of-coefficients convention: m corresponds to source F^sc_(m-1).
The span of no generators is {0}, including the source F^sc_(-1). -/
def scalarReachable (τ : ℝ) (m : ℕ) : Submodule ℂ (History 1 τ) :=
  Submodule.span ℂ (Set.range fun j : Fin m =>
    historyClass τ (fun x => WithLp.toLp 2 fun _ : Fin 1 =>
      (Real.exp (-x) : ℂ) * (x : ℂ) ^ j.val))

/-- A scalar coordinate of an E-valued L² equivalence class. -/
def historyComponent {e : ℕ} {τ : ℝ} (q : History e τ) (i : Fin e) : History 1 τ :=
  historyClass τ (fun x => WithLp.toLp 2 fun _ : Fin 1 => q x i)

/-- Eq. (104) tensored with E, by its finitely many scalar coordinates. -/
def InReachable {e : ℕ} {τ : ℝ} (m : ℕ) (q : History e τ) : Prop :=
  ∀ i : Fin e, historyComponent q i ∈ scalarReachable τ m

abbrev Grid (G e : ℕ) := EuclideanSpace ℂ (Fin G × Fin e)

/-- Coordinatewise tensor extension of the scalar comparison isometry.
Outside its specified domain this total function is zero coordinatewise. -/
def gridEncode {τ : ℝ} {m G e : ℕ}
    (E : scalarReachable τ m →ₗᵢ[ℂ] Vec G) (q : History e τ) : Grid G e :=
  WithLp.toLp 2 fun ji =>
    if h : historyComponent q ji.2 ∈ scalarReachable τ m then
      E ⟨historyComponent q ji.2, h⟩ ji.1 else 0

/-- Pointwise action I_C^G ⊗ T, with the Euclidean tensor norm. -/
def gridLift {G e : ℕ} (T : Matrix (Fin e) (Fin e) ℂ) (q : Grid G e) : Grid G e :=
  WithLp.toLp 2 fun ji => ∑ h, T ji.2 h * q (ji.1, h)

/-- Eq. (105); all uses assume τ>0. -/
def derivativeFactor (R : ℕ) (τ : ℝ) : ℝ :=
  1 + (R : ℝ) ^ 2 / min τ 1

end SparseHamiltonianNorm.Simulation.Supplement


