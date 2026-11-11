-- Prove2me | Definitions.Def_InducedExpanderTest989_Structural_Parameters
-- name    : InducedExpanderTest989_Structural_Parameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:57:56.729114+00:00
-- url     : https://prove2.me/theorems/c7c1d31b-8cf3-4de3-9e6c-5b778ea36d74
-- title:
--   Algorithm 1 parameters, conditional scores and cost expressions
-- statement:
--   For n vertices, size fraction α, relaxation κ and conductance ϕ, write β=(1−κ)α. The analysis uses t=⌈8 log(8√n)/ϕ²⌉, c_exc=1+8(1−α)/β and ℓ=⌈16c_exc t⌉. Set Λ=log(128/β), k=⌈64αβ⁻²log(128/α)⌉, ω=min{k,n/Λ}, m_A=⌈32√(nΛω)⌉, m_D=⌈32√(nΛ/ω)⌉ and R=⌈48α⁻¹log(2/δ)⌉. With L=⌊log₂(1/(α−β))⌋+1, the rejection conductance is exactly
--   $$\psi=\frac{\alpha\beta}{64\cdot1089\,\Lambda\ell L}.$$
--   The general tester evaluates these expressions at κ′=max{κ,3/4}. The functions thetaShape and costShape are precisely the expressions g and f in the mission target. Admissibility includes every stated range and n≥4/β. Given an anchor list A, its conditional score averages the probability of intersection with an independent fresh partner list over a uniform partner vertex. Anchor event probabilities average over a uniform anchor and its independent endpoint list. A binomial event is the finite sum of the masses choose(k,j)p^j(1−p)^(k−j). These are derived quantities, never freely supplied certificates.
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.16 (PDF p.18), Algorithm 1; (19) p.28; (21) p.30; Theorem 4.1 p.15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Chains

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

def effectiveKappa (κ : ℝ) : ℝ := max κ (3/4)
def beta (α κ : ℝ) : ℝ := (1-κ)*α
def traceSteps (n : ℕ) (ϕ : ℝ) : ℕ := ⌈8 * Real.log (8 * Real.sqrt n) / ϕ^2⌉₊
def excursion (α κ : ℝ) : ℝ := 1 + 8*(1-α)/beta α κ
def window (n : ℕ) (α κ ϕ : ℝ) : ℕ := ⌈16 * excursion α κ * traceSteps n ϕ⌉₊
def confidence (α κ : ℝ) : ℝ := Real.log (128 / beta α κ)
def partners (α κ : ℝ) : ℕ := ⌈(64*α/(beta α κ)^2) * Real.log (128/α)⌉₊
def balance (n : ℕ) (α κ : ℝ) : ℝ := min (partners α κ : ℝ) (n / confidence α κ)
def anchorsLength (n : ℕ) (α κ : ℝ) : ℕ :=
  ⌈32 * Real.sqrt (n * confidence α κ * balance n α κ)⌉₊
def partnersLength (n : ℕ) (α κ : ℝ) : ℕ :=
  ⌈32 * Real.sqrt (n * confidence α κ / balance n α κ)⌉₊
def rounds (α δ : ℝ) : ℕ := ⌈(48/α) * Real.log (2/δ)⌉₊
def psi (n : ℕ) (α κ ϕ : ℝ) : ℝ :=
  α * beta α κ / (64 * 1089 * confidence α κ * window n α κ ϕ * partitionLevels (α-beta α κ))
def thetaShape (n : ℕ) (α κ : ℝ) : ℝ :=
  (1-κ)^2 * α^3 / ((1-κ*α) * Real.log n * Real.log (1/((1-κ)*α)) * Real.log (2/α))
def costShape (n : ℕ) (α κ ϕ δ : ℝ) : ℝ :=
  (Real.sqrt n * Real.log n / ϕ^2) * ((1-κ*α)/((1-κ)^2 * Real.rpow α (5/2))) *
    Real.sqrt (Real.log (2/α) * Real.log (1/((1-κ)*α))) * Real.log (1/δ)
def BaseParams (α κ ϕ : ℝ) : Prop :=
  0 < α ∧ α ≤ 1 ∧ 0 < ϕ ∧ ϕ ≤ 1 ∧ 3/4 ≤ κ ∧ κ < 1
def LargeEnough (n : ℕ) (α κ : ℝ) : Prop := 4 / beta α κ ≤ (n : ℝ)
def Admissible (n d : ℕ) (α κ ϕ δ : ℝ) : Prop :=
  1 ≤ d ∧ 0 < α ∧ α ≤ 1 ∧ 0 < ϕ ∧ ϕ ≤ 1 ∧ 0 < δ ∧ δ ≤ 1/3 ∧
    0 < κ ∧ κ < 1 ∧ LargeEnough n α (effectiveKappa κ)

/-- Score (19), with an independent uniform fresh partner and iid partner list. -/
def conditionalScore {n m : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (mD : ℕ) (A : Fin m → Fin n) : ℝ := by
  classical
  exact (∑ y, ∑ D : Fin mD → Fin n, if collide A D then iidWeight (Q y) mD D else 0) / n

def anchorEventProb {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (mA mD : ℕ)
    (E : ℝ → Prop) : ℝ := by
  classical
  exact (∑ x, ∑ A : Fin mA → Fin n,
    if E (conditionalScore Q mD A) then iidWeight (Q x) mA A else 0) / n

/-- Binomial mass and events, including k=0 and p=0,1. -/
def binomialMass (k : ℕ) (p : ℝ) (j : ℕ) : ℝ := (k.choose j : ℝ) * p^j * (1-p)^(k-j)
def binomialEvent (k : ℕ) (p : ℝ) (E : ℕ → Prop) : ℝ := by
  classical
  exact ∑ j ∈ Finset.range (k+1), if E j then binomialMass k p j else 0

end InducedExpanderTest989.Structural


