-- Prove2me | Definitions.Def_BooleanHiddenPartition_LowerBounds_OneWay
-- name    : BooleanHiddenPartition_LowerBounds_OneWay
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T15:20:10.488934+00:00
-- url     : https://prove2.me/theorems/a4b9e1d9-992c-455c-977c-68300925c351
-- title:
--   General randomized classical and unassisted quantum one-way protocols
-- statement:
--   For finite input spaces X and Y and a cost c, a deterministic classical strategy consists of an encoder X → Fin (2^c) and a binary decoder depending on Y and the received symbol. A randomized protocol is an arbitrary probability mass on these finite deterministic tables, including joint public and private randomness.
--
--   $$P_{\rm acc}(x,y)=\sum_s w_s\,1[s_{\rm dec}(y,s_{\rm enc}(x))=\mathrm{YES}].$$
--
--   A quantum strategy maps each x to an arbitrary 2^c-dimensional density matrix rho(x) and each y to an effect E(y) with E and I−E positive semidefinite. Its YES probability is the real part of Tr(E(y)rho(x)). A quantum protocol averages these probabilities over a measurable public seed on any probability space. Density matrices include private randomization, and effects include arbitrary two-outcome measurements. Born probabilities are measurable and bounded, hence integrable. There is no preshared entangled register. The two general protocol types have no paper-specific promise or communication lower bound built into them.
-- source:
--   Mark Bun, Joao F. Doriguello, John Kallaugher, Nadezhda Voronova, STOC 2027 submission #1085 (October 2026), pp. 2, 15, 22–23, definitions and conventions.

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator

open scoped BigOperators ENNReal ComplexOrder
open Classical
set_option autoImplicit false

namespace BooleanHiddenPartition.LowerBounds

noncomputable section

/-- General finite-input deterministic one-way binary-decision strategy. -/
abbrev ClassicalStrategy (X Y : Type) (c : ℕ) :=
  (X → Fin (2 ^ c)) × (Y → Fin (2 ^ c) → Bool)

/-- Arbitrary joint public/private randomness is a law on deterministic tables. -/
structure ClassicalProtocol (X Y : Type) [Fintype X] [Fintype Y] (c : ℕ) where
  weight : ClassicalStrategy X Y c → ℝ
  nonneg : ∀ s, 0 ≤ weight s
  total : ∑ s, weight s = 1

def classicalAccept {X Y : Type} [Fintype X] [Fintype Y] {c : ℕ}
    (P : ClassicalProtocol X Y c) (x : X) (y : Y) : ℝ :=
  ∑ s, P.weight s * if s.2 y (s.1 x) then 1 else 0

abbrev QMat (c : ℕ) := Matrix (Fin (2 ^ c)) (Fin (2 ^ c)) ℂ

/-- An unassisted quantum message and an arbitrary two-outcome POVM. -/
structure QuantumStrategy (X Y : Type) (c : ℕ) where
  state : X → QMat c
  density : ∀ x, WildeQIT.IsDensityOperator (state x)
  effect : Y → QMat c
  positive : ∀ y, (effect y).PosSemidef
  complement_positive : ∀ y, (1 - effect y).PosSemidef

def quantumAccept {X Y : Type} {c : ℕ} (P : QuantumStrategy X Y c)
    (x : X) (y : Y) : ℝ := ((P.effect y * P.state x).trace).re

/-- A public random seed on any probability space. Private random encodings and
measurements are already included by density matrices and effects. -/
structure QuantumProtocol (X Y Ω : Type) [MeasurableSpace Ω] (c : ℕ) where
  seedLaw : MeasureTheory.Measure Ω
  probability : MeasureTheory.IsProbabilityMeasure seedLaw
  strategy : Ω → QuantumStrategy X Y c
  measurable_accept : ∀ x y, Measurable (fun ω => quantumAccept (strategy ω) x y)

/-- Real integral of bounded Born probabilities; measurability is part of the model. -/
def randomizedQuantumAccept {X Y Ω : Type} [MeasurableSpace Ω] {c : ℕ}
    (P : QuantumProtocol X Y Ω c) (x : X) (y : Y) : ℝ :=
  ∫ ω, quantumAccept (P.strategy ω) x y ∂P.seedLaw

end

end BooleanHiddenPartition.LowerBounds


