-- Prove2me | Definitions.Def_XORFullTilt_Hardness_QuantumModel
-- name    : XORFullTilt_Hardness_QuantumModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T14:51:14.8192+00:00
-- url     : https://prove2.me/theorems/ee887f66-cb4e-431c-a6bc-7590e4c05fe1
-- title:
--   Finite-dimensional POVM strategies and Born-rule values
-- statement:
--   For finite question and answer alphabets, a quantum strategy consists of a unit shared vector $\psi\in\mathbb C^d\otimes\mathbb C^e$ and a local POVM for each question. Dimensions range over all finite dimensions; normalization forces both dimensions to be positive whenever a strategy exists. Measurements use the published complex Hermitian PSD effects summing to identity. A PVM additionally has idempotent effects.
--
--   The outcome probability and winning value are
--   $$p(a,b\mid x,y)=\langle\psi|P_a^x\otimes Q_b^y|\psi\rangle,\qquad
--   \omega(G,p)=\sum_{x,y,a,b}\pi(x,y)V(a,b\mid x,y)p(a,b\mid x,y).$$
--   The quantum value is the real supremum over all finite dimensions and POVMs. The classical value is the supremum over deterministic response functions. These families are nonempty and bounded for every binary game used here. No maximum is required for the quantum value. The bundle also defines binary observables, the deterministic zero-answer measurement, tensor swap and the Euclidean norm of a complex coordinate vector.
--
--   These definitions provide the shared semantics for all later estimates.
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), pp.8–10, §2.1 and Definitions 2.1–2.5

import Mathlib
import Definitions.Def_MIPRE_Foundations_Games

open scoped MatrixOrder
open Matrix Kronecker ComplexOrder

namespace XORFullTilt.Hardness

/-- A unit pure state in the tensor product, in fixed orthonormal coordinates. -/
structure State (d e : ℕ) where
  vec : Fin d × Fin e → ℂ
  unit : ∑ i, Complex.normSq (vec i) = 1

abbrev Measurement (A : Type) [Fintype A] (d : ℕ) := MIPRE.POVM A (Fin d)

def effect {A : Type} [Fintype A] {d : ℕ} (P : Measurement A d) (a : A) :
    Matrix (Fin d) (Fin d) ℂ := (P.mats a).val

def IsPVM {A : Type} [Fintype A] {d : ℕ} (P : Measurement A d) : Prop :=
  ∀ a, effect P a * effect P a = effect P a

noncomputable def born {d e : ℕ} (ψ : State d e)
    (P : Matrix (Fin d) (Fin d) ℂ) (Q : Matrix (Fin e) (Fin e) ℂ) : ℝ :=
  (star ψ.vec ⬝ᵥ ((P ⊗ₖ Q) *ᵥ ψ.vec)).re

structure QuantumStrategy (X Y A B : Type) [Fintype A] [Fintype B] (d e : ℕ) where
  state : State d e
  alice : X → Measurement A d
  bob : Y → Measurement B e

noncomputable def strategyValue {X Y A B : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] {d e : ℕ} (G : MIPRE.Game X Y A B)
    (S : QuantumStrategy X Y A B d e) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
    born S.state (effect (S.alice x) a) (effect (S.bob y) b)

/-- Supremum over all finite dimensions and POVMs; no attained optimum is required. -/
noncomputable def quantumValue {X Y A B : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (G : MIPRE.Game X Y A B) : ℝ :=
  sSup {v | ∃ d e : ℕ, ∃ S : QuantumStrategy X Y A B d e, v = strategyValue G S}

noncomputable def deterministicValue {X Y A B : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (G : MIPRE.Game X Y A B) (g : X → A) (h : Y → B) : ℝ :=
  ∑ x, ∑ y, G.μ x y * (if G.D x y (g x) (h y) then 1 else 0)

noncomputable def classicalValue {X Y A B : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (G : MIPRE.Game X Y A B) : ℝ :=
  sSup {v | ∃ g : X → A, ∃ h : Y → B, v = deterministicValue G g h}

noncomputable def observable {d : ℕ} (P : Measurement Bool d) : Matrix (Fin d) (Fin d) ℂ :=
  effect P false - effect P true

/-- The deterministic zero-answer measurement. -/
def zeroMeasurement (d : ℕ) : Measurement Bool d where
  mats a := if a then 0 else 1
  nonneg a := by
    cases a
    · change (0 : Matrix (Fin d) (Fin d) ℂ) ≤ 1
      exact (Matrix.PosSemidef.one : (1 : Matrix (Fin d) (Fin d) ℂ).PosSemidef).nonneg
    · simp
  normalized := by simp

noncomputable def State.swap {d e : ℕ} (ψ : State d e) : State e d where
  vec i := ψ.vec (i.2, i.1)
  unit := by
    simp only [Fintype.sum_prod_type] at *
    rw [Finset.sum_comm]
    simpa only [Fintype.sum_prod_type] using ψ.unit

/-- Euclidean norm of a coordinate vector, never the sup norm on functions. -/
noncomputable def vectorNorm {ι : Type} [Fintype ι] (v : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, Complex.normSq (v i))

end XORFullTilt.Hardness


