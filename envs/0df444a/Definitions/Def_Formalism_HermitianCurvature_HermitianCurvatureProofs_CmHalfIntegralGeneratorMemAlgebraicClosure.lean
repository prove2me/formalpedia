-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T14:23:14.372334+00:00
-- url     : https://prove2.me/theorems/337a9360-c5fd-44b0-a7b5-21fedb5e6ea9
-- title:
--   Cm Half Integral Generator Mem Algebraic Closure
-- statement:
--   Definitions and structural lemmas for Cm Half Integral Generator Mem Algebraic Closure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
section herm
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
end herm
def mk3 (k r' : ℕ) (a : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) (b : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ :=
  a • e0 k r' + liftVec k 1 r' y + b • es0 k r'
def cF (u : Fin (2 * (1 + r') + k + 1) → ℂ) : ℂ := u ⟨0, by omega⟩
def cL (u : Fin (2 * (1 + r') + k + 1) → ℂ) : ℂ := u ⟨2 * (1 + r') + k, by omega⟩
def mid (u : Fin (2 * (1 + r') + k + 1) → ℂ) : Fin (2 * r' + k + 1) → ℂ := fun j => u (levPos k 1 r' j)
lemma e0_apply_eq_ite (i : Fin (2 * (1 + r') + k + 1)) : e0 k r' i = if i.val = 0 then 1 else 0 := by
  have h : (i = eI k (1 + r') (a0 r')) ↔ i.val = 0 := Fin.ext_iff
  simp only [e0, bvec, Pi.single_apply, h]
lemma es0_apply (i : Fin (2 * (1 + r') + k + 1)) :
    es0 k r' i = if i.val = 2 * (1 + r') + k then 1 else 0 := by
  have h : (i = esI k (1 + r') (a0 r')) ↔ i.val = 2 * (1 + r') + k := Fin.ext_iff
  simp only [es0, bvec, Pi.single_apply, h]
lemma three_block_apply (a : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) (b : ℂ) (i : Fin (2 * (1 + r') + k + 1)) :
    mk3 k r' a y b i = if i.val = 0 then a else if h : 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1 then y ⟨i.val - 1, by omega⟩ else b := by
  have hi := i.isLt
  simp only [mk3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, e0_apply_eq_ite, es0_apply, liftVec]
  split_ifs <;> first | omega | simp
lemma three_block_add (a a' b b' : ℂ) (y y' : Fin (2 * r' + k + 1) → ℂ) :
    mk3 k r' a y b + mk3 k r' a' y' b' = mk3 k r' (a + a') (y + y') (b + b') := by
  funext i
  simp only [Pi.add_apply, three_block_apply]
  split_ifs <;> simp
lemma three_block_smul (c a b : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) :
    c • mk3 k r' a y b = mk3 k r' (c * a) (c • y) (c * b) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, three_block_apply]
  split_ifs <;> simp
def tkF (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := ⟨0, by omega⟩
def tkL (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := ⟨2 * (1 + r') + k, by omega⟩
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
def μx : Measure ℂ := (volume : Measure ℂ).withDensity fun c => ENNReal.ofReal ((‖c‖ ^ 2)⁻¹)
instance : SFinite μx := by unfold μx; infer_instance
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
def mi2D (l c : ℂ) : ℂ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (l * -((conj c) ^ 2)⁻¹)).restrictScalars ℝ).comp
    (Complex.conjCLE : ℂ →L[ℝ] ℂ)
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
def Ψt (k r' : ℕ) (p : ℂ × HPar k r') : Fin (2 * (1 + r') + k + 1) → ℂ :=
  mk3 k r' (hb k r' p.2.1 p.2.2 / conj p.1) p.2.1 p.1
def Tw (k r' : ℕ) (c₀ : ℂ) (p : ℂ × HPar k r') : ℂ × HPar k r' :=
  (c₀ * hb k r' p.2.1 p.2.2 / conj p.1, (p.2.1, -p.2.2))
def Tl (k r' : ℕ) (g₁ : Mat k r') (p : ℂ × HPar k r') : ℂ × HPar k r' := (p.1, (g₁ *ᵥ p.2.1, p.2.2))
def Tn (k r' : ℕ) (x₀ : HPar k r') (p : ℂ × HPar k r') : ℂ × HPar k r' :=
  (p.1, (p.2.1 + p.1 • x₀.1, p.2.2 - (conj p.1 * herm (Hpk k r') p.2.1 x₀.1).im + ‖p.1‖ ^ 2 * x₀.2))
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
def cm1Θ (k r' : ℕ) (p : ℂ × HPar k r') : ℂ × HPar k r' := (p.1, (p.1 • p.2.1, ‖p.1‖ ^ 2 * p.2.2))
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
section
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
end
def alL (h : Mat k (1 + r')) : (Fin (2 * r' + k + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r' + k + 1) → ℂ) where
  toFun y := mid (h *ᵥ mk3 k r' 0 y 0)
  map_add' y y' := by
    have : mk3 k r' 0 (y + y') 0 = mk3 k r' 0 y 0 + mk3 k r' 0 y' 0 := by rw [three_block_add]; simp
    rw [this, Matrix.mulVec_add]; rfl
  map_smul' c y := by
    have : mk3 k r' 0 (c • y) 0 = c • mk3 k r' 0 y 0 := by rw [three_block_smul]; simp
    rw [this, Matrix.mulVec_smul]; rfl
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 B2x8
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
def cgS (k r' : ℕ) (R : ℝ) : Set (ℂ × HPar k r') := {p | ‖p.1‖ ≤ R ∧ ‖p.2.1‖ ≤ R ∧ |p.2.2| ≤ R * ‖p.1‖}
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 B2x8
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
section dj
variable {k r : ℕ}
end dj
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.B2x8
end Formalism.FourierDecayAlt.P


