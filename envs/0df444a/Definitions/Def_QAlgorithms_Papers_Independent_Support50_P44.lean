-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P44
-- name    : QAlgorithms_Papers_Independent_Support50_P44
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T22:37:28.703912+00:00
-- url     : https://prove2.me/theorems/4eb02eba-ac26-4e40-be5b-b12b3def8db0
-- title:
--   Definitions for Universal recovery map for approximate Markov chains
-- statement:
--   The objects the formalized statements of *Universal recovery map for approximate Markov chains* (arXiv:1504.07251) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `hilbertTrace`: PDF pp.23–24: ordinary basis trace, used only on trace-class arguments.
--   - `IsHilbertDensity`: PDF pp.1–3: positive trace-class operators with trace one.
--   - `hilbertFidelity`: PDF p.2 footnote 1: root fidelity Tr sqrt(sqrt(rho) sigma sqrt(rho)). For positive trace-class inputs the operator traced is itself trace class.
--   - `hilbertTraceNorm`: PDF p.24, (143): trace norm Tr sqrt(T-adjoint T), on trace-class arguments.
--   - `hilbertMix`: PDF pp.23–25: convex mixture, with the interval guard in every theorem.
--   - `OrthogonalBlocks`: PDF pp.23–24: all four orthogonality conditions between the two blocks.
--   - `compressedRelativeEntropy`: PDF p.24: generalized relative entropy of compressions, in bits. The trace correction in qRelEntropy is essential on unequal traces. This is the accepted Dependency50.P13 finiteRelativeEntropy construction, converted from nats to bits.
--   - `hilbertRelativeEntropy`: PDF p.24, (147): full normalized Umegaki entropy via finite orthogonal compressions of generalized entropy, following accepted Dependency50.P13. The extended supremum retains infinity; no entropy finiteness is assumed.
--   - `IsHilbertPOVM`: PDF p.24, Definition B.1: finite positive bounded effects summing to identity.
--   - `measuredRelativeEntropy`: PDF p.24, Definition B.1: supremum over all finite POVMs, without attainment.
--   - `IsFiniteProjector`: PDF p.27: finite-rank orthogonal projector, with no nesting requirement.
--   - `WeaklyExhausts`: PDF p.27: weak operator convergence to identity against every pair of vectors.
--   - `finiteEntropyBits`: PDF pp.1,19: finite von Neumann entropy in bits, with 0 log 0 = 0.
--   - `finiteCMI`: PDF p.19, (117): four finite entropies, never used for infinite systems.
--   - `finiteSupport`: PDF pp.2,19: spectral support projection, including a zero kernel.
--   - `rotatedTranspose`: PDF pp.19,22,28, (116),(134): rotated transpose formula on supported inputs. The inverse square root is zero at a zero eigenvalue.
--   - `mapChoi`: PDF p.26: a linear map in Choi coordinates, with input index first.
--   - `finiteMapTopology`: PDF p.26: topology of all Choi entries, a finite map-coordinate topology.
--   - `FiniteCP`: PDF p.26, Remark C.3: complete positivity via its Choi representation.
--   - `FiniteTNI`: PDF p.26: trace nonincrease on every positive, possibly unnormalized input.
--   - `FiniteTP`: PDF p.26: full trace preservation of a complex-linear map.
--   - `counterexampleState`: PDF p.28, (169): the diagonal qubit counterexample, A tensor (B tensor C), false = zero. Its trace is 1/2 + 4/8 = 1.
--   - `counterexampleRecovery`: PDF p.28, (171): measure B in its basis, then prepare the prescribed state. This full linear map kills off-diagonal matrix units.
--   - `counterexampleTranspose`: PDF pp.22,28, (134),(170): full transpose map, with invertible rhoB.
--   - `finiteRecoveryFidelity`: PDF p.2, (3): optimal root fidelity over all full CPTP recovery channels. For density inputs the set is nonempty and bounded by one.
-- source:
--   Universal recovery map for approximate Markov chains, arXiv:1504.07251v3, https://arxiv.org/abs/1504.07251v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_SDP
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P37

/-!
Sutter–Fawzi–Renner, arXiv:1504.07251v3; citations use PDF pages.
Infinite systems below are complete complex Hilbert spaces with countable Hilbert
bases, including finite spaces. Nuclearity and compression import accepted
Dependency50.P13 definitions; finite marginalAB imports Dependency50.P21; finite
classical KL in bits imports Renew46.P37. Accepted-library imports follow the
independent-paper workflow override. Compilation and moderation are pending.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P44

-- Reuse the inspected pinned definitions without local aliases or redeclarations.
open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass compression)
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)
open QAlgorithms.Papers.Independent.Renew46.P37 (classicalKL)

open Filter
open scoped ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF pp.23–24: ordinary basis trace, used only on trace-class arguments. -/
def hilbertTrace {I : Type*} (b : HilbertBasis I ℂ H) (T : H →L[ℂ] H) : ℂ :=
  ∑' i, inner ℂ (b i) (T (b i))

/-- PDF pp.1–3: positive trace-class operators with trace one. -/
def IsHilbertDensity {I : Type*} (b : HilbertBasis I ℂ H) (rho : H →L[ℂ] H) : Prop :=
  IsTraceClass rho ∧ rho.IsPositive ∧ hilbertTrace b rho = 1

/-- PDF p.2 footnote 1: root fidelity Tr sqrt(sqrt(rho) sigma sqrt(rho)).
For positive trace-class inputs the operator traced is itself trace class. -/
def hilbertFidelity {I : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : H →L[ℂ] H) : ℝ :=
  (hilbertTrace b (cfc Real.sqrt
    ((cfc Real.sqrt rho).comp (sigma.comp (cfc Real.sqrt rho))))).re

/-- PDF p.24, (143): trace norm Tr sqrt(T-adjoint T), on trace-class arguments. -/
def hilbertTraceNorm {I : Type*} (b : HilbertBasis I ℂ H) (T : H →L[ℂ] H) : ℝ :=
  (hilbertTrace b (cfc Real.sqrt (T.adjoint.comp T))).re

/-- PDF pp.23–25: convex mixture, with the interval guard in every theorem. -/
def hilbertMix (p : ℝ) (rho sigma : H →L[ℂ] H) : H →L[ℂ] H :=
  (p : ℂ) • rho + ((1 - p : ℝ) : ℂ) • sigma

/-- PDF pp.23–24: all four orthogonality conditions between the two blocks. -/
def OrthogonalBlocks (rho rho2 sigma sigma2 : H →L[ℂ] H) : Prop :=
  rho.comp rho2 = 0 ∧ rho.comp sigma2 = 0 ∧
    sigma.comp rho2 = 0 ∧ sigma.comp sigma2 = 0

/-- PDF p.24: generalized relative entropy of compressions, in bits. The trace
correction in qRelEntropy is essential on unequal traces. This is the accepted
Dependency50.P13 finiteRelativeEntropy construction, converted from nats to bits. -/
def compressedRelativeEntropy {n : ℕ} (rho sigma : Matrix (Fin n) (Fin n) ℂ) : ℝ≥0∞ :=
  if LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker rho.mulVecLin then
    ENNReal.ofReal (qRelEntropy rho sigma / Real.log 2)
  else ⊤

/-- PDF p.24, (147): full normalized Umegaki entropy via finite orthogonal
compressions of generalized entropy, following accepted Dependency50.P13.
The extended supremum retains infinity; no entropy finiteness is assumed. -/
def hilbertRelativeEntropy (rho sigma : H →L[ℂ] H) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ v : {v : Fin n → H // Orthonormal ℂ v},
    compressedRelativeEntropy (compression v.val rho) (compression v.val sigma)

/-- PDF p.24, Definition B.1: finite positive bounded effects summing to identity. -/
def IsHilbertPOVM {n : ℕ} (M : Fin n → H →L[ℂ] H) : Prop :=
  (∀ i, (M i).IsPositive) ∧ ∑ i, M i = 1

/-- PDF p.24, Definition B.1: supremum over all finite POVMs, without attainment. -/
def measuredRelativeEntropy {I : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : H →L[ℂ] H) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ M : {M : Fin n → H →L[ℂ] H // IsHilbertPOVM M},
    classicalKL
      (fun i => (hilbertTrace b ((M.val i).comp rho)).re)
      (fun i => (hilbertTrace b ((M.val i).comp sigma)).re)

/-- PDF p.27: finite-rank orthogonal projector, with no nesting requirement. -/
def IsFiniteProjector (P : H →L[ℂ] H) : Prop :=
  P.adjoint = P ∧ P.comp P = P ∧ FiniteDimensional ℂ (LinearMap.range P.toLinearMap)

/-- PDF p.27: weak operator convergence to identity against every pair of vectors. -/
def WeaklyExhausts (P : ℕ → H →L[ℂ] H) : Prop :=
  ∀ x y : H, Tendsto (fun n => inner ℂ x (P n y)) atTop (nhds (inner ℂ x y))

example : IsTraceClass (0 : H →L[ℂ] H) := by
  unfold IsTraceClass QAlgorithms.Papers.Independent.Dependency50.P13.NuclearRepresentation
  refine ⟨fun _ => 0, fun _ => 0, ?_, ?_⟩
  · simp
  · intro x
    simp

example {I : Type*} (b : HilbertBasis I ℂ H) : hilbertTrace b 0 = 0 := by
  simp [hilbertTrace]

example {I : Type*} (b : HilbertBasis I ℂ H) : ¬ IsHilbertDensity b 0 := by
  simp [IsHilbertDensity, hilbertTrace]

example {I : Type*} (b : HilbertBasis I ℂ H) : hilbertFidelity b 0 0 = 0 := by
  simp [hilbertFidelity, hilbertTrace]

example {I : Type*} (b : HilbertBasis I ℂ H) : hilbertTraceNorm b 0 = 0 := by
  simp [hilbertTraceNorm, hilbertTrace]

example : OrthogonalBlocks (0 : H →L[ℂ] H) 0 0 0 := by
  simp [OrthogonalBlocks]

example : WeaklyExhausts (fun _ : ℕ => (1 : H →L[ℂ] H)) := by
  intro x y
  simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => inner ℂ x y) atTop
    (nhds (inner ℂ x y)))

example (rho sigma : H →L[ℂ] H) : hilbertMix 0 rho sigma = sigma := by
  simp [hilbertMix]

example (rho sigma : H →L[ℂ] H) : hilbertMix 1 rho sigma = rho := by
  simp [hilbertMix]

example : classicalKL (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 0) = ⊤ := by
  simp [classicalKL]

example : classicalKL (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 1) = 0 := by
  simp [classicalKL]

example {n : ℕ} (rho sigma : Matrix (Fin n) (Fin n) ℂ)
    (h : ¬ LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker rho.mulVecLin) :
    compressedRelativeEntropy rho sigma = ⊤ := by
  simp [compressedRelativeEntropy, h]

example {n : ℕ} (v : Fin n → H) : compression v (0 : H →L[ℂ] H) = 0 := by
  ext i j
  simp [compression]

example : IsHilbertPOVM (fun _ : Fin 1 => (1 : H →L[ℂ] H)) := by
  simp [IsHilbertPOVM, ContinuousLinearMap.isPositive_one]

example : IsFiniteProjector (0 : H →L[ℂ] H) := by
  refine ⟨by simp, by simp, ?_⟩
  change FiniteDimensional ℂ (LinearMap.range (0 : H →ₗ[ℂ] H))
  rw [LinearMap.range_zero]
  infer_instance

variable {A B C E G : Type*}

/-- PDF pp.1,19: finite von Neumann entropy in bits, with 0 log 0 = 0. -/
def finiteEntropyBits {J : Type*} [Fintype J] [DecidableEq J]
    (rho : Matrix J J ℂ) : ℝ :=
  -(cfc (fun x : ℝ => x * Real.logb 2 x) rho).trace.re

/-- PDF p.19, (117): four finite entropies, never used for infinite systems. -/
def finiteCMI [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (rho : Matrix (A × (B × C)) (A × (B × C)) ℂ) : ℝ :=
  finiteEntropyBits (marginalAB rho) + finiteEntropyBits (traceLeft rho) -
    finiteEntropyBits (fun b b2 => ∑ c, (traceLeft rho) (b,c) (b2,c)) -
    finiteEntropyBits rho

/-- PDF pp.2,19: spectral support projection, including a zero kernel. -/
def finiteSupport {J : Type*} [Fintype J] [DecidableEq J]
    (rho : Matrix J J ℂ) : Matrix J J ℂ :=
  rho * cfc (fun x : ℝ => x⁻¹) rho

/-- PDF pp.19,22,28, (116),(134): rotated transpose formula on supported inputs.
The inverse square root is zero at a zero eigenvalue. -/
def rotatedTranspose [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    (rhoBC : Matrix (B × C) (B × C) ℂ) (U : Matrix B B ℂ)
    (V : Matrix (B × C) (B × C) ℂ) (X : Matrix B B ℂ) :
    Matrix (B × C) (B × C) ℂ :=
  let rhoB : Matrix B B ℂ := fun b b2 => ∑ c, rhoBC (b,c) (b2,c)
  let D := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) rhoB
  let S := cfc Real.sqrt rhoBC
  V * S * Matrix.kronecker (D * U * X * Uᴴ * D) (1 : Matrix C C ℂ) * S * Vᴴ

example {J : Type*} [Fintype J] [DecidableEq J] :
    finiteSupport (0 : Matrix J J ℂ) = 0 := by
  simp [finiteSupport]

example {J : Type*} [Fintype J] [DecidableEq J] :
    finiteEntropyBits (0 : Matrix J J ℂ) = 0 := by
  simp [finiteEntropyBits, cfc_zero]

example [Fintype C] : marginalAB (0 : Matrix (A × (B × C)) (A × (B × C)) ℂ) = 0 := by
  ext p q
  simp [marginalAB]

example [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    (rhoBC : Matrix (B × C) (B × C) ℂ) (U : Matrix B B ℂ)
    (V : Matrix (B × C) (B × C) ℂ) : rotatedTranspose rhoBC U V 0 = 0 := by
  simp [rotatedTranspose]

/-- PDF p.26: a linear map in Choi coordinates, with input index first. -/
def mapChoi [Fintype E] [DecidableEq E]
    (Phi : Matrix E E ℂ →ₗ[ℂ] Matrix G G ℂ) : Matrix (E × G) (E × G) ℂ :=
  fun p q => Phi (Matrix.single p.1 q.1 1) p.2 q.2

/-- PDF p.26: topology of all Choi entries, a finite map-coordinate topology. -/
def finiteMapTopology [Fintype E] [DecidableEq E] :
    TopologicalSpace (Matrix E E ℂ →ₗ[ℂ] Matrix G G ℂ) :=
  TopologicalSpace.induced mapChoi inferInstance

/-- PDF p.26, Remark C.3: complete positivity via its Choi representation. -/
def FiniteCP [Fintype E] [Fintype G] [DecidableEq E]
    (Phi : Matrix E E ℂ →ₗ[ℂ] Matrix G G ℂ) : Prop :=
  (mapChoi Phi).PosSemidef

/-- PDF p.26: trace nonincrease on every positive, possibly unnormalized input. -/
def FiniteTNI [Fintype E] [Fintype G]
    (Phi : Matrix E E ℂ →ₗ[ℂ] Matrix G G ℂ) : Prop :=
  ∀ X, X.PosSemidef → (Phi X).trace.re ≤ X.trace.re

/-- PDF p.26: full trace preservation of a complex-linear map. -/
def FiniteTP [Fintype E] [Fintype G]
    (Phi : Matrix E E ℂ →ₗ[ℂ] Matrix G G ℂ) : Prop :=
  ∀ X, (Phi X).trace = X.trace

example [Fintype E] [DecidableEq E] :
    mapChoi (0 : Matrix E E ℂ →ₗ[ℂ] Matrix G G ℂ) = 0 := by
  ext p q
  simp [mapChoi]

example [Fintype E] :
    FiniteTP (LinearMap.id : Matrix E E ℂ →ₗ[ℂ] Matrix E E ℂ) := by
  intro X
  rfl

/-- PDF p.28, (169): the diagonal qubit counterexample, A tensor (B tensor C),
false = zero. Its trace is 1/2 + 4/8 = 1. -/
def counterexampleState : Matrix (Bool × (Bool × Bool)) (Bool × (Bool × Bool)) ℂ :=
  Matrix.diagonal fun z => if z.1 then (1/8 : ℂ)
    else if z.2 = (false, false) then (1/2 : ℂ) else 0

/-- PDF p.28, (171): measure B in its basis, then prepare the prescribed state.
This full linear map kills off-diagonal matrix units. -/
def counterexampleRecovery : Superop Bool (Bool × Bool) :=
  fun X => Matrix.diagonal fun z =>
    if z = (false, false) then X false false else (1/3 : ℂ) * X true true

/-- PDF pp.22,28, (134),(170): full transpose map, with invertible rhoB. -/
def counterexampleTranspose : Superop Bool (Bool × Bool) :=
  rotatedTranspose (traceLeft counterexampleState) 1 1

/-- PDF p.2, (3): optimal root fidelity over all full CPTP recovery channels.
For density inputs the set is nonempty and bounded by one. -/
def finiteRecoveryFidelity [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (rho : Matrix (A × (B × C)) (A × (B × C)) ℂ) : ℝ :=
  ⨆ R : {R : Superop B (B × C) // IsChannel R},
    rootFidelity rho (idTensorSuperop R.val (marginalAB rho))

example : counterexampleState (false, (false, false)) (false, (false, false)) = 1/2 := by
  norm_num [counterexampleState]

example : counterexampleRecovery (Matrix.single false true 1) = 0 := by
  ext p q
  simp [counterexampleRecovery, Matrix.diagonal, Matrix.single]

end QAlgorithms.Papers.Independent.Support50.P44


