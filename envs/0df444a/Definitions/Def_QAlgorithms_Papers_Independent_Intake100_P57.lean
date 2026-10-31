-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P57
-- name    : QAlgorithms_Papers_Independent_Intake100_P57
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T13:56:43.811342+00:00
-- url     : https://prove2.me/theorems/7b342554-724a-431f-ab2b-cb5e66833cd9
-- title:
--   Definitions for Simplified instantaneous non-local quantum computation with applications to position-based cryptography
-- statement:
--   The objects the formalized statements of *Simplified instantaneous non-local quantum computation with applications to position-based cryptography* (arXiv:1101.1065) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `sourceChoi`: PDF pp.7–8: the accepted normalized Choi state, permuted from reference,output order into the source's output,reference order.
--   - `bellPorts`: PDF p.6: density of exactly N copies of Phi_d, in Alice-ports,Bob-ports order. The amplitudes have coefficient d^(-N/2), hence density coefficient d^(-N). Physical uses require d>0.
--   - `retainPort`: PDF p.6, (5): retain port i, tracing out every other port, without corrections.
--   - `pbtInput`: PDF p.6: the input tensor the fixed Bell resource, reordered as (input,Alice-ports),Bob-ports. This resource never depends on the input.
--   - `pbtChannel`: PDF p.6, (5): Alice measures E, Bob retains the named port. Left multiplication by the effect followed by partial trace equals the corresponding measurement branch; no outcome-dependent operation on the retained port is included.
--   - `InstantMeasurement`: Fig.1, PDF pp.1–2: simultaneous local POVMs and unrestricted finite classical outcomes, with a function evaluated in the common causal future. All data are chosen before the unknown input. The resource is supplied separately.
--   - `instantEffect`: Fig.1 Born statistics: the induced effect after contraction with the normalized resource eta. Tensor order is input-A,input-B and resource-A,resource-B. Only classical outcomes are simulated, not conditional postmeasurement states.
--   - `IsMUB`: Section IV, PDF p.9: the columns of distinct unitary bases have squared overlap 1/d. There are d+1 basis labels, and d columns per basis.
--   - `mubEffect`: PDF p.11, corrected probability effects for (13): block diagonal in a, with block |e_x^a><e_x^a|. Equivalently U_AB^dagger(I tensor |x><x|)U_AB. The printed (I tensor |x><x|)U_AB is a Kraus operator, not a POVM effect. The construction requires Alice dimension d+1, correcting the p.12 dimension typo.
--   - `mubState`: The normalized ensemble rho_x in Theorem IV.1, PDF p.10. The basis label a is uniform and independent of the uniformly sampled x.
--   - `mubSuccess`: PDF p.10: average success, with x uniform and all physical measurement data fixed independently of x.
--   - `ensembleMeanRank`: PDF p.16: arithmetic mean of the ranks of the individual states.
-- source:
--   Simplified instantaneous non-local quantum computation with applications to position-based cryptography, arXiv:1101.1065v3, https://arxiv.org/abs/1101.1065v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

/-!
Beigi–Koenig, arXiv:1101.1065v3. Citations use PDF page numbers.
Local definitions specify the source's tensor coordinates and protocols explicitly.
The accepted normalized Choi state is reused with an explicit swap.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P57

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

-- P34 uses half the channel distance. Every occurrence below is multiplied by two.
open QAlgorithms.Papers.Independent.Information100.P34 (diamondDistance)
open QAlgorithms.Papers.Independent.Dependency50.P07 (ensembleMean)

/- PDF p.7, (7): on differences of CPTP maps the full stabilized induced
trace norm equals twice the accepted P34.diamondDistance, whose optimization
uses normalized density matrices and an input-sized reference. PDF p.8 states
this equivalence explicitly. No new diamond-distance definition is introduced. -/

/-- Sanity: identical maps have zero distance whenever a normalized input exists. -/
example {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (F : Superop I O) (rho : Matrix (I × I) (I × I) ℂ)
    (hrho : IsDensityMatrix rho) : 2 * diamondDistance F F = 0 := by
  have hs : {v : ℝ | ∃ tau : Matrix (I × I) (I × I) ℂ,
      IsDensityMatrix tau ∧ v = traceNorm
        (idTensorSuperop (R := I) F tau - idTensorSuperop (R := I) F tau) / 2} = {0} := by
    ext v
    constructor
    · rintro ⟨tau, _, hv⟩
      simpa [traceNorm, cfc_zero] using hv
    · intro hv
      have hv0 : v = 0 := Set.mem_singleton_iff.mp hv
      subst v
      exact ⟨rho, hrho, by simp [traceNorm, cfc_zero]⟩
  unfold diamondDistance
  rw [hs, csSup_singleton]
  norm_num

/-- PDF pp.7–8: the accepted normalized Choi state, permuted from
reference,output order into the source's output,reference order. -/
def sourceChoi {I O : Type*} [Fintype I] [DecidableEq I] (F : Superop I O) :
    Matrix (O × I) (O × I) ℂ :=
  fun p q => QAlgorithms.Papers.Independent.Support50.P11.choiState F
    (p.2, p.1) (q.2, q.1)

/-- Sanity: the swap preserves every diagonal entry under its coordinate bijection. -/
example {I O : Type*} [Fintype I] [DecidableEq I] (F : Superop I O)
    (o : O) (i : I) : sourceChoi F (o,i) (o,i) =
      QAlgorithms.Papers.Independent.Support50.P11.choiState F (i,o) (i,o) := by
  rfl

/-- PDF p.6: density of exactly N copies of Phi_d, in Alice-ports,Bob-ports
order. The amplitudes have coefficient d^(-N/2), hence density coefficient d^(-N).
Physical uses require d>0. -/
def bellPorts (d N : ℕ) :
    Matrix ((Fin N → Fin d) × (Fin N → Fin d))
      ((Fin N → Fin d) × (Fin N → Fin d)) ℂ :=
  fun p q => if p.1 = p.2 ∧ q.1 = q.2 then ((d : ℂ) ^ N)⁻¹ else 0

/-- Sanity: the unique entry of one dimension-one Bell pair is one. -/
example : bellPorts 1 1 ((fun _ => 0), (fun _ => 0))
    ((fun _ => 0), (fun _ => 0)) = 1 := by
  norm_num [bellPorts]

/-- PDF p.6, (5): retain port i, tracing out every other port, without corrections. -/
def retainPort {d N : ℕ} (i : Fin N)
    (R : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun b c => ∑ p : Fin N → Fin d, ∑ q : Fin N → Fin d,
    if p i = b ∧ q i = c ∧ (∀ j, j ≠ i → p j = q j) then R p q else 0

/-- PDF p.6: the input tensor the fixed Bell resource, reordered as
(input,Alice-ports),Bob-ports. This resource never depends on the input. -/
def pbtInput {d N : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix ((Fin d × (Fin N → Fin d)) × (Fin N → Fin d))
      ((Fin d × (Fin N → Fin d)) × (Fin N → Fin d)) ℂ :=
  fun p q => X p.1.1 q.1.1 * bellPorts d N (p.1.2,p.2) (q.1.2,q.2)

/-- PDF p.6, (5): Alice measures E, Bob retains the named port. Left multiplication
by the effect followed by partial trace equals the corresponding measurement branch;
no outcome-dependent operation on the retained port is included. -/
def pbtChannel {d N : ℕ}
    (E : Fin N → Matrix (Fin d × (Fin N → Fin d))
      (Fin d × (Fin N → Fin d)) ℂ) : Superop (Fin d) (Fin d) :=
  fun X => ∑ i, retainPort i
    (traceLeft (Matrix.kronecker (E i)
      (1 : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) * pbtInput X))

/-- Sanity: zero input gives zero output, rather than a prepared fixed state. -/
example {d N : ℕ}
    (E : Fin N → Matrix (Fin d × (Fin N → Fin d))
      (Fin d × (Fin N → Fin d)) ℂ) : pbtChannel E 0 = 0 := by
  classical
  have input_zero : pbtInput (d := d) (N := N) (0 : Matrix (Fin d) (Fin d) ℂ) = 0 := by
    ext p q
    simp [pbtInput]
  unfold pbtChannel
  rw [input_zero]
  simp only [Matrix.mul_zero]
  ext b c
  simp [traceLeft, retainPort, Matrix.sum_apply]

/-- PDF p.9: the classical-output channels are written directly with the
imported Matrix.diagonal and complex trace below. The frozen namesake
ClassicalShadows.measurementChannel is an averaged measurement-and-repreparation
channel with a different input and output model, so it cannot be substituted.

Sanity: the singleton identity measurement keeps the trace as its sole output. -/
example {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) :
    (Matrix.diagonal (fun _ : Fin 1 => ((1 : Matrix I I ℂ) * X).trace)) 0 0 = X.trace := by
  simp

/-- Fig.1, PDF pp.1–2: simultaneous local POVMs and unrestricted finite
classical outcomes, with a function evaluated in the common causal future.
All data are chosen before the unknown input. The resource is supplied separately. -/
structure InstantMeasurement (a b l r o : ℕ) where
  alpha : ℕ
  beta : ℕ
  alice : Fin alpha → Matrix (Fin a × Fin l) (Fin a × Fin l) ℂ
  bob : Fin beta → Matrix (Fin b × Fin r) (Fin b × Fin r) ℂ
  alice_povm : IsPOVM alice
  bob_povm : IsPOVM bob
  output : Fin alpha → Fin beta → Fin o

/-- Fig.1 Born statistics: the induced effect after contraction with the
normalized resource eta. Tensor order is input-A,input-B and resource-A,resource-B.
Only classical outcomes are simulated, not conditional postmeasurement states. -/
def instantEffect {a b l r o : ℕ} (s : InstantMeasurement a b l r o)
    (eta : Matrix (Fin l × Fin r) (Fin l × Fin r) ℂ) :
    Fin o → Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ :=
  fun x p q => ∑ alpha, ∑ beta,
    if s.output alpha beta = x then
      ∑ u : Fin l × Fin r, ∑ v : Fin l × Fin r,
        eta v u * s.alice alpha (p.1,u.1) (q.1,v.1) *
          s.bob beta (p.2,u.2) (q.2,v.2)
    else 0

/-- Sanity: an absent (zero) resource has zero Born weight. Physical uses below
require trace one, so this cannot produce a spurious successful protocol. -/
example {a b l r o : ℕ} (s : InstantMeasurement a b l r o) :
    instantEffect s 0 = 0 := by
  classical
  funext x p q
  simp [instantEffect]

/-- Section IV, PDF p.9: the columns of distinct unitary bases have squared
overlap 1/d. There are d+1 basis labels, and d columns per basis. -/
def IsMUB (d : ℕ) (U : Fin (d+1) → Matrix.unitaryGroup (Fin d) ℂ) : Prop :=
  ∀ a b, a ≠ b → ∀ x y : Fin d,
    Complex.normSq (((U a : Matrix (Fin d) (Fin d) ℂ)ᴴ *
      (U b : Matrix (Fin d) (Fin d) ℂ)) x y) = 1 / (d : ℝ)

/-- PDF p.11, corrected probability effects for (13): block diagonal in a,
with block |e_x^a><e_x^a|. Equivalently U_AB^dagger(I tensor |x><x|)U_AB.
The printed (I tensor |x><x|)U_AB is a Kraus operator, not a POVM effect.
The construction requires Alice dimension d+1, correcting the p.12 dimension typo. -/
def mubEffect {d : ℕ} (U : Fin (d+1) → Matrix.unitaryGroup (Fin d) ℂ) :
    Fin d → Matrix (Fin (d+1) × Fin d) (Fin (d+1) × Fin d) ℂ :=
  fun x p q => if p.1 = q.1 then
    (U p.1 : Matrix (Fin d) (Fin d) ℂ) p.2 x *
      conj ((U p.1 : Matrix (Fin d) (Fin d) ℂ) q.2 x) else 0

/-- Sanity: off-diagonal basis-label blocks vanish in the corrected effects. -/
example {d : ℕ} (U : Fin (d+1) → Matrix.unitaryGroup (Fin d) ℂ)
    (x : Fin d) (p q : Fin (d+1) × Fin d) (h : p.1 ≠ q.1) :
    mubEffect U x p q = 0 := by
  simp [mubEffect, h]

/-- The normalized ensemble rho_x in Theorem IV.1, PDF p.10.
The basis label a is uniform and independent of the uniformly sampled x. -/
def mubState {d : ℕ} (U : Fin (d+1) → Matrix.unitaryGroup (Fin d) ℂ)
    (x : Fin d) : Matrix (Fin (d+1) × Fin d) (Fin (d+1) × Fin d) ℂ :=
  ((d+1 : ℂ)⁻¹) • mubEffect U x

/-- PDF p.10: average success, with x uniform and all physical measurement
data fixed independently of x. -/
def mubSuccess {d l r : ℕ} (U : Fin (d+1) → Matrix.unitaryGroup (Fin d) ℂ)
    (s : InstantMeasurement (d+1) d l r d)
    (eta : Matrix (Fin l × Fin r) (Fin l × Fin r) ℂ) : ℝ :=
  (d : ℝ)⁻¹ * ∑ x, effectProb (instantEffect s eta x) (mubState U x)

/-- Sanity: the ensemble definition averages all d+1 basis-label blocks. -/
example {d : ℕ} (U : Fin (d+1) → Matrix.unitaryGroup (Fin d) ℂ) (x : Fin d) :
    mubState U x = ((d+1 : ℂ)⁻¹) • mubEffect U x := by rfl

/-- PDF p.16: arithmetic mean of the ranks of the individual states. -/
def ensembleMeanRank {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ}
    (eta : Fin N → Matrix I I ℂ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, (Matrix.rank (eta i) : ℝ)

/-- Sanity: a singleton ensemble has its original density and rank. -/
example {I : Type} [Fintype I] [DecidableEq I] (eta : Fin 1 → Matrix I I ℂ) :
    ensembleMean ⟨(fun _ : Fin 1 => 1), eta⟩ = eta 0 ∧
      ensembleMeanRank eta = Matrix.rank (eta 0) := by
  simp [ensembleMean, QAlgorithms.Papers.Independent.Information100.P27.average,
    ensembleMeanRank]

end QAlgorithms.Papers.Independent.Intake100.P57


