-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P62
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P62
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T08:30:15.539905+00:00
-- url     : https://prove2.me/theorems/2a06143a-b098-4977-b99b-4200f919edf7
-- title:
--   Definitions for Steering, Entanglement, Nonlocality, and the EPR Paradox
-- statement:
--   The objects the formalized statements of *Steering, Entanglement, Nonlocality, and the EPR Paradox* (arXiv:quant-ph/0612147) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ProjectiveResolution`: PDF p.2: a complete orthogonal spectral resolution, with zero projectors permitted for padding unused outcome labels. This includes degenerate observables.
--   - `IsResponse`: PDF p.2, (3),(5),(6): for each setting, a measurable stochastic kernel on the hidden variable, with no strict positivity requirement. No measurability in the external setting parameter is imposed by the source.
--   - `IsHiddenEnsemble`: PDF p.2: one normalized ensemble of arbitrary Bob density matrices. Integrability excludes the Bochner integral's default value on bad inputs.
--   - `assemblage`: PDF p.2, before (5): unnormalized conditional Bob operator. In particular, a zero-probability outcome is kept as a zero operator, never renormalized.
--   - `jointProbability`: PDF p.2, (2): joint Born outcome probability.
--   - `HasProjectiveLHS`: PDF p.2, (5): one ensemble and one response family precede every setting and outcome. The sample space is arbitrary and may support continuous mixtures.
--   - `HasHybrid`: PDF p.2, (6): hybrid factorization against every Bob projective observable, with the same ensemble and Alice kernel for all Bob settings and outcomes.
--   - `HasBellLocal`: PDF p.2, (3): one local hidden-variable model for all local projective settings. Each response sees only its own setting and the shared variable.
--   - `Steerable`: PDF pp.2--3: state-level Alice-to-Bob steering, allowing all projective observables. A model for all settings also models every restricted strategy.
--   - `BellNonlocal`: PDF p.2: state-level Bell nonlocality for single-copy projective measurements.
--   - `wernerEta`: PDF p.3, (8): convert the paper's eta to the antisymmetric weight p=(d-1+(d+1)eta)/(2d) of the frozen Werner family. For d>=2 this is exactly Eq.(8), including the physical negative-eta interval. The frozen family uses a different parameter, so it cannot be applied directly at eta.
--   - `oneProjective`: Sanity: the one-dimensional projective measurement has a single certain outcome.
-- source:
--   Steering, Entanglement, Nonlocality, and the EPR Paradox, arXiv:quant-ph/0612147v3, https://arxiv.org/abs/quant-ph/0612147v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04

/-!
Wiseman--Jones--Doherty, arXiv:quant-ph/0612147v3, PDF pp.1--4.
Finite-dimensional, single-copy, local projective measurements only. Steering is
from Alice to Bob. All hidden-variable integrals below use genuine probability
measures; hidden states may be mixed. The general-Hilbert-space hierarchy and hybrid equivalence, and Gaussian
Theorem 2, are explicitly deferred in the unit's HARD.md. The finite model
below is used to state only the Werner and isotropic steering thresholds.

A d-dimensional projective measurement has at most d nonzero spectral
projectors. Fin d labels accommodate every such measurement by zero padding;
relabeling the distinct eigenvalues does not change either hidden-model test.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

namespace QAlgorithms.Papers.Independent.Intakethird100.P62

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2: continuous extended norm for finite-dimensional operator integrals.
The elementwise matrix norm and topology are those of the underlying function space. -/
local instance matrixContinuousENorm (d : ℕ) : ContinuousENorm (Mat (Fin d)) :=
  inferInstanceAs (ContinuousENorm (Fin d → Fin d → ℂ))

/-- Sanity: the selected matrix extended norm is continuous in every finite dimension. -/
example (d : ℕ) : Continuous (enorm : Mat (Fin d) → ENNReal) :=
  ContinuousENorm.continuous_enorm

/-- PDF p.2: Borel structure for finite-dimensional density-operator ensembles. -/
local instance matrixMeasurable (d : ℕ) : MeasurableSpace (Mat (Fin d)) := borel _

/-- PDF p.2: a complete orthogonal spectral resolution, with zero projectors
permitted for padding unused outcome labels. This includes degenerate observables. -/
structure ProjectiveResolution (d : ℕ) where
  projector : Fin d → Mat (Fin d)
  hermitian : ∀ a, (projector a).IsHermitian
  idempotent : ∀ a, projector a * projector a = projector a
  orthogonal : ∀ a b, a ≠ b → projector a * projector b = 0
  complete : ∑ a, projector a = 1

/-- PDF p.2, (3),(5),(6): for each setting, a measurable stochastic kernel
on the hidden variable, with no strict positivity requirement. No measurability
in the external setting parameter is imposed by the source. -/
def IsResponse {Omega S : Type} [MeasurableSpace Omega] {d : ℕ}
    (r : S → Fin d → Omega → ℝ) : Prop :=
  (∀ s a, Measurable (r s a)) ∧
  (∀ s a w, 0 ≤ r s a w) ∧
  (∀ s w, ∑ a, r s a w = 1)

/-- PDF p.2: one normalized ensemble of arbitrary Bob density matrices.
Integrability excludes the Bochner integral's default value on bad inputs. -/
def IsHiddenEnsemble {Omega : Type} [MeasurableSpace Omega] {b : ℕ}
    (mu : Measure Omega) (rho : Omega → Mat (Fin b)) : Prop :=
  IsProbabilityMeasure mu ∧ Measurable rho ∧ Integrable rho mu ∧
  ∀ w, IsDensityMatrix (rho w)

/-- PDF p.2, before (5): unnormalized conditional Bob operator. In particular,
a zero-probability outcome is kept as a zero operator, never renormalized. -/
def assemblage {a b : ℕ} (W : Mat (Fin a × Fin b)) (A : ProjectiveResolution a) (x : Fin a) : Mat (Fin b) :=
  traceLeft (W * Matrix.kronecker (A.projector x) (1 : Mat (Fin b)))

/-- PDF p.2, (2): joint Born outcome probability. -/
def jointProbability {a b : ℕ} (W : Mat (Fin a × Fin b))
    (A : ProjectiveResolution a) (B : ProjectiveResolution b) (x : Fin a) (y : Fin b) : ℝ :=
  effectProb (Matrix.kronecker (A.projector x) (B.projector y)) W

/-- PDF p.2, (5): one ensemble and one response family precede every setting
and outcome. The sample space is arbitrary and may support continuous mixtures. -/
def HasProjectiveLHS {a b : ℕ} (W : Mat (Fin a × Fin b)) (M : Set (ProjectiveResolution a)) : Prop :=
  ∃ (Omega : Type) (m : MeasurableSpace Omega),
    letI : MeasurableSpace Omega := m
    ∃ (mu : Measure Omega) (rho : Omega → Mat (Fin b))
      (r : M → Fin a → Omega → ℝ),
      IsHiddenEnsemble mu rho ∧ IsResponse r ∧
      (∀ A x, Integrable (fun w => (r A x w : ℂ) • rho w) mu) ∧
      ∀ A x, assemblage W A.val x = ∫ w, (r A x w : ℂ) • rho w ∂mu

/-- PDF p.2, (6): hybrid factorization against every Bob projective observable,
with the same ensemble and Alice kernel for all Bob settings and outcomes. -/
def HasHybrid {a b : ℕ} (W : Mat (Fin a × Fin b)) (M : Set (ProjectiveResolution a)) : Prop :=
  ∃ (Omega : Type) (m : MeasurableSpace Omega),
    letI : MeasurableSpace Omega := m
    ∃ (mu : Measure Omega) (rho : Omega → Mat (Fin b))
      (r : M → Fin a → Omega → ℝ),
      IsHiddenEnsemble mu rho ∧ IsResponse r ∧
      (∀ A x (B : ProjectiveResolution b) y,
        Integrable (fun w => r A x w * effectProb (B.projector y) (rho w)) mu) ∧
      ∀ A x (B : ProjectiveResolution b) y, jointProbability W A.val B x y =
        ∫ w, r A x w * effectProb (B.projector y) (rho w) ∂mu

/-- PDF p.2, (3): one local hidden-variable model for all local projective
settings. Each response sees only its own setting and the shared variable. -/
def HasBellLocal {a b : ℕ} (W : Mat (Fin a × Fin b)) : Prop :=
  ∃ (Omega : Type) (m : MeasurableSpace Omega),
    letI : MeasurableSpace Omega := m
    ∃ (mu : Measure Omega)
      (r : ProjectiveResolution a → Fin a → Omega → ℝ)
      (s : ProjectiveResolution b → Fin b → Omega → ℝ),
      IsProbabilityMeasure mu ∧ IsResponse r ∧ IsResponse s ∧
      (∀ A B x y, Integrable (fun w => r A x w * s B y w) mu) ∧
      ∀ A B x y, jointProbability W A B x y = ∫ w, r A x w * s B y w ∂mu

/-- PDF pp.2--3: state-level Alice-to-Bob steering, allowing all projective
observables. A model for all settings also models every restricted strategy. -/
def Steerable {a b : ℕ} (W : Mat (Fin a × Fin b)) : Prop :=
  ¬ HasProjectiveLHS W Set.univ

/-- PDF p.2: state-level Bell nonlocality for single-copy projective measurements. -/
def BellNonlocal {a b : ℕ} (W : Mat (Fin a × Fin b)) : Prop := ¬ HasBellLocal W

/-- PDF p.3, (8): convert the paper's eta to the antisymmetric weight
p=(d-1+(d+1)eta)/(2d) of the frozen Werner family. For d>=2 this is
exactly Eq.(8), including the physical negative-eta interval. The frozen
family uses a different parameter, so it cannot be applied directly at eta. -/
def wernerEta (d : ℕ) (eta : ℝ) : Mat (Fin d × Fin d) :=
  QAlgorithms.Papers.Independent.Information100.P04.werner d
    (((d : ℝ) - 1 + ((d : ℝ) + 1) * eta) / (2 * (d : ℝ)))

/-- Sanity: the one-dimensional projective measurement has a single certain outcome. -/
def oneProjective : ProjectiveResolution 1 where
  projector := fun _ => 1
  hermitian := by intro x; simp
  idempotent := by intro x; simp
  orthogonal := by
    intro x y h
    exact (h (Subsingleton.elim x y)).elim
  complete := by simp

/-- Sanity: stochastic kernels can have constant deterministic responses. -/
example {Omega S : Type} [MeasurableSpace Omega] :
    IsResponse (fun (_ : S) (_ : Fin 1) (_ : Omega) => (1 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s x; exact measurable_const
  · intro s x w; norm_num
  · intro s w; simp

/-- Sanity: impossible outcomes never invoke a normalized conditional state. -/
example {a b : ℕ} (A : ProjectiveResolution a) (x : Fin a) :
    assemblage (0 : Mat (Fin a × Fin b)) A x = 0 := by
  ext i j
  simp [assemblage, traceLeft]

/-- Sanity: eta=0 in (8) is the maximally mixed product density. -/
example : wernerEta 2 0 = (1 / 4 : ℂ) • (1 : Mat (Fin 2 × Fin 2)) := by
  norm_num [wernerEta, QAlgorithms.Papers.Independent.Information100.P04.werner,
    QAlgorithms.Papers.Independent.Information100.P04.wernerP1] <;> module

/-- Sanity: the two-qubit eta=1 endpoint has antisymmetric weight one. -/
example : wernerEta 2 1 =
    QAlgorithms.Papers.Independent.Information100.P04.werner 2 1 := by
  norm_num [wernerEta]

/-- Sanity: at d=2 the finite harmonic number is 3/2. -/
example : (harmonic 2 : ℝ) = 3 / 2 := by norm_num [harmonic, Finset.sum_range_succ]

end QAlgorithms.Papers.Independent.Intakethird100.P62


