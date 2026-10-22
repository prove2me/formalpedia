-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P16
-- name    : QAlgorithms_Papers_Independent_Gap20_P16
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T20:33:33.545643+00:00
-- url     : https://prove2.me/theorems/bfa0a6e5-8e6a-4fe5-ab39-7d9108682c34
-- title:
--   Definitions for Remarks on the classical capacity of quantum channel
-- statement:
--   The objects the formalized statements of *Remarks on the classical capacity of quantum channel* (arXiv:quant-ph/0212025) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `unitaryAction`: PDF p.2, (3): unitary conjugation on every operator.
--   - `ProjectiveRepresentation`: PDF pp.1--2: a projective unitary representation, continuous in its conjugation action. A continuous global choice of phase is not required.
--   - `CovariantBetween`: PDF p.2, (3),(6): covariance for input and output families on the SAME space.
--   - `CapacityEntropyIdentity`: PDF pp.1--2, (1),(2): capacity--minimum-output-entropy identity, with an attained minimum and an attaining FINITE ensemble. The reused Holevo capacity ranges over all finite normalized mixed-state ensembles. On positive finite-dimensional CPTP maps its score set is nonempty and bounded.
--   - `CharacterGroup`: PDF p.3: the FULL character group, written additively; evaluation takes values in the complex unit circle. This is not a chosen cyclic subgroup.
--   - `characterValue`: PDF p.3: evaluation beta(alpha) = exp(i <beta,alpha>).
--   - `FiniteAbelianWeylSystem`: PDF p.3: two ordinary unitary representations obeying the Weyl commutation law with the printed POSITIVE phase.
--   - `finiteAbelianWeylOperator`: PDF p.3: W_(alpha,beta) = U_alpha V_beta.
--   - `PositiveDefinite`: PDF pp.3--4: positive definiteness on the additive group, tested on all finite lists, including repetitions, using the full complex Hermitian PSD condition.
--   - `finiteAbelianWeylMultiplier`: PDF pp.3--4, constructive converse to (9): extend the prescribed Weyl values by their trace-basis expansion. On an irreducible finite Weyl system W_z/sqrt(d) is an orthonormal operator basis. The definition assumes neither positivity nor the channel property; these are conclusions below. At d=0 the inverse dimension is Lean's zero default, outside every theorem's domain.
--   - `WeylCovariant`: PDF p.3, (8): the adjoint-first convention of Weyl covariance.
--   - `fourierCharacteristic`: PDF p.4, (10): Fourier characteristic function of a law on Hhat x H, with the positive phase x(alpha) beta(y).
--   - `fourierMixture`: PDF p.4, (11), corrected: J(x,y)=(-y,x), with W_J X W_J^*. The printed W_J^* X W_J has the opposite Fourier phase.
-- source:
--   Remarks on the classical capacity of quantum channel, arXiv:quant-ph/0212025v1, https://arxiv.org/abs/quant-ph/0212025v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09

/-!
Holevo, Remarks on the classical capacity of quantum channel,
arXiv:quant-ph/0212025v1. Page numbers are PDF pages. Entropies are in bits.
Only accepted, pinned library modules are imported. Paper-local definitions
retain arbitrary positive dimensions and projective, rather than only ordinary,
representations. Equation (11) has its adjoints corrected as documented below.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P16

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

/-- PDF p.2, (3): unitary conjugation on every operator. -/
def unitaryAction {d : ℕ} (V : Unitary d) (X : Mat d) : Mat d :=
  (V : Mat d) * X * (V : Mat d)ᴴ

/-- PDF pp.1--2: a projective unitary representation, continuous in its
conjugation action. A continuous global choice of phase is not required. -/
structure ProjectiveRepresentation (G : Type*) [Group G] [TopologicalSpace G]
    (d : ℕ) where
  unitary : G → Unitary d
  multiply : ∀ g h, ∃ c : ℂ, ‖c‖ = 1 ∧
    (unitary (g * h) : Mat d) = c • ((unitary g : Mat d) * (unitary h : Mat d))
  continuous_conjugation : ∀ X : Mat d, Continuous (fun g => unitaryAction (unitary g) X)

/-- PDF p.2, (3),(6): covariance for input and output families on the SAME space. -/
def CovariantBetween {G : Type*} {d : ℕ} (Phi : Superop (Fin d) (Fin d))
    (V1 V2 : G → Unitary d) : Prop :=
  ∀ g X, Phi (unitaryAction (V1 g) X) = unitaryAction (V2 g) (Phi X)

/-- PDF pp.1--2, (1),(2): capacity--minimum-output-entropy identity,
with an attained minimum and an attaining FINITE ensemble. The reused Holevo
capacity ranges over all finite normalized mixed-state ensembles. On positive
finite-dimensional CPTP maps its score set is nonempty and bounded. -/
def CapacityEntropyIdentity {d : ℕ} (Phi : Superop (Fin d) (Fin d)) : Prop :=
  ∃ rho : Mat d, IsDensityMatrix rho ∧
    (∀ sigma : Mat d, IsDensityMatrix sigma → vnEntropy (Phi rho) ≤ vnEntropy (Phi sigma)) ∧
    QAlgorithms.Papers.Independent.Dependency50.P45.holevoCapacity Phi =
      Real.logb 2 d - vnEntropy (Phi rho) ∧
    ∃ e : QAlgorithms.Papers.Independent.Information100.P08.Ensemble (Fin d),
      QAlgorithms.Papers.Independent.Information100.P08.outputHolevo Phi e =
        QAlgorithms.Papers.Independent.Dependency50.P45.holevoCapacity Phi

example {d : ℕ} (X : Mat d) : unitaryAction (1 : Unitary d) X = X := by
  simp [unitaryAction]

example {G : Type*} [Group G] [TopologicalSpace G] (d : ℕ) :
    ProjectiveRepresentation G d where
  unitary := fun _ => 1
  multiply := by
    intro g h
    exact ⟨1, by simp, by simp⟩
  continuous_conjugation := by
    intro X
    simpa [unitaryAction] using (continuous_const : Continuous (fun _ : G => X))

example {G : Type*} {d : ℕ} (Phi : Superop (Fin d) (Fin d)) (V : G → Unitary d) :
    CovariantBetween Phi V V ↔ ∀ g X, Phi (unitaryAction (V g) X) = unitaryAction (V g) (Phi X) := by
  rfl

/-- PDF p.3: the FULL character group, written additively; evaluation takes
values in the complex unit circle. This is not a chosen cyclic subgroup. -/
abbrev CharacterGroup (H : Type*) [AddCommGroup H] := Additive (AddChar H Circle)

/-- PDF p.3: evaluation beta(alpha) = exp(i <beta,alpha>). -/
def characterValue {H : Type*} [AddCommGroup H] (beta : CharacterGroup H) (alpha : H) : ℂ :=
  ((Additive.toMul beta) alpha : ℂ)

/-- PDF p.3: two ordinary unitary representations obeying the Weyl
commutation law with the printed POSITIVE phase. -/
structure FiniteAbelianWeylSystem (H : Type*) [AddCommGroup H] (d : ℕ) where
  U : H → Unitary d
  V : CharacterGroup H → Unitary d
  U_zero : U 0 = 1
  V_zero : V 0 = 1
  U_add : ∀ a b, U (a + b) = U a * U b
  V_add : ∀ a b, V (a + b) = V a * V b
  commutation : ∀ a b, (V b : Mat d) * (U a : Mat d) =
    characterValue b a • ((U a : Mat d) * (V b : Mat d))

/-- PDF p.3: W_(alpha,beta) = U_alpha V_beta. -/
def finiteAbelianWeylOperator {H : Type*} [AddCommGroup H] {d : ℕ} (W : FiniteAbelianWeylSystem H d)
    (z : H × CharacterGroup H) : Unitary d := W.U z.1 * W.V z.2

/-- PDF pp.3--4: positive definiteness on the additive group, tested on all
finite lists, including repetitions, using the full complex Hermitian PSD condition. -/
def PositiveDefinite {A : Type*} [AddGroup A] (phi : A → ℂ) : Prop :=
  ∀ (n : ℕ) (z : Fin n → A),
    Matrix.PosSemidef (fun i j : Fin n => phi (z i - z j))

/-- PDF pp.3--4, constructive converse to (9): extend the prescribed Weyl
values by their trace-basis expansion. On an irreducible finite Weyl system
W_z/sqrt(d) is an orthonormal operator basis. The definition assumes neither
positivity nor the channel property; these are conclusions below. At d=0 the
inverse dimension is Lean's zero default, outside every theorem's domain. -/
def finiteAbelianWeylMultiplier {H : Type*} [AddCommGroup H] [Fintype H]
    [Fintype (CharacterGroup H)] {d : ℕ} (W : FiniteAbelianWeylSystem H d)
    (phi : H × CharacterGroup H → ℂ) : Superop (Fin d) (Fin d) :=
  fun X => ∑ z : H × CharacterGroup H,
    (((finiteAbelianWeylOperator W z : Mat d)ᴴ * X).trace / (d : ℂ) * phi z) •
      (finiteAbelianWeylOperator W z : Mat d)

/-- PDF p.3, (8): the adjoint-first convention of Weyl covariance. -/
def WeylCovariant {H : Type*} [AddCommGroup H] {d : ℕ}
    (W : FiniteAbelianWeylSystem H d) (Phi : Superop (Fin d) (Fin d)) : Prop :=
  ∀ z X, Phi ((finiteAbelianWeylOperator W z : Mat d)ᴴ * X * (finiteAbelianWeylOperator W z : Mat d)) =
    (finiteAbelianWeylOperator W z : Mat d)ᴴ * Phi X * (finiteAbelianWeylOperator W z : Mat d)

/-- PDF p.4, (10): Fourier characteristic function of a law on Hhat x H,
with the positive phase x(alpha) beta(y). -/
def fourierCharacteristic {H : Type*} [AddCommGroup H] [Fintype H] [Fintype (CharacterGroup H)]
    (p : CharacterGroup H × H → ℝ) (z : H × CharacterGroup H) : ℂ :=
  ∑ t, (p t : ℂ) * characterValue t.1 z.1 * characterValue z.2 t.2

/-- PDF p.4, (11), corrected: J(x,y)=(-y,x), with W_J X W_J^*.
The printed W_J^* X W_J has the opposite Fourier phase. -/
def fourierMixture {H : Type*} [AddCommGroup H] [Fintype H] [Fintype (CharacterGroup H)]
    {d : ℕ} (W : FiniteAbelianWeylSystem H d) (p : CharacterGroup H × H → ℝ) (X : Mat d) : Mat d :=
  ∑ t, (p t : ℂ) • unitaryAction (finiteAbelianWeylOperator W (-t.2, t.1)) X

example {H : Type*} [AddCommGroup H] {d : ℕ} (W : FiniteAbelianWeylSystem H d) :
    finiteAbelianWeylOperator W (0, 0) = 1 := by
  simp [finiteAbelianWeylOperator, W.U_zero, W.V_zero]

example {H : Type*} [AddCommGroup H] (b : CharacterGroup H) (a : H) :
    characterValue b a = ((Additive.toMul b) a : ℂ) := by rfl

example {A : Type*} [AddGroup A] (phi : A → ℂ) :
    PositiveDefinite phi ↔ ∀ n (z : Fin n → A),
      Matrix.PosSemidef (fun i j : Fin n => phi (z i - z j)) := by rfl

example {H : Type*} [AddCommGroup H] [Fintype H] [Fintype (CharacterGroup H)]
    (z : H × CharacterGroup H) : fourierCharacteristic (fun _ => 0) z = 0 := by
  simp [fourierCharacteristic]

example {H : Type*} [AddCommGroup H] [Fintype H] [Fintype (CharacterGroup H)]
    {d : ℕ} (W : FiniteAbelianWeylSystem H d) (X : Mat d) : fourierMixture W (fun _ => 0) X = 0 := by
  simp [fourierMixture]

example {H : Type*} [AddCommGroup H] [Fintype H] [Fintype (CharacterGroup H)]
    {d : ℕ} (W : FiniteAbelianWeylSystem H d) (X : Mat d) :
    finiteAbelianWeylMultiplier W (fun _ => 0) X = 0 := by
  simp [finiteAbelianWeylMultiplier]

end QAlgorithms.Papers.Independent.Gap20.P16


