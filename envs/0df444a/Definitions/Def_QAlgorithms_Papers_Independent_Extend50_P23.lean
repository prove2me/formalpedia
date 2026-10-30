-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P23
-- name    : QAlgorithms_Papers_Independent_Extend50_P23
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T17:39:46.512992+00:00
-- url     : https://prove2.me/theorems/5718c454-8b59-45ec-b433-61029a559322
-- title:
--   Definitions for RepLAB: a computational/numerical approach to representation theory
-- statement:
--   The objects the formalized statements of *RepLAB: a computational/numerical approach to representation theory* (arXiv:1911.09154) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsUnitaryRepresentation`: PDF p.3, Eq.(2) and footnote 8: a continuous complex unitary representation. The matrix homomorphism laws are included, even for zero-dimensional spaces.
--   - `Commutes`: PDF p.3, Eq.(4): membership in the full complex commutant, without a Hermitian, positivity, or trace restriction.
--   - `representationHaarProjection`: PDF p.4, Eq.(8): exact normalized-Haar averaging. Theorems supply the probability-Haar and continuity assumptions which make this integral genuine.
--   - `representationInvariant`: PDF pp.3,5: invariance of a complex linear subspace.
--   - `IrreducibleOn`: PDF pp.3,5: an irreducible subrepresentation is nonzero, invariant, and has no invariant subspace other than zero and itself.
--   - `rowCompression`: PDF p.5, Eq.(10): representation in an orthonormal row basis B.
--   - `eigenSpace`: PDF p.5: eigenspace in the original coordinates, with no simple-spectrum assumption on the full n by n matrix.
--   - `multiplicityBlock`: PDF p.3, Eq.(7): the multiplicity block extracted from the actual matrix in an independently fixed Eq.(6) isotypic basis. The first irreducible coordinate exists because deg i is positive. The scalar-tensor identity is not assumed.
--   - `GaussianCoordinates`: PDF p.4, §2.1: independent real Gaussian coordinates used to sample GUE.
--   - `gaussianCoordinatesLaw`: PDF p.4, §2.1: independent standard normals, before any fixed basis is examined. Using the coordinate probability space avoids an implicit pushforward.
--   - `gueMatrix`: PDF p.4, §2.1: GUE sample H=(Z+Z†)/2, where Z has independent N(0,1) real and imaginary entries. Diagonal variance is 1 and off-diagonal real and imaginary variances are 1/2. An overall positive scale is immaterial here.
--   - `NonzeroCertificate`: PDF pp.5–6, Proposition 1: the full nonzero-block certificate, including similarity in the printed direction and a nonzero scalar making F unitary.
--   - `DetectionLaw`: PDF pp.5–6, Proposition 1: zero detects inequivalence almost surely; nonzero gives an exact certificate for every draw. The probability law is concrete, and the bases are chosen before this law is quantified.
--   - `representationDirectSum`: PDF p.6, §2.3: the constructed representation sigma ⊕ tau. The sum index is the canonical coordinate model for C^(n1+n2). Reuses the frozen matrix direct-sum constructor pointwise in g.
-- source:
--   RepLAB: a computational/numerical approach to representation theory, arXiv:1911.09154v1, https://arxiv.org/abs/1911.09154v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

/-!
Exact components of RepLAB, arXiv:1911.09154v1, PDF pp.3–6.
Paper-specific definitions are local; matching concepts reuse pinned accepted libraries. No floating point correctness,
unspecified stochastic limit, or numerical complexity guarantee is asserted.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P23

open MeasureTheory
open scoped ComplexConjugate BigOperators Matrix.Norms.Elementwise

open QAlgorithms.Papers.Independent.Support21.P09 (EquivalentModels)
open QAlgorithms.Papers.Independent.Dependency50.P05 (UnitaryBetween)

/-- PDF p.3, Eq.(2) and footnote 8: a continuous complex unitary representation.
The matrix homomorphism laws are included, even for zero-dimensional spaces. -/
def IsUnitaryRepresentation {G ι : Type*} [Group G] [TopologicalSpace G]
    [Fintype ι] [DecidableEq ι] (rho : G → Matrix ι ι ℂ) : Prop :=
  rho 1 = 1 ∧ (∀ g h, rho (g * h) = rho g * rho h) ∧
    (∀ g, rho g ∈ Matrix.unitaryGroup ι ℂ) ∧ Continuous rho

/-- PDF p.3, Eq.(4): membership in the full complex commutant, without a
Hermitian, positivity, or trace restriction. -/
def Commutes {G ι : Type*} [Fintype ι]
    (rho : G → Matrix ι ι ℂ) (X : Matrix ι ι ℂ) : Prop :=
  ∀ g, rho g * X = X * rho g

/-- PDF p.4, Eq.(8): exact normalized-Haar averaging. Theorems supply the
probability-Haar and continuity assumptions which make this integral genuine. -/
def representationHaarProjection {G ι : Type*} [MeasurableSpace G] [Fintype ι]
    (rho : G → Matrix ι ι ℂ) (mu : Measure G) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∫ g, rho g * X * (rho g).conjTranspose ∂mu

/-- PDF pp.3,5: invariance of a complex linear subspace. -/
def representationInvariant {G ι : Type*} [Fintype ι] (rho : G → Matrix ι ι ℂ)
    (S : Submodule ℂ (ι → ℂ)) : Prop :=
  ∀ g v, v ∈ S → (rho g).mulVec v ∈ S

/-- PDF pp.3,5: an irreducible subrepresentation is nonzero, invariant, and has
no invariant subspace other than zero and itself. -/
def IrreducibleOn {G ι : Type*} [Fintype ι] (rho : G → Matrix ι ι ℂ)
    (S : Submodule ℂ (ι → ℂ)) : Prop :=
  S ≠ ⊥ ∧ representationInvariant rho S ∧
    ∀ T : Submodule ℂ (ι → ℂ), T ≤ S → representationInvariant rho T → T = ⊥ ∨ T = S

/-- PDF p.5, Eq.(10): representation in an orthonormal row basis B. -/
def rowCompression {G ι κ : Type*} [Fintype ι]
    (rho : G → Matrix ι ι ℂ) (B : Matrix κ ι ℂ) : G → Matrix κ κ ℂ :=
  fun g => B * rho g * B.conjTranspose

/-- PDF p.5: eigenspace in the original coordinates, with no simple-spectrum
assumption on the full n by n matrix. -/
def eigenSpace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) (z : ℂ) : Submodule ℂ (ι → ℂ) :=
  LinearMap.ker (Matrix.toLin' X - z • LinearMap.id)

/-- PDF p.3, Eq.(7): the multiplicity block extracted from the actual matrix
in an independently fixed Eq.(6) isotypic basis. The first irreducible coordinate
exists because deg i is positive. The scalar-tensor identity is not assumed. -/
def multiplicityBlock {k n : ℕ} (deg mult : Fin k → ℕ)
    (hdeg : ∀ i, 0 < deg i)
    (U : Matrix (QAlgorithms.Papers.Independent.Support21.P09.BlockIndex mult deg) (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (i : Fin k) :
    Matrix (Fin (mult i)) (Fin (mult i)) ℂ :=
  fun a b => (U * X * U.conjTranspose)
    ⟨i, (a, ⟨0, hdeg i⟩)⟩ ⟨i, (b, ⟨0, hdeg i⟩)⟩

/-- PDF p.4, §2.1: independent real Gaussian coordinates used to sample GUE. -/
abbrev GaussianCoordinates (ι : Type*) := (ι × ι × Bool) → ℝ

/-- PDF p.4, §2.1: independent standard normals, before any fixed basis is
examined. Using the coordinate probability space avoids an implicit pushforward. -/
def gaussianCoordinatesLaw (ι : Type*) [Fintype ι] : Measure (GaussianCoordinates ι) :=
  Measure.pi (fun _ : ι × ι × Bool => ProbabilityTheory.gaussianReal 0 1)

/-- PDF p.4, §2.1: GUE sample H=(Z+Z†)/2, where Z has independent N(0,1)
real and imaginary entries. Diagonal variance is 1 and off-diagonal real and
imaginary variances are 1/2. An overall positive scale is immaterial here. -/
def gueMatrix {ι : Type*} (x : GaussianCoordinates ι) : Matrix ι ι ℂ :=
  fun a b => (((x (a, b, false) : ℂ) + Complex.I * (x (a, b, true) : ℂ)) +
    conj ((x (b, a, false) : ℂ) + Complex.I * (x (b, a, true) : ℂ))) / 2

/-- PDF pp.5–6, Proposition 1: the full nonzero-block certificate, including
similarity in the printed direction and a nonzero scalar making F unitary. -/
def NonzeroCertificate {G : Type*} {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (sigma : G → Matrix ι ι ℂ) (tau : G → Matrix κ κ ℂ) (F : Matrix ι κ ℂ) : Prop :=
  EquivalentModels sigma tau ∧
    (∃ B : Matrix κ ι ℂ, F * B = 1 ∧ B * F = 1 ∧
      ∀ g, sigma g = F * tau g * B) ∧
    ∃ alpha : ℂ, alpha ≠ 0 ∧ UnitaryBetween (alpha • F)

/-- PDF pp.5–6, Proposition 1: zero detects inequivalence almost surely;
nonzero gives an exact certificate for every draw. The probability law is
concrete, and the bases are chosen before this law is quantified. -/
def DetectionLaw {G Ω : Type*} {ι κ : Type} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (sigma : G → Matrix ι ι ℂ) (tau : G → Matrix κ κ ℂ)
    (sample : Ω → Matrix ι κ ℂ) (nu : Measure Ω) : Prop :=
  (∀ᵐ x ∂nu, sample x = 0 ↔ ¬ EquivalentModels sigma tau) ∧
    ∀ x, sample x ≠ 0 → NonzeroCertificate sigma tau (sample x)

/-- PDF p.6, §2.3: the constructed representation sigma ⊕ tau.
The sum index is the canonical coordinate model for C^(n1+n2).
Reuses the frozen matrix direct-sum constructor pointwise in g. -/
def representationDirectSum {G : Type*} {ι κ : Type}
    (sigma : G → Matrix ι ι ℂ) (tau : G → Matrix κ κ ℂ) :
    G → Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ :=
  fun g => QAlgorithms.Papers.Independent.Dependency50.P35.directSum (sigma g) (tau g)

/-- Sanity: the commutant includes the identity. -/
example {G ι : Type*} [Fintype ι] [DecidableEq ι] (rho : G → Matrix ι ι ℂ) :
    Commutes rho 1 := by
  intro g
  simp

/-- Sanity: Haar averaging never creates a vector from the zero matrix. -/
example {G ι : Type*} [MeasurableSpace G] [Fintype ι]
    (rho : G → Matrix ι ι ℂ) (mu : Measure G) : representationHaarProjection rho mu 0 = 0 := by
  simp [representationHaarProjection]

/-- Sanity: the extracted multiplicity block is precisely the stated coordinate
slice of U X U†, with no diagonalization premise. -/
example {k n : ℕ} (deg mult : Fin k → ℕ) (hdeg : ∀ i, 0 < deg i)
    (U : Matrix (QAlgorithms.Papers.Independent.Support21.P09.BlockIndex mult deg) (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (i : Fin k) (a b : Fin (mult i)) :
    multiplicityBlock deg mult hdeg U X i a b =
      (U * X * U.conjTranspose) ⟨i, (a, ⟨0, hdeg i⟩)⟩ ⟨i, (b, ⟨0, hdeg i⟩)⟩ := rfl

/-- Sanity: the GUE sample is zero on zero Gaussian coordinates. -/
example {ι : Type*} : gueMatrix (0 : GaussianCoordinates ι) = 0 := by
  ext a b
  simp [gueMatrix]

/-- Sanity: irreducibility excludes the zero representation space. -/
example {G ι : Type*} [Fintype ι] (rho : G → Matrix ι ι ℂ)
    (h : QAlgorithms.Papers.Independent.Support21.P09.Irreducible rho) : Nonempty ι := h.1

/-- Sanity: the constructed direct sum has zero off-diagonal blocks. -/
example {G : Type*} {ι κ : Type} (sigma : G → Matrix ι ι ℂ) (tau : G → Matrix κ κ ℂ)
    (g : G) (i : ι) (j : κ) : representationDirectSum sigma tau g (Sum.inl i) (Sum.inr j) = 0 := rfl

end QAlgorithms.Papers.Independent.Extend50.P23


