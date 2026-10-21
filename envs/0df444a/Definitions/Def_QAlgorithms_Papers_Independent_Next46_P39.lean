-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P39
-- name    : QAlgorithms_Papers_Independent_Next46_P39
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T14:42:47.43298+00:00
-- url     : https://prove2.me/theorems/fca1c098-83b0-455d-b572-c1d9ce184445
-- title:
--   Definitions for Maximum likelihood estimation for a group of physical transformations
-- statement:
--   The objects the formalized statements of *Maximum likelihood estimation for a group of physical transformations* (arXiv:quant-ph/0507007) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `FiniteModel`: PDF pp.4–5, Eqs.(4)–(5): a complete based isotypic decomposition. All blocks share the multiplier of the physical projective action. Irreducibility is defined by invariant subspaces; inequivalence by absence of nonzero intertwiners. The latter is equivalent to inequivalence for these irreducible blocks.
--   - `rectAct`: PDF p.5: apply a rectangular coordinate embedding to a vector.
--   - `densityOrbit`: PDF p.3, Eq.(1): the physical density orbit.
--   - `IsSeed`: PDF p.6, Eqs.(10)–(11): actual full-space Haar normalization. The partial-trace constraints are not extra assumed representation data.
--   - `averageLikelihood`: PDF pp.4,6: uniform-prior success density of an arbitrary POVM.
--   - `likelihood`: PDF p.6: the constant on-diagonal density for a covariant seed.
--   - `SchmidtInput`: PDF pp.6–7, Eqs.(9),(12): normalized Schmidt data. A zero sector has rank zero, so neither the eta vector nor any sum receives an absent-sector term.
--   - `SchmidtInput.block`: PDF p.7, Eq.(12): unit bipartite vector in an occupied block; zero otherwise.
--   - `SchmidtInput.vector`: PDF p.6, Eq.(9): the input built from its Schmidt expansion.
--   - `SchmidtInput.projector`: PDF p.7, Eq.(13): explicit orbit projector.
--   - `SchmidtInput.eta`: PDF p.7, Eq.(15): the phase is c/|c| in each occupied sector. At c=0 the sum is empty, so the total inverse introduces no contribution.
--   - `SchmidtInput.formula`: PDF p.7, Eq.(16): formula for the optimum, not a definition of an operational optimum.
--   - `cyclicSpan`: PDF p.9: actual cyclic span of an arbitrary vector.
--   - `orbitDimension`: PDF p.9, Lemma 1: actual dimension of the cyclic span.
--   - `ceilingLikelihood`: PDF p.10, Eq.(24): representation-dependent likelihood ceiling.
--   - `SchmidtInput.Balanced`: PDF pp.9–10, Eq.(19): the equality-case Schmidt weights. The conditions on individual coefficients range over Fin(r), hence contain no division at absent sectors.
--   - `SchmidtInput.OptimalShape`: PDF p.10, Eq.(25): arbitrary phases and maximally entangled Schmidt bases with the source's fixed sector weights.
--   - `frame`: PDF pp.8–9: frame operator defined by the actual Haar integral.
--   - `inverseSqrt`: PDF p.8: finite-spectrum pseudoinverse square root. Zero eigenvalues are sent to zero; no full-space invertibility hypothesis is imposed.
--   - `orbitHolevo`: PDF p.11, Eq.(26): Holevo quantity of the continuous group orbit, using accepted natural-log matrix entropy. Unlike the accepted finite-ensemble `Information100.P56.holevo`, this uses the actual probability Haar integral.
--   - `assistedAction`: PDF p.12: actual action with an n-dimensional inert reference.
--   - `AssistedSeed`: PDF p.12: a normalized covariant measurement on the actual assisted space.
--   - `AssistedMaximum`: PDF p.12: operational maximum, with a universal bound and actual pure-state attainment; no real supremum on an empty or unbounded set occurs.
--   - `assistedCeiling`: PDF p.12, Eq.(30): assisted numerical bound, tied to actual measurements in `ancilla_likelihood` below.
--   - `referenceThreshold`: PDF p.12, Eq.(29): finite maximum of the usual non-strict ceilings.
--   - `CanonicalIndex`: PDF p.12, proof of Theorem 4: the saturated canonical multiplicity space.
--   - `canonicalAction`: PDF p.12: group action with every multiplicity exactly d_mu, in coordinates.
--   - `CompressesOrbit`: PDF p.12: orbit compression as an isometry on the actual cyclic span, intertwining the source and target group actions. No dimension count replaces it.
--   - `displacementDensity`: PDF pp.18–19, Eqs.(43),(55): Gaussian error density, relative to d²z/pi. Only the statistical comparison node uses this definition; it does not stand in for an oscillator POVM or an optimality assertion.
--   - `phaseMeasure`: PDF pp.15–18: the fixed phase-space Haar measure d²z/pi.
--   - `SpinGroup`: PDF pp.10–11: the actual fundamental spin group, not abstract dimensions.
--   - `spinAction`: PDF pp.10–11: the actual tensor-square fundamental SU(2) action.
--   - `tripletZero`: PDF pp.10–11: the m=0 triplet vector in the same basis.
--   - `optimalSpin`: PDF p.11: the optimal singlet/triplet weights 1/2 and sqrt(3)/2.
--   - `SpinSeed`: PDF pp.6,10–11: genuine normalized covariant SU(2) measurements.
--   - `SpinMaximum`: PDF pp.10–11: bound and attainment for the specified physical spin input.
-- source:
--   Maximum likelihood estimation for a group of physical transformations, arXiv:quant-ph/0507007v1, https://arxiv.org/abs/quant-ph/0507007v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_ContinuousPOVMDensities
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14

/-!
Statements from Chiribella, D'Ariano, Perinotti and Sacchi, quant-ph/0507007v1.
Paper-local coordinate models below have complete bodies. No optimum, orbit dimension,
or group-average formula is assumed as part of a representation's data.
Likelihoods are densities relative to probability Haar measure, not probabilities.
Compilation is pending the authorized batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P39

open MeasureTheory
open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator Manifold ContDiff

open QAlgorithms.Measurements (DensityPOVM)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable

/-- PDF pp.3–5: Borel measurable finite matrices with the operator norm topology. -/
local instance operatorMatrixMeasurable (A : Type*) [Fintype A] :
    MeasurableSpace (Matrix A A ℂ) := borel _

/-- PDF pp.3–5: compatibility of the finite-matrix Borel structure and topology. -/
local instance operatorMatrixBorel (A : Type*) [Fintype A] :
    BorelSpace (Matrix A A ℂ) := ⟨rfl⟩

variable {G I S : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype S] [DecidableEq S] [Nonempty S]

/-- PDF pp.4–5, Eqs.(4)–(5): a complete based isotypic decomposition.
All blocks share the multiplier of the physical projective action. Irreducibility
is defined by invariant subspaces; inequivalence by absence of nonzero intertwiners.
The latter is equivalent to inequivalence for these irreducible blocks. -/
structure FiniteModel (G I S : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype S] [DecidableEq S] [Nonempty S] where
  d : S → ℕ
  m : S → ℕ
  d_pos : ∀ s, 0 < d s
  m_pos : ∀ s, 0 < m s
  U : G → Matrix.unitaryGroup I ℂ
  rep : (s : S) → G → Matrix.unitaryGroup (Fin (d s)) ℂ
  phase : G → G → ℂ
  phase_norm : ∀ g h, ‖phase g h‖ = 1
  mul_phase : ∀ g h, (U (g * h) : Matrix I I ℂ) =
    phase g h • ((U g : Matrix I I ℂ) * (U h : Matrix I I ℂ))
  rep_mul : ∀ s g h, (rep s (g * h) : Matrix (Fin (d s)) (Fin (d s)) ℂ) =
    phase g h • ((rep s g : Matrix (Fin (d s)) (Fin (d s)) ℂ) * (rep s h : Matrix (Fin (d s)) (Fin (d s)) ℂ))
  measurable_U : Measurable (fun g => (U g : Matrix I I ℂ))
  continuous_conjugation : ∀ A : Matrix I I ℂ,
    Continuous (fun g => (U g : Matrix I I ℂ) * A * (U g : Matrix I I ℂ)ᴴ)
  measurable_rep : ∀ s, Measurable (fun g => (rep s g : Matrix (Fin (d s)) (Fin (d s)) ℂ))
  continuous_rep_conjugation : ∀ s (A : Matrix (Fin (d s)) (Fin (d s)) ℂ),
    Continuous (fun g => (rep s g : Matrix (Fin (d s)) (Fin (d s)) ℂ) * A * (rep s g : Matrix (Fin (d s)) (Fin (d s)) ℂ)ᴴ)
  irreducible : ∀ s (K : Submodule ℂ (Fin (d s) → ℂ)),
    (∀ g v, v ∈ K → Matrix.mulVec (rep s g : Matrix (Fin (d s)) (Fin (d s)) ℂ) v ∈ K) → K = ⊥ ∨ K = ⊤
  inequivalent : ∀ s t, s ≠ t → ∀ A : Matrix (Fin (d s)) (Fin (d t)) ℂ,
    (∀ g, (rep s g : Matrix (Fin (d s)) (Fin (d s)) ℂ) * A = A * (rep t g : Matrix (Fin (d t)) (Fin (d t)) ℂ)) → A = 0
  embed : (s : S) → Matrix I (Fin (d s) × Fin (m s)) ℂ
  embed_isometry : ∀ s, (embed s)ᴴ * embed s = 1
  embed_orthogonal : ∀ s t, s ≠ t → (embed s)ᴴ * embed t = 0
  embed_complete : ∑ s, embed s * (embed s)ᴴ = 1
  intertwines : ∀ g s, (U g : Matrix I I ℂ) * embed s =
    embed s * Matrix.kronecker (rep s g : Matrix (Fin (d s)) (Fin (d s)) ℂ) (1 : Matrix (Fin (m s)) _ ℂ)
  dg : Measure G
  haar_probability : dg Set.univ = 1
  haar_left : ∀ h, Measure.map (fun g => h * g) dg = dg
  haar_right : ∀ h, Measure.map (fun g => g * h) dg = dg

variable (R : FiniteModel G I S)

/-- PDF p.5: apply a rectangular coordinate embedding to a vector. -/
def rectAct {A B : Type*} [Fintype B] (M : Matrix A B ℂ)
    (v : EuclideanSpace ℂ B) : EuclideanSpace ℂ A :=
  WithLp.toLp 2 (M.mulVec (WithLp.ofLp v))

/-- PDF p.3, Eq.(1): the physical density orbit. -/
def densityOrbit (rho : Matrix I I ℂ) (g : G) : Matrix I I ℂ :=
  (R.U g : Matrix I I ℂ) * rho * (R.U g : Matrix I I ℂ)ᴴ

/-- PDF p.6, Eqs.(10)–(11): actual full-space Haar normalization.
The partial-trace constraints are not extra assumed representation data. -/
def IsSeed (Xi : Matrix I I ℂ) : Prop :=
  Xi.PosSemidef ∧ Measurable (densityOrbit R Xi) ∧ Integrable (densityOrbit R Xi) R.dg ∧
    (∫ g, densityOrbit R Xi g ∂(R.dg)) = 1

/-- PDF pp.4,6: uniform-prior success density of an arbitrary POVM. -/
def averageLikelihood (M : DensityPOVM I G) (rho : Matrix I I ℂ) : ℝ :=
  ∫ g, QAlgorithms.effectProb (M.density g) (densityOrbit R rho g) ∂(R.dg)

/-- PDF p.6: the constant on-diagonal density for a covariant seed. -/
def likelihood (Xi rho : Matrix I I ℂ) : ℝ := QAlgorithms.effectProb Xi rho

/-- PDF pp.6–7, Eqs.(9),(12): normalized Schmidt data. A zero sector has rank
zero, so neither the eta vector nor any sum receives an absent-sector term. -/
structure SchmidtInput where
  c : S → ℂ
  weights : ∑ s, Complex.normSq (c s) = 1
  r : S → ℕ
  absent : ∀ s, r s = 0 ↔ c s = 0
  rank_bound : ∀ s, r s ≤ min (R.d s) (R.m s)
  lam : (s : S) → Fin (r s) → ℝ
  lam_pos : ∀ s t, 0 < lam s t
  lam_sum : ∀ s, c s ≠ 0 → ∑ t, lam s t = 1
  left : (s : S) → Fin (r s) → EuclideanSpace ℂ (Fin (R.d s))
  right : (s : S) → Fin (r s) → EuclideanSpace ℂ (Fin (R.m s))
  left_orthonormal : ∀ s, Orthonormal ℂ (left s)
  right_orthonormal : ∀ s, Orthonormal ℂ (right s)

variable {R}

/-- PDF p.7, Eq.(12): unit bipartite vector in an occupied block; zero otherwise. -/
def SchmidtInput.block (D : SchmidtInput R) (s : S) :
    EuclideanSpace ℂ (Fin (R.d s) × Fin (R.m s)) :=
  ∑ t, (Real.sqrt (D.lam s t) : ℂ) • QAlgorithms.tensorVec (D.left s t) (D.right s t)

/-- PDF p.6, Eq.(9): the input built from its Schmidt expansion. -/
def SchmidtInput.vector (D : SchmidtInput R) : EuclideanSpace ℂ I :=
  ∑ s, D.c s • rectAct (R.embed s) (D.block s)

/-- PDF p.7, Eq.(13): explicit orbit projector. -/
def SchmidtInput.projector (D : SchmidtInput R) : Matrix I I ℂ :=
  ∑ s, R.embed s * Matrix.kronecker (1 : Matrix (Fin (R.d s)) _ ℂ)
    (∑ t, QAlgorithms.pureDensity (D.right s t)) * (R.embed s)ᴴ

/-- PDF p.7, Eq.(15): the phase is c/|c| in each occupied sector.
At c=0 the sum is empty, so the total inverse introduces no contribution. -/
def SchmidtInput.eta (D : SchmidtInput R) : EuclideanSpace ℂ I :=
  ∑ s, ((Real.sqrt (R.d s) : ℂ) * (D.c s / (‖D.c s‖ : ℂ))) •
    rectAct (R.embed s) (∑ t, QAlgorithms.tensorVec (D.left s t) (D.right s t))

/-- PDF p.7, Eq.(16): formula for the optimum, not a definition of an operational optimum. -/
def SchmidtInput.formula (D : SchmidtInput R) : ℝ :=
  (∑ s, ‖D.c s‖ * ∑ t, Real.sqrt (D.lam s t * R.d s)) ^ 2

/-- PDF p.9: actual cyclic span of an arbitrary vector. -/
def cyclicSpan (psi : EuclideanSpace ℂ I) : Submodule ℂ (EuclideanSpace ℂ I) :=
  Submodule.span ℂ (Set.range (fun g => QAlgorithms.act (R.U g : Matrix I I ℂ) psi))

/-- PDF p.9, Lemma 1: actual dimension of the cyclic span. -/
def orbitDimension (psi : EuclideanSpace ℂ I) : ℕ :=
  Module.finrank ℂ (cyclicSpan (R := R) psi)

/-- PDF p.10, Eq.(24): representation-dependent likelihood ceiling. -/
def ceilingLikelihood (R : FiniteModel G I S) : ℕ :=
  ∑ s, R.d s * min (R.d s) (R.m s)

/-- PDF pp.9–10, Eq.(19): the equality-case Schmidt weights. The conditions on
individual coefficients range over Fin(r), hence contain no division at absent sectors. -/
def SchmidtInput.Balanced (D : SchmidtInput R) : Prop :=
  (∀ s, Complex.normSq (D.c s) =
    ((R.d s * D.r s : ℕ) : ℝ) / (orbitDimension (R := R) D.vector : ℝ)) ∧
  (∀ s t, D.lam s t = (D.r s : ℝ)⁻¹)

/-- PDF p.10, Eq.(25): arbitrary phases and maximally entangled Schmidt bases
with the source's fixed sector weights. -/
def SchmidtInput.OptimalShape (D : SchmidtInput R) : Prop :=
  (∀ s, D.r s = min (R.d s) (R.m s)) ∧
  (∀ s t, D.lam s t = (min (R.d s) (R.m s) : ℝ)⁻¹) ∧
  (∀ s, Complex.normSq (D.c s) =
    ((R.d s * min (R.d s) (R.m s) : ℕ) : ℝ) / (ceilingLikelihood R : ℝ))

/-- PDF pp.8–9: frame operator defined by the actual Haar integral. -/
def frame (psi : EuclideanSpace ℂ I) : Matrix I I ℂ :=
  ∫ g, densityOrbit R (QAlgorithms.pureDensity psi) g ∂(R.dg)

/-- PDF p.8: finite-spectrum pseudoinverse square root. Zero eigenvalues are
sent to zero; no full-space invertibility hypothesis is imposed. -/
def inverseSqrt (F : Matrix I I ℂ) : Matrix I I ℂ :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) F

/-- PDF p.11, Eq.(26): Holevo quantity of the continuous group orbit, using
accepted natural-log matrix entropy. Unlike the accepted finite-ensemble
`Information100.P56.holevo`, this uses the actual probability Haar integral. -/
def orbitHolevo (rho : Matrix I I ℂ) : ℝ :=
  entropy (∫ g, densityOrbit R rho g ∂(R.dg)) -
    ∫ g, entropy (densityOrbit R rho g) ∂(R.dg)

/-- PDF p.12: actual action with an n-dimensional inert reference. -/
def assistedAction (R : FiniteModel G I S) (n : ℕ) (g : G) :
    Matrix (I × Fin n) (I × Fin n) ℂ :=
  Matrix.kronecker (R.U g : Matrix I I ℂ) (1 : Matrix (Fin n) (Fin n) ℂ)

/-- PDF p.12: a normalized covariant measurement on the actual assisted space. -/
def AssistedSeed (R : FiniteModel G I S) (n : ℕ)
    (Xi : Matrix (I × Fin n) (I × Fin n) ℂ) : Prop :=
  Xi.PosSemidef ∧
  Measurable (fun g => assistedAction R n g * Xi * (assistedAction R n g)ᴴ) ∧
  Integrable (fun g => assistedAction R n g * Xi * (assistedAction R n g)ᴴ) R.dg ∧
  (∫ g, assistedAction R n g * Xi * (assistedAction R n g)ᴴ ∂(R.dg)) = 1

/-- PDF p.12: operational maximum, with a universal bound and actual pure-state
attainment; no real supremum on an empty or unbounded set occurs. -/
def AssistedMaximum (R : FiniteModel G I S) (n : ℕ) (L : ℝ) : Prop :=
  (∀ rho Xi : Matrix (I × Fin n) (I × Fin n) ℂ,
    QAlgorithms.IsDensityMatrix rho → AssistedSeed R n Xi → likelihood Xi rho ≤ L) ∧
  (∃ (psi : EuclideanSpace ℂ (I × Fin n)) (Xi : Matrix (I × Fin n) (I × Fin n) ℂ),
    QAlgorithms.IsState psi ∧ AssistedSeed R n Xi ∧
      likelihood Xi (QAlgorithms.pureDensity psi) = L)

/-- PDF p.12, Eq.(30): assisted numerical bound, tied to actual measurements in
`ancilla_likelihood` below. -/
def assistedCeiling (R : FiniteModel G I S) (n : ℕ) : ℕ :=
  ∑ s, R.d s * min (R.d s) (R.m s * n)

/-- PDF p.12, Eq.(29): finite maximum of the usual non-strict ceilings. -/
def referenceThreshold (R : FiniteModel G I S) : ℕ :=
  Finset.univ.sup (fun s => Nat.ceil ((R.d s : ℝ) / R.m s))

/-- PDF p.12, proof of Theorem 4: the saturated canonical multiplicity space. -/
abbrev CanonicalIndex (R : FiniteModel G I S) := Σ s, Fin (R.d s) × Fin (R.d s)

/-- PDF p.12: group action with every multiplicity exactly d_mu, in coordinates. -/
def canonicalAction (R : FiniteModel G I S) (g : G)
    (v : EuclideanSpace ℂ (CanonicalIndex R)) : EuclideanSpace ℂ (CanonicalIndex R) :=
  WithLp.toLp 2 (fun i => ∑ a, (R.rep i.1 g : Matrix (Fin (R.d i.1)) (Fin (R.d i.1)) ℂ) i.2.1 a * v ⟨i.1, a, i.2.2⟩)

/-- PDF p.12: orbit compression as an isometry on the actual cyclic span,
intertwining the source and target group actions. No dimension count replaces it. -/
def CompressesOrbit (R : FiniteModel G I S) (n : ℕ)
    (psi : EuclideanSpace ℂ (I × Fin n)) : Prop :=
  ∃ A : Matrix (CanonicalIndex R) (I × Fin n) ℂ,
    (∀ v ∈ Submodule.span ℂ (Set.range (fun g => QAlgorithms.act (assistedAction R n g) psi)),
      ‖rectAct A v‖ = ‖v‖) ∧
    (∀ g v, v ∈ Submodule.span ℂ
        (Set.range (fun h => QAlgorithms.act (assistedAction R n h) psi)) →
      rectAct A (QAlgorithms.act (assistedAction R n g) v) = canonicalAction R g (rectAct A v))

/-- PDF pp.18–19, Eqs.(43),(55): Gaussian error density, relative to d²z/pi.
Only the statistical comparison node uses this definition; it does not stand in
for an oscillator POVM or an optimality assertion. -/
def displacementDensity (k : ℝ) (a z : ℂ) : ℝ :=
  k * Real.exp (-k * Complex.normSq (z - a))

/-- PDF pp.15–18: the fixed phase-space Haar measure d²z/pi. -/
def phaseMeasure : Measure ℂ := (ENNReal.ofReal (Real.pi⁻¹)) • volume

/-- PDF pp.10–11: the actual fundamental spin group, not abstract dimensions. -/
abbrev SpinGroup := ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)

/-- PDF pp.10–11: Borel outcome sigma-algebra for the actual spin group. -/
instance spinMeasurable : MeasurableSpace SpinGroup := borel _

/-- PDF pp.10–11: the spin outcome sigma-algebra is its Borel structure. -/
instance spinBorel : BorelSpace SpinGroup := ⟨rfl⟩

/-- PDF pp.10–11: the actual tensor-square fundamental SU(2) action. -/
def spinAction (g : SpinGroup) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker (g : Matrix (Fin 2) (Fin 2) ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ)

/-- PDF pp.10–11: the m=0 triplet vector in the same basis. -/
def tripletZero : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  (Real.sqrt 2 : ℂ)⁻¹ • (QAlgorithms.ket (0, 1) + QAlgorithms.ket (1, 0))

/-- PDF p.11: the optimal singlet/triplet weights 1/2 and sqrt(3)/2. -/
def optimalSpin : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  (1/2 : ℂ) • WithLp.toLp 2 QAlgorithms.Papers.Independent.Frontier18.P14.singlet +
    (Real.sqrt 3 / 2 : ℂ) • tripletZero

/-- PDF pp.6,10–11: genuine normalized covariant SU(2) measurements. -/
def SpinSeed (dg : Measure SpinGroup)
    (Xi : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Prop :=
  Xi.PosSemidef ∧
  Measurable (fun g => spinAction g * Xi * (spinAction g)ᴴ) ∧
  Integrable (fun g => spinAction g * Xi * (spinAction g)ᴴ) dg ∧
  (∫ g, spinAction g * Xi * (spinAction g)ᴴ ∂dg) = 1

/-- PDF pp.10–11: bound and attainment for the specified physical spin input. -/
def SpinMaximum (dg : Measure SpinGroup)
    (psi : EuclideanSpace ℂ (Fin 2 × Fin 2)) (L : ℝ) : Prop :=
  (∀ Xi, SpinSeed dg Xi → likelihood Xi (QAlgorithms.pureDensity psi) ≤ L) ∧
  (∃ Xi, SpinSeed dg Xi ∧ likelihood Xi (QAlgorithms.pureDensity psi) = L)

/-! Sanity examples pin definitions without proving any source theorem. -/

example {A B : Type*} [Fintype B] (v : EuclideanSpace ℂ B) :
    rectAct (0 : Matrix A B ℂ) v = 0 := by
  simp [rectAct]

example (R : FiniteModel G I S) : assistedCeiling R 0 = 0 := by
  simp [assistedCeiling]

example (a : ℂ) : displacementDensity 2 a a = 2 := by
  simp [displacementDensity]

example : entropy (0 : Matrix I I ℂ) = 0 := by
  simp [QAlgorithms.Papers.Independent.Information100.P56.entropy, cfc_zero]

example (R : FiniteModel G Unit Unit) (hd : ∀ s, R.d s = 1)
    (hm : ∀ s, R.m s = 1) : ceilingLikelihood R = 1 := by
  simp [ceilingLikelihood, hd, hm]

example (R : FiniteModel G Unit Unit) (hd : ∀ s, R.d s = 1)
    (hm : ∀ s, R.m s = 1) : referenceThreshold R = 1 := by
  simp [referenceThreshold, hd, hm]

/-! Each finite theorem retains the source's compact Lie-group hypothesis.
Finite groups are included through zero-dimensional Lie charts. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E G]

end QAlgorithms.Papers.Independent.Next46.P39


