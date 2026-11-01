-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P44
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P44
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T05:18:31.625034+00:00
-- url     : https://prove2.me/theorems/8a86e79b-4455-4ce4-8f7e-fad6ca03ca46
-- title:
--   Definitions for Approximate recovery with locality and symmetry constraints
-- statement:
--   The objects the formalized statements of *Approximate recovery with locality and symmetry constraints* (arXiv:1806.10324) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ObservableAlgebra`: PDF p.3: unital dagger algebra with its canonical Hilbert--Schmidt orthogonal projection channel. Range and orthogonality uniquely specify it.
--   - `IsPhysicalChannel`: PDF p.3, Definition 1; no condition is imposed on forbidden output coherences.
--   - `FixesObservables`: PDF pp.7--8: fixing an observable algebra is a Heisenberg condition.
--   - `fixedFidelity`: Root entanglement fidelity on the specified normalized input, retaining the identity reference. PDF p.4, Eq.(5).
--   - `Comparison`: The two comparison domains in Eqs.(5)--(6), PDF pp.3--4. An encoding is an isometry; no surjectivity or fixed-charge assumption occurs.
--   - `comparisonRootFidelity`: PDF p.4, Eq.(6): infimum over ALL normalized logical densities. For channels the value set is nonempty and contained in [0,1]; compactness makes this infimum a minimum. The fixed branch uses ROOT fidelity as well.
--   - `SameMaximum`: Equality of attained maxima, avoiding totalized real suprema on empty sets. This includes the existence of both optimizers stated on PDF pp.5,8--9.
--   - `IsChannelDilation`: A true Stinespring dilation of N, on every matrix. PDF pp.4,8.
--   - `krausComplement`: Ordinary complementary channel of a normalized Kraus family. The entry (i,j) is Tr(E_j† E_i rho), PDF p.4, Eq.(9).
--   - `IsGeneralizedComplement`: PDF p.4: complements include channels reversibly postprocessable to a Stinespring complement, with BOTH postprocessings CPTP.
--   - `localComplement`: PDF p.8, Definition 3, Eq.(33): the local environment retains B TOGETHER with the dilation environment, rather than the environment alone.
--   - `Sectors`: PDF p.5, Section III B: nonzero orthogonal sector projectors, with pairwise distinct real charge eigenvalues.
--   - `sectorProject`: PDF p.5, Eq.(14), the canonical blind charge measurement.
--   - `sectorChargeObservable`: PDF p.5: the charge is computed from the sector data.
--   - `PhysicallyCorrectable`: Exact PHYSICAL correction to P on the encoded space, PDF pp.3,5. Equality on all logical matrices is equivalent by linearity to equality on all logical density matrices; reference extensions are thereby retained.
--   - `ChargeStateCondition`: PDF p.5, Eqs.(18),(20): each conditional output is normalized only AFTER summing its classical output sectors. Individual blocks need not have trace 1.
--   - `ChargeCoefficients`: PDF p.5, Eq.(21): one coefficient family, uniform in all subsequent indices.
--   - `constantChannel`: PDF p.9, Eq.(48): constant-output channel, on ALL matrices.
--   - `TensorCorrectable`: PDF pp.9--10: tensor-local exact correction on an arbitrary JOINT code.
--   - `codeSlice`: PDF p.10, Eq.(51): W_n = (I tensor <n|) W.
--   - `Fermions`: PDF pp.2--3: a finite spinless-fermion CAR representation on its actual 2^n-dimensional Fock space. Minimal dimension prevents extra spectator sectors.
--   - `totalParity`: PDF pp.2--3: total parity, up to the immaterial global sign convention. i^n times the ordered product of 2n Majoranas is a Hermitian involution. Printed, PDF p.2 Eq.(1): i^(|omega|-1) for Majorana labels. Changed: i^n on 2n ordered modes. Why: the printed four-mode value is anti-Hermitian and squares to -I; parity must be a Hermitian involution.
--   - `parityProject`: PDF p.3: blind parity measurement.
--   - `DefiniteParity`: PDF p.3, Proposition 1: both preserving and flipping parity are allowed.
--   - `evenRegion`: PDF pp.2--3,10: the even algebra supported on a set of Majorana indices. Repeated indices are harmless under CAR; the empty word supplies the identity.
--   - `StrongLocal`: PDF p.7, Definition 2: strong locality retains BOTH clauses.
--   - `siteModes`: The two Majoranas for each fermionic SITE in omega, PDF pp.2--3,10.
--   - `regionParity`: PDF p.10: regional parity for site regions, including the empty region. Printed, PDF p.2 Eq.(1): i^(|omega|-1) for Majorana labels. Changed: i^m on the 2m ordered modes of m sites, up to overall sign. Why: the printed four-mode value is anti-Hermitian and squares to -I, contrary to the source's parity involution and sector-projector conventions.
--   - `paritySector`: PDF pp.3,10: plus sector indexed by false, minus by true.
--   - `StrongCorrectable`: PDF pp.9--10: exact strong-local correction of the algebra A vee A'. For the even algebra of a SITE region this target is regional parity dephasing.
--   - `RegionalStateCondition`: PDF p.10, Eq.(53); one normalized environmental state per regional sector. The order X_ij E_i† B E_j is copied from the rendered page.
--   - `RegionalCoefficients`: PDF p.10, Eq.(54): the coefficient family is UNIFORM in the commutant observable Y. Sector compression is on both sides, without division by its weight.
--   - `ringGap`: PDF pp.6,10: number of paired Majoranas strictly between adjacent free modes.
--   - `RingLayout`: PDF pp.6--7,10--11: ordered free modes and the alternating nearest-neighbor paired intervals between them. Even gaps give the alternating pairing types.
--   - `modeAt`: Cyclic mode at a specified offset.
--   - `pairingProjector`: PDF pp.6--7,10--11: ACTUAL pairing-ground projector. Each paired nearest-neighbor fermion is initialized in its vacuum. The ordered bond (a,b) has vacuum projector (I-i w_a w_b)/2; reversing bond orientation changes its sign. The free modes receive no projector, so ALL their states are encoded.
--   - `RingCode`: PDF pp.6--7: an isometry ONTO the computed pairing ground code, not an arbitrary invariant subspace. Logical dimension is exactly 2^k.
--   - `minimumGap`: PDF p.10: shortest paired interval. Initial bound 2n dominates every gap; the nonempty list has length 2k. Empty paired intervals therefore give d=0.
--   - `HasIntervalSupport`: PDF p.10: a WHOLE Kraus operator is an even polynomial supported in one cyclic interval containing length modes; length=0 permits only scalar operators.
--   - `poisoning`: PDF pp.6--7: equally weighted jumps on the first two unpaired Majoranas.
-- source:
--   Approximate recovery with locality and symmetry constraints, arXiv:1806.10324v2, https://arxiv.org/abs/1806.10324v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

/-!
Statements from Bény, Zimborás and Pastawski, arXiv:1806.10324v2.
All spaces are finite matrix spaces. Nonempty ambient and logical index types
are explicit theorem assumptions. New interfaces are paper-local.
The independent-paper override permits imports from the pinned accepted library;
exactly matching matrix, tensor, adjoint and purification interfaces are reused.
The four source-ambiguity nodes are recorded in HARD.md, not asserted here.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P44

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)
open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)
open QAlgorithms.Papers.Independent.Claimed50.P48 (operatorTraceDual)
open QAlgorithms.Papers.Independent.Renew46.P43 (purification)

variable {H K L J E F B : Type*}
variable [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
variable [Fintype L] [DecidableEq L] [Fintype J] [DecidableEq J]
variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
variable [Fintype B] [DecidableEq B]

/-- PDF p.3: unital dagger algebra with its canonical Hilbert--Schmidt
orthogonal projection channel. Range and orthogonality uniquely specify it. -/
structure ObservableAlgebra (H : Type*) [Fintype H] [DecidableEq H] where
  algebra : StarSubalgebra ℂ (Mat H)
  project : Superop H H
  channel : IsChannel project
  range_mem : ∀ X, project X ∈ algebra
  orthogonal : ∀ X Y, Y ∈ algebra → ((X - project X)ᴴ * Y).trace = 0

/-- PDF p.3, Definition 1; no condition is imposed on forbidden output coherences. -/
def IsPhysicalChannel (P : Superop H H) (Q : Superop K K) (N : Superop H K) : Prop :=
  ∀ X, Q (N (P X)) = Q (N X)

/-- PDF pp.7--8: fixing an observable algebra is a Heisenberg condition. -/
def FixesObservables (A : Set (Mat H)) (N : Superop H H) : Prop :=
  ∀ X ∈ A, operatorTraceDual N X = X

/-- Root entanglement fidelity on the specified normalized input, retaining
the identity reference. PDF p.4, Eq.(5). -/
def fixedFidelity (rho : Mat H) (N M : Superop H K) : ℝ :=
  rootFidelity (idTensorSuperop N (purification rho))
    (idTensorSuperop M (purification rho))

/-- The two comparison domains in Eqs.(5)--(6), PDF pp.3--4.
An encoding is an isometry; no surjectivity or fixed-charge assumption occurs. -/
inductive Comparison (H : Type*) [Fintype H] [DecidableEq H] where
  | fixed (rho : Mat H) (normalized : IsDensityMatrix rho)
  | code (k : ℕ) (positive : 0 < k) (W : Matrix H (Fin k) ℂ)
      (isometry : Wᴴ * W = 1)

/-- PDF p.4, Eq.(6): infimum over ALL normalized logical densities.
For channels the value set is nonempty and contained in [0,1]; compactness
makes this infimum a minimum. The fixed branch uses ROOT fidelity as well. -/
def comparisonRootFidelity (c : Comparison H) (N M : Superop H K) : ℝ :=
  match c with
  | .fixed rho _ => fixedFidelity rho N M
  | .code k _ W _ =>
      sInf {t : ℝ | ∃ rho : Mat (Fin k), IsDensityMatrix rho ∧
        t = fixedFidelity rho (N ∘ conjSuperop W) (M ∘ conjSuperop W)}

/-- Equality of attained maxima, avoiding totalized real suprema on empty sets.
This includes the existence of both optimizers stated on PDF pp.5,8--9. -/
def SameMaximum {X Y : Type*} (allowedX : X → Prop) (f : X → ℝ)
    (allowedY : Y → Prop) (g : Y → ℝ) : Prop :=
  ∃ x y, allowedX x ∧ allowedY y ∧ f x = g y ∧
    (∀ x2, allowedX x2 → f x2 ≤ f x) ∧
    (∀ y2, allowedY y2 → g y2 ≤ g y)

/-- A true Stinespring dilation of N, on every matrix. PDF pp.4,8. -/
def IsChannelDilation (N : Superop H K) (V : Matrix (K × E) H ℂ) : Prop :=
  Vᴴ * V = 1 ∧ ∀ X, N X = traceRight (conjSuperop V X)

/-- Ordinary complementary channel of a normalized Kraus family. The entry
(i,j) is Tr(E_j† E_i rho), PDF p.4, Eq.(9). -/
def krausComplement (A : J → Matrix K H ℂ) : Superop H J :=
  fun X i j => (A i * X * (A j)ᴴ).trace

/-- PDF p.4: complements include channels reversibly postprocessable to a
Stinespring complement, with BOTH postprocessings CPTP. -/
def IsGeneralizedComplement (N : Superop H K) (C : Superop H E) : Prop :=
  ∃ (m : ℕ) (A : Fin m → Matrix K H ℂ), IsKrausFamily A ∧ N = krausApply A ∧
    ∃ (R : Superop (Fin m) E) (S : Superop E (Fin m)),
      IsChannel R ∧ IsChannel S ∧ C = R ∘ krausComplement A ∧
      krausComplement A = S ∘ C

/-- PDF p.8, Definition 3, Eq.(33): the local environment retains B TOGETHER
with the dilation environment, rather than the environment alone. -/
def localComplement (A : ObservableAlgebra H) (V : Matrix (H × E) H ℂ) :
    Superop H (H × E) :=
  mapFirst A.project ∘ conjSuperop V

/-- PDF p.5, Section III B: nonzero orthogonal sector projectors, with
pairwise distinct real charge eigenvalues. -/
structure Sectors (H : Type*) [Fintype H] [DecidableEq H] (r : ℕ) where
  P : Fin r → Mat H
  hermitian : ∀ i, (P i)ᴴ = P i
  nonzero : ∀ i, P i ≠ 0
  orthogonal : ∀ i j, P i * P j = if i = j then P i else 0
  complete : ∑ i, P i = 1
  values : Fin r → ℝ
  distinct : Function.Injective values

/-- PDF p.5, Eq.(14), the canonical blind charge measurement. -/
def sectorProject {r : ℕ} (s : Sectors H r) : Superop H H :=
  fun X => ∑ i, s.P i * X * s.P i

/-- PDF p.5: the charge is computed from the sector data. -/
def sectorChargeObservable {r : ℕ} (s : Sectors H r) : Mat H :=
  ∑ i, (s.values i : ℂ) • s.P i

/-- Exact PHYSICAL correction to P on the encoded space, PDF pp.3,5.
Equality on all logical matrices is equivalent by linearity to equality on
all logical density matrices; reference extensions are thereby retained. -/
def PhysicallyCorrectable (P : Superop H H) (N : Superop H H) (W : Matrix H L ℂ) : Prop :=
  ∃ R : Superop H H, IsChannel R ∧ IsPhysicalChannel P P R ∧
    ∀ X : Mat L, R (N (conjSuperop W X)) = P (conjSuperop W X)

/-- PDF p.5, Eqs.(18),(20): each conditional output is normalized only
AFTER summing its classical output sectors. Individual blocks need not have trace 1. -/
def ChargeStateCondition {r : ℕ} (s : Sectors H r) (A : J → Mat H)
    (W : Matrix H L ℂ) : Prop :=
  ∃ sigma : Fin r → Fin r → Mat J,
    (∀ i j, (sigma i j).PosSemidef) ∧
    (∀ i, ∑ j, (sigma i j).trace = 1) ∧
    ∀ j n m, Wᴴ * (A n)ᴴ * s.P j * A m * W =
      ∑ i, (sigma i j n m) • (Wᴴ * s.P i * W)

/-- PDF p.5, Eq.(21): one coefficient family, uniform in all subsequent indices. -/
def ChargeCoefficients {r : ℕ} (s : Sectors H r) (A : J → Mat H)
    (W : Matrix H L ℂ) : Prop :=
  ∃ c : Fin r → Fin r → J → J → ℂ,
    ∀ j n m, Wᴴ * (A n)ᴴ * s.P j * A m * W =
      ∑ i, c i j n m • (Wᴴ * s.P i * W)

/-- PDF p.9, Eq.(48): constant-output channel, on ALL matrices. -/
def constantChannel (sigma : Mat K) : Superop H K :=
  fun X => X.trace • sigma

/-- PDF pp.9--10: tensor-local exact correction on an arbitrary JOINT code. -/
def TensorCorrectable (N : Superop H H) (W : Matrix (H × B) L ℂ) : Prop :=
  ∃ R : Superop H H, IsChannel R ∧ ∀ X : Mat L,
    mapFirst (R ∘ N) (conjSuperop W X) = conjSuperop W X

/-- PDF p.10, Eq.(51): W_n = (I tensor <n|) W. -/
def codeSlice (W : Matrix (H × B) L ℂ) (n : B) : Matrix H L ℂ :=
  fun a l => W (a, n) l

/-- PDF pp.2--3: a finite spinless-fermion CAR representation on its actual
2^n-dimensional Fock space. Minimal dimension prevents extra spectator sectors. -/
structure Fermions (n : ℕ) where
  w : Fin (2 * n) → Mat (Fin (2 ^ n))
  hermitian : ∀ j, (w j)ᴴ = w j
  car : ∀ i j, w i * w j + w j * w i =
    if i = j then (2 : ℂ) • 1 else 0

/-- PDF pp.2--3: total parity, up to the immaterial global sign convention.
i^n times the ordered product of 2n Majoranas is a Hermitian involution.
Printed, PDF p.2 Eq.(1): i^(|omega|-1) for Majorana labels.
Changed: i^n on 2n ordered modes. Why: the printed four-mode value is
anti-Hermitian and squares to -I; parity must be a Hermitian involution. -/
def totalParity {n : ℕ} (f : Fermions n) : Mat (Fin (2 ^ n)) :=
  (Complex.I ^ n) • (List.ofFn f.w).prod

/-- PDF p.3: blind parity measurement. -/
def parityProject (C : Mat H) : Superop H H :=
  fun X => (1 / 2 : ℂ) • (X + C * X * C)

/-- PDF p.3, Proposition 1: both preserving and flipping parity are allowed. -/
def DefiniteParity (C X : Mat H) : Prop :=
  X * C = C * X ∨ X * C = -(C * X)

/-- PDF pp.2--3,10: the even algebra supported on a set of Majorana indices.
Repeated indices are harmless under CAR; the empty word supplies the identity. -/
def evenRegion {n : ℕ} (f : Fermions n) (S : Finset (Fin (2 * n))) :
    Submodule ℂ (Mat (Fin (2 ^ n))) :=
  Submodule.span ℂ {X | ∃ word : List (Fin (2 * n)),
    (∀ j ∈ word, j ∈ S) ∧ Even word.length ∧ X = (word.map f.w).prod}

/-- PDF p.7, Definition 2: strong locality retains BOTH clauses. -/
def StrongLocal (A : Set (Mat H)) (N : Superop H H) : Prop :=
  IsChannel N ∧ (∀ X ∈ A, operatorTraceDual N X ∈ A) ∧
    FixesObservables (Set.centralizer A) N

/-- The two Majoranas for each fermionic SITE in omega, PDF pp.2--3,10. -/
def siteModes {n : ℕ} (omega : Finset (Fin n)) : Finset (Fin (2 * n)) :=
  Finset.univ.filter fun j => ∃ s ∈ omega, j.val / 2 = s.val

/-- PDF p.10: regional parity for site regions, including the empty region.
Printed, PDF p.2 Eq.(1): i^(|omega|-1) for Majorana labels.
Changed: i^m on the 2m ordered modes of m sites, up to overall sign.
Why: the printed four-mode value is anti-Hermitian and squares to -I,
contrary to the source's parity involution and sector-projector conventions. -/
def regionParity {n : ℕ} (f : Fermions n) (omega : Finset (Fin n)) :
    Mat (Fin (2 ^ n)) :=
  (Complex.I ^ omega.card) •
    (((List.finRange (2 * n)).filter fun j => j ∈ siteModes omega).map f.w).prod

/-- PDF pp.3,10: plus sector indexed by false, minus by true. -/
def paritySector (C : Mat H) (k : Bool) : Mat H :=
  (1 / 2 : ℂ) • (1 + (if k then -C else C))

/-- PDF pp.9--10: exact strong-local correction of the algebra A vee A'.
For the even algebra of a SITE region this target is regional parity dephasing. -/
def StrongCorrectable (A : Set (Mat H)) (C : Mat H)
    (N : Superop H H) (W : Matrix H L ℂ) : Prop :=
  ∃ R : Superop H H, StrongLocal A R ∧ ∀ X : Mat L,
    R (N (conjSuperop W X)) = parityProject C (conjSuperop W X)

/-- PDF p.10, Eq.(53); one normalized environmental state per regional sector.
The order X_ij E_i† B E_j is copied from the rendered page. -/
def RegionalStateCondition (A : Set (Mat H)) (C : Mat H)
    (noise : J → Mat H) (W : Matrix H L ℂ) : Prop :=
  ∃ rho : Bool → Mat J, (∀ k, IsDensityMatrix (rho k)) ∧
    ∀ (Y : Mat H), Y ∈ Set.centralizer A → ∀ X : Mat J,
      (∑ i, ∑ j, X i j • (Wᴴ * (noise i)ᴴ * Y * noise j * W)) =
      ∑ k : Bool, (rho k * X).trace •
        (Wᴴ * paritySector C k * Y * paritySector C k * W)

/-- PDF p.10, Eq.(54): the coefficient family is UNIFORM in the commutant
observable Y. Sector compression is on both sides, without division by its weight. -/
def RegionalCoefficients (A : Set (Mat H)) (C : Mat H)
    (noise : J → Mat H) (W : Matrix H L ℂ) : Prop :=
  ∃ lambda : J → J → Bool → ℂ, ∀ i j k (Y : Mat H), Y ∈ Set.centralizer A →
    Wᴴ * (noise i)ᴴ * noise j * (paritySector C k * Y * paritySector C k) * W =
      lambda i j k • (Wᴴ * (paritySector C k * Y * paritySector C k) * W)

/-- PDF pp.6,10: number of paired Majoranas strictly between adjacent free modes. -/
def ringGap {n k : ℕ} (free : Fin (2 * k) → Fin (2 * n))
    (j : Fin (2 * k)) : ℕ :=
  ((free (finRotate (2 * k) j)).val + 2 * n - (free j).val - 1) % (2 * n)

/-- PDF pp.6--7,10--11: ordered free modes and the alternating nearest-neighbor
paired intervals between them. Even gaps give the alternating pairing types. -/
structure RingLayout (n k : ℕ) where
  sites_pos : 0 < n
  logical_pos : 0 < k
  free : Fin (2 * k) → Fin (2 * n)
  ordered : StrictMono free
  even_gaps : ∀ j, Even (ringGap free j)

/-- Cyclic mode at a specified offset. -/
def modeAt {n : ℕ} (hn : 0 < n) (j : Fin (2 * n)) (offset : ℕ) : Fin (2 * n) :=
  ⟨(j.val + offset) % (2 * n), Nat.mod_lt _ (by omega)⟩

/-- PDF pp.6--7,10--11: ACTUAL pairing-ground projector. Each paired
nearest-neighbor fermion is initialized in its vacuum. The ordered bond (a,b)
has vacuum projector (I-i w_a w_b)/2; reversing bond orientation changes its sign.
The free modes receive no projector, so ALL their states are encoded. -/
def pairingProjector {n k : ℕ} (f : Fermions n) (r : RingLayout n k) :
    Mat (Fin (2 ^ n)) :=
  (((List.finRange (2 * k)).flatMap fun j =>
    (List.range (ringGap r.free j / 2)).map fun t =>
      (1 / 2 : ℂ) • (1 - Complex.I •
        (f.w (modeAt r.sites_pos (r.free j) (1 + 2 * t)) *
         f.w (modeAt r.sites_pos (r.free j) (2 + 2 * t)))))).prod

/-- PDF pp.6--7: an isometry ONTO the computed pairing ground code, not an
arbitrary invariant subspace. Logical dimension is exactly 2^k. -/
structure RingCode {n k : ℕ} (f : Fermions n) (r : RingLayout n k) where
  W : Matrix (Fin (2 ^ n)) (Fin (2 ^ k)) ℂ
  isometry : Wᴴ * W = 1
  onto_pairing_ground : W * Wᴴ = pairingProjector f r

/-- PDF p.10: shortest paired interval. Initial bound 2n dominates every gap;
the nonempty list has length 2k. Empty paired intervals therefore give d=0. -/
def minimumGap {n k : ℕ} (r : RingLayout n k) : ℕ :=
  (List.ofFn (ringGap r.free)).foldl min (2 * n)

/-- PDF p.10: a WHOLE Kraus operator is an even polynomial supported in one
cyclic interval containing length modes; length=0 permits only scalar operators. -/
def HasIntervalSupport {n : ℕ} (f : Fermions n)
    (X : Mat (Fin (2 ^ n))) (length : ℕ) : Prop :=
  ∃ start : Fin (2 * n), X ∈ evenRegion f
    (Finset.univ.filter fun j =>
      (j.val + 2 * n - start.val) % (2 * n) < length)

/-- PDF pp.6--7: equally weighted jumps on the first two unpaired Majoranas. -/
def poisoning {n k : ℕ} (f : Fermions n) (r : RingLayout n k) :
    Superop (Fin (2 ^ n)) (Fin (2 ^ n)) :=
  let a : Fin (2 * k) := ⟨0, by have := r.logical_pos; omega⟩
  let b : Fin (2 * k) := ⟨1, by have := r.logical_pos; omega⟩
  fun X => (1 / 2 : ℂ) •
    (conjSuperop (f.w (r.free a)) X + conjSuperop (f.w (r.free b)) X)

/-- Sanity check for the reused trace adjoint on matrix units. -/
example (N : Superop H K) (X : Mat K) (i j : H) :
    operatorTraceDual N X i j = (N (Matrix.single j i 1) * X).trace := by
  rfl

example {n k : ℕ} (f : Fermions n) (r : RingLayout n k)
    (hz : ∀ j, ringGap r.free j = 0) : pairingProjector f r = 1 := by
  simp only [pairingProjector, hz, Nat.zero_div, List.range_zero, List.map_nil]
  have hempty : ∀ js : List (Fin (2 * k)),
      js.flatMap (fun _ => ([] : List (Mat (Fin (2 ^ n))))) = [] := by
    intro js
    induction js with
    | nil => rfl
    | cons j js ih => simpa only [List.flatMap_cons, List.nil_append] using ih
  rw [hempty]
  rfl

example (N : Superop H K) : IsPhysicalChannel id id N := by
  intro X
  rfl

example (N : Superop H K) (X : Mat (H × B)) (i j : K) (b b2 : B) :
    mapFirst N X (i, b) (j, b2) = N (fun a a2 => X (a, b) (a2, b2)) i j := by
  rfl

example (sigma : Mat K) : constantChannel (H := H) sigma (0 : Mat H) = 0 := by
  simp [constantChannel]

example (W : Matrix (H × B) L ℂ) (a : H) (b : B) (l : L) :
    codeSlice W b a l = W (a, b) l := by
  rfl

example (f : Fermions 0) : totalParity f = 1 := by
  simp [totalParity]

example {n : ℕ} (f : Fermions n) : regionParity f ∅ = 1 := by
  simp [regionParity, siteModes]

example : paritySector (1 : Mat H) true = 0 := by
  simp [paritySector]

example (C : Mat H) : DefiniteParity C 1 := by
  exact Or.inl (by simp)

end QAlgorithms.Papers.Independent.Intakethird100.P44


