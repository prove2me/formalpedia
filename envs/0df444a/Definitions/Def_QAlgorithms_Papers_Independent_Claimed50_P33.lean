-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
-- name    : QAlgorithms_Papers_Independent_Claimed50_P33
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T12:30:53.692868+00:00
-- url     : https://prove2.me/theorems/1dc6d110-e2d4-4a1b-87e6-b08b21ab5bb0
-- title:
--   Definitions for Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof
-- statement:
--   The objects the formalized statements of *Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof* (arXiv:0704.2236) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `RegisterBasis`: Product computational basis of local registers (PDF pp.2–3).
--   - `SubBasis`: Basis on a selected set of registers (PDF pp.2–3).
--   - `registerMarginal`: Partial trace outside s, retaining both off-diagonal E indices (PDF pp.2–4).
--   - `entropyAt`: Entropy in bits of selected registers together with E (PDF pp.2–3).
--   - `InformationKind`: The two information quantities (PDF pp.2–3, equations (10),(13)).
--   - `allParties`: Union of the party registers (PDF p.3).
--   - `DisjointRegisters`: Party registers are disjoint and avoid the conditioning registers (PDF pp.3–6).
--   - `conditionalMultipartiteInformation`: Condition every entropy term on E and e, without 1/2 (PDF pp.2–4). The coefficient m-1 is used only with m≥1.
--   - `trivialExtension`: Attach a one-dimensional external register (PDF p.4).
--   - `info`: Correlation conditioned only on the named registers e (PDF pp.3–6).
--   - `singleParties`: One physical register per party (PDF p.4, Definition 3).
--   - `forgetEnvironment`: Trace out the last tensor factor (PDF p.4, Definition 3).
--   - `IsClassicalExtension`: Classical-on-E extensions in any orthonormal basis (PDF p.7, Definition 5). The conditional states may be mixed.
--   - `multipartiteSquashed`: Definitions 3,5 (PDF pp.4,7), with NO 1/2. All positive finite e and all normalized extensions are allowed, without a cap or attainment. For density inputs and m≥2 the value sets are nonempty and bounded below: the trivial extension is admissible, and conditional information is nonnegative. Invalid-input total-function defaults are excluded by every theorem.
--   - `halfExtensionSquashed`: Explicit half-rescaling of Definition 3 (PDF p.4; equation (58), p.7).
--   - `halfChannelSquashed`: Half-infimum over all positive output dimensions and all CPTP maps on the FIXED purifying register, preserving the reference (PDF p.7,(58)).
--   - `pairedProduct`: Independent product, pairing honest parties and external registers (PDF p.6).
--   - `partyProduct`: Partywise tensor product (PDF p.6, Proposition 4).
--   - `unprimedMarginal`: Unprimed marginal; product structure is not required (PDF p.6,(49)).
--   - `primedMarginal`: Primed marginal; product structure is not required (PDF p.6,(49)).
--   - `entropyExpression`: Condition an arbitrary linear entropy expression term by term (PDF p.3,(16)).
--   - `twiceConditioned`: Successive conditioning without losing any coefficient (PDF p.3,(16)).
--   - `attachFirst`: Attach X to the first party (PDF p.4,(18)–(22)).
--   - `earlierParties`: Parties earlier than Ai, including A1 (PDF p.4,(19)).
--   - `laterParties`: All parties except A1 (PDF p.4,(20),(21)).
--   - `localAction`: Lift a local channel, allowing a new output dimension. Elsewhere the equivalences identify unchanged bases. E is untouched (PDF p.4, Prop.2(ii)).
--   - `flowerFourier`: Unitary Fourier coefficients U_j|i>, U_0=identity and U_1=DFT (PDF p.7, Definition 7). Positive phase is a fixed DFT convention.
--   - `flowerVector`: Constructed normalized flower purification for m≥1,d≥1: repeat the same (i,j) in every honest register and apply U_j to X (PDF pp.7–8,(57)).
--   - `multipartiteFlower`: Flower state obtained by actually tracing X out (PDF p.7,(57)).
--   - `eraseFlowerFlag`: Loss of party p's flag qubit, followed by replacement with a fixed pure zero flag. This realizes the erased state with a harmless local pure ancilla, using a fixed common ambient basis (PDF pp.7–8, Prop.6).
--   - `privateDit`: Twisted GHZ private dit (PDF p.9,(70)). All key indices run independently in the double sum; the shield may be mixed and entangled.
--   - `FiniteState`: Bundled finite normalized state, across arbitrary nonzero local dimensions (PDF p.4, Definition 2).
--   - `stateEntry`: Extend entries by zero outside the finite basis; facilitates exact mixtures of states on the SAME space without casts (PDF p.6, Definition 4).
--   - `IsMixture`: All finite mixed-state decompositions, not pure-state decompositions; zero weights are allowed (PDF p.6, Definition 4).
--   - `bundledMixedRoof`: Bundled-state adapter to the accepted mixed convex roof (PDF p.6,(50)). The imported Information100.P08.mixedRoof optimizes every finite ensemble of normalized mixed matrices on this fixed space. The zero fallback of the score on a non-density matrix is never used by any admissible ensemble. For continuous g compactness bounds the nonempty value set below.
--   - `IsConvexFunctional`: Convexity for every finite ensemble on a fixed space (PDF pp.5–6).
--   - `IsContinuousFunctional`: Continuity on every finite state space, as required in Theorem 1 (PDF pp.6–7). No nonnegativity or separable-state normalization is imposed.
--   - `liftLocalKraus`: Lift one rectangular local Kraus operator, identity on every other party (PDF p.4,(23),(26)). Other parties' dimensions must be unchanged.
--   - `LocalInstrument`: A complete local instrument with normalized outcomes. Arbitrary finite Kraus multiplicities, ancillary preparation and disposal, and different output dimensions are included. The displayed subnormalized-state equation handles zero-probability outcomes without division (PDF p.4,(23),(26), p.6,(51)).
--   - `LOCC`: Finite adaptive LOCC tree: each local outcome selects its own continuation. The final constructor forgets the transcript and mixes the leaves. This includes selective and deterministic LOCC (PDF p.4, Definition 2).
--   - `IsAverageLocalMonotone`: Average monotonicity for every local instrument (PDF pp.4,6, Theorem 1).
--   - `IsAdaptiveLOCCMonotone`: Average monotonicity for all adaptive LOCC outcomes (PDF p.4,(26)).
--   - `squashedFunctional`: Squashed functional on bundled states (PDF pp.4,7, Definitions 3,5).
--   - `informationFunctional`: Unconditional I_m or S_m on a bundled state (PDF pp.2–3).
--   - `HasLocalFlags`: Orthogonal flags belong to a specified HONEST party, not to E. Flag index j is encoded as j*localDimension+oldIndex (PDF p.4,(28), p.5).
--   - `SatisfiesFlags`: Exact FLAGS identity for all local flags (PDF pp.4–5).
--   - `IsMixedFullySeparable`: Fully separable honest states, with all finite product decompositions (PDF p.5,(30)). This is not just separability across honest-system:E.
--   - `IsLocalUnitaryInvariant`: Local unitary invariance, with every party unitary acting on its own register and the same local dimensions (PDF p.4,(27), p.5).
--   - `measuredJoint`: Independent local POVMs with two independent outcome indices, as intended by equation (54), PDF p.7. No communication is allowed.
--   - `independentMeasuredInformation`: Bipartite measured classical correlation I_c, supremum over all finite independent local POVMs, without an outcome cap (PDF p.7,(54)). The set is nonempty (one-outcome identity POVMs) and bounded by the local log dimensions.
--   - `ExtensionRestriction`: The two specific extension restrictions endorsed in Section VI (PDF p.12).
--   - `allowedExtension`: The cut is the ENTIRE joint honest system versus E (PDF p.12). Density normalization is supplied separately. For normalized input, IsSeparablePositive is exactly separability, since the weights then sum to one.
--   - `restrictedSquashed`: Squashing with separable or PPT system:E extensions, over all positive finite environment dimensions; no factor 1/2 (PDF p.12, Section VI). The trivial extension is admissible, and all objective values are nonnegative.
--   - `restrictedFunctional`: Restricted measure on bundled finite states (PDF p.12).
-- source:
--   Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof, arXiv:0704.2236v3, https://arxiv.org/abs/0704.2236v3

import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

/-! Yang et al., arXiv:0704.2236v3. Finite dimensions, entropies in bits.
Definition 3 has NO factor 1/2; the named half quantities are rescalings.
Compilation is pending the separately authorized batch compilation stage. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Product computational basis of local registers (PDF pp.2–3). -/
abbrev RegisterBasis {n : ℕ} (D : Fin n → Type) := (i : Fin n) → D i

/-- Basis on a selected set of registers (PDF pp.2–3). -/
abbrev SubBasis {n : ℕ} (D : Fin n → Type) (s : Finset (Fin n)) :=
  (i : {i : Fin n // i ∈ s}) → D i.val

/-- Partial trace outside s, retaining both off-diagonal E indices (PDF pp.2–4). -/
def registerMarginal {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)] {E : Type}
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ) (s : Finset (Fin n)) :
    Matrix (SubBasis D s × E) (SubBasis D s × E) ℂ :=
  fun a b => ∑ x : RegisterBasis D, ∑ y : RegisterBasis D,
    if (∀ i (hi : i ∈ s), x i = a.1 ⟨i,hi⟩ ∧ y i = b.1 ⟨i,hi⟩) ∧
        (∀ i, i ∉ s → x i = y i) then rho (x,a.2) (y,b.2) else 0

/-- Entropy in bits of selected registers together with E (PDF pp.2–3). -/
def entropyAt {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)] {E : Type}
    [Fintype E] (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (s : Finset (Fin n)) : ℝ := vnEntropy (registerMarginal rho s)

/-- The two information quantities (PDF pp.2–3, equations (10),(13)). -/
inductive InformationKind where
  | total
  | dual
  deriving DecidableEq

/-- Union of the party registers (PDF p.3). -/
def allParties {n m : ℕ} (a : Fin m → Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.biUnion a

/-- Party registers are disjoint and avoid the conditioning registers (PDF pp.3–6). -/
def DisjointRegisters {n m : ℕ} (a : Fin m → Finset (Fin n))
    (e : Finset (Fin n)) : Prop :=
  (∀ i j, i ≠ j → Disjoint (a i) (a j)) ∧ ∀ i, Disjoint (a i) e

/-- Condition every entropy term on E and e, without 1/2 (PDF pp.2–4).
The coefficient m-1 is used only with m≥1. -/
def conditionalMultipartiteInformation {n m : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    {E : Type} [Fintype E] (kind : InformationKind)
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (a : Fin m → Finset (Fin n)) (e : Finset (Fin n)) : ℝ :=
  match kind with
  | .total => (∑ i, entropyAt rho (a i ∪ e)) -
      entropyAt rho (allParties a ∪ e) - (m-1 : ℕ) * entropyAt rho e
  | .dual => (∑ i, entropyAt rho ((Finset.univ.erase i).biUnion a ∪ e)) -
      (m-1 : ℕ) * entropyAt rho (allParties a ∪ e) - entropyAt rho e

/-- Attach a one-dimensional external register (PDF p.4). -/
def trivialExtension {n : ℕ} {D : Fin n → Type}
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    Matrix (RegisterBasis D × Unit) (RegisterBasis D × Unit) ℂ := fun a b => rho a.1 b.1

/-- Correlation conditioned only on the named registers e (PDF pp.3–6). -/
def info {n m : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (kind : InformationKind) (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (a : Fin m → Finset (Fin n)) (e : Finset (Fin n)) : ℝ :=
  conditionalMultipartiteInformation kind (trivialExtension rho) a e

/-- One physical register per party (PDF p.4, Definition 3). -/
def singleParties (m : ℕ) : Fin m → Finset (Fin m) := fun i => {i}

/-- Trace out the last tensor factor (PDF p.4, Definition 3). -/
def forgetEnvironment {I E : Type} [Fintype E]
    (rho : Matrix (I × E) (I × E) ℂ) : Matrix I I ℂ :=
  fun a b => ∑ e, rho (a,e) (b,e)

/-- Classical-on-E extensions in any orthonormal basis (PDF p.7, Definition 5).
The conditional states may be mixed. -/
def IsClassicalExtension {I : Type} [Fintype I] {e : ℕ}
    (sigma : Matrix (I × Fin e) (I × Fin e) ℂ) : Prop :=
  ∃ U : Matrix.unitaryGroup (Fin e) ℂ, ∃ p : Fin e → ℝ,
    ∃ r : Fin e → Matrix I I ℂ,
    (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧ (∀ j, IsDensityMatrix (r j)) ∧
    ∀ a b, sigma a b = ∑ j, (p j : ℂ) * r j a.1 b.1 *
      (U : Matrix (Fin e) (Fin e) ℂ) a.2 j *
      conj ((U : Matrix (Fin e) (Fin e) ℂ) b.2 j)

/-- Definitions 3,5 (PDF pp.4,7), with NO 1/2. All positive finite e and
all normalized extensions are allowed, without a cap or attainment.
For density inputs and m≥2 the value sets are nonempty and bounded below:
the trivial extension is admissible, and conditional information is nonnegative.
Invalid-input total-function defaults are excluded by every theorem. -/
def multipartiteSquashed {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    (classical : Bool) (kind : InformationKind)
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) : ℝ :=
  sInf {v : ℝ | ∃ e : ℕ, 0 < e ∧
    ∃ sigma : Matrix (RegisterBasis D × Fin e) (RegisterBasis D × Fin e) ℂ,
      IsDensityMatrix sigma ∧ forgetEnvironment sigma = rho ∧
      (classical = true → IsClassicalExtension sigma) ∧
      v = conditionalMultipartiteInformation kind sigma (singleParties m) ∅}

/-- Explicit half-rescaling of Definition 3 (PDF p.4; equation (58), p.7). -/
def halfExtensionSquashed {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    (kind : InformationKind) (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) : ℝ :=
  multipartiteSquashed false kind rho / 2

/-- Half-infimum over all positive output dimensions and all CPTP maps on
the FIXED purifying register, preserving the reference (PDF p.7,(58)). -/
def halfChannelSquashed {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R] (kind : InformationKind)
    (psi : EuclideanSpace ℂ (RegisterBasis D × R)) : ℝ :=
  sInf {v : ℝ | ∃ e : ℕ, 0 < e ∧ ∃ Phi : Superop R (Fin e),
    IsChannel Phi ∧ v = conditionalMultipartiteInformation kind
      (idTensorSuperop Phi (pureDensity psi)) (singleParties m) ∅ / 2}

/-- Independent product, pairing honest parties and external registers (PDF p.6). -/
def pairedProduct {m : ℕ} {D F : Fin m → Type} {E Z : Type}
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (sigma : Matrix (RegisterBasis F × Z) (RegisterBasis F × Z) ℂ) :
    Matrix (RegisterBasis (fun i => D i × F i) × (E × Z))
      (RegisterBasis (fun i => D i × F i) × (E × Z)) ℂ :=
  fun a b => rho ((fun i => (a.1 i).1),a.2.1) ((fun i => (b.1 i).1),b.2.1) *
    sigma ((fun i => (a.1 i).2),a.2.2) ((fun i => (b.1 i).2),b.2.2)

/-- Partywise tensor product (PDF p.6, Proposition 4). -/
def partyProduct {m : ℕ} {D F : Fin m → Type}
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (sigma : Matrix (RegisterBasis F) (RegisterBasis F) ℂ) :
    Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ :=
  fun a b => rho (fun i => (a i).1) (fun i => (b i).1) *
    sigma (fun i => (a i).2) (fun i => (b i).2)

/-- Unprimed marginal; product structure is not required (PDF p.6,(49)). -/
def unprimedMarginal {m : ℕ} {D F : Fin m → Type} [∀ i, Fintype (F i)]
    (rho : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ) :
    Matrix (RegisterBasis D) (RegisterBasis D) ℂ :=
  fun a b => ∑ z : RegisterBasis F, rho (fun i => (a i,z i)) (fun i => (b i,z i))

/-- Primed marginal; product structure is not required (PDF p.6,(49)). -/
def primedMarginal {m : ℕ} {D F : Fin m → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ) :
    Matrix (RegisterBasis F) (RegisterBasis F) ℂ :=
  fun a b => ∑ z : RegisterBasis D, rho (fun i => (z i,a i)) (fun i => (z i,b i))

/-- Condition an arbitrary linear entropy expression term by term (PDF p.3,(16)). -/
def entropyExpression {n k : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    {E : Type} [Fintype E] (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (c : Fin k → ℝ) (s : Fin k → Finset (Fin n)) (e : Finset (Fin n)) : ℝ :=
  ∑ j, c j * (entropyAt rho (s j ∪ e) - entropyAt rho e)

/-- Successive conditioning without losing any coefficient (PDF p.3,(16)). -/
def twiceConditioned {n k : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    {E : Type} [Fintype E] (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (c : Fin k → ℝ) (s : Fin k → Finset (Fin n)) (e f : Finset (Fin n)) : ℝ :=
  ∑ j, c j * ((entropyAt rho ((s j ∪ e) ∪ f) - entropyAt rho f) -
    (entropyAt rho (e ∪ f) - entropyAt rho f))

/-- Attach X to the first party (PDF p.4,(18)–(22)). -/
def attachFirst {n k : ℕ} (a : Fin (k+2) → Finset (Fin n))
    (x : Finset (Fin n)) : Fin (k+2) → Finset (Fin n) :=
  fun i => if i = 0 then x ∪ a i else a i

/-- Parties earlier than Ai, including A1 (PDF p.4,(19)). -/
def earlierParties {n m : ℕ} (a : Fin m → Finset (Fin n)) (i : Fin m) :
    Finset (Fin n) := (Finset.univ.filter fun j => j.val < i.val).biUnion a

/-- All parties except A1 (PDF p.4,(20),(21)). -/
def laterParties {n k : ℕ} (a : Fin (k+2) → Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ.erase 0).biUnion a

/-- Lift a local channel, allowing a new output dimension. Elsewhere the
equivalences identify unchanged bases. E is untouched (PDF p.4, Prop.2(ii)). -/
def localAction {n : ℕ} {D F : Fin n → Type} [∀ i, Fintype (D i)]
    {E : Type} (p : Fin n) (other : ∀ j, j ≠ p → D j ≃ F j)
    (Phi : Superop (D p) (F p))
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ) :
    Matrix (RegisterBasis F × E) (RegisterBasis F × E) ℂ :=
  fun a b => ∑ x : RegisterBasis D, ∑ y : RegisterBasis D,
    if ∀ j (hj : j ≠ p), a.1 j = other j hj (x j) ∧ b.1 j = other j hj (y j)
    then rho (x,a.2) (y,b.2) * Phi (Matrix.single (x p) (y p) 1) (a.1 p) (b.1 p)
    else 0

/-- Unitary Fourier coefficients U_j|i>, U_0=identity and U_1=DFT
(PDF p.7, Definition 7). Positive phase is a fixed DFT convention. -/
def flowerFourier (d : ℕ) (j : Bool) (i x : Fin d) : ℂ :=
  if j then (Real.sqrt (d : ℝ) : ℂ)⁻¹ *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (i.val : ℂ) * (x.val : ℂ) / (d : ℂ))
  else if x = i then 1 else 0

/-- Constructed normalized flower purification for m≥1,d≥1: repeat the
same (i,j) in every honest register and apply U_j to X (PDF pp.7–8,(57)). -/
def flowerVector (m d : ℕ) :
    EuclideanSpace ℂ (RegisterBasis (fun _ : Fin m => Fin d × Bool) × Fin d) :=
  WithLp.toLp 2 fun x => (Real.sqrt (2 * (d : ℝ)) : ℂ)⁻¹ *
    ∑ i : Fin d, ∑ j : Bool,
      if ∀ p, x.1 p = (i,j) then flowerFourier d j i x.2 else 0

/-- Flower state obtained by actually tracing X out (PDF p.7,(57)). -/
def multipartiteFlower (m d : ℕ) :
    Matrix (RegisterBasis (fun _ : Fin m => Fin d × Bool))
      (RegisterBasis (fun _ : Fin m => Fin d × Bool)) ℂ :=
  forgetEnvironment (pureDensity (flowerVector m d))

/-- Loss of party p's flag qubit, followed by replacement with a fixed
pure zero flag. This realizes the erased state with a harmless local pure
ancilla, using a fixed common ambient basis (PDF pp.7–8, Prop.6). -/
def eraseFlowerFlag {m d : ℕ} (p : Fin m)
    (rho : Matrix (RegisterBasis (fun _ : Fin m => Fin d × Bool))
      (RegisterBasis (fun _ : Fin m => Fin d × Bool)) ℂ) :
    Matrix (RegisterBasis (fun _ : Fin m => Fin d × Bool))
      (RegisterBasis (fun _ : Fin m => Fin d × Bool)) ℂ :=
  fun x y => if (x p).2 = false ∧ (y p).2 = false then
    ∑ j : Bool, rho (Function.update x p ((x p).1,j))
      (Function.update y p ((y p).1,j)) else 0

/-- Twisted GHZ private dit (PDF p.9,(70)). All key indices run
independently in the double sum; the shield may be mixed and entangled. -/
def privateDit {m : ℕ} {H : Fin m → Type} [∀ i, Fintype (H i)]
    (d : ℕ) (tau : Matrix (RegisterBasis H) (RegisterBasis H) ℂ)
    (U : Fin d → Matrix.unitaryGroup (RegisterBasis H) ℂ) :
    Matrix (RegisterBasis (fun i => Fin d × H i)) (RegisterBasis (fun i => Fin d × H i)) ℂ :=
  fun x y => ∑ a : Fin d, ∑ b : Fin d,
    if (∀ i, (x i).1 = a ∧ (y i).1 = b) then
      (d : ℂ)⁻¹ * ((U a : Matrix (RegisterBasis H) (RegisterBasis H) ℂ) * tau *
        (U b : Matrix (RegisterBasis H) (RegisterBasis H) ℂ)ᴴ)
        (fun i => (x i).2) (fun i => (y i).2) else 0

/-- Bundled finite normalized state, across arbitrary nonzero local dimensions
(PDF p.4, Definition 2). -/
structure FiniteState (m : ℕ) where
  dims : Fin m → ℕ
  positive : ∀ i, 0 < dims i
  rho : Matrix (RegisterBasis (fun i => Fin (dims i))) (RegisterBasis (fun i => Fin (dims i))) ℂ
  normalized : IsDensityMatrix rho

/-- Extend entries by zero outside the finite basis; facilitates exact mixtures
of states on the SAME space without casts (PDF p.6, Definition 4). -/
def stateEntry {m : ℕ} (s : FiniteState m) (x y : Fin m → ℕ) : ℂ :=
  if h : (∀ i, x i < s.dims i) ∧ (∀ i, y i < s.dims i) then
    s.rho (fun i => ⟨x i,h.1 i⟩) (fun i => ⟨y i,h.2 i⟩) else 0

/-- All finite mixed-state decompositions, not pure-state decompositions;
zero weights are allowed (PDF p.6, Definition 4). -/
def IsMixture {m k : ℕ} (s : FiniteState m) (p : Fin k → ℝ)
    (r : Fin k → FiniteState m) : Prop :=
  (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧ (∀ j, (r j).dims = s.dims) ∧
    ∀ x y, stateEntry s x y = ∑ j, (p j : ℂ) * stateEntry (r j) x y

/-- Bundled-state adapter to the accepted mixed convex roof (PDF p.6,(50)).
The imported Information100.P08.mixedRoof optimizes every finite ensemble of
normalized mixed matrices on this fixed space. The zero fallback of the score
on a non-density matrix is never used by any admissible ensemble.
For continuous g compactness bounds the nonempty value set below. -/
def bundledMixedRoof {m : ℕ} (g : FiniteState m → ℝ) (s : FiniteState m) : ℝ :=
  QAlgorithms.Papers.Independent.Information100.P08.mixedRoof
    (fun rho => if h : IsDensityMatrix rho then g ⟨s.dims,s.positive,rho,h⟩ else 0)
    s.rho

/-- Convexity for every finite ensemble on a fixed space (PDF pp.5–6). -/
def IsConvexFunctional {m : ℕ} (g : FiniteState m → ℝ) : Prop :=
  ∀ (k : ℕ) (s : FiniteState m) (p : Fin k → ℝ) (r : Fin k → FiniteState m),
    IsMixture s p r → g s ≤ ∑ j, p j * g (r j)

/-- Continuity on every finite state space, as required in Theorem 1
(PDF pp.6–7). No nonnegativity or separable-state normalization is imposed. -/
def IsContinuousFunctional {m : ℕ} (g : FiniteState m → ℝ) : Prop :=
  ∀ (d : Fin m → ℕ) (hd : ∀ i, 0 < d i),
    Continuous (fun r : {r : Matrix (RegisterBasis (fun i => Fin (d i)))
      (RegisterBasis (fun i => Fin (d i))) ℂ // IsDensityMatrix r} => g ⟨d,hd,r.val,r.property⟩)

/-- Lift one rectangular local Kraus operator, identity on every other
party (PDF p.4,(23),(26)). Other parties' dimensions must be unchanged. -/
def liftLocalKraus {m : ℕ} (s t : FiniteState m) (party : Fin m)
    (A : Matrix (Fin (t.dims party)) (Fin (s.dims party)) ℂ) :
    Matrix (RegisterBasis (fun i => Fin (t.dims i))) (RegisterBasis (fun i => Fin (s.dims i))) ℂ :=
  fun x y => if ∀ i, i ≠ party → (x i).val = (y i).val then A (x party) (y party) else 0

/-- A complete local instrument with normalized outcomes. Arbitrary finite
Kraus multiplicities, ancillary preparation and disposal, and different output
dimensions are included. The displayed subnormalized-state equation handles
zero-probability outcomes without division (PDF p.4,(23),(26), p.6,(51)). -/
def LocalInstrument {m k : ℕ} (s : FiniteState m) (p : Fin k → ℝ)
    (r : Fin k → FiniteState m) : Prop :=
  (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧
  ∃ party : Fin m, ∃ count : Fin k → ℕ,
  ∃ A : (j : Fin k) → Fin (count j) →
    Matrix (Fin ((r j).dims party)) (Fin (s.dims party)) ℂ,
  (∀ j i, i ≠ party → (r j).dims i = s.dims i) ∧
  (∑ j, ∑ z, (liftLocalKraus s (r j) party (A j z))ᴴ *
      liftLocalKraus s (r j) party (A j z)) = 1 ∧
  ∀ j, (p j : ℂ) • (r j).rho =
    ∑ z, liftLocalKraus s (r j) party (A j z) * s.rho *
      (liftLocalKraus s (r j) party (A j z))ᴴ

/-- Finite adaptive LOCC tree: each local outcome selects its own continuation.
The final constructor forgets the transcript and mixes the leaves. This
includes selective and deterministic LOCC (PDF p.4, Definition 2). -/
inductive LOCC {m : ℕ} : FiniteState m → List (ℝ × FiniteState m) → Prop where
  | stop (s) : LOCC s [(1,s)]
  | step (s : FiniteState m) (k : ℕ) (p : Fin k → ℝ) (r : Fin k → FiniteState m)
      (h : LocalInstrument s p r) (next : Fin k → List (ℝ × FiniteState m))
      (hn : ∀ j, LOCC (r j) (next j)) :
      LOCC s ((List.finRange k).flatMap fun j =>
        (next j).map fun w => (p j * w.1,w.2))
  | forget (s t : FiniteState m) (out : List (ℝ × FiniteState m))
      (h : LOCC s out) (hd : ∀ w ∈ out, w.2.dims = t.dims)
      (hmix : ∀ x y, stateEntry t x y =
        (out.map fun w => (w.1 : ℂ) * stateEntry w.2 x y).sum) : LOCC s [(1,t)]

/-- Average monotonicity for every local instrument (PDF pp.4,6, Theorem 1). -/
def IsAverageLocalMonotone {m : ℕ} (g : FiniteState m → ℝ) : Prop :=
  ∀ (s : FiniteState m) (k : ℕ) (p : Fin k → ℝ) (r : Fin k → FiniteState m),
    LocalInstrument s p r → (∑ j, p j * g (r j)) ≤ g s

/-- Average monotonicity for all adaptive LOCC outcomes (PDF p.4,(26)). -/
def IsAdaptiveLOCCMonotone {m : ℕ} (g : FiniteState m → ℝ) : Prop :=
  ∀ (s : FiniteState m) (out : List (ℝ × FiniteState m)),
    LOCC s out → (out.map fun w => w.1 * g w.2).sum ≤ g s

/-- Squashed functional on bundled states (PDF pp.4,7, Definitions 3,5). -/
def squashedFunctional {m : ℕ} (classical : Bool) (kind : InformationKind)
    (s : FiniteState m) : ℝ := multipartiteSquashed classical kind s.rho

/-- Unconditional I_m or S_m on a bundled state (PDF pp.2–3). -/
def informationFunctional {m : ℕ} (kind : InformationKind) (s : FiniteState m) : ℝ :=
  info kind s.rho (singleParties m) ∅

/-- Orthogonal flags belong to a specified HONEST party, not to E.
Flag index j is encoded as j*localDimension+oldIndex (PDF p.4,(28), p.5). -/
def HasLocalFlags {m k : ℕ} (t : FiniteState m) (party : Fin m)
    (p : Fin k → ℝ) (r : Fin k → FiniteState m) : Prop :=
  (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧ ∃ d : Fin m → ℕ,
  (∀ i, 0 < d i) ∧ (∀ j, (r j).dims = d) ∧
  (∀ i, t.dims i = if i = party then k * d i else d i) ∧
  ∀ x y, stateEntry t x y = ∑ j,
    if x party / d party = j.val ∧ y party / d party = j.val then
      (p j : ℂ) * stateEntry (r j)
        (fun i => if i = party then x i % d i else x i)
        (fun i => if i = party then y i % d i else y i) else 0

/-- Exact FLAGS identity for all local flags (PDF pp.4–5). -/
def SatisfiesFlags {m : ℕ} (g : FiniteState m → ℝ) : Prop :=
  ∀ (k : ℕ) (t : FiniteState m) (party : Fin m)
    (p : Fin k → ℝ) (r : Fin k → FiniteState m),
    HasLocalFlags t party p r → g t = ∑ j, p j * g (r j)

/-- Fully separable honest states, with all finite product decompositions
(PDF p.5,(30)). This is not just separability across honest-system:E. -/
def IsMixedFullySeparable {m : ℕ} (s : FiniteState m) : Prop :=
  ∃ k : ℕ, ∃ p : Fin k → ℝ,
  ∃ r : (j : Fin k) → (i : Fin m) → Matrix (Fin (s.dims i)) (Fin (s.dims i)) ℂ,
    (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧ (∀ j i, IsDensityMatrix (r j i)) ∧
    ∀ x y, s.rho x y = ∑ j, (p j : ℂ) * ∏ i, r j i (x i) (y i)

/-- Local unitary invariance, with every party unitary acting on its own
register and the same local dimensions (PDF p.4,(27), p.5). -/
def IsLocalUnitaryInvariant {m : ℕ} (g : FiniteState m → ℝ) : Prop :=
  ∀ (s t : FiniteState m), t.dims = s.dims →
    ∀ U : (i : Fin m) → Matrix.unitaryGroup (Fin (s.dims i)) ℂ,
    let V : Matrix (RegisterBasis (fun i => Fin (s.dims i)))
        (RegisterBasis (fun i => Fin (s.dims i))) ℂ :=
      fun a b => ∏ i, (U i : Matrix (Fin (s.dims i)) (Fin (s.dims i)) ℂ) (a i) (b i)
    (∀ x y : RegisterBasis (fun i => Fin (s.dims i)),
      stateEntry t (fun i => (x i).val) (fun i => (y i).val) =
        (V * s.rho * Vᴴ) x y) →
    g t = g s

/-- Independent local POVMs with two independent outcome indices, as
intended by equation (54), PDF p.7. No communication is allowed. -/
def measuredJoint {k ell : ℕ} (s : FiniteState 2)
    (A : Fin k → Matrix (Fin (s.dims 0)) (Fin (s.dims 0)) ℂ)
    (B : Fin ell → Matrix (Fin (s.dims 1)) (Fin (s.dims 1)) ℂ) :
    Fin k × Fin ell → ℝ :=
  fun o =>
    let effect : Matrix (RegisterBasis (fun i => Fin (s.dims i)))
        (RegisterBasis (fun i => Fin (s.dims i))) ℂ :=
      fun x y => A o.1 (x 0) (y 0) * B o.2 (x 1) (y 1)
    (effect * s.rho).trace.re

/-- Bipartite measured classical correlation I_c, supremum over all finite
independent local POVMs, without an outcome cap (PDF p.7,(54)). The set is
nonempty (one-outcome identity POVMs) and bounded by the local log dimensions. -/
def independentMeasuredInformation (s : FiniteState 2) : ℝ :=
  sSup {v : ℝ | ∃ k ell : ℕ,
    ∃ A : Fin k → Matrix (Fin (s.dims 0)) (Fin (s.dims 0)) ℂ,
    ∃ B : Fin ell → Matrix (Fin (s.dims 1)) (Fin (s.dims 1)) ℂ,
      IsPOVM A ∧ IsPOVM B ∧ v = mutualInfoBits (measuredJoint s A B)}

/-- The two specific extension restrictions endorsed in Section VI (PDF p.12). -/
inductive ExtensionRestriction where
  | separable
  | ppt
  deriving DecidableEq

/-- The cut is the ENTIRE joint honest system versus E (PDF p.12).
Density normalization is supplied separately. For normalized input,
IsSeparablePositive is exactly separability, since the weights then sum to one. -/
def allowedExtension {I E : Type} [Fintype I] [Fintype E]
    (restriction : ExtensionRestriction) (sigma : Matrix (I × E) (I × E) ℂ) : Prop :=
  match restriction with
  | .separable => Entanglement.IsSeparablePositive sigma
  | .ppt => (Entanglement.partialTransposeFirst sigma).PosSemidef

/-- Squashing with separable or PPT system:E extensions, over all positive
finite environment dimensions; no factor 1/2 (PDF p.12, Section VI).
The trivial extension is admissible, and all objective values are nonnegative. -/
def restrictedSquashed {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    (restriction : ExtensionRestriction) (kind : InformationKind)
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) : ℝ :=
  sInf {v : ℝ | ∃ e : ℕ, 0 < e ∧
    ∃ sigma : Matrix (RegisterBasis D × Fin e) (RegisterBasis D × Fin e) ℂ,
      IsDensityMatrix sigma ∧ forgetEnvironment sigma = rho ∧
      allowedExtension restriction sigma ∧
      v = conditionalMultipartiteInformation kind sigma (singleParties m) ∅}

/-- Restricted measure on bundled finite states (PDF p.12). -/
def restrictedFunctional {m : ℕ} (restriction : ExtensionRestriction)
    (kind : InformationKind) (s : FiniteState m) : ℝ :=
  restrictedSquashed restriction kind s.rho

/-- Sanity: the trivial extension preserves matrix entries. -/
example {n : ℕ} {D : Fin n → Type} (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (x y : RegisterBasis D) : trivialExtension rho (x,()) (y,()) = rho x y := rfl

/-- Sanity: an empty linear expression is zero under conditioning. -/
example {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (s : Fin 0 → Finset (Fin n))
    (e : Finset (Fin n)) : entropyExpression (trivialExtension rho) Fin.elim0 s e = 0 := by
  simp [entropyExpression]

/-- Sanity: half normalization is explicit, not part of Definition 3. -/
example {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (kind : InformationKind) :
    halfExtensionSquashed kind rho = multipartiteSquashed false kind rho / 2 := rfl

/-- Sanity: pairing keeps the unprimed coordinates in the first state. -/
example {m : ℕ} {D F : Fin m → Type} (r : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (s : Matrix (RegisterBasis F) (RegisterBasis F) ℂ) (a b : RegisterBasis (fun i => D i × F i)) :
    partyProduct r s a b = r (fun i => (a i).1) (fun i => (b i).1) *
      s (fun i => (a i).2) (fun i => (b i).2) := rfl

/-- Sanity: the Fourier normalization at d=1 is one for both flags. -/
example (j : Bool) (i x : Fin 1) : flowerFourier 1 j i x = 1 := by
  have hi : i = 0 := Subsingleton.elim _ _
  have hx : x = 0 := Subsingleton.elim _ _
  subst i
  subst x
  cases j <;> simp [flowerFourier]

/-- Sanity: a lost flag has no matrix entries in the flag-one subspace. -/
example {m d : ℕ} (p : Fin m)
    (rho : Matrix (RegisterBasis (fun _ : Fin m => Fin d × Bool))
      (RegisterBasis (fun _ : Fin m => Fin d × Bool)) ℂ)
    (x y : RegisterBasis (fun _ : Fin m => Fin d × Bool)) (h : (x p).2 = true) :
    eraseFlowerFlag p rho x y = 0 := by
  simp [eraseFlowerFlag, h]

/-- Sanity: no LOCC steps gives the unit-weight input state. -/
example {m : ℕ} (s : FiniteState m) : LOCC s [(1,s)] := LOCC.stop s

/-- Sanity: explicit probabilities prevent an empty decomposition. -/
example {m : ℕ} (s : FiniteState m) (r : Fin 0 → FiniteState m)
    (h : IsMixture s Fin.elim0 r) : False := by
  have hh := h.2.1
  simpa using hh

/-- Sanity: ordinary PPT transpose is taken across the complete honest basis. -/
example {I E : Type} [Fintype I] [Fintype E]
    (sigma : Matrix (I × E) (I × E) ℂ) :
    allowedExtension .ppt sigma =
      (Entanglement.partialTransposeFirst sigma).PosSemidef := rfl

end QAlgorithms.Papers.Independent.Claimed50.P33


