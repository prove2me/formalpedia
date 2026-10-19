-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P07_Model
-- name    : QAlgorithms_Papers_Independent_Independent1_P07_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:22:33.95598+00:00
-- url     : https://prove2.me/theorems/77a11dbc-a011-42af-9d53-8437fba2dbb3
-- title:
--   A computable measure of entanglement: supporting definitions
-- statement:
--   Reviewed paper-local supporting definitions and conventions. The attached text aggregates the existing blind readbacks of every definition; it makes no theorem proof claim.
-- source:
--   A computable measure of entanglement, arXiv:quant-ph/0102117v1. PDF SHA-256: a6bc5031b04d93cf18e71e39425eea8b9b8c938252bb87d8067d890269b90f7b. Exact locators remain in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_EntanglementNegativity
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
/-! Vidal–Werner, arXiv:quant-ph/0102117v1. All locators are PDF pages.
Paper-local operational and variational definitions precede their statements.
Deferred source inconsistencies and interfaces are recorded in HARD.md. -/

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P07

open Entanglement

/-- Eq. (2), PDF pp. 1–2, with base two. -/
def logNeg {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (X : Matrix (I × J) (I × J) ℂ) : ℝ :=
  Real.logb 2 (traceNorm (partialTransposeFirst X))

/-- Regroup by party before applying partial transpose (Eq. (11), PDF p. 3). -/
def bipartiteTensor {I J K L : Type*}
    (X : Matrix (I × J) (I × J) ℂ) (Y : Matrix (K × L) (K × L) ℂ) :
    Matrix ((I × K) × (J × L)) ((I × K) × (J × L)) ℂ :=
  (Matrix.kronecker X Y).submatrix
    (fun z => ((z.1.1,z.2.1),(z.1.2,z.2.2)))
    (fun z => ((z.1.1,z.2.1),(z.1.2,z.2.2)))

/-- Eq. (8), PDF p. 3. Zero coefficients are allowed. -/
def JordanDecomposition {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (ap am : ℝ) (rp rm : Matrix I I ℂ) : Prop :=
  0 ≤ ap ∧ 0 ≤ am ∧ IsDensityMatrix rp ∧ IsDensityMatrix rm ∧
    A = (ap : ℂ) • rp - (am : ℂ) • rm

/-- Absolute sum of the negative eigenvalues, with multiplicity (Lemma 2, PDF p. 3). -/
def negativeMass {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) : ℝ :=
  ∑ k, max 0 (-ascEigenvalues A k)

/-- Eqs. (18)–(19), PDF p. 4: decomposition over a specified trace-one base. -/
def BaseDecomposition {I : Type*} (S : Set (Matrix I I ℂ))
    (A : Matrix I I ℂ) (ap am : ℝ) (rp rm : Matrix I I ℂ) : Prop :=
  0 ≤ ap ∧ 0 ≤ am ∧ rp ∈ S ∧ rm ∈ S ∧ A = (ap : ℂ) • rp - (am : ℂ) • rm

/-- Eq. (18), PDF p. 4; feasibility and boundedness are derived below. -/
def baseNorm {I : Type*} (S : Set (Matrix I I ℂ)) (A : Matrix I I ℂ) : ℝ :=
  sInf {v | ∃ ap am rp rm, BaseDecomposition S A ap am rp rm ∧ v = ap+am}

/-- Eq. (19), PDF p. 4; this is not itself a norm. -/
def baseNeg {I : Type*} (S : Set (Matrix I I ℂ)) (A : Matrix I I ℂ) : ℝ :=
  sInf {v | ∃ ap am rp rm, BaseDecomposition S A ap am rp rm ∧ v = am}

/-- §II.C, PDF p. 4: compact convex trace-one base spanning every Hermitian matrix.
Positivity of members is deliberately not required. -/
def IsBase {I : Type*} [Fintype I] [DecidableEq I] (S : Set (Matrix I I ℂ)) : Prop :=
  IsCompact S ∧ Convex ℝ S ∧ (∀ X ∈ S, X.IsHermitian ∧ X.trace = 1) ∧
    ∀ X : Matrix I I ℂ, X.IsHermitian → X ∈ Submodule.span ℝ S

/-- PPT-state base, §II.C, PDF p. 4. -/
def pptBase {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] :
    Set (Matrix (I × J) (I × J) ℂ) :=
  {X | IsDensityMatrix X ∧ (partialTransposeFirst X).PosSemidef}

/-- Separable-state base, §II.C, PDF p. 4. -/
def separableBase {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] :
    Set (Matrix (I × J) (I × J) ℂ) := {X | IsSeparableDensity X}

/-- Separable robustness with Eq. (19)'s normalization, PDF p. 4. -/
def separableRobustness {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (X : Matrix (I × J) (I × J) ℂ) : ℝ := baseNeg separableBase X

/-- PPT robustness with Eq. (19)'s normalization, PDF p. 4. -/
def pptRobustness {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (X : Matrix (I × J) (I × J) ℂ) : ℝ := baseNeg pptBase X

example {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] :
    negativity (0 : Matrix (I × J) (I × J) ℂ) = -(1/2) := by
  have h : partialTransposeFirst (0 : Matrix (I × J) (I × J) ℂ) = 0 := rfl
  rw [negativity,h]
  norm_num [traceNorm,cfc_zero]

example {I J K L : Type*} (X : Matrix (I × J) (I × J) ℂ)
    (Y : Matrix (K × L) (K × L) ℂ) (i i' : I) (j j' : J) (k k' : K) (l l' : L) :
    bipartiteTensor X Y ((i,k),(j,l)) ((i',k'),(j',l')) = X (i,j) (i',j')*Y (k,l) (k',l') := rfl

example {I : Type*} (S : Set (Matrix I I ℂ)) :
    BaseDecomposition S 0 0 0 (0 : Matrix I I ℂ) 0 ↔ (0 : Matrix I I ℂ) ∈ S := by
  simp [BaseDecomposition]







/-- A local CP instrument with arbitrary finite output dimension and Kraus multiplicity
(§II.B, PDF p. 3); rectangular Kraus operators include ancillas and discarding. -/
structure LocalInstrument (a c o : ℕ) where
  multiplicity : Fin o → ℕ
  kraus : (i : Fin o) → Fin (multiplicity i) → Matrix (Fin c) (Fin a) ℂ
  complete : ∑ i, ∑ j, (kraus i j)ᴴ*kraus i j = 1

/-- Finite adaptive LOCC tree (§II.B, PDF p. 3). Each continuation can depend on
all prior outcomes. The tree is fixed independently of the input density matrix. -/
inductive Protocol : ℕ → ℕ → ℕ → ℕ → Type where
  | finish (a b : ℕ) : Protocol a b a b
  | alice {a b c d : ℕ} (aNext o : ℕ) (positive : 0 < aNext)
      (M : LocalInstrument a aNext o) (next : Fin o → Protocol aNext b c d) : Protocol a b c d
  | bob {a b c d : ℕ} (bNext o : ℕ) (positive : 0 < bNext)
      (M : LocalInstrument b bNext o) (next : Fin o → Protocol a bNext c d) : Protocol a b c d

/-- Subnormalized states at full-transcript leaves (PDF pp. 3–4). -/
def protocolBranches {a b c d : ℕ} (P : Protocol a b c d)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    List (Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ) :=
  match P with
  | .finish _ _ => [rho]
  | .alice _ o _ M next => (List.finRange o).flatMap fun i =>
      protocolBranches (next i) (krausApply (fun j => Matrix.kronecker (M.kraus i j)
        (1 : Matrix (Fin b) (Fin b) ℂ)) rho)
  | .bob _ o _ M next => (List.finRange o).flatMap fun i =>
      protocolBranches (next i) (krausApply (fun j => Matrix.kronecker
        (1 : Matrix (Fin a) (Fin a) ℂ) (M.kraus i j)) rho)

/-- Deterministic output obtained by forgetting the transcript. -/
def protocolOutput {a b c d : ℕ} (P : Protocol a b c d)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) := (protocolBranches P rho).sum

/-- Selective average; no normalized state is required on a zero-probability branch. -/
def selectiveAverage {c d : ℕ} (E : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ → ℝ)
    (branches : List (Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ)) : ℝ :=
  (branches.map fun X => if 0 < X.trace.re then X.trace.re*E ((X.trace.re : ℂ)⁻¹ • X) else 0).sum

example {a b : ℕ} (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    protocolOutput (.finish a b) rho = rho := by simp [protocolOutput,protocolBranches]

example {c d : ℕ} (E : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ → ℝ) :
    selectiveAverage E [0] = 0 := by simp [selectiveAverage]

/-- Classical coarse-graining of full transcripts. Its choice is input-independent.
This includes retaining all outcomes or forgetting some or all outcomes. -/
def recordedBranches {I : Type*} [Fintype I]
    (branches : List (Matrix I I ℂ)) (o : ℕ) (record : ℕ → Fin o) : List (Matrix I I ℂ) :=
  List.ofFn fun i : Fin o => ∑ j : Fin branches.length,
    if record j.val = i then branches.get j else 0

example {I : Type*} [Fintype I] :
    recordedBranches ([] : List (Matrix I I ℂ)) 1 (fun _ => 0) = [0] := by
  simp [recordedBranches,List.ofFn_succ]



/-- Eq. (22), PDF p. 4. -/
def singlet (m : ℕ) (hm : 0 < m) : Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ :=
  letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  pureDensity (finiteMaxEntangled (Fin m))

/-- Eq. (23), PDF p. 5: unhalved trace distance over deterministic LOCC outputs. -/
def singletDistance {a b : ℕ} (m : ℕ) (hm : 0 < m)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : ℝ :=
  sInf {v | ∃ P : Protocol a b m m, v = traceNorm (singlet m hm-protocolOutput P rho)}

example : singlet 1 (by omega) = 1 := by
  ext i j
  have hi : i = (0,0) := Subsingleton.elim _ _
  have hj : j = (0,0) := Subsingleton.elim _ _
  subst i; subst j
  simp [singlet,finiteMaxEntangled,pureDensity]


/-- Schmidt expansion (§V.A, PDF p. 7). Nonnegative coefficients allow zero padding. -/
def schmidtState {I J : Type*} {r : ℕ} (c : Fin r → ℝ)
    (u : Fin r → EuclideanSpace ℂ I) (v : Fin r → EuclideanSpace ℂ J) :
    EuclideanSpace ℂ (I × J) := ∑ i, (c i : ℂ) • tensorVec (u i) (v i)

example {I J : Type*} (c : Fin 0 → ℝ) (u : Fin 0 → EuclideanSpace ℂ I)
    (v : Fin 0 → EuclideanSpace ℂ J) : schmidtState c u v = 0 := by simp [schmidtState]



/-- Eq. (51), PDF p. 8: explicit orthogonally invariant family. -/
def orthogonalFamily (d : ℕ) (hd : 0 < d) (a b c : ℝ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ((a*d : ℝ) : ℂ) • singlet d hd + (b : ℂ) • swapOp + (c : ℂ) • 1

/-- f = d Tr(rho Pplus), PDF p. 8. -/
def orthogonalF {d : ℕ} (hd : 0 < d) (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  d*(rho*singlet d hd).trace.re

/-- g = Tr(rho F), PDF p. 8. -/
def orthogonalG {d : ℕ} (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  (rho*swapOp).trace.re

example (d : ℕ) (hd : 0 < d) : orthogonalFamily d hd 0 0 1 = 1 := by
  simp [orthogonalFamily]



/-- Antisymmetric canonical form from Eq. (54), PDF pp. 8–9. The printed
standard block on p. 9 incorrectly has a plus sign at its lower-left entry. -/
def symplecticTwo : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks (!![0,1;-1,0]) 0 0 (!![0,1;-1,0])

/-- Reverse Alice's momentum only (§V.C, PDF p. 9). -/
def momentumReversal : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  Matrix.diagonal (Sum.elim (![1,-1]) (![1,1]))

example : symplecticTwo.transpose = -symplecticTwo := by
  ext i j
  rcases i with i|i <;> rcases j with j|j <;>
    fin_cases i <;> fin_cases j <;> norm_num [symplecticTwo,Matrix.fromBlocks]



/-- §III.B, PDF p. 5: the unknown input belongs to Alice together with her
share of the resource. The protocol is chosen before that unknown input. -/
def teleportationOutput {m : ℕ} (P : Protocol (m*m) m 1 m)
    (rho : Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ)
    (X : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  traceLeft (protocolOutput P ((Matrix.kronecker X rho).submatrix
    (fun z : Fin (m*m) × Fin m =>
      ((finProdFinEquiv.symm z.1).1,((finProdFinEquiv.symm z.1).2,z.2)))
    (fun z : Fin (m*m) × Fin m =>
      ((finProdFinEquiv.symm z.1).1,((finProdFinEquiv.symm z.1).2,z.2)))))

/-- Eqs. (31) and (37), PDF pp. 5–6: Haar-average unhalved distance, optimized
over arbitrary deterministic LOCC teleportation protocols, with no attainment hypothesis. -/
def teleportationDistance {m : ℕ} (hm : 0 < m)
    (rho : Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ) : ℝ :=
  sInf {v | ∃ P : Protocol (m*m) m 1 m, v =
    ∫ psi, traceNorm (pureDensity psi-teleportationOutput P rho (pureDensity psi))
      ∂QuditFidelity.haarPureStateLaw m hm}

example : teleportationOutput (m := 1) (.finish 1 1) 1 1 = 1 := by
  ext i j
  simp [teleportationOutput,protocolOutput,protocolBranches,traceLeft,
    Matrix.kronecker_apply,Matrix.one_apply,Subsingleton.elim]

/-- Copies of a bipartite matrix, with all Alice factors grouped first (§IV, PDF pp. 6–7). -/
def bipartiteCopies {a b : ℕ} (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (r : ℕ) : Matrix (Fin (a^r) × Fin (b^r)) (Fin (a^r) × Fin (b^r)) ℂ :=
  let ea : (Fin r → Fin a) ≃ Fin (a^r) := finFunctionFinEquiv
  let eb : (Fin r → Fin b) ≃ Fin (b^r) := finFunctionFinEquiv
  Matrix.of fun x y => ∏ i, rho (ea.symm x.1 i,eb.symm x.2 i) (ea.symm y.1 i,eb.symm y.2 i)

/-- Eqs. (41)–(43), PDF pp. 6–7, resolving the input/output-letter interchange
using Eq. (43) and the proof: m input copies, n output Bell pairs. -/
def distillationError {a b : ℕ} (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (m n : ℕ) : ℝ :=
  singletDistance (2^n) (Nat.two_pow_pos n) (bipartiteCopies rho m)

/-- The printed universal sequence definition, using extended limsups to avoid
real limsup defaults for unbounded ratios. Both copy-count sequences diverge. -/
def AchievableRate {a b : ℕ} (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (eps : ℝ) (rate : ℝ≥0) : Prop :=
  ∀ m n : ℕ → ℕ, Filter.Tendsto m Filter.atTop Filter.atTop →
    Filter.Tendsto n Filter.atTop Filter.atTop →
    Filter.limsup (fun j => (n j : ℝ≥0∞)/(m j : ℝ≥0∞)) Filter.atTop ≤ (rate : ℝ≥0∞) →
    Filter.limsup (fun j => ENNReal.ofReal (distillationError rho (m j) (n j))) Filter.atTop ≤
      ENNReal.ofReal eps

/-- Extended nonnegative supremum of achievable rates, §IV, PDF pp. 6–7. -/
def distillableEntanglement {a b : ℕ}
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (eps : ℝ) : ℝ≥0∞ :=
  ⨆ r : {r : ℝ≥0 // AchievableRate rho eps r}, (r.val : ℝ≥0∞)

example {a b : ℕ} (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (i j : Fin (a^0) × Fin (b^0)) : bipartiteCopies rho 0 i j = 1 := by
  simp [bipartiteCopies,Matrix.of_apply]
  rfl

/-- Finite, adaptive, separated-party LOCC on three registers (§VI.A, PDF pp. 10–11). -/
inductive ThreePartyProtocol : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Type where
  | finish (a b c : ℕ) : ThreePartyProtocol a b c a b c
  | alice {a b c x y z : ℕ} (aNext o : ℕ) (positive : 0 < aNext)
      (M : LocalInstrument a aNext o)
      (next : Fin o → ThreePartyProtocol aNext b c x y z) : ThreePartyProtocol a b c x y z
  | bob {a b c x y z : ℕ} (bNext o : ℕ) (positive : 0 < bNext)
      (M : LocalInstrument b bNext o)
      (next : Fin o → ThreePartyProtocol a bNext c x y z) : ThreePartyProtocol a b c x y z
  | charlie {a b c x y z : ℕ} (cNext o : ℕ) (positive : 0 < cNext)
      (M : LocalInstrument c cNext o)
      (next : Fin o → ThreePartyProtocol a b cNext x y z) : ThreePartyProtocol a b c x y z

/-- Subnormalized triple-register leaf operators, computed from local Kraus maps. -/
def threePartyBranches {a b c x y z : ℕ} (P : ThreePartyProtocol a b c x y z)
    (rho : Matrix (Fin a × (Fin b × Fin c)) (Fin a × (Fin b × Fin c)) ℂ) :
    List (Matrix (Fin x × (Fin y × Fin z)) (Fin x × (Fin y × Fin z)) ℂ) :=
  match P with
  | .finish _ _ _ => [rho]
  | .alice _ o _ M next => (List.finRange o).flatMap fun i =>
      threePartyBranches (next i) (krausApply (fun j => Matrix.kronecker (M.kraus i j)
        (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ)) rho)
  | .bob _ o _ M next => (List.finRange o).flatMap fun i =>
      threePartyBranches (next i) (krausApply (fun j => Matrix.kronecker
        (1 : Matrix (Fin a) (Fin a) ℂ) (Matrix.kronecker (M.kraus i j)
          (1 : Matrix (Fin c) (Fin c) ℂ))) rho)
  | .charlie _ o _ M next => (List.finRange o).flatMap fun i =>
      threePartyBranches (next i) (krausApply (fun j => Matrix.kronecker
        (1 : Matrix (Fin a) (Fin a) ℂ) (Matrix.kronecker
          (1 : Matrix (Fin b) (Fin b) ℂ) (M.kraus i j))) rho)

/-- All six negativities of §VI.A, PDF p. 10, ordered AB|C, AC|B, BC|A,
A|B after discarding C, A|C after discarding B, and B|C after discarding A. -/
def threePartyMeasures {a b c : ℕ}
    (rho : Matrix (Fin a × (Fin b × Fin c)) (Fin a × (Fin b × Fin c)) ℂ) : Fin 6 → ℝ :=
  let abC := rho.submatrix (fun t : (Fin a × Fin b) × Fin c => (t.1.1,(t.1.2,t.2)))
    (fun t : (Fin a × Fin b) × Fin c => (t.1.1,(t.1.2,t.2)))
  let acB := rho.submatrix (fun t : (Fin a × Fin c) × Fin b => (t.1.1,(t.2,t.1.2)))
    (fun t : (Fin a × Fin c) × Fin b => (t.1.1,(t.2,t.1.2)))
  let bcA := rho.submatrix (fun t : (Fin b × Fin c) × Fin a => (t.2,t.1))
    (fun t : (Fin b × Fin c) × Fin a => (t.2,t.1))
  ![negativity abC,negativity acB,negativity bcA,
    negativity (traceRight abC),negativity (traceRight acB),negativity (traceLeft rho)]

example {a b c : ℕ}
    (rho : Matrix (Fin a × (Fin b × Fin c)) (Fin a × (Fin b × Fin c)) ℂ) :
    threePartyBranches (.finish a b c) rho = [rho] := rfl

end QAlgorithms.Papers.Independent.Independent1.P07


