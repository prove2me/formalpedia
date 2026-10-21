-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43
-- name    : QAlgorithms_Papers_Independent_Claimed50_P43
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T13:16:49.399308+00:00
-- url     : https://prove2.me/theorems/63324fb7-2124-496e-b920-008b26079d77
-- title:
--   Definitions for On entanglement-assisted classical capacity
-- statement:
--   The objects the formalized statements of *On entanglement-assisted classical capacity* (arXiv:quant-ph/0106075) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `AssistedEnsemble`: PDF p.2, (1): one finite distribution, one normalized message-independent resource, and a local CPTP encoder for each message. Bob's register is the first factor.
--   - `encodedAssistedState`: PDF p.5, (16): actual encoded state, with the unchanged reference first.
--   - `assistedScore`: PDF pp.2,5, (1),(17): the output Holevo quantity of this entire ensemble.
--   - `assistedValues`: PDF p.2, (1): all feasible finite-ensemble Holevo scores.
--   - `assistedOneShot`: PDF p.2, (1): supremum representing the one-shot maximum; attainment is a theorem. On nonzero finite CPTP channels this set is nonempty and bounded.
--   - `assistedRate`: PDF p.2, (2),(3): the normalized n-use Holevo value. The n=0 total extension is 0.
--   - `ordinaryLimit`: PDF pp.2,7: ordinary limit, with zero only as the nonconvergent total extension. Every capacity result below asserts convergence; no limsup or diagonal convention is used.
--   - `regularizedAssistedHolevo`: PDF p.2, (3): full assisted capacity is the ordinary normalized block limit.
--   - `classicalRate`: PDF p.7: regularized unassisted Holevo capacity, with ordinary-limit convention.
--   - `regularizedClassicalHolevo`: PDF p.7: C, as distinct from the single-use Holevo value C^(1).
--   - `CommonBob`: PDF p.6, (20): every component has the same Bob marginal; this marginal can vary between candidate ensembles. The first tensor factor is Bob.
--   - `commonBobValues`: PDF p.6, (20): feasible Holevo scores of all internally common-marginal ensembles.
--   - `frameProjector`: PDF p.3: orthogonal projector onto the columns of a frame J.
--   - `frameResource`: PDF p.3: copied-frame entangled vector. No conjugation on the copied frame; this is the sum of e_k tensor e_k, in Bob-first order. Used only for m>0.
--   - `frameWeyl`: PDF p.3: W is shift^alpha clock^beta on the frame and identity off it. Residue indices replace 1,...,m; the source's initial clock labels change only scalar phases.
--   - `frameBell`: PDF p.3: the m^2 encoded vectors, with the Weyl operation on Alice.
--   - `chaotic`: PDF pp.7--8: the chaotic input I/d. Used only when d>0.
--   - `finiteWeyl`: PDF p.7: full-space Weyl system, reindexed from residues to Fin d. The pair (0,0) is the identity label.
--   - `weylDepolarizingKraus`: PDF p.7, (24): genuine d^2 Kraus operators, with exactly d^2-1 nonidentity terms.
--   - `basisHolevo`: PDF p.8: d equiprobable basis states, for any chosen orthonormal basis U.
--   - `extremeEnhancement`: PDF p.8: actual-capacity enhancement at the maximal allowed parameter. The dimension offset restricts this sequence to d>=2. Denominator positivity is a theorem.
-- source:
--   On entanglement-assisted classical capacity, arXiv:quant-ph/0106075v2, https://arxiv.org/abs/quant-ph/0106075v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34

/-!
Holevo, arXiv:quant-ph/0106075v2. All page references are PDF pages.
Reference B is first in products, Alice is second; B is a copied input space.
Capacities are the paper's Holevo maxima and ordinary block limits, not operational
integer-message capacities. Theorems include convergence and attainment explicitly.
Equations (10), (11), and the literal claimed linear asymptote are deferred.
-/

noncomputable section

open scoped Matrix ComplexConjugate
open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

/-- PDF p.2, (1): one finite distribution, one normalized message-independent resource,
and a local CPTP encoder for each message. Bob's register is the first factor. -/
structure AssistedEnsemble (A : Type) [Fintype A] [DecidableEq A] (m : ℕ) where
  prob : Fin m → ℝ
  nonneg : ∀ i, 0 ≤ prob i
  total : ∑ i, prob i = 1
  resource : EuclideanSpace ℂ (A × A)
  normalized : ‖resource‖ = 1
  encode : Fin m → Superop A A
  channel : ∀ i, IsChannel (encode i)

/-- PDF p.5, (16): actual encoded state, with the unchanged reference first. -/
def encodedAssistedState {A : Type} [Fintype A] [DecidableEq A] {m : ℕ}
    (e : AssistedEnsemble A m) (i : Fin m) : Matrix (A × A) (A × A) ℂ :=
  idTensorSuperop (e.encode i) (pureDensity e.resource)

/-- PDF pp.2,5, (1),(17): the output Holevo quantity of this entire ensemble. -/
def assistedScore {A C : Type} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] (N : Superop A C) {m : ℕ}
    (e : AssistedEnsemble A m) : ℝ :=
  vnEntropy (∑ i, (e.prob i : ℂ) • idTensorSuperop N (encodedAssistedState e i)) -
    ∑ i, e.prob i * vnEntropy (idTensorSuperop N (encodedAssistedState e i))

/-- PDF p.2, (1): all feasible finite-ensemble Holevo scores. -/
def assistedValues {A C : Type} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] (N : Superop A C) : Set ℝ :=
  {v | ∃ (m : ℕ) (e : AssistedEnsemble A m), v = assistedScore N e}

/-- PDF p.2, (1): supremum representing the one-shot maximum; attainment is a theorem.
On nonzero finite CPTP channels this set is nonempty and bounded. -/
def assistedOneShot {A C : Type} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] (N : Superop A C) : ℝ :=
  sSup (assistedValues N)

/-- PDF p.2, (2),(3): the normalized n-use Holevo value. The n=0 total extension is 0. -/
def assistedRate {A C : Type} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] (N : Superop A C) (n : ℕ) : ℝ :=
  assistedOneShot (piSuperop (fun _ : Fin n => N)) / n

/-- PDF pp.2,7: ordinary limit, with zero only as the nonconvergent total extension.
Every capacity result below asserts convergence; no limsup or diagonal convention is used. -/
def ordinaryLimit (f : ℕ → ℝ) : ℝ :=
  if h : ∃ r, Tendsto f atTop (nhds r) then h.choose else 0

/-- PDF p.2, (3): full assisted capacity is the ordinary normalized block limit. -/
def regularizedAssistedHolevo {A C : Type} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] (N : Superop A C) : ℝ :=
  ordinaryLimit (assistedRate N)

/-- PDF p.7: regularized unassisted Holevo capacity, with ordinary-limit convention. -/
def classicalRate {A C : Type} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] (N : Superop A C) (n : ℕ) : ℝ :=
  holevoCapacity (piSuperop (fun _ : Fin n => N)) / n

/-- PDF p.7: C, as distinct from the single-use Holevo value C^(1). -/
def regularizedClassicalHolevo {A C : Type} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] (N : Superop A C) : ℝ :=
  ordinaryLimit (classicalRate N)

/-- PDF p.6, (20): every component has the same Bob marginal; this marginal can
vary between candidate ensembles. The first tensor factor is Bob. -/
def CommonBob {A : Type} [Fintype A]
    (e : QAlgorithms.Papers.Independent.Information100.P08.Ensemble (A × A)) : Prop :=
  ∃ s : Matrix A A ℂ, IsDensityMatrix s ∧ ∀ i, traceRight (e.state i) = s

/-- PDF p.6, (20): feasible Holevo scores of all internally common-marginal ensembles. -/
def commonBobValues {A C : Type} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] (N : Superop A C) : Set ℝ :=
  {v | ∃ e : QAlgorithms.Papers.Independent.Information100.P08.Ensemble (A × A),
    CommonBob e ∧ v = QAlgorithms.Papers.Independent.Information100.P08.outputHolevo
      (idTensorSuperop (R := A) N) e}

/-- PDF p.3: orthogonal projector onto the columns of a frame J. -/
def frameProjector {A K : Type} [Fintype K] (J : Matrix A K ℂ) : Matrix A A ℂ :=
  J * Jᴴ

/-- PDF p.3: copied-frame entangled vector. No conjugation on the copied frame;
this is the sum of e_k tensor e_k, in Bob-first order. Used only for m>0. -/
def frameResource {A : Type} {m : ℕ} (J : Matrix A (ZMod m) ℂ)
    [Fintype (ZMod m)] : EuclideanSpace ℂ (A × A) :=
  WithLp.toLp 2 fun x => ((Real.sqrt m)⁻¹ : ℂ) * ∑ k, J x.1 k * J x.2 k

/-- PDF p.3: W is shift^alpha clock^beta on the frame and identity off it.
Residue indices replace 1,...,m; the source's initial clock labels change only scalar phases. -/
def frameWeyl {A : Type} [Fintype A] [DecidableEq A] {m : ℕ} [NeZero m]
    (J : Matrix A (ZMod m) ℂ) (a b : ZMod m) : Matrix A A ℂ :=
  extendEncodedUnitary J (QAlgorithms.Papers.Independent.Information100.P34.weyl a b)

/-- PDF p.3: the m^2 encoded vectors, with the Weyl operation on Alice. -/
def frameBell {A : Type} [Fintype A] [DecidableEq A] {m : ℕ} [NeZero m]
    (J : Matrix A (ZMod m) ℂ) (x : ZMod m × ZMod m) : EuclideanSpace ℂ (A × A) :=
  act (Matrix.kronecker (1 : Matrix A A ℂ) (frameWeyl J x.1 x.2)) (frameResource J)

/-- PDF pp.7--8: the chaotic input I/d. Used only when d>0. -/
def chaotic (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := (d : ℂ)⁻¹ • 1

/-- PDF p.7: full-space Weyl system, reindexed from residues to Fin d.
The pair (0,0) is the identity label. -/
def finiteWeyl (d : ℕ) (hd : 0 < d) (a b : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let e := ZMod.finEquiv d
  (QAlgorithms.Papers.Independent.Information100.P34.weyl
    (e a) (e b)).submatrix e e

/-- PDF p.7, (24): genuine d^2 Kraus operators, with exactly d^2-1 nonidentity terms. -/
def weylDepolarizingKraus (d : ℕ) (hd : 0 < d) (p : ℝ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (x : Fin d × Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  if x.1.val = 0 ∧ x.2.val = 0 then
    (Real.sqrt (1 - p * ((d : ℝ)^2 - 1) / (d : ℝ)^2) : ℂ) • 1
  else (Real.sqrt (p / (d : ℝ)^2) : ℂ) •
    ((U : Matrix (Fin d) (Fin d) ℂ) * finiteWeyl d hd x.1 x.2 *
      (U : Matrix (Fin d) (Fin d) ℂ)ᴴ)

/-- PDF p.8: d equiprobable basis states, for any chosen orthonormal basis U. -/
def basisHolevo {d : ℕ} (hd : 0 < d) (p : ℝ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : ℝ :=
  vnEntropy (QAlgorithms.QuditFidelity.depolarizingMap d hd p
    ((d : ℂ)⁻¹ • ∑ j, pureDensity (act (U : Matrix (Fin d) (Fin d) ℂ) (ket j)))) -
    (d : ℝ)⁻¹ * ∑ j, vnEntropy (QAlgorithms.QuditFidelity.depolarizingMap d hd p
      (pureDensity (act (U : Matrix (Fin d) (Fin d) ℂ) (ket j))))

/-- PDF p.8: actual-capacity enhancement at the maximal allowed parameter.
The dimension offset restricts this sequence to d>=2. Denominator positivity is a theorem. -/
def extremeEnhancement (k : ℕ) : ℝ :=
  let d := k + 2
  let N := QAlgorithms.QuditFidelity.depolarizingMap d (by omega)
    ((d : ℝ)^2 / ((d : ℝ)^2 - 1))
  regularizedAssistedHolevo N / holevoCapacity N

/-! Sanity examples check the new definitions, not the source theorems. -/

example {A : Type} [Fintype A] [DecidableEq A] {m : ℕ}
    (e : AssistedEnsemble A m) (i : Fin m) :
    encodedAssistedState e i = idTensorSuperop (e.encode i) (pureDensity e.resource) := rfl

example {A C : Type} [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq C]
    (N : Superop A C) : assistedRate N 0 = 0 ∧ classicalRate N 0 = 0 := by
  simp [assistedRate, classicalRate]

example : ordinaryLimit (fun _ => (0 : ℝ)) = 0 := by
  have h : ∃ r : ℝ, Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds r) :=
    ⟨0, tendsto_const_nhds⟩
  rw [ordinaryLimit, dif_pos h]
  exact tendsto_nhds_unique h.choose_spec tendsto_const_nhds

example : chaotic 1 = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  simp [chaotic]

example {A : Type} [Fintype A] [DecidableEq A] (J : Matrix A (ZMod 1) ℂ) :
    frameWeyl J 0 0 = 1 := by
  simp [frameWeyl, QAlgorithms.Papers.Independent.Information100.P34.weyl,
    extendEncodedUnitary]

example {A K : Type} [Fintype K] (J : Matrix A K ℂ) :
    frameProjector J = J * Jᴴ := rfl

example (J : Matrix Unit (ZMod 1) ℂ) :
    frameResource J ((), ()) = J () 0 * J () 0 := by
  simp [frameResource]
  have hzero : (default : ZMod 1) = 0 := Subsingleton.elim _ _
  exact congrArg (fun k : ZMod 1 => J () k * J () k) hzero

example (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    weylDepolarizingKraus 2 (by decide) 0 U (0, 0) =
    (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [weylDepolarizingKraus]

example {A C : Type} [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq C]
    (N : Superop A C) : regularizedAssistedHolevo N = ordinaryLimit (assistedRate N) ∧
      regularizedClassicalHolevo N = ordinaryLimit (classicalRate N) := ⟨rfl, rfl⟩

example {A : Type} [Fintype A] [DecidableEq A]
    (psi : EuclideanSpace ℂ (A × A)) (hpsi : ‖psi‖ = 1) :
    ∃ e : AssistedEnsemble A 1, e.prob 0 = 1 ∧ e.resource = psi := by
  let e : AssistedEnsemble A 1 :=
    { prob := fun _ => 1
      nonneg := fun _ => by norm_num
      total := by simp
      resource := psi
      normalized := hpsi
      encode := fun _ rho => rho
      channel := fun _ => by
        refine ⟨1, fun _ => 1, ?_, ?_⟩
        · simp [IsKrausFamily]
        · intro rho
          simp [krausApply] }
  exact ⟨e, rfl, rfl⟩

example : extremeEnhancement 0 =
    regularizedAssistedHolevo (QAlgorithms.QuditFidelity.depolarizingMap 2 (by decide) (4 / 3)) /
      holevoCapacity (QAlgorithms.QuditFidelity.depolarizingMap 2 (by decide) (4 / 3)) := by
  norm_num [extremeEnhancement]

end QAlgorithms.Papers.Independent.Claimed50.P43


