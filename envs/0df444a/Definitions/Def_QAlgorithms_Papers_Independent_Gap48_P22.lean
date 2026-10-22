-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P22
-- name    : QAlgorithms_Papers_Independent_Gap48_P22
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T22:12:40.7711+00:00
-- url     : https://prove2.me/theorems/b9fe8980-95fa-4b6e-b985-07a366113fa6
-- title:
--   Definitions for Squashed entanglement, k-extendibility, quantum Markov chains, and recovery maps
-- statement:
--   The objects the formalized statements of *Squashed entanglement, k-extendibility, quantum Markov chains, and recovery maps* (arXiv:1410.4184) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `FinitePureEnsemble`: Eq.(2), PDF p.2: a finite pure-state decomposition, with unit vectors, probability weights and the exact prescribed barycenter.
--   - `formationEntanglement`: Eq.(2), PDF p.2: finite pure-ensemble convex roof. The infimum equals the printed minimum in finite dimensions; no optimizing decomposition is a premise. For normalized inputs the value set is nonempty and bounded below by zero.
--   - `conditionalLaw`: Classical conditional law, PDF pp.8–9. Filter on f=y, then push forward by g. If the event has zero mass, use the unconditional g-marginal as completion.
--   - `discreteKL`: Relative entropy in bits, PDF pp.8–9. All subsets are measurable; Mathlib KL retains infinity for failure of absolute continuity.
--   - `discreteL1`: Full l1 distance of discrete laws, p.8 (no factor 1/2). PMF mass differences are absolutely summable even on arbitrary alphabets.
--   - `markovApproximation`: P(XY)P(Z|Y), PDF p.8. Its null-Y conditional is P_Z.
--   - `channelJoint`: Q(x)T(u|x), the joint law used by Bayes recovery, pp.8–9.
--   - `transposeChannel`: Classical transpose recovery, pp.8–9. It is constructed from Q,T alone. On a zero TQ event the conditional completion is Q itself.
--   - `groupedCMI`: Two grouped parties of the SAME extension, Appendix p.11; external E retained.
--   - `partyCopyMultiplicity`: Appendix p.12: A_1 is retained once, every other A_i has k copies.
--   - `ReplicaBasis`: Computational basis of the actual replicated tensor product, Appendix p.12.
--   - `selectedReplicaMarginal`: Trace out every unselected copy, retaining the original party order, p.12. The selected entries are fixed before summation, so each discarded string is counted once.
-- source:
--   Squashed entanglement, k-extendibility, quantum Markov chains, and recovery maps, arXiv:1410.4184v4, https://arxiv.org/abs/1410.4184v4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P35

/-! Li and Winter, arXiv:1410.4184v4. Finite quantum systems; discrete
classical alphabets may be infinite. Entropies are in bits. Compilation pending. -/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Gap48.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P12 (squashedEntanglement KExtendible)
open QAlgorithms.Papers.Independent.Claimed50.P33
  (RegisterBasis registerMarginal entropyAt conditionalMultipartiteInformation singleParties
   forgetEnvironment)
open QAlgorithms.Papers.Independent.Renew46.P35 (classicalCMI)
open QAlgorithms.Entanglement (IsSeparableDensity)

/-- Eq.(2), PDF p.2: a finite pure-state decomposition, with unit vectors,
probability weights and the exact prescribed barycenter. -/
structure FinitePureEnsemble {A B : Type*} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) where
  count : ℕ
  weight : Fin count → ℝ
  vector : Fin count → EuclideanSpace ℂ (A × B)
  nonnegative : ∀ j, 0 ≤ weight j
  total : ∑ j, weight j = 1
  unit : ∀ j, ‖vector j‖ = 1
  barycenter : rho = ∑ j, (weight j : ℂ) • pureDensity (vector j)

/-- Eq.(2), PDF p.2: finite pure-ensemble convex roof. The infimum equals the
printed minimum in finite dimensions; no optimizing decomposition is a premise.
For normalized inputs the value set is nonempty and bounded below by zero. -/
def formationEntanglement {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sInf {v : ℝ | ∃ d : FinitePureEnsemble rho,
    v = ∑ j, d.weight j * vnEntropy (traceRight (pureDensity (d.vector j)))}

/-- A normalized pure state has its one-term decomposition (Eq.(2), p.2). -/
example {A B : Type*} [Fintype A] [Fintype B]
    (psi : EuclideanSpace ℂ (A × B)) (hpsi : ‖psi‖ = 1) :
    Nonempty (FinitePureEnsemble (pureDensity psi)) := by
  refine ⟨⟨1, (fun _ => 1), (fun _ => psi), (fun _ => by norm_num), ?_,
    (fun _ => hpsi), ?_⟩⟩
  · simp
  · simp

/-- Classical conditional law, PDF pp.8–9. Filter on f=y, then push forward by g.
If the event has zero mass, use the unconditional g-marginal as completion. -/
def conditionalLaw {X Y Z : Type*} (p : PMF X) (f : X → Y) (g : X → Z) (y : Y) : PMF Z :=
  if h : ∃ x ∈ {x | f x = y}, x ∈ p.support then
    (p.filter {x | f x = y} h).map g
  else p.map g

/-- Null-event completion is a normalized marginal, rather than a zero law. -/
example {X Y Z : Type*} (p : PMF X) (f : X → Y) (g : X → Z) (y : Y)
    (h : ¬ ∃ x ∈ {x | f x = y}, x ∈ p.support) :
    conditionalLaw p f g y = p.map g := by
  unfold conditionalLaw
  exact dif_neg h

/-- Relative entropy in bits, PDF pp.8–9. All subsets are measurable;
Mathlib KL retains infinity for failure of absolute continuity. -/
def discreteKL {X : Type*} (p q : PMF X) : ℝ≥0∞ :=
  letI : MeasurableSpace X := ⊤
  InformationTheory.klDiv p.toMeasure q.toMeasure / ENNReal.ofReal (Real.log 2)

/-- Full l1 distance of discrete laws, p.8 (no factor 1/2).
PMF mass differences are absolutely summable even on arbitrary alphabets. -/
def discreteL1 {X : Type*} (p q : PMF X) : ℝ :=
  ∑' x, |(p x).toReal - (q x).toReal|

/-- P(XY)P(Z|Y), PDF p.8. Its null-Y conditional is P_Z. -/
def markovApproximation {X Y Z : Type*} (p : PMF (X × (Y × Z))) : PMF (X × (Y × Z)) :=
  (p.map fun x => (x.1,x.2.1)).bind fun xy =>
    (conditionalLaw p (fun x => x.2.1) (fun x => x.2.2) xy.2).map
      fun z => (xy.1,(xy.2,z))

/-- Q(x)T(u|x), the joint law used by Bayes recovery, pp.8–9. -/
def channelJoint {X U : Type*} (q : PMF X) (t : X → PMF U) : PMF (X × U) :=
  q.bind fun x => (t x).map fun u => (x,u)

/-- Classical transpose recovery, pp.8–9. It is constructed from Q,T alone.
On a zero TQ event the conditional completion is Q itself. -/
def transposeChannel {X U : Type*} (q : PMF X) (t : X → PMF U) (u : U) : PMF X :=
  if h : ∃ xu ∈ {xu : X × U | xu.2 = u}, xu ∈ (channelJoint q t).support then
    ((channelJoint q t).filter {xu | xu.2 = u} h).map Prod.fst
  else q

/-- The transpose's null-output completion is independent of P, pp.8–9. -/
example {X U : Type*} (q : PMF X) (t : X → PMF U) (u : U)
    (h : ¬ ∃ xu ∈ {xu : X × U | xu.2 = u}, xu ∈ (channelJoint q t).support) :
    transposeChannel q t u = q := by
  unfold transposeChannel
  exact dif_neg h

/-- Distance vanishes on identical laws, including infinite support, p.8. -/
example {X : Type*} (p : PMF X) : discreteL1 p p = 0 := by
  simp [discreteL1]

/-- Two grouped parties of the SAME extension, Appendix p.11; external E retained. -/
def groupedCMI {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    {E : Type} [Fintype E]
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (s t : Finset (Fin n)) : ℝ :=
  conditionalMultipartiteInformation .total rho
    (fun j : Fin 2 => if j = 0 then s else t) ∅

/-- Appendix p.12: A_1 is retained once, every other A_i has k copies. -/
def partyCopyMultiplicity {n : ℕ} (i : Fin n) (k : ℕ) : ℕ := if i.val = 0 then 1 else k

/-- Computational basis of the actual replicated tensor product, Appendix p.12. -/
abbrev ReplicaBasis {n : ℕ} (D : Fin n → Type) (k : ℕ) :=
  (i : Fin n) → Fin (partyCopyMultiplicity i k) → D i

/-- Trace out every unselected copy, retaining the original party order, p.12.
The selected entries are fixed before summation, so each discarded string is counted once. -/
def selectedReplicaMarginal {n k : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (omega : Matrix (ReplicaBasis D k) (ReplicaBasis D k) ℂ)
    (j : (i : Fin n) → Fin (partyCopyMultiplicity i k)) :
    Matrix (RegisterBasis D) (RegisterBasis D) ℂ :=
  fun a b => ∑ z : ReplicaBasis D k,
    if (∀ i, z i (j i) = a i) then
      omega z (fun i => Function.update (z i) (j i) (b i)) else 0

/-- The source's first system is never copied, including k=0 at the definition level. -/
example {n : ℕ} (k : ℕ) : partyCopyMultiplicity (0 : Fin (n+1)) k = 1 := by
  simp [partyCopyMultiplicity]

/-- At k=1 every party appears exactly once, Appendix p.12. -/
example {n : ℕ} (i : Fin n) : partyCopyMultiplicity i 1 = 1 := by
  simp [partyCopyMultiplicity]

/-- Partial trace sends the zero operator to zero, p.12. -/
example {n k : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (j : (i : Fin n) → Fin (partyCopyMultiplicity i k)) :
    selectedReplicaMarginal (0 : Matrix (ReplicaBasis D k) (ReplicaBasis D k) ℂ) j = 0 := by
  ext a b
  simp [selectedReplicaMarginal]

/-- Identical normalized laws have zero KL, including infinite alphabets, p.8. -/
example {X : Type*} (p : PMF X) : discreteKL p p = 0 := by
  simp [discreteKL, InformationTheory.klDiv_self]

/-- A deterministic one-point input gives its actual input/output pair, pp.8–9. -/
example {X U : Type*} (x : X) (u : U) :
    channelJoint (PMF.pure x) (fun _ => PMF.pure u) = PMF.pure (x,u) := by
  simp only [channelJoint, PMF.pure_bind, PMF.pure_map]

/-- Grouping does not create entropy from the zero operator, Appendix p.11.
The theorem domain excludes this unnormalized input. -/
example {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    {E : Type} [Fintype E] (s t : Finset (Fin n)) :
    groupedCMI (0 : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ) s t = 0 := by
  have hm (u : Finset (Fin n)) :
      registerMarginal (0 : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ) u = 0 := by
    ext a b
    simp [registerMarginal]
  have he (u : Finset (Fin n)) :
      entropyAt (0 : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ) u = 0 := by
    unfold entropyAt
    rw [hm]
    simp [vnEntropy]
  simp [groupedCMI, conditionalMultipartiteInformation, he]

end QAlgorithms.Papers.Independent.Gap48.P22


