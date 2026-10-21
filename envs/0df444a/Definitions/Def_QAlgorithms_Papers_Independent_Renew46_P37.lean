-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P37
-- name    : QAlgorithms_Papers_Independent_Renew46_P37
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T22:09:47.546862+00:00
-- url     : https://prove2.me/theorems/a569bbf3-7bc7-4bae-938b-3684cb4b8959
-- title:
--   Definitions for Multipartite Classical and Quantum Secrecy Monotones
-- statement:
--   The objects the formalized statements of *Multipartite Classical and Quantum Secrecy Monotones* (arXiv:quant-ph/0202103) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ClassicalBasis`: PDF pp.3--4: specialize the accepted RegisterBasis to finite local alphabets.
--   - `CData`: PDF pp.3--4: finite classical data. Normalization and positive dimensions are imposed by IsValidClassicalData; keeping these unbundled permits explicit laws.
--   - `IsValidClassicalData`: PDF pp.3--4: normalized finite laws on nonempty local alphabets.
--   - `lawMarginal`: PDF p.4: a lawMarginal, including the one-point empty lawMarginal.
--   - `cH`: PDF p.4: Shannon entropy of the selected party registers, in bits.
--   - `lawCMI`: PDF p.5: conditional mutual information I(A:B|E).
--   - `cInfo`: PDF pp.4--5, (13),(17): information for disjoint groups. The coefficient is the number of groups minus one, with no normalization divisor.
--   - `cValue`: PDF pp.4--5: S_n is dual information and T_n is total information.
--   - `cProduct`: PDF p.3, (5): partywise independent product with explicit paired coding.
--   - `cCopies`: PDF p.3, (8): exact independent copies, regrouped by honest party. The finite equivalence only codes words; it introduces no correlations.
--   - `IsIndependentLaw`: PDF p.5: independent local distributions, not a mixture of products.
--   - `CInstrument`: PDF pp.3,6--7: a stochastic local operation with a public outcome j. Only the acting party changes its register. The row sums include both the public outcome and retained local data. At zero weight the equation is subnormalized, so no conditional law is selected by division.
--   - `CLOPC`: PDF p.3: finite adaptive local stochastic/public-communication tree. Each leaf index records the full public transcript known to Eve. A one-outcome step is a private stochastic channel. There is no transcript-forgetting rule.
--   - `ExactSecretConversion`: PDF pp.3,7--8: exact secret conversion; on every positive-probability transcript the honest law is the SAME target law. Thus the target is independent of Eve's entire transcript. Alphabet codings are required to agree.
--   - `IsCMonotone`: PDF p.3, properties 1--6, in their finite-alphabet scope. Local/public monotonicity is averaged over the public outcome.
--   - `permuteData`: PDF p.5: permutation symmetry is independent of alphabet cardinalities.
--   - `EData`: PDF p.4: a classical law including Eve's finite variable.
--   - `EValid`: PDF pp.3--4: normalized joint law and nonempty honest/Eve alphabets.
--   - `eveLetterProbability`: PDF p.4: probability of an Eve letter.
--   - `givenE`: PDF p.4: honest conditional data; only positive-weight uses are physical.
--   - `conditionalAverage`: PDF p.4: M_1, explicitly zero on zero-weight Eve letters.
--   - `processE`: PDF p.4: push the joint law through the stochastic channel on Eve alone.
--   - `intrinsicExtensionScores`: PDF p.4: admissible values, with NO fixed output alphabet or deterministic channel restriction. On valid p and nonnegative M the set is nonempty and bounded below by zero (the one-output channel is feasible).
--   - `intrinsicExtensionValue`: PDF p.4: define the intrinsic extension by the infimum; attainment is a conclusion of the extension theorem, never built into this definition.
--   - `EInstrument`: PDF pp.3--4: local honest instruments preserving Eve's original variable. The public outcome is retained separately from that original variable.
--   - `evePublicBranch`: PDF p.3, property 8: Eve publicly announces a stochastic function of E, retaining E. Zero-probability branches use the total-function value zero.
--   - `evePublicWeight`: PDF p.3, property 8: the public probability, summing honest data and Eve.
--   - `ExtensionMonotonicity`: PDF pp.3--4: honest local/public and Eve-public inequalities. The latter is an increase. No Eve-local inequality is hidden in this predicate.
--   - `groupData`: PDF p.4: grouping by a surjection, hence disjoint nonempty blocks.
--   - `earlier`: Earlier parties in the fixed source order.
--   - `later`: Later parties in the fixed source order.
--   - `mergeLast`: PDF p.5, (15): merge the final two parties; used only for n≥3.
--   - `firstParties`: PDF p.5, (19): retain the first n-1 parties.
--   - `classicalKL`: PDF p.5, (18): support-aware relative entropy IN BITS. The printed ln is corrected to log_2 to match (17) and the one-bit examples on p.7.
--   - `productLaw`: PDF p.5: the product of arbitrary local laws.
--   - `localLaw`: PDF p.5, (18): local marginals in their original alphabets.
--   - `exampleLaw`: PDF p.7, (41)--(45): source law order AB, AC, BC, common, xor; the uncorrelated spectator for each pair is chosen constant.
--   - `fiveValues`: PDF p.7: order I(A:BC), I(B:AC), I(C:AB), S_3, T_3.
--   - `fiveTable`: PDF p.7: all 25 entries, with pair-law order AB, AC, BC.
--   - `secrecyCoordinates`: PDF p.8, (47): r,s,t,u use pair order AB, BC, AC.
--   - `formalYields`: PDF pp.8--9: nonnegative formal yields, in order AB, BC, AC, xor, common. These are real coefficients of monotone vectors, NOT tensor exponents.
--   - `combination`: PDF pp.5--6, (23): the linear combination with both endpoints included.
--   - `qH`: PDF pp.9--10: quantum lawMarginal entropy with trivial external register.
--   - `stateCMI`: PDF pp.9--10: quantum conditional mutual information.
--   - `qValue`: PDF pp.9--10: accepted dual/total entropy expressions, no factor 1/2.
--   - `QLOPC`: PDF pp.10--12: public-transcript quantum LOCC, using the accepted complete local instruments, but excluding the transcript-forgetting constructor.
--   - `readout`: PDF pp.11--12: final classical output in the local computational bases.
--   - `IsDiagonalOutput`: PDF p.12: all retained quantum registers have become classical outputs.
--   - `labelledProductDensity`: PDF p.10: product density in labelled local bases.
--   - `localDensity`: PDF p.10: canonical one-party partial trace, retaining off-diagonals.
--   - `quantumKL`: PDF p.10: support-aware accepted Umegaki divergence divided by ln 2. The invalid-input branch is unused: density of product candidates is part of our theorem's conclusion, never an assumed missing lemma.
--   - `ghzVector`: PDF pp.10--11: plus GHZ vector, including Bell for n=2. The n=0 overlapping support is excluded whenever this is called a state.
--   - `labelledSingletVector`: PDF p.10: relabel the frozen normalized singlet from a pair to party-labelled qubits.
--   - `qubitBasis`: PDF p.11: local z basis (false) and standard Hadamard x basis (true).
--   - `ghzMeasurement`: PDF p.11: independent projective GHZ measurement probabilities.
--   - `IsSchmidtExpansion`: PDF p.12: a Schmidt expansion in orthonormal local bases, allowing zero coefficients and arbitrary unequal finite dimensions.
--   - `schmidtLaw`: PDF p.12: outcomes of measurement in a Schmidt basis, with unused zero-weight outcomes omitted.
--   - `eProduct`: PDF p.4: partywise independent products, including independent Eve data.
--   - `ConditionalProduct`: PDF p.4: zero on products conditional on every positive-mass Eve letter.
--   - `ExtensionBasics`: PDF pp.3--4: inherited positivity, product normalization, additivity, and continuity on each FIXED honest/Eve alphabet.
--   - `ghzCopiesVector`: PDF p.11: GHZ copies coded partywise, with the same word coding as cCopies.
--   - `QExtracts`: PDF pp.11--12: exact classical extraction leaves the target independent of the complete public transcript. The final density is diagonal and its classical law equals q on every positive-weight leaf.
--   - `localEntropySum`: PDF p.12: the entropy at each singleton cut of the pure initial state.
--   - `conditionalCounterexample`: PDF p.4, the possible failure of property 7: A,B are independent fair bits and Eve stores their xor. Forgetting E changes conditional I from 1 to 0.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, https://arxiv.org/abs/quant-ph/0202103v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P12
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42

/-!
Cerf--Massar--Schneider, arXiv:quant-ph/0202103v1.
Finite alphabets and nonzero finite Hilbert dimensions; all entropies in bits.
Public information is retained in the branch index. In particular we do not
use the accepted LOCC.forget constructor. No asymptotic operational claim is
inferred from continuity on a fixed alphabet. Compilation is pending handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P37

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Claimed50.P33
  (InformationKind RegisterBasis FiniteState singleParties allParties
   info entropyAt trivialExtension informationFunctional LocalInstrument
   IsContinuousFunctional partyProduct registerMarginal)

/-- PDF pp.3--4: specialize the accepted RegisterBasis to finite local alphabets. -/
abbrev ClassicalBasis {n : ℕ} (d : Fin n → ℕ) := RegisterBasis (fun i => Fin (d i))

/-- PDF pp.3--4: finite classical data. Normalization and positive dimensions
are imposed by IsValidClassicalData; keeping these unbundled permits explicit laws. -/
structure CData (n : ℕ) where
  dims : Fin n → ℕ
  prob : ClassicalBasis dims → ℝ

/-- PDF pp.3--4: normalized finite laws on nonempty local alphabets. -/
def IsValidClassicalData {n : ℕ} (p : CData n) : Prop :=
  (∀ i, 0 < p.dims i) ∧ IsLaw p.prob

/-- PDF p.4: a lawMarginal, including the one-point empty lawMarginal. -/
def lawMarginal {n : ℕ} (p : CData n) (s : Finset (Fin n))
    (a : (i : {i : Fin n // i ∈ s}) → Fin (p.dims i.val)) : ℝ :=
  ∑ x : ClassicalBasis p.dims, if ∀ i, x i.val = a i then p.prob x else 0

/-- PDF p.4: Shannon entropy of the selected party registers, in bits. -/
def cH {n : ℕ} (p : CData n) (s : Finset (Fin n)) : ℝ :=
  shannon (lawMarginal p s)

/-- PDF p.5: conditional mutual information I(A:B|E). -/
def lawCMI {n : ℕ} (p : CData n) (a b e : Finset (Fin n)) : ℝ :=
  cH p (a ∪ e) + cH p (b ∪ e) - cH p e - cH p (a ∪ b ∪ e)

/-- PDF pp.4--5, (13),(17): information for disjoint groups. The coefficient
is the number of groups minus one, with no normalization divisor. -/
def cInfo {n m : ℕ} (kind : InformationKind) (p : CData n)
    (a : Fin m → Finset (Fin n)) : ℝ :=
  match kind with
  | .dual => (∑ i, cH p ((Finset.univ.erase i).biUnion a)) -
      (m - 1 : ℕ) * cH p (allParties a)
  | .total => (∑ i, cH p (a i)) - cH p (allParties a)

/-- PDF pp.4--5: S_n is dual information and T_n is total information. -/
def cValue {n : ℕ} (kind : InformationKind) (p : CData n) : ℝ :=
  cInfo kind p (singleParties n)

/-- PDF p.3, (5): partywise independent product with explicit paired coding. -/
def cProduct {n : ℕ} (p q : CData n) : CData n where
  dims := fun i => p.dims i * q.dims i
  prob := fun x => p.prob (fun i => (finProdFinEquiv.symm (x i)).1) *
    q.prob (fun i => (finProdFinEquiv.symm (x i)).2)

/-- PDF p.3, (8): exact independent copies, regrouped by honest party.
The finite equivalence only codes words; it introduces no correlations. -/
def cCopies {n : ℕ} (p : CData n) (k : ℕ) : CData n where
  dims := fun i => Fintype.card (Fin k → Fin (p.dims i))
  prob := fun x => ∏ j : Fin k, p.prob
    (fun i => (Fintype.equivFin (Fin k → Fin (p.dims i))).symm (x i) j)

/-- PDF p.5: independent local distributions, not a mixture of products. -/
def IsIndependentLaw {n : ℕ} (p : CData n) : Prop :=
  ∃ q : (i : Fin n) → Fin (p.dims i) → ℝ,
    (∀ i, IsLaw (q i)) ∧ ∀ x, p.prob x = ∏ i, q i (x i)

/-- PDF pp.3,6--7: a stochastic local operation with a public outcome j.
Only the acting party changes its register. The row sums include both the
public outcome and retained local data. At zero weight the equation is
subnormalized, so no conditional law is selected by division. -/
def CInstrument {n k : ℕ} (p : CData n) (w : Fin k → ℝ)
    (r : Fin k → CData n) : Prop :=
  IsValidClassicalData p ∧ IsLaw w ∧ (∀ j, IsValidClassicalData (r j)) ∧
  ∃ party : Fin n,
  ∃ K : (j : Fin k) → Fin (p.dims party) → Fin ((r j).dims party) → ℝ,
    (∀ j i, i ≠ party → (r j).dims i = p.dims i) ∧
    (∀ j a b, 0 ≤ K j a b) ∧
    (∀ a, (∑ j, ∑ b, K j a b) = 1) ∧
    ∀ j (y : ClassicalBasis (r j).dims),
      w j * (r j).prob y = ∑ x : ClassicalBasis p.dims,
        if ∀ i, i ≠ party → (x i).val = (y i).val
        then p.prob x * K j (x party) (y party) else 0

/-- PDF p.3: finite adaptive local stochastic/public-communication tree.
Each leaf index records the full public transcript known to Eve. A one-outcome
step is a private stochastic channel. There is no transcript-forgetting rule. -/
inductive CLOPC {n : ℕ} : CData n → List (ℝ × CData n) → Prop where
  | stop (p : CData n) (h : IsValidClassicalData p) : CLOPC p [(1,p)]
  | step (p : CData n) (k : ℕ) (w : Fin k → ℝ) (r : Fin k → CData n)
      (h : CInstrument p w r) (next : Fin k → List (ℝ × CData n))
      (hn : ∀ j, CLOPC (r j) (next j)) :
      CLOPC p ((List.finRange k).flatMap fun j =>
        (next j).map fun z => (w j * z.1,z.2))

/-- PDF pp.3,7--8: exact secret conversion; on every positive-probability
transcript the honest law is the SAME target law. Thus the target is independent
of Eve's entire transcript. Alphabet codings are required to agree. -/
def ExactSecretConversion {n : ℕ} (p q : CData n) : Prop :=
  ∃ out : List (ℝ × CData n), CLOPC p out ∧
    ∀ z ∈ out, 0 < z.1 → z.2 = q

/-- PDF p.3, properties 1--6, in their finite-alphabet scope.
Local/public monotonicity is averaged over the public outcome. -/
def IsCMonotone {n : ℕ} (M : CData n → ℝ) : Prop :=
  (∀ p, IsValidClassicalData p → 0 ≤ M p) ∧
  (∀ p, IsValidClassicalData p → IsIndependentLaw p → M p = 0) ∧
  (∀ (p : CData n) (k : ℕ) (w : Fin k → ℝ) (r : Fin k → CData n),
    CInstrument p w r → (∑ j, w j * M (r j)) ≤ M p) ∧
  (∀ p q, IsValidClassicalData p → IsValidClassicalData q → M (cProduct p q) = M p + M q) ∧
  ∀ (d : Fin n → ℕ) (hd : ∀ i, 0 < d i),
    Continuous (fun p : {p : ClassicalBasis d → ℝ // IsLaw p} => M ⟨d,p.val⟩)

/-- PDF p.5: permutation symmetry is independent of alphabet cardinalities. -/
def permuteData {n : ℕ} (p : CData n) (e : Equiv.Perm (Fin n)) : CData n where
  dims := fun i => p.dims (e i)
  prob := fun x => p.prob (fun i => Fin.cast (congrArg p.dims (e.apply_symm_apply i)) (x (e.symm i)))

/-- PDF p.4: a classical law including Eve's finite variable. -/
structure EData (n : ℕ) where
  dims : Fin n → ℕ
  eve : ℕ
  prob : ClassicalBasis dims × Fin eve → ℝ

/-- PDF pp.3--4: normalized joint law and nonempty honest/Eve alphabets. -/
def EValid {n : ℕ} (p : EData n) : Prop :=
  (∀ i, 0 < p.dims i) ∧ 0 < p.eve ∧ IsLaw p.prob

/-- PDF p.4: probability of an Eve letter. -/
def eveLetterProbability {n : ℕ} (p : EData n) (e : Fin p.eve) : ℝ :=
  ∑ x, p.prob (x,e)

/-- PDF p.4: honest conditional data; only positive-weight uses are physical. -/
def givenE {n : ℕ} (p : EData n) (e : Fin p.eve) : CData n :=
  ⟨p.dims, fun x => p.prob (x,e) / eveLetterProbability p e⟩

/-- PDF p.4: M_1, explicitly zero on zero-weight Eve letters. -/
def conditionalAverage {n : ℕ} (M : CData n → ℝ) (p : EData n) : ℝ :=
  ∑ e, if 0 < eveLetterProbability p e then eveLetterProbability p e * M (givenE p e) else 0

/-- PDF p.4: push the joint law through the stochastic channel on Eve alone. -/
def processE {n f : ℕ} (p : EData n) (K : Fin p.eve → Fin f → ℝ) : EData n :=
  ⟨p.dims, f, fun z => ∑ e, p.prob (z.1,e) * K e z.2⟩

/-- PDF p.4: admissible values, with NO fixed output alphabet or deterministic
channel restriction. On valid p and nonnegative M the set is nonempty and
bounded below by zero (the one-output channel is feasible). -/
def intrinsicExtensionScores {n : ℕ} (M : CData n → ℝ) (p : EData n) : Set ℝ :=
  {v | ∃ f : ℕ, 0 < f ∧ ∃ K : Fin p.eve → Fin f → ℝ,
    IsStochastic K ∧ v = conditionalAverage M (processE p K)}

/-- PDF p.4: define the intrinsic extension by the infimum; attainment is a
conclusion of the extension theorem, never built into this definition. -/
def intrinsicExtensionValue {n : ℕ} (M : CData n → ℝ) (p : EData n) : ℝ :=
  sInf (intrinsicExtensionScores M p)

/-- PDF pp.3--4: local honest instruments preserving Eve's original variable.
The public outcome is retained separately from that original variable. -/
def EInstrument {n k : ℕ} (p : EData n) (w : Fin k → ℝ)
    (r : Fin k → EData n) : Prop :=
  EValid p ∧ IsLaw w ∧ (∀ j, EValid (r j)) ∧
  ∃ party : Fin n,
  ∃ K : (j : Fin k) → Fin (p.dims party) → Fin ((r j).dims party) → ℝ,
    (∀ j, (r j).eve = p.eve) ∧
    (∀ j i, i ≠ party → (r j).dims i = p.dims i) ∧
    (∀ j a b, 0 ≤ K j a b) ∧
    (∀ a, (∑ j, ∑ b, K j a b) = 1) ∧
    ∀ j (y : ClassicalBasis (r j).dims) (e : Fin (r j).eve),
      w j * (r j).prob (y,e) = ∑ x : ClassicalBasis p.dims, ∑ z : Fin p.eve,
        if e.val = z.val ∧ (∀ i, i ≠ party → (x i).val = (y i).val)
        then p.prob (x,z) * K j (x party) (y party) else 0

/-- PDF p.3, property 8: Eve publicly announces a stochastic function of E,
retaining E. Zero-probability branches use the total-function value zero. -/
def evePublicBranch {n f : ℕ} (p : EData n)
    (K : Fin p.eve → Fin f → ℝ) (j : Fin f) : EData n :=
  let w := ∑ x : ClassicalBasis p.dims, ∑ e : Fin p.eve, p.prob (x,e) * K e j
  ⟨p.dims,p.eve,fun z => p.prob z * K z.2 j / w⟩

/-- PDF p.3, property 8: the public probability, summing honest data and Eve. -/
def evePublicWeight {n f : ℕ} (p : EData n)
    (K : Fin p.eve → Fin f → ℝ) (j : Fin f) : ℝ :=
  ∑ x : ClassicalBasis p.dims, ∑ e : Fin p.eve, p.prob (x,e) * K e j

/-- PDF pp.3--4: honest local/public and Eve-public inequalities.
The latter is an increase. No Eve-local inequality is hidden in this predicate. -/
def ExtensionMonotonicity {n : ℕ} (F : EData n → ℝ) : Prop :=
  (∀ (p : EData n) (k : ℕ) (w : Fin k → ℝ) (r : Fin k → EData n),
    EInstrument p w r → (∑ j, w j * F (r j)) ≤ F p) ∧
  ∀ (p : EData n) (f : ℕ) (K : Fin p.eve → Fin f → ℝ),
    EValid p → 0 < f → IsStochastic K →
    F p ≤ ∑ j, if 0 < evePublicWeight p K j then
      evePublicWeight p K j * F (evePublicBranch p K j) else 0

/-- PDF p.4: grouping by a surjection, hence disjoint nonempty blocks. -/
def groupData {m n : ℕ} (g : Fin m → Fin n) (p : CData m) : CData n where
  dims := fun b => Fintype.card ((i : {i : Fin m // g i = b}) → Fin (p.dims i.val))
  prob := fun y => ∑ x : ClassicalBasis p.dims,
    if ∀ b, y b = Fintype.equivFin
      ((i : {i : Fin m // g i = b}) → Fin (p.dims i.val)) (fun i => x i.val)
    then p.prob x else 0

/-- Earlier parties in the fixed source order. -/
def earlier {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => j.val < i.val

/-- Later parties in the fixed source order. -/
def later {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => i.val < j.val

/-- PDF p.5, (15): merge the final two parties; used only for n≥3. -/
def mergeLast (n : ℕ) : Fin (n-1) → Finset (Fin n) :=
  fun i => Finset.univ.filter fun j =>
    if i.val + 1 = n-1 then i.val ≤ j.val else i.val = j.val

/-- PDF p.5, (19): retain the first n-1 parties. -/
def firstParties (n : ℕ) : Fin (n-1) → Finset (Fin n) :=
  fun i => Finset.univ.filter fun j => j.val = i.val

/-- PDF p.5, (18): support-aware relative entropy IN BITS. The printed ln
is corrected to log_2 to match (17) and the one-bit examples on p.7. -/
def classicalKL {I : Type} [Fintype I] (p q : I → ℝ) : ℝ≥0∞ :=
  if ∃ x, 0 < p x ∧ q x = 0 then ⊤
  else ENNReal.ofReal (∑ x, if p x = 0 then 0 else p x * Real.logb 2 (p x / q x))

/-- PDF p.5: the product of arbitrary local laws. -/
def productLaw {n : ℕ} {d : Fin n → ℕ}
    (q : (i : Fin n) → Fin (d i) → ℝ) : ClassicalBasis d → ℝ := fun x => ∏ i, q i (x i)

/-- PDF p.5, (18): local marginals in their original alphabets. -/
def localLaw {n : ℕ} (p : CData n) (i : Fin n) (a : Fin (p.dims i)) : ℝ :=
  ∑ x, if x i = a then p.prob x else 0

/-- PDF p.7, (41)--(45): source law order AB, AC, BC, common, xor;
the uncorrelated spectator for each pair is chosen constant. -/
def exampleLaw (j : Fin 5) : CData 3 where
  dims := fun _ => 2
  prob := fun x =>
    if j.val = 0 then (if x 0 = x 1 ∧ x 2 = 0 then 1/2 else 0)
    else if j.val = 1 then (if x 0 = x 2 ∧ x 1 = 0 then 1/2 else 0)
    else if j.val = 2 then (if x 1 = x 2 ∧ x 0 = 0 then 1/2 else 0)
    else if j.val = 3 then (if x 0 = x 1 ∧ x 1 = x 2 then 1/2 else 0)
    else (if ((x 0).val + (x 1).val + (x 2).val) % 2 = 0 then 1/4 else 0)

/-- PDF p.7: order I(A:BC), I(B:AC), I(C:AB), S_3, T_3. -/
def fiveValues (p : CData 3) : Fin 5 → ℝ :=
  ![lawCMI p {0} {1,2} ∅, lawCMI p {1} {0,2} ∅, lawCMI p {2} {0,1} ∅,
    cValue .dual p, cValue .total p]

/-- PDF p.7: all 25 entries, with pair-law order AB, AC, BC. -/
def fiveTable : Fin 5 → Fin 5 → ℝ :=
  ![![1,1,0,1,1], ![1,0,1,1,1], ![0,1,1,1,1], ![1,1,1,1,2], ![1,1,1,2,1]]

/-- PDF p.8, (47): r,s,t,u use pair order AB, BC, AC. -/
def secrecyCoordinates (p : CData 3) : Fin 4 → ℝ :=
  ![lawCMI p {0} {1} {2}, lawCMI p {1} {2} {0}, lawCMI p {2} {0} {1},
    lawCMI p {0} {1} ∅ - lawCMI p {0} {1} {2}]

/-- PDF pp.8--9: nonnegative formal yields, in order AB, BC, AC, xor, common.
These are real coefficients of monotone vectors, NOT tensor exponents. -/
def formalYields (p : CData 3) : Fin 5 → ℝ :=
  let v := secrecyCoordinates p
  if 0 ≤ v 3 then ![v 0,v 1,v 2,0,v 3]
  else ![v 0 + v 3,v 1 + v 3,v 2 + v 3,-v 3,0]

/-- PDF pp.5--6, (23): the linear combination with both endpoints included. -/
def combination {n : ℕ} (lambda : ℝ) (p : CData n) : ℝ :=
  lambda * cValue .dual p + (1-lambda) * cValue .total p

/-- PDF pp.9--10: quantum lawMarginal entropy with trivial external register. -/
def qH {n : ℕ} (s : FiniteState n) (a : Finset (Fin n)) : ℝ :=
  entropyAt (trivialExtension s.rho) a

/-- PDF pp.9--10: quantum conditional mutual information. -/
def stateCMI {n : ℕ} (s : FiniteState n) (a b e : Finset (Fin n)) : ℝ :=
  qH s (a ∪ e) + qH s (b ∪ e) - qH s e - qH s (a ∪ b ∪ e)

/-- PDF pp.9--10: accepted dual/total entropy expressions, no factor 1/2. -/
def qValue {n : ℕ} (kind : InformationKind) (s : FiniteState n) : ℝ :=
  informationFunctional kind s

/-- PDF pp.10--12: public-transcript quantum LOCC, using the accepted complete
local instruments, but excluding the transcript-forgetting constructor. -/
inductive QLOPC {n : ℕ} : FiniteState n → List (ℝ × FiniteState n) → Prop where
  | stop (s : FiniteState n) : QLOPC s [(1,s)]
  | step (s : FiniteState n) (k : ℕ) (w : Fin k → ℝ) (r : Fin k → FiniteState n)
      (h : LocalInstrument s w r) (next : Fin k → List (ℝ × FiniteState n))
      (hn : ∀ j, QLOPC (r j) (next j)) :
      QLOPC s ((List.finRange k).flatMap fun j =>
        (next j).map fun z => (w j * z.1,z.2))

/-- PDF pp.11--12: final classical output in the local computational bases. -/
def readout {n : ℕ} (s : FiniteState n) : CData n :=
  ⟨s.dims,fun x => (s.rho x x).re⟩

/-- PDF p.12: all retained quantum registers have become classical outputs. -/
def IsDiagonalOutput {n : ℕ} (s : FiniteState n) : Prop :=
  ∀ x y, x ≠ y → s.rho x y = 0

/-- PDF p.10: product density in labelled local bases. -/
def labelledProductDensity {n : ℕ} {d : Fin n → ℕ}
    (eta : (i : Fin n) → Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    Matrix (ClassicalBasis d) (ClassicalBasis d) ℂ := fun x y => ∏ i, eta i (x i) (y i)

/-- PDF p.10: canonical one-party partial trace, retaining off-diagonals. -/
def localDensity {n : ℕ} (s : FiniteState n) (i : Fin n) :
    Matrix (Fin (s.dims i)) (Fin (s.dims i)) ℂ :=
  fun a b => ∑ x : ClassicalBasis s.dims, ∑ y : ClassicalBasis s.dims,
    if x i = a ∧ y i = b ∧ (∀ j, j ≠ i → x j = y j)
    then s.rho x y else 0

/-- PDF p.10: support-aware accepted Umegaki divergence divided by ln 2.
The invalid-input branch is unused: density of product candidates is part of
our theorem's conclusion, never an assumed missing lemma. -/
def quantumKL {I : Type} [Fintype I] (rho sigma : Matrix I I ℂ) : ℝ≥0∞ :=
  if hr : IsDensityMatrix rho then
    if hs : IsDensityMatrix sigma then
      QAlgorithms.QuantumLoss.umegakiEntropy rho sigma hr hs / ENNReal.ofReal (Real.log 2)
    else 0
  else 0

/-- PDF pp.10--11: plus GHZ vector, including Bell for n=2.
The n=0 overlapping support is excluded whenever this is called a state. -/
def ghzVector (n : ℕ) : EuclideanSpace ℂ (Fin n → Fin 2) :=
  WithLp.toLp 2 fun x =>
    if (∀ i, x i = 0) ∨ (∀ i, x i = 1) then ((Real.sqrt 2 : ℂ)⁻¹) else 0

/-- PDF p.10: relabel the frozen normalized singlet from a pair to party-labelled qubits. -/
def labelledSingletVector : EuclideanSpace ℂ (Fin 2 → Fin 2) :=
  WithLp.toLp 2 fun x =>
    QAlgorithms.Papers.Independent.Dependency50.P42.singletVector (x 0, x 1)

/-- PDF p.11: local z basis (false) and standard Hadamard x basis (true). -/
def qubitBasis (isX : Bool) (a x : Fin 2) : ℂ :=
  if isX then (if a = 1 ∧ x = 1 then -1 else 1) / (Real.sqrt 2 : ℂ)
  else if a = x then 1 else 0

/-- PDF p.11: independent projective GHZ measurement probabilities. -/
def ghzMeasurement (isX : Bool) : CData 3 :=
  ⟨fun _ => 2, fun a => Complex.normSq
    (∑ x : Fin 3 → Fin 2, (∏ i, conj (qubitBasis isX (a i) (x i))) * ghzVector 3 x)⟩

/-- PDF p.12: a Schmidt expansion in orthonormal local bases, allowing zero
coefficients and arbitrary unequal finite dimensions. -/
def IsSchmidtExpansion (s : FiniteState 2) (k : ℕ) (w : Fin k → ℝ)
    (u : Fin k → EuclideanSpace ℂ (Fin (s.dims 0)))
    (v : Fin k → EuclideanSpace ℂ (Fin (s.dims 1))) : Prop :=
  IsLaw w ∧ Orthonormal ℂ u ∧ Orthonormal ℂ v ∧
  s.rho = pureDensity (WithLp.toLp 2 fun x : ClassicalBasis s.dims =>
    ∑ j, (Real.sqrt (w j) : ℂ) * u j (x 0) * v j (x 1))

/-- PDF p.12: outcomes of measurement in a Schmidt basis, with unused
zero-weight outcomes omitted. -/
def schmidtLaw {k : ℕ} (w : Fin k → ℝ) : CData 2 :=
  ⟨fun _ => k, fun x => if x 0 = x 1 then w (x 0) else 0⟩

/-- Sanity: the xor law has even parity and weight 1/4 at 110. -/
example : (exampleLaw 4).prob (![1,1,0] : Fin 3 → Fin 2) = 1/4 := by
  change (if (1 + 1 + 0 : ℕ) % 2 = 0 then (1 / 4 : ℝ) else 0) = 1 / 4
  norm_num

/-- Sanity: the pair spectator is constant, not an extra shared secret bit. -/
example : (exampleLaw 0).prob (![1,1,1] : Fin 3 → Fin 2) = 0 := by
  change (if (1 : Fin 2) = 1 ∧ (1 : Fin 2) = 0 then (1 / 2 : ℝ) else 0) = 0
  norm_num

/-- Sanity: every public branch is kept; zero steps has one input leaf. -/
example {n : ℕ} (s : FiniteState n) : QLOPC s [(1,s)] := QLOPC.stop s

/-- Sanity: classical relative entropy detects support violation. -/
example {I : Type} [Fintype I] (p q : I → ℝ)
    (h : ∃ x, 0 < p x ∧ q x = 0) : classicalKL p q = ⊤ := by
  simp [classicalKL,h]

/-- Sanity: a zero Eve slice contributes zero without choosing a law there. -/
example {n : ℕ} (M : CData n → ℝ) (p : EData n) (e : Fin p.eve)
    (h : eveLetterProbability p e = 0) :
    (if 0 < eveLetterProbability p e then eveLetterProbability p e * M (givenE p e) else 0) = 0 := by
  simp [h]

/-- Sanity: Shannon's zero-mass summand is zero in the accepted bits convention. -/
example : (0 : ℝ) * Real.logb 2 0 = 0 := by simp

/-- PDF p.4: partywise independent products, including independent Eve data. -/
def eProduct {n : ℕ} (p q : EData n) : EData n where
  dims := fun i => p.dims i * q.dims i
  eve := p.eve * q.eve
  prob := fun z =>
    p.prob ((fun i => (finProdFinEquiv.symm (z.1 i)).1),
      (finProdFinEquiv.symm z.2).1) *
    q.prob ((fun i => (finProdFinEquiv.symm (z.1 i)).2),
      (finProdFinEquiv.symm z.2).2)

/-- PDF p.4: zero on products conditional on every positive-mass Eve letter. -/
def ConditionalProduct {n : ℕ} (p : EData n) : Prop :=
  ∀ e, 0 < eveLetterProbability p e → IsIndependentLaw (givenE p e)

/-- PDF pp.3--4: inherited positivity, product normalization, additivity,
and continuity on each FIXED honest/Eve alphabet. -/
def ExtensionBasics {n : ℕ} (F : EData n → ℝ) : Prop :=
  (∀ p, EValid p → 0 ≤ F p) ∧
  (∀ p, EValid p → ConditionalProduct p → F p = 0) ∧
  (∀ p q, EValid p → EValid q → F (eProduct p q) = F p + F q) ∧
  ∀ (d : Fin n → ℕ) (e : ℕ), (∀ i, 0 < d i) → 0 < e →
    Continuous (fun p : {p : ClassicalBasis d × Fin e → ℝ // IsLaw p} =>
      F ⟨d,e,p.val⟩)

/-- PDF p.11: GHZ copies coded partywise, with the same word coding as cCopies. -/
def ghzCopiesVector (k : ℕ) :
    EuclideanSpace ℂ (Fin 3 → Fin (Fintype.card (Fin k → Fin 2))) :=
  WithLp.toLp 2 fun x => ∏ j : Fin k,
    ghzVector 3 (fun i => (Fintype.equivFin (Fin k → Fin 2)).symm (x i) j)

/-- PDF pp.11--12: exact classical extraction leaves the target independent
of the complete public transcript. The final density is diagonal and its
classical law equals q on every positive-weight leaf. -/
def QExtracts {n : ℕ} (s : FiniteState n) (q : CData n) : Prop :=
  ∃ out : List (ℝ × FiniteState n), QLOPC s out ∧
    ∀ z ∈ out, 0 < z.1 → IsDiagonalOutput z.2 ∧ readout z.2 = q

/-- PDF p.12: the entropy at each singleton cut of the pure initial state. -/
def localEntropySum {n : ℕ} (s : FiniteState n) : ℝ := ∑ i, qH s {i}

/-- PDF p.4, the possible failure of property 7: A,B are independent fair
bits and Eve stores their xor. Forgetting E changes conditional I from 1 to 0. -/
def conditionalCounterexample : EData 2 :=
  ⟨fun _ => 2, 2, fun z =>
    if z.2.val = ((z.1 0).val + (z.1 1).val) % 2 then 1/4 else 0⟩

end QAlgorithms.Papers.Independent.Renew46.P37


