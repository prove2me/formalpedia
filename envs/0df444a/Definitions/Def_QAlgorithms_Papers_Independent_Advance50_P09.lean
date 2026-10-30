-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P09
-- name    : QAlgorithms_Papers_Independent_Advance50_P09
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T08:30:36.302531+00:00
-- url     : https://prove2.me/theorems/7b7499c8-41ea-4578-a752-f0b7349f07c2
-- title:
--   Definitions for One-shot rates for entanglement manipulation under non-entangling maps
-- statement:
--   The objects the formalized statements of *One-shot rates for entanglement manipulation under non-entangling maps* (arXiv:0905.2673) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `MultipartiteSystem`: PDF p.2, section II: finite, nonzero local Hilbert spaces, with at least two parties.
--   - `ProductBasis`: PDF p.2: the computational product basis of the full multipartite space.
--   - `MultipartiteOperator`: PDF p.2: operators on the full multipartite space.
--   - `IsFullySeparable`: PDF p.2, Eq.(1): full multipartite separability, with normalized local factors.
--   - `negativeLog`: PDF p.2, Eq.(12): the zero-probability score is positive infinity.
--   - `maxEntanglement`: PDF p.2, Eqs.(3),(5): max-relative entropy of entanglement. The scalar is at least one because both comparison matrices are normalized states. ComplexOrder supplies Mathlib's complex order required by PosSemidef.
--   - `globalRobustness`: PDF p.2, Eq.(8): global robustness permits arbitrary normalized noise.
--   - `logRobustness`: PDF p.2, Eq.(9): standard logarithmic robustness; the noise must be separable.
--   - `fidelitySmoothMaxEntanglement`: PDF p.2, Eq.(10): smoothing over normalized states in the squared-fidelity ball.
--   - `smoothLogRobustness`: PDF p.2, Eq.(11): fidelity-ball smoothing of standard logarithmic robustness.
--   - `operatorSmoothMinEntanglement`: PDF p.2, Eq.(12): operator smoothing, not state-ball smoothing. Extended-real extrema preserve the zero-effect branch at eps >= 1.
--   - `IsSEPP`: PDF p.3, Definition 5: an actual CPTP map preserving full separability. Input and output local dimensions may differ.
--   - `IsDeltaSEPP`: PDF p.3, Definition 6: delta-SEPP, measured using global robustness.
--   - `resourceSystem`: PDF p.3, preamble to Definitions 7--9: MES registers of positive arbitrary rank M; the first two parties have dimension M and the remaining parties dimension one.
--   - `mes`: PDF p.2: density matrix of M^(-1/2) sum_i |i,i>, extended by trivial registers.
--   - `tensorSystem`: PDF pp.3,5: a tensor product keeps the same parties, pairing their local registers.
--   - `partyTensor`: PDF pp.3,5: tensor product with local registers grouped by party.
--   - `copySystem`: PDF pp.2--3, Eqs.(13),(15): n copies, with each party holding all its n registers.
--   - `partyTensorPower`: PDF pp.2--3: the actual matrix rho tensor n, including the scalar empty tensor.
--   - `distillationRates`: PDF p.3, Eq.(18): attainable log-ranks under actual SEPP channels.
--   - `distillation`: PDF p.3, Eq.(18): extended distillation optimum, with infinity if ranks are unbounded.
--   - `formationRates`: PDF p.3, Eq.(17): attainable formation costs, with arbitrary positive MES rank.
--   - `catalyticRates`: PDF p.3, Definition 8: catalyst ranks are optimized, with exact, uncorrelated return.
--   - `catalyticCost`: PDF p.3, Definition 8: optimized catalytic cost, with an extended empty-set convention.
--   - `complementMes`: PDF p.5, Eq.(36): the normalized complementary isotropic block. The lemma uses K >= 2 so this real denominator is strictly positive.
--   - `isotropicMixture`: PDF p.5, Eqs.(36),(40): the block state constructed from lambda, rho_eps, and theta.
--   - `fullRelativeEntanglement`: PDF p.3, Eq.(16): infimum over the full multipartite separable state set.
--   - `perCopy`: PDF pp.2--3: divide the (n+1)-copy quantity by the strictly positive block size.
--   - `HasRelativeLimit`: PDF p.3, Eq.(15): ordinary tensor-power limit; this predicate asserts its existence.
--   - `HasMinLimit`: PDF p.2, Eqs.(13)--(14): liminf over copy number, then epsilon down to zero.
--   - `HasMaxLimit`: PDF p.2, Eqs.(13)--(14): limsup over copy number, then epsilon down to zero.
--   - `HasDistillationLimit`: PDF p.3, Eq.(23): both ordinary limits are asserted, in the source's order.
--   - `HasCatalyticLimit`: PDF pp.3--4, Eq.(24): ordinary limits n, then delta down to zero, then epsilon down to zero. Corrects the printed missing tensor power on rho.
-- source:
--   One-shot rates for entanglement manipulation under non-entangling maps, arXiv:0905.2673v2, https://arxiv.org/abs/0905.2673v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

/-!
Statements from Brandao--Datta, arXiv:0905.2673v2.
Paper-specific multipartite definitions are local; exact accepted fidelity,
base-two logarithm, relative entropy, and ordinary partyTensor-power interfaces are imported. There are m+2 parties;
partyTensor products and powers group registers belonging to the same party.
Theorem 3 and cited Lemma 4 are deferred in the accompanying HARD.md.
-/

noncomputable section

open Filter Set
open scoped Topology Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P09

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)
open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

/-- PDF p.2, section II: finite, nonzero local Hilbert spaces, with at least two parties. -/
structure MultipartiteSystem (m : ℕ) where
  localBasis : Fin (m + 2) → Type
  finiteBasis : ∀ i, Fintype (localBasis i)
  inhabitedBasis : ∀ i, Nonempty (localBasis i)

attribute [instance] MultipartiteSystem.finiteBasis MultipartiteSystem.inhabitedBasis

/-- PDF p.2: the computational product basis of the full multipartite space. -/
abbrev ProductBasis {m : ℕ} (H : MultipartiteSystem m) := (i : Fin (m + 2)) → H.localBasis i

/-- PDF p.2: operators on the full multipartite space. -/
abbrev MultipartiteOperator {m : ℕ} (H : MultipartiteSystem m) := Matrix (ProductBasis H) (ProductBasis H) ℂ

/-- PDF p.2, Eq.(1): full multipartite separability, with normalized local factors. -/
def IsFullySeparable {m : ℕ} {H : MultipartiteSystem m} (rho : MultipartiteOperator H) : Prop :=
  IsDensityMatrix rho ∧
    ∃ k : ℕ, ∃ w : Fin k → ℝ,
      ∃ sigma : (j : Fin k) → (i : Fin (m + 2)) →
        Matrix (H.localBasis i) (H.localBasis i) ℂ,
      (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧
      (∀ j i, IsDensityMatrix (sigma j i)) ∧
      rho = ∑ j, (w j : ℂ) • (Matrix.of fun x y => ∏ i, sigma j i (x i) (y i))

/-- PDF p.2, Eq.(12): the zero-probability score is positive infinity. -/
def negativeLog (p : ℝ) : EReal := if p = 0 then ⊤ else (-logTwo p : ℝ)

/-- PDF p.2, Eqs.(3),(5): max-relative entropy of entanglement.
The scalar is at least one because both comparison matrices are normalized states.
ComplexOrder supplies Mathlib's complex order required by PosSemidef. -/
def maxEntanglement {m : ℕ} {H : MultipartiteSystem m} (rho : MultipartiteOperator H) : EReal :=
  sInf {e | ∃ s : ℝ, 1 ≤ s ∧ ∃ sigma : MultipartiteOperator H,
    IsFullySeparable sigma ∧ ((s : ℂ) • sigma - rho).PosSemidef ∧ e = (logTwo s : EReal)}

/-- PDF p.2, Eq.(8): global robustness permits arbitrary normalized noise. -/
def globalRobustness {m : ℕ} {H : MultipartiteSystem m} (rho : MultipartiteOperator H) : EReal :=
  sInf {e | ∃ s : ℝ, 0 ≤ s ∧ ∃ omega : MultipartiteOperator H,
    IsDensityMatrix omega ∧
    IsFullySeparable (((1 + s)⁻¹ : ℂ) • (rho + (s : ℂ) • omega)) ∧ e = (s : EReal)}

/-- PDF p.2, Eq.(9): standard logarithmic robustness; the noise must be separable. -/
def logRobustness {m : ℕ} {H : MultipartiteSystem m} (rho : MultipartiteOperator H) : EReal :=
  sInf {e | ∃ s : ℝ, 0 ≤ s ∧ ∃ omega : MultipartiteOperator H,
    IsFullySeparable omega ∧
    IsFullySeparable (((1 + s)⁻¹ : ℂ) • (rho + (s : ℂ) • omega)) ∧
    e = (logTwo (1 + s) : EReal)}

/-- PDF p.2, Eq.(10): smoothing over normalized states in the squared-fidelity ball. -/
def fidelitySmoothMaxEntanglement {m : ℕ} {H : MultipartiteSystem m} (rho : MultipartiteOperator H) (eps : ℝ) : EReal :=
  sInf {e | ∃ sigma : MultipartiteOperator H, IsDensityMatrix sigma ∧
    1 - eps ≤ fidelity sigma rho ∧ e = maxEntanglement sigma}

/-- PDF p.2, Eq.(11): fidelity-ball smoothing of standard logarithmic robustness. -/
def smoothLogRobustness {m : ℕ} {H : MultipartiteSystem m} (rho : MultipartiteOperator H) (eps : ℝ) : EReal :=
  sInf {e | ∃ sigma : MultipartiteOperator H, IsDensityMatrix sigma ∧
    1 - eps ≤ fidelity sigma rho ∧ e = logRobustness sigma}

/-- PDF p.2, Eq.(12): operator smoothing, not state-ball smoothing.
Extended-real extrema preserve the zero-effect branch at eps >= 1. -/
def operatorSmoothMinEntanglement {m : ℕ} {H : MultipartiteSystem m} (rho : MultipartiteOperator H) (eps : ℝ) : EReal :=
  sSup {e | ∃ A : MultipartiteOperator H, IsEffect A ∧ 1 - eps ≤ effectProb A rho ∧
    e = sInf {v | ∃ sigma : MultipartiteOperator H, IsFullySeparable sigma ∧
      v = negativeLog (effectProb A sigma)}}

/-- PDF p.3, Definition 5: an actual CPTP map preserving full separability.
Input and output local dimensions may differ. -/
def IsSEPP {m : ℕ} {H J : MultipartiteSystem m} (Phi : Superop (ProductBasis H) (ProductBasis J)) : Prop :=
  IsChannel Phi ∧ ∀ sigma : MultipartiteOperator H, IsFullySeparable sigma → IsFullySeparable (Phi sigma)

/-- PDF p.3, Definition 6: delta-SEPP, measured using global robustness. -/
def IsDeltaSEPP {m : ℕ} {H J : MultipartiteSystem m}
    (delta : ℝ) (Phi : Superop (ProductBasis H) (ProductBasis J)) : Prop :=
  IsChannel Phi ∧ ∀ sigma : MultipartiteOperator H, IsFullySeparable sigma →
    globalRobustness (Phi sigma) ≤ (delta : EReal)

/-- PDF p.3, preamble to Definitions 7--9: MES registers of positive arbitrary rank M;
the first two parties have dimension M and the remaining parties dimension one. -/
def resourceSystem (m : ℕ) (M : ℕ+) : MultipartiteSystem m where
  localBasis i := Fin (if i.val < 2 then (M : ℕ) else 1)
  finiteBasis _ := inferInstance
  inhabitedBasis i := ⟨⟨0, by
    split_ifs
    · exact M.property
    · decide⟩⟩

/-- PDF p.2: density matrix of M^(-1/2) sum_i |i,i>, extended by trivial registers. -/
def mes (m : ℕ) (M : ℕ+) : MultipartiteOperator (resourceSystem m M) :=
  Matrix.of fun x y =>
    if (x ⟨0, by omega⟩).val = (x ⟨1, by omega⟩).val ∧
       (y ⟨0, by omega⟩).val = (y ⟨1, by omega⟩).val
    then ((M : ℕ) : ℂ)⁻¹ else 0

/-- PDF pp.3,5: a tensor product keeps the same parties, pairing their local registers. -/
def tensorSystem {m : ℕ} (H J : MultipartiteSystem m) : MultipartiteSystem m where
  localBasis i := H.localBasis i × J.localBasis i
  finiteBasis _ := inferInstance
  inhabitedBasis _ := inferInstance

/-- PDF pp.3,5: tensor product with local registers grouped by party. -/
def partyTensor {m : ℕ} {H J : MultipartiteSystem m} (rho : MultipartiteOperator H) (sigma : MultipartiteOperator J) :
    MultipartiteOperator (tensorSystem H J) :=
  (Matrix.kronecker rho sigma).submatrix
    (fun x => ((fun i => (x i).1), (fun i => (x i).2)))
    (fun y => ((fun i => (y i).1), (fun i => (y i).2)))

/-- PDF pp.2--3, Eqs.(13),(15): n copies, with each party holding all its n registers. -/
def copySystem {m : ℕ} (H : MultipartiteSystem m) (n : ℕ) : MultipartiteSystem m where
  localBasis i := Fin n → H.localBasis i
  finiteBasis _ := inferInstance
  inhabitedBasis _ := inferInstance

/-- PDF pp.2--3: the actual matrix rho tensor n, including the scalar empty tensor. -/
def partyTensorPower {m : ℕ} {H : MultipartiteSystem m} (rho : MultipartiteOperator H) (n : ℕ) :
    MultipartiteOperator (copySystem H n) :=
  (QAlgorithms.Papers.Independent.Information100.P63.tensorPower n rho).submatrix
    (fun x j i => x i j) (fun y j i => y i j)

/-- PDF p.3, Eq.(18): attainable log-ranks under actual SEPP channels. -/
def distillationRates {m : ℕ} {H : MultipartiteSystem m} (rho : MultipartiteOperator H) (eps : ℝ) : Set ℝ :=
  {r | ∃ M : ℕ+, ∃ Phi : Superop (ProductBasis H) (ProductBasis (resourceSystem m M)),
    IsSEPP Phi ∧ 1 - eps ≤ fidelity (Phi rho) (mes m M) ∧
    r = logTwo (M : ℕ)}

/-- PDF p.3, Eq.(18): extended distillation optimum, with infinity if ranks are unbounded. -/
def distillation {m : ℕ} {H : MultipartiteSystem m} (rho : MultipartiteOperator H) (eps : ℝ) : EReal :=
  sSup {e | ∃ r ∈ distillationRates rho eps, e = (r : EReal)}

/-- PDF p.3, Eq.(17): attainable formation costs, with arbitrary positive MES rank. -/
def formationRates {m : ℕ} {H : MultipartiteSystem m} (rho : MultipartiteOperator H) (eps : ℝ) : Set ℝ :=
  {r | ∃ M : ℕ+, ∃ Phi : Superop (ProductBasis (resourceSystem m M)) (ProductBasis H),
    IsSEPP Phi ∧ 1 - eps ≤ fidelity rho (Phi (mes m M)) ∧
    r = logTwo (M : ℕ)}

/-- PDF p.3, Definition 8: catalyst ranks are optimized, with exact, uncorrelated return. -/
def catalyticRates {m : ℕ} {H : MultipartiteSystem m}
    (rho : MultipartiteOperator H) (delta eps : ℝ) : Set ℝ :=
  {r | ∃ M K : ℕ+, ∃ rhoOut : MultipartiteOperator H, IsDensityMatrix rhoOut ∧
    1 - eps ≤ fidelity rho rhoOut ∧
    ∃ Phi : Superop (ProductBasis (tensorSystem (resourceSystem m M) (resourceSystem m K)))
      (ProductBasis (tensorSystem H (resourceSystem m K))),
      IsDeltaSEPP delta Phi ∧
      Phi (partyTensor (mes m M) (mes m K)) = partyTensor rhoOut (mes m K) ∧
      r = logTwo (M : ℕ)}

/-- PDF p.3, Definition 8: optimized catalytic cost, with an extended empty-set convention. -/
def catalyticCost {m : ℕ} {H : MultipartiteSystem m}
    (rho : MultipartiteOperator H) (delta eps : ℝ) : EReal :=
  sInf {e | ∃ r ∈ catalyticRates rho delta eps, e = (r : EReal)}

/-- PDF p.5, Eq.(36): the normalized complementary isotropic block.
The lemma uses K >= 2 so this real denominator is strictly positive. -/
def complementMes (m : ℕ) (K : ℕ+) : MultipartiteOperator (resourceSystem m K) :=
  (((((K : ℕ) : ℝ) ^ 2 - 1)⁻¹ : ℝ) : ℂ) • (1 - mes m K)

/-- PDF p.5, Eqs.(36),(40): the block state constructed from lambda, rho_eps, and theta. -/
def isotropicMixture {m : ℕ} {H : MultipartiteSystem m} (K : ℕ+) (lam : ℝ)
    (rhoE theta : MultipartiteOperator H) : MultipartiteOperator (tensorSystem H (resourceSystem m K)) :=
  ((1 - lam : ℝ) : ℂ) • partyTensor rhoE (mes m K) +
    (lam : ℂ) • partyTensor theta (complementMes m K)

/-- PDF p.3, Eq.(16): infimum over the full multipartite separable state set. -/
def fullRelativeEntanglement {m : ℕ} {H : MultipartiteSystem m} (rho : MultipartiteOperator H) : EReal :=
  sInf {e | ∃ sigma : MultipartiteOperator H, IsFullySeparable sigma ∧
    e = (QAlgorithms.Papers.Independent.Information100.P54.relativeEntropyBits rho sigma).toEReal}

/-- PDF pp.2--3: divide the (n+1)-copy quantity by the strictly positive block size. -/
def perCopy (n : ℕ) (e : EReal) : EReal := ((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * e

/-- PDF p.3, Eq.(15): ordinary tensor-power limit; this predicate asserts its existence. -/
def HasRelativeLimit {m : ℕ} {H : MultipartiteSystem m} (rho : MultipartiteOperator H) (r : ℝ) : Prop :=
  Tendsto (fun n => perCopy n (fullRelativeEntanglement (partyTensorPower rho (n + 1))))
    atTop (𝓝 (r : EReal))

/-- PDF p.2, Eqs.(13)--(14): liminf over copy number, then epsilon down to zero. -/
def HasMinLimit {m : ℕ} {H : MultipartiteSystem m} (rho : MultipartiteOperator H) (r : ℝ) : Prop :=
  Tendsto (fun eps : ℝ => liminf
    (fun n => perCopy n (operatorSmoothMinEntanglement (partyTensorPower rho (n + 1)) eps)) atTop)
    (𝓝[>] (0 : ℝ)) (𝓝 (r : EReal))

/-- PDF p.2, Eqs.(13)--(14): limsup over copy number, then epsilon down to zero. -/
def HasMaxLimit {m : ℕ} {H : MultipartiteSystem m} (rho : MultipartiteOperator H) (r : ℝ) : Prop :=
  Tendsto (fun eps : ℝ => limsup
    (fun n => perCopy n (fidelitySmoothMaxEntanglement (partyTensorPower rho (n + 1)) eps)) atTop)
    (𝓝[>] (0 : ℝ)) (𝓝 (r : EReal))

/-- PDF p.3, Eq.(23): both ordinary limits are asserted, in the source's order. -/
def HasDistillationLimit {m : ℕ} {H : MultipartiteSystem m} (rho : MultipartiteOperator H) (r : ℝ) : Prop :=
  ∃ d : ℝ → ℝ,
    (∀ eps : ℝ, 0 < eps → eps < 1 →
      Tendsto (fun n => perCopy n (distillation (partyTensorPower rho (n + 1)) eps))
        atTop (𝓝 (d eps : EReal))) ∧
    Tendsto d (𝓝[>] (0 : ℝ)) (𝓝 r)

/-- PDF pp.3--4, Eq.(24): ordinary limits n, then delta down to zero, then epsilon
 down to zero. Corrects the printed missing tensor power on rho. -/
def HasCatalyticLimit {m : ℕ} {H : MultipartiteSystem m} (rho : MultipartiteOperator H) (r : ℝ) : Prop :=
  ∃ c : ℝ → ℝ → ℝ, ∃ d : ℝ → ℝ,
    (∀ eps : ℝ, 0 < eps → eps < 1 → ∀ delta : ℝ, 0 < delta →
      Tendsto (fun n => perCopy n (catalyticCost (partyTensorPower rho (n + 1)) delta eps))
        atTop (𝓝 (c eps delta : EReal))) ∧
    (∀ eps : ℝ, 0 < eps → eps < 1 →
      Tendsto (c eps) (𝓝[>] (0 : ℝ)) (𝓝 (d eps))) ∧
    Tendsto d (𝓝[>] (0 : ℝ)) (𝓝 r)

/-- Sanity: a zero testing probability has infinite score, not Real.log 0's default. -/
example : negativeLog 0 = ⊤ := by simp [negativeLog]

/-- Sanity: a certain testing outcome has zero score. -/
example : negativeLog 1 = 0 := by simp [negativeLog, QAlgorithms.Papers.Independent.Information100.P63.logTwo]

/-- Sanity: the fidelity convention is the square of the accepted root fidelity. -/
example {I : Type*} [Fintype I] [DecidableEq I] (rho sigma : Matrix I I ℂ) :
    fidelity rho sigma = (rootFidelity rho sigma) ^ 2 := rfl

/-- Sanity: the empty tensor power is scalar one, before restricting rates to positive blocks. -/
example {m : ℕ} {H : MultipartiteSystem m} (rho : MultipartiteOperator H)
    (x y : ProductBasis (copySystem H 0)) : partyTensorPower rho 0 x y = 1 := by
  simp [partyTensorPower, QAlgorithms.Papers.Independent.Information100.P63.tensorPower]

/-- Sanity: grouped tensor entries multiply the entries of the two actual input matrices. -/
example {m : ℕ} {H J : MultipartiteSystem m} (rho : MultipartiteOperator H) (sigma : MultipartiteOperator J)
    (x y : ProductBasis (tensorSystem H J)) :
    partyTensor rho sigma x y = rho (fun i => (x i).1) (fun i => (y i).1) *
      sigma (fun i => (x i).2) (fun i => (y i).2) := rfl

/-- Sanity: unit MES rank has zero resource cost. -/
example : logTwo ((1 : ℕ+) : ℕ) = 0 := by simp [QAlgorithms.Papers.Independent.Information100.P63.logTwo]

/-- Sanity: the rank-one MES has its sole matrix entry equal to one. -/
example (m : ℕ) (x y : ProductBasis (resourceSystem m 1)) : mes m 1 x y = 1 := by
  have coordZero : ∀ z : ProductBasis (resourceSystem m 1), ∀ i : Fin (m + 2), (z i).val = 0 := by
    intro z i
    have hz := (z i).isLt
    change (z i).val < (if i.val < 2 then (1 : ℕ) else 1) at hz
    split_ifs at hz <;> omega
  simp [mes, coordZero]

/-- Sanity: the zero effect is a genuine two-outcome test. -/
example {m : ℕ} (H : MultipartiteSystem m) : IsEffect (0 : MultipartiteOperator H) := by
  exact ⟨Matrix.PosSemidef.zero, by simpa using (Matrix.PosSemidef.one :
    (1 : MultipartiteOperator H).PosSemidef)⟩

end QAlgorithms.Papers.Independent.Advance50.P09


