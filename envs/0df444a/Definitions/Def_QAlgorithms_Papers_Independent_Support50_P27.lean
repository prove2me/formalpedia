-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P27
-- name    : QAlgorithms_Papers_Independent_Support50_P27
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T21:08:26.018488+00:00
-- url     : https://prove2.me/theorems/b9e9c021-8cc0-43c9-8a08-1dce10219e51
-- title:
--   Definitions for The Universal Composable Security of Quantum Key Distribution
-- statement:
--   The objects the formalized statements of *The Universal Composable Security of Quantum Key Distribution* (arXiv:quant-ph/0409078) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `idealPairProb`: PDF p.6, Eq.(2): equal uniform keys, including the unique empty key at m=0.
--   - `KeyData`: PDF pp.5--6,9--10: conditional output data at one security parameter and one arbitrary attack. L is a finite output-register bound, not an assumed rate. Every branch is normalized, even at null length/key outcomes; its arbitrary normalized representative remains weighted by the actual length/key probability. No relation between a null-outcome representative and an execution is assumed.
--   - `diagonalEnsemble`: PDF pp.12--13 and Appendix p.18: F_m is the UNIFORM diagonal ensemble, not the actual-prior ensemble stored in branch. Null actual diagonal outcomes still occur here with probability 2^(-m).
--   - `diagonalMean`: PDF p.10, Eq.(14): the uniform-diagonal mean rho_bar_m, computed from F_m.
--   - `actualEveMean`: PDF p.10, Eq.(8): the actual Eve marginal rho_tilde_m. This generally differs from diagonalMean.
--   - `idealBranch`: PDF p.10, Eq.(9): the ideal conditional output ensemble. A fresh uniform identical key is independent of Eve conditional on the public length; Eve keeps the ACTUAL marginal of the fake run, whose key is discarded. This describes that output ensemble, without claiming an operational circuit simulator.
--   - `equalityUniformityDefect`: PDF p.6, Eq.(3): full classical l1 defect, with NO factor one half.
--   - `KeyPairLabel`: PDF pp.9--10: classical output labels retain both equal-length keys. The length is recorded once, since both key lengths agree.
--   - `hybridWeight`: PDF p.10, Eqs.(12),(13): joint weight of a public length and ideal key pair.
--   - `firstHybrid`: PDF p.10, Eq.(12): rho_qi1 retains Eve's diagonal conditional states. The auxiliary choice off the equal-key support is multiplied by zero.
--   - `secondHybrid`: PDF p.10, Eq.(13): rho_qi2 uses the uniform-diagonal Eve mean, not the actual Eve marginal of Eq.(9).
--   - `composablePrivacy`: PDF p.11, Eq.(15): one half the weighted UNIFORM-diagonal average of full trace norms. For these classical blocks it equals one half the first/second-hybrid trace norm. It is not an actual-prior privacy measure.
--   - `maxKeyLength`: PDF pp.12--13: the largest positive-probability key length. The finite maximum is zero for an all-abort distribution. Normalization of lengthProb excludes an empty positive-probability support.
--   - `diagonalAccessible`: PDF pp.12--13: weighted accessible information of F_m, in bits. This is deliberately NOT called the source's actual-prior usual privacy.
--   - `diagonalHolevo`: PDF p.13, Eq.(18): weighted Holevo information of F_m, in bits. Accepted ensembleInformation uses S(rho)=-Tr(rho log_2 rho).
--   - `shannonDistinguishability`: PDF p.12 and Appendix p.17: fair-binary Shannon distinguishability, in bits. On normalized density operators the accessible-information supremum is nonempty and bounded by one; it is not a supremum over arbitrary real scores.
-- source:
--   The Universal Composable Security of Quantum Key Distribution, arXiv:quant-ph/0409078v1, https://arxiv.org/abs/quant-ph/0409078v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

/-!
Finite information-theoretic statements from quant-ph/0409078v1.
All page references are PDF pages. Operational circuit statements and disputed
source implications are deferred in this unit's HARD.md and GAPS.json.
The accepted Dependency50.P07 ensemble definitions, Dependency50.P24 key-pair
alphabet and Dependency50.P47 cq matrix are reused under the independent-paper
workflow. No unreviewed chunk is imported.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P27

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P07
  (CQData ensembleMean ensembleInformation accessibleInformation)
open QAlgorithms.Papers.Independent.Dependency50.P24 (Key)
open QAlgorithms.Papers.Independent.Dependency50.P47 (cqMatrix)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.6, Eq.(2): equal uniform keys, including the unique empty key at m=0. -/
def idealPairProb (m : ℕ) (z : Key (2 ^ m)) : ℝ :=
  if z.1 = z.2 then ((2 : ℝ) ^ m)⁻¹ else 0

/-- PDF pp.5--6,9--10: conditional output data at one security parameter and
one arbitrary attack. L is a finite output-register bound, not an assumed rate.
Every branch is normalized, even at null length/key outcomes; its arbitrary
normalized representative remains weighted by the actual length/key probability.
No relation between a null-outcome representative and an execution is assumed. -/
structure KeyData (L : ℕ) (E : Type) [Fintype E] where
  lengthProb : Fin (L + 1) → ℝ
  lengthNonnegative : ∀ m, 0 ≤ lengthProb m
  lengthNormalized : (∑ m, lengthProb m) = 1
  branch : (m : Fin (L + 1)) → CQData (Key (2 ^ m.val)) E
  branchValid : ∀ m, (branch m).Valid

/-- PDF pp.12--13 and Appendix p.18: F_m is the UNIFORM diagonal ensemble,
not the actual-prior ensemble stored in branch. Null actual diagonal outcomes
still occur here with probability 2^(-m). -/
def diagonalEnsemble {L : ℕ} {E : Type} [Fintype E]
    (D : KeyData L E) (m : Fin (L + 1)) : CQData (Fin (2 ^ m.val)) E where
  prob := fun _ => ((2 : ℝ) ^ m.val)⁻¹
  state := fun k => (D.branch m).state (k, k)

/-- PDF p.10, Eq.(14): the uniform-diagonal mean rho_bar_m, computed from F_m. -/
def diagonalMean {L : ℕ} {E : Type} [Fintype E]
    (D : KeyData L E) (m : Fin (L + 1)) : Matrix E E ℂ :=
  ensembleMean (diagonalEnsemble D m)

/-- PDF p.10, Eq.(8): the actual Eve marginal rho_tilde_m.
This generally differs from diagonalMean. -/
def actualEveMean {L : ℕ} {E : Type} [Fintype E]
    (D : KeyData L E) (m : Fin (L + 1)) : Matrix E E ℂ :=
  ensembleMean (D.branch m)

/-- PDF p.10, Eq.(9): the ideal conditional output ensemble. A fresh uniform
identical key is independent of Eve conditional on the public length; Eve keeps
the ACTUAL marginal of the fake run, whose key is discarded. This describes
that output ensemble, without claiming an operational circuit simulator. -/
def idealBranch {L : ℕ} {E : Type} [Fintype E]
    (D : KeyData L E) (m : Fin (L + 1)) : CQData (Key (2 ^ m.val)) E where
  prob := idealPairProb m.val
  state := fun _ => actualEveMean D m

/-- PDF p.6, Eq.(3): full classical l1 defect, with NO factor one half. -/
def equalityUniformityDefect {L : ℕ} {E : Type} (w : Fin (L + 1) → ℝ)
    (B : (m : Fin (L + 1)) → CQData (Key (2 ^ m.val)) E) : ℝ :=
  ∑ m, w m * ∑ z, |idealPairProb m.val z - (B m).prob z|

/-- PDF pp.9--10: classical output labels retain both equal-length keys.
The length is recorded once, since both key lengths agree. -/
abbrev KeyPairLabel (L : ℕ) :=
  Sigma (fun m : Fin (L + 1) => Key (2 ^ m.val))

/-- PDF p.10, Eqs.(12),(13): joint weight of a public length and ideal key pair. -/
def hybridWeight {L : ℕ} {E : Type} [Fintype E]
    (D : KeyData L E) (z : KeyPairLabel L) : ℝ :=
  D.lengthProb z.1 * idealPairProb z.1.val z.2

/-- PDF p.10, Eq.(12): rho_qi1 retains Eve's diagonal conditional states.
The auxiliary choice off the equal-key support is multiplied by zero. -/
def firstHybrid {L : ℕ} {E : Type} [Fintype E] (D : KeyData L E) :
    Matrix (KeyPairLabel L × E) (KeyPairLabel L × E) ℂ :=
  cqMatrix (hybridWeight D) (fun z => (D.branch z.1).state (z.2.1, z.2.1)) id

/-- PDF p.10, Eq.(13): rho_qi2 uses the uniform-diagonal Eve mean,
not the actual Eve marginal of Eq.(9). -/
def secondHybrid {L : ℕ} {E : Type} [Fintype E] (D : KeyData L E) :
    Matrix (KeyPairLabel L × E) (KeyPairLabel L × E) ℂ :=
  cqMatrix (hybridWeight D) (fun z => diagonalMean D z.1) id

/-- PDF p.11, Eq.(15): one half the weighted UNIFORM-diagonal average
of full trace norms. For these classical blocks it equals one half the
first/second-hybrid trace norm. It is not an actual-prior privacy measure. -/
def composablePrivacy {L : ℕ} {E : Type} [Fintype E] (D : KeyData L E) : ℝ :=
  (∑ m, D.lengthProb m * ((2 : ℝ) ^ m.val)⁻¹ *
    ∑ k : Fin (2 ^ m.val), traceNorm ((D.branch m).state (k, k) - diagonalMean D m)) / 2

/-- PDF pp.12--13: the largest positive-probability key length.
The finite maximum is zero for an all-abort distribution. Normalization of
lengthProb excludes an empty positive-probability support. -/
def maxKeyLength {L : ℕ} {E : Type} [Fintype E] (D : KeyData L E) : ℕ :=
  (Finset.univ.filter (fun m => 0 < D.lengthProb m)).sup Fin.val

/-- PDF pp.12--13: weighted accessible information of F_m, in bits.
This is deliberately NOT called the source's actual-prior usual privacy. -/
def diagonalAccessible {L : ℕ} {E : Type} [Fintype E] (D : KeyData L E) : ℝ :=
  ∑ m, D.lengthProb m * accessibleInformation (diagonalEnsemble D m)

/-- PDF p.13, Eq.(18): weighted Holevo information of F_m, in bits.
Accepted ensembleInformation uses S(rho)=-Tr(rho log_2 rho). -/
def diagonalHolevo {L : ℕ} {E : Type} [Fintype E] (D : KeyData L E) : ℝ :=
  ∑ m, D.lengthProb m * ensembleInformation (diagonalEnsemble D m)

/-- PDF p.12 and Appendix p.17: fair-binary Shannon distinguishability, in bits.
On normalized density operators the accessible-information supremum is nonempty
and bounded by one; it is not a supremum over arbitrary real scores. -/
def shannonDistinguishability {E : Type} [Fintype E]
    (rho0 rho1 : Matrix E E ℂ) : ℝ :=
  accessibleInformation ({
    prob := fun _ : Bool => (1 / 2 : ℝ)
    state := fun b => if b then rho1 else rho0
  } : CQData Bool E)

/-- The abort branch has exactly the unique pair of empty keys (PDF p.6). -/
example (a b : Fin (2 ^ 0)) : idealPairProb 0 (a, b) = 1 := by
  have h : a = b := by
    apply Fin.ext
    omega
  simp [idealPairProb, h]

/-- Unequal keys receive zero probability (PDF p.6). -/
example (m : ℕ) (a b : Fin (2 ^ m)) (h : a ≠ b) : idealPairProb m (a, b) = 0 := by
  simp [idealPairProb, h]

/-- The first hybrid really retains rho_E,k,k, including at null actual keys. -/
example {L : ℕ} {E : Type} [Fintype E] (D : KeyData L E)
    (m : Fin (L + 1)) (k : Fin (2 ^ m.val)) (e f : E) :
    firstHybrid D ((⟨m, (k, k)⟩ : KeyPairLabel L), e)
      ((⟨m, (k, k)⟩ : KeyPairLabel L), f) =
      ((D.lengthProb m * ((2 : ℝ) ^ m.val)⁻¹ : ℝ) : ℂ) *
        (D.branch m).state (k, k) e f := by
  simp [firstHybrid, cqMatrix, hybridWeight, idealPairProb]

/-- The ideal conditional Eve state is independent of BOTH key outputs (PDF p.10). -/
example {L : ℕ} {E : Type} [Fintype E] (D : KeyData L E)
    (m : Fin (L + 1)) (z : Key (2 ^ m.val)) :
    (idealBranch D m).state z = actualEveMean D m := by
  rfl

/-- A one-dimensional all-abort execution is admissible; the output-data
hypotheses have a concrete inhabitant at the smallest length/register sizes. -/
example : Nonempty (KeyData 0 (Fin 1)) := by
  refine ⟨{
    lengthProb := fun _ => 1
    lengthNonnegative := by intro m; norm_num
    lengthNormalized := by simp
    branch := fun _ => {
      prob := fun _ => 1
      state := fun _ => 1 }
    branchValid := ?_ }⟩
  intro m
  have hm : m.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ m.isLt)
  refine ⟨?_, ?_, ?_⟩
  · intro z
    norm_num
  · simp [Key, hm]
  · intro z
    exact ⟨Matrix.PosSemidef.one, by simp [Matrix.trace]⟩

end QAlgorithms.Papers.Independent.Support50.P27


