-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P25
-- name    : QAlgorithms_Papers_Independent_Frontier30_P25
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T18:38:17.533672+00:00
-- url     : https://prove2.me/theorems/9028492b-204a-45b5-9902-308e11515efd
-- title:
--   Definitions for Converse bounds for private communication over quantum channels
-- statement:
--   The objects the formalized statements of *Converse bounds for private communication over quantum channels* (arXiv:1602.08898) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `groupAverage`: PDF pp.7,23: group average of a density operator.
--   - `Covariant`: PDF p.7, (2.11): covariance, without an additional one-design hypothesis.
--   - `bellPOVM`: PDF p.36, (A.4): the fixed orbit-Bell POVM on input and Alice's resource share.
--   - `teleportBranch`: PDF p.36, (A.5): unnormalized Bob output, tracing M times (rho tensor omega). All off-diagonal blocks are retained.
--   - `teleportOutput`: PDF p.36: Alice measures M, sends g, and Bob applies V(g). The resource, measurement and corrections are fixed before the input.
--   - `entanglement`: PDF pp.15,21: infimum over all separable states on the stated A:B cut. Extended extrema preserve the infinite value of an empty feasible set.
--   - `channelSandwiched`: PDF p.22, (5.28): channel sandwiched REE, with reference isomorphic to input. The output is computed from a unit pure input, rather than assumed as free data.
--   - `CCQData`: PDF p.37, (B.1): ccq data with uniform K, stochastic p(l|k), and normalized Eve states. Dimension fields allow varying systems in protocol families.
--   - `ccqState`: PDF p.37, (B.1): actual ccq state in coordinates ((K,L),E).
--   - `eveMarginal`: PDF p.37: actual Eve marginal, rather than an arbitrary ideal Eve state.
--   - `keyEveMarginal`: PDF p.37: actual KE marginal after discarding L.
--   - `disagreement`: PDF p.37, (B.2): disagreement probability.
--   - `security`: PDF p.37, (B.3): half the unhalved trace norm of rho_KE minus pi_K tensor rho_E.
-- source:
--   Converse bounds for private communication over quantum channels, arXiv:1602.08898v3, https://arxiv.org/abs/1602.08898v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

/-!
Wilde, Tomamichel and Berta, arXiv:1602.08898v3; citations are PDF pages.
Finite dimensions are arbitrary. Operational and infinite-dimensional interfaces
not completed here are individually deferred in HARD.md. Compilation is pending.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P25

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

-- Pinned accepted definitions; assessments record the domains of equivalence.
open QAlgorithms.Papers.Independent.Dependency50.P09 (OneDesign relativeD sandwichedD)
open QAlgorithms.Papers.Independent.Dependency50.P24 (logBits idealCCQ)
open QAlgorithms.Papers.Independent.Information100.P22 (bell)
open QAlgorithms.Papers.Independent.Information100.P58 (testingD)
open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity privateState privacyTest)

/-- PDF pp.7,23: group average of a density operator. -/
def groupAverage {G I : Type*} [Fintype G] [Fintype I]
    (U : G → Matrix.unitaryGroup I ℂ) (rho : Matrix I I ℂ) : Matrix I I ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, (U g : Matrix I I ℂ) * rho * (U g : Matrix I I ℂ)ᴴ

/-- PDF p.7, (2.11): covariance, without an additional one-design hypothesis. -/
def Covariant {G I B : Type} [Fintype I] [Fintype B]
    (N : Superop I B) (U : G → Matrix.unitaryGroup I ℂ)
    (V : G → Matrix.unitaryGroup B ℂ) : Prop :=
  ∀ g rho, IsDensityMatrix rho →
    N ((U g : Matrix I I ℂ) * rho * (U g : Matrix I I ℂ)ᴴ) =
      (V g : Matrix B B ℂ) * N rho * (V g : Matrix B B ℂ)ᴴ

/-- PDF p.36, (A.4): the fixed orbit-Bell POVM on input and Alice's resource share. -/
def bellPOVM {G I : Type*} [Fintype G] [Fintype I]
    (U : G → Matrix.unitaryGroup I ℂ) : G → Matrix (I × I) (I × I) ℂ :=
  fun g => ((Fintype.card I : ℂ)^2 / (Fintype.card G : ℂ)) •
    (Matrix.kronecker (U g : Matrix I I ℂ) (1 : Matrix I I ℂ) * pureDensity (bell I) *
      (Matrix.kronecker (U g : Matrix I I ℂ) (1 : Matrix I I ℂ))ᴴ)

/-- PDF p.36, (A.5): unnormalized Bob output, tracing M times (rho tensor omega).
All off-diagonal blocks are retained. -/
def teleportBranch {I B : Type*} [Fintype I]
    (M : Matrix (I × I) (I × I) ℂ) (omega : Matrix (I × B) (I × B) ℂ)
    (rho : Matrix I I ℂ) : Matrix B B ℂ :=
  fun b c => ∑ i, ∑ a, ∑ j, ∑ t, M (j,t) (i,a) * rho i j * omega (a,b) (t,c)

/-- PDF p.36: Alice measures M, sends g, and Bob applies V(g).
The resource, measurement and corrections are fixed before the input. -/
def teleportOutput {G I B : Type} [Fintype G] [Fintype I] [Fintype B]
    (M : G → Matrix (I × I) (I × I) ℂ) (V : G → Matrix.unitaryGroup B ℂ)
    (omega : Matrix (I × B) (I × B) ℂ) (rho : Matrix I I ℂ) : Matrix B B ℂ :=
  ∑ g, (V g : Matrix B B ℂ) * teleportBranch (M g) omega rho * (V g : Matrix B B ℂ)ᴴ

/-- PDF pp.15,21: infimum over all separable states on the stated A:B cut.
Extended extrema preserve the infinite value of an empty feasible set. -/
def entanglement {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (D : Matrix (A × B) (A × B) ℂ → Matrix (A × B) (A × B) ℂ → EReal)
    (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  ⨅ sigma : {sigma : Matrix (A × B) (A × B) ℂ //
    QAlgorithms.Entanglement.IsSeparableDensity sigma}, D rho sigma.val

/-- PDF p.22, (5.28): channel sandwiched REE, with reference isomorphic to input.
The output is computed from a unit pure input, rather than assumed as free data. -/
def channelSandwiched {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (alpha : ℝ) (N : Superop A B) : EReal :=
  ⨆ psi : {psi : EuclideanSpace ℂ (A × A) // IsState psi},
    entanglement (sandwichedD alpha) (idTensorSuperop (R := A) N (pureDensity psi.val))

/-- PDF p.37, (B.1): ccq data with uniform K, stochastic p(l|k), and normalized Eve states.
Dimension fields allow varying systems in protocol families. -/
structure CCQData where
  d : ℕ
  d_pos : 0 < d
  e : ℕ
  e_pos : 0 < e
  conditional : Fin d → Fin d → ℝ
  conditional_nonneg : ∀ k l, 0 ≤ conditional k l
  conditional_sum : ∀ k, ∑ l, conditional k l = 1
  eve : Fin d → Fin d → Matrix (Fin e) (Fin e) ℂ
  eve_density : ∀ k l, IsDensityMatrix (eve k l)

/-- PDF p.37, (B.1): actual ccq state in coordinates ((K,L),E). -/
def ccqState (c : CCQData) : Matrix ((Fin c.d × Fin c.d) × Fin c.e)
    ((Fin c.d × Fin c.d) × Fin c.e) ℂ :=
  fun x y => if x.1 = y.1 then
    ((c.d : ℂ)⁻¹ * (c.conditional x.1.1 x.1.2 : ℂ)) * c.eve x.1.1 x.1.2 x.2 y.2 else 0

/-- PDF p.37: actual Eve marginal, rather than an arbitrary ideal Eve state. -/
def eveMarginal (c : CCQData) : Matrix (Fin c.e) (Fin c.e) ℂ := traceLeft (ccqState c)

/-- PDF p.37: actual KE marginal after discarding L. -/
def keyEveMarginal (c : CCQData) : Matrix (Fin c.d × Fin c.e) (Fin c.d × Fin c.e) ℂ :=
  fun x y => ∑ l, ccqState c ((x.1,l),x.2) ((y.1,l),y.2)

/-- PDF p.37, (B.2): disagreement probability. -/
def disagreement (c : CCQData) : ℝ :=
  (c.d : ℝ)⁻¹ * ∑ k, ∑ l, if k ≠ l then c.conditional k l else 0

/-- PDF p.37, (B.3): half the unhalved trace norm of rho_KE minus pi_K tensor rho_E. -/
def security (c : CCQData) : ℝ :=
  traceNorm (keyEveMarginal c -
    Matrix.kronecker ((c.d : ℂ)⁻¹ • (1 : Matrix (Fin c.d) (Fin c.d) ℂ)) (eveMarginal c)) / 2

/-- PDF p.7: zero input yields zero in the unnormalized measurement branch. -/
example {I B : Type*} [Fintype I] (M : Matrix (I × I) (I × I) ℂ)
    (omega : Matrix (I × B) (I × B) ℂ) : teleportBranch M omega 0 = 0 := by
  ext b c
  simp [teleportBranch]

/-- PDF pp.7,23: the group average is linear at the zero operator. -/
example {G I : Type*} [Fintype G] [Fintype I]
    (U : G → Matrix.unitaryGroup I ℂ) : groupAverage U 0 = 0 := by
  simp [groupAverage]

/-- PDF p.37: the actual Eve marginal traces out both key registers. -/
example (c : CCQData) : eveMarginal c = traceLeft (ccqState c) := rfl

/-- PDF p.37: the mixed ideal key has no support on disagreeing key values. -/
example (c : CCQData) (k l : Fin c.d) (a b : Fin c.e) (h : k ≠ l) :
    idealCCQ (eveMarginal c) ((k,l),a) ((k,l),b) = 0 := by simp [idealCCQ, h]

end QAlgorithms.Papers.Independent.Frontier30.P25


