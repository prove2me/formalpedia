-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P90
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P90
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T06:18:42.307861+00:00
-- url     : https://prove2.me/theorems/ff08a0db-6a1c-4b42-922a-92ebefd2aeda
-- title:
--   Definitions for Irreversibility of Asymptotic Entanglement Manipulation Under Quantum Operations Completely Preserving Positivity of Partial Transpose
-- statement:
--   The objects the formalized statements of *Irreversibility of Asymptotic Entanglement Manipulation Under Quantum Operations Completely Preserving Positivity of Partial Transpose* (arXiv:1606.09421) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `pptRelativeEntropy`: PDF p.2: PPT-relative entropy in bits, with extended Umegaki entropy. Support failure in relativeEntropy gives +infinity, including singular inputs.
--   - `regularizedPptRelativeEntropy`: PDF p.2: infimum over positive tensor powers; n=0 is never divided by.
--   - `regularizedRains`: PDF p.2: regularized Rains bound, using the independent accepted Rains cone.
--   - `preparationRate`: PDF pp.1--2: operational dilution at rate r. The input target(2^m) is m standard Bell pairs in their Schmidt product basis. All sufficiently large positive n admit consumption at most n(r+delta) and error at most epsilon. A full trace norm is used; its scale does not change vanishing-error rates.
--   - `asymptoticEntanglementCost`: PDF pp.1--2: infimum of operational Bell-pair consumption rates. Empty rate sets give +infinity, not an artificial real zero. On the theorem's finite-dimensional density inputs the value is finite and nonnegative.
--   - `loccDistillationRate`: PDF pp.1--2,5: operational two-way LOCC Bell-pair yield, with all branches retained and arbitrarily small error. No bounded number of rounds is imposed.
--   - `loccDistillable`: PDF pp.1--2,5: supremum of vanishing-error LOCC distillation rates.
--   - `etaFeasible`: PDF p.3, Eq.(4): both support sandwich inequalities, in Loewner order.
--   - `supportEta`: PDF p.3, Eq.(4): infimum of the partially transposed spectral norm over the support sandwich. For a density matrix the set is nonempty and its minimum is strictly positive; eta_sdp_duality below explicitly includes this fact and attainment.
--   - `etaEntanglement`: PDF pp.3,6: the additive support bound in bits. Used only for normalized states, whose nonzero support ensures supportEta>0, so log(0) is never a physical value.
--   - `etaPrimalFeasible`: PDF p.6, Eq.(12): primal SDP with two two-sided operator sandwiches.
--   - `etaPrimal`: PDF p.6, Eq.(12): primal value, defined independently of the dual.
--   - `etaDualFeasible`: PDF p.6, Eq.(13): four PSD dual variables and the printed two constraints.
--   - `etaDualObjective`: PDF p.6, Eq.(13): real trace pairing with the support projector.
--   - `etaDual`: PDF p.6, Eq.(13): dual supremum, not defined to equal the primal.
--   - `supportOverlap`: PDF pp.3,7, Eq.(16): PPT-state overlap with the actual support projection.
--   - `supportDualFeasible`: PDF p.7, Eqs.(16),(18): exactly the two one-sided constraints.
--   - `supportDual`: PDF p.7, Eq.(16): one-sided dual infimum, independently defined.
--   - `wangDuanBound`: PDF p.4: E_W, the improved logarithmic-negativity upper bound from Ref.[30]. X>=rho is Loewner order; no normalization of X is imposed. On density inputs traceNorm(gamma X)>=Tr X>=1, so logarithms have positive arguments.
--   - `antisymmetricSupported`: PDF pp.1--2,7: range contained in the two-qutrit antisymmetric subspace. Each column has swap eigenvalue -1, which is exactly that range inclusion.
--   - `stateRank`: PDF pp.1--2: rank is the complex dimension of the matrix's linear-map range.
--   - `antisymmetricKet`: PDF p.2: the normalized antisymmetric ket on basis coordinates 0 and j.
--   - `rhoV`: PDF p.2: rho_v is the specified equally weighted mixture, not a free state.
--   - `exteriorKet`: PDF pp.4,7: arbitrary complex exterior-product spectral vector. Only its unit norm and orthogonality to u1 are assumed in Proposition 5.
--   - `alphaKet`: PDF p.4: the two disjoint-support unit vectors in the alpha family.
--   - `alphaState`: PDF pp.4--5: rho^(alpha); theorems use the exact interval [21/50,1/2].
-- source:
--   Irreversibility of Asymptotic Entanglement Manipulation Under Quantum Operations Completely Preserving Positivity of Partial Transpose, arXiv:1606.09421v3, https://arxiv.org/abs/1606.09421v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P36
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06

/-!
arXiv:1606.09421v3 (Wang--Duan), PDF pp.1--7. All matrices use fixed
orthonormal product bases. Only pinned accepted-library modules are imported;
the independent-paper workflow permits their reuse. New objects stay here.
The source's PPT class is completely PPT-preserving CPTP, and its operational
currency is the normalized Bell pair. Rates use deterministic unconditional
outputs and vanishing trace-norm error (equivalently, fidelity tending to one).
No assertion is made about the separable infinite-dimensional interfaces in
the motivating supporting-paper gap list.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P90

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms
open QAlgorithms.Papers.Independent.Dependency50.P36
  (relativeEntropy rains target canonicalMatrix allowed pptDistillable)
open QAlgorithms.Papers.Independent.Information100.P04 (gamma copies IsPPT)
open QAlgorithms.Papers.Independent.Next46.P42 (regroupProduct)
open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)
open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)
open QAlgorithms.Papers.Independent.Gap48.P32 (antisymmetricQutrit)

/-- PDF p.2: PPT-relative entropy in bits, with extended Umegaki entropy.
Support failure in relativeEntropy gives +infinity, including singular inputs. -/
def pptRelativeEntropy {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  sInf {e | ∃ sigma : Matrix (A × B) (A × B) ℂ,
    IsPPT sigma ∧ e = relativeEntropy rho sigma}

/-- PDF p.2: infimum over positive tensor powers; n=0 is never divided by. -/
def regularizedPptRelativeEntropy {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  ⨅ n : ℕ, pptRelativeEntropy (copies rho (n+1)) / ((n+1 : ℕ) : EReal)

/-- PDF p.2: regularized Rains bound, using the independent accepted Rains cone. -/
def regularizedRains {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  ⨅ n : ℕ, rains (copies rho (n+1)) / ((n+1 : ℕ) : EReal)

/-- PDF pp.1--2: operational dilution at rate r. The input target(2^m) is m
standard Bell pairs in their Schmidt product basis. All sufficiently large
positive n admit consumption at most n(r+delta) and error at most epsilon.
A full trace norm is used; its scale does not change vanishing-error rates. -/
def preparationRate {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (locc : Bool)
    (rho : Matrix (A × B) (A × B) ℂ) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ epsilon > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → 0 < n → ∃ m : ℕ,
      (m : ℝ) ≤ (n : ℝ) * (r + delta) ∧
      ∃ Phi : Superop (Fin (2^m) × Fin (2^m))
        (Fin (Fintype.card (Fin n → A)) × Fin (Fintype.card (Fin n → B))),
        allowed (if locc then .locc else .ppt) Phi ∧
        traceNorm (Phi (target (2^m)) - canonicalMatrix (copies rho n)) ≤ epsilon

/-- PDF pp.1--2: infimum of operational Bell-pair consumption rates.
Empty rate sets give +infinity, not an artificial real zero. On the theorem's
finite-dimensional density inputs the value is finite and nonnegative. -/
def asymptoticEntanglementCost {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (locc : Bool)
    (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  sInf {e | ∃ r : ℝ, preparationRate locc rho r ∧ e = (r : EReal)}

/-- PDF pp.1--2,5: operational two-way LOCC Bell-pair yield, with all branches
retained and arbitrarily small error. No bounded number of rounds is imposed. -/
def loccDistillationRate {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ epsilon > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → 0 < n → ∃ m : ℕ,
      (n : ℝ) * (r - delta) ≤ (m : ℝ) ∧
      ∃ Phi : Superop
        (Fin (Fintype.card (Fin n → A)) × Fin (Fintype.card (Fin n → B)))
        (Fin (2^m) × Fin (2^m)),
        FiniteLOCC Phi ∧
        traceNorm (Phi (canonicalMatrix (copies rho n)) - target (2^m)) ≤ epsilon

/-- PDF pp.1--2,5: supremum of vanishing-error LOCC distillation rates. -/
def loccDistillable {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  sSup {e | ∃ r : ℝ, loccDistillationRate rho r ∧ e = (r : EReal)}

/-- PDF p.3, Eq.(4): both support sandwich inequalities, in Loewner order. -/
def etaFeasible {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho Y : Matrix (A × B) (A × B) ℂ) : Prop :=
  Y.IsHermitian ∧ (Y - gamma (supportProjection rho)).PosSemidef ∧
    (Y + gamma (supportProjection rho)).PosSemidef

/-- PDF p.3, Eq.(4): infimum of the partially transposed spectral norm over the
support sandwich. For a density matrix the set is nonempty and its minimum is
strictly positive; eta_sdp_duality below explicitly includes this fact and attainment. -/
def supportEta {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sInf {t | ∃ Y, etaFeasible rho Y ∧ t = specNorm (gamma Y)}

/-- PDF pp.3,6: the additive support bound in bits. Used only for normalized
states, whose nonzero support ensures supportEta>0, so log(0) is never a physical value. -/
def etaEntanglement {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  -Real.logb 2 (supportEta rho)

/-- PDF p.6, Eq.(12): primal SDP with two two-sided operator sandwiches. -/
def etaPrimalFeasible {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ)
    (t : ℝ) (Y : Matrix (A × B) (A × B) ℂ) : Prop :=
  etaFeasible rho Y ∧
    ((t : ℂ) • (1 : Matrix (A × B) (A × B) ℂ) - gamma Y).PosSemidef ∧
    (gamma Y + (t : ℂ) • (1 : Matrix (A × B) (A × B) ℂ)).PosSemidef

/-- PDF p.6, Eq.(12): primal value, defined independently of the dual. -/
def etaPrimal {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sInf {t | ∃ Y, etaPrimalFeasible rho t Y}

/-- PDF p.6, Eq.(13): four PSD dual variables and the printed two constraints. -/
def etaDualFeasible {A B : Type} [Fintype A] [Fintype B]
    (V F W X : Matrix (A × B) (A × B) ℂ) : Prop :=
  V.PosSemidef ∧ F.PosSemidef ∧ W.PosSemidef ∧ X.PosSemidef ∧
    (gamma (W-X) - (V+F)).PosSemidef ∧ (W+X).trace.re ≤ 1

/-- PDF p.6, Eq.(13): real trace pairing with the support projector. -/
def etaDualObjective {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (rho V F : Matrix (A × B) (A × B) ℂ) : ℝ :=
  (supportProjection rho * gamma (V-F)).trace.re

/-- PDF p.6, Eq.(13): dual supremum, not defined to equal the primal. -/
def etaDual {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sSup {v | ∃ V F W X : Matrix (A × B) (A × B) ℂ,
    etaDualFeasible V F W X ∧ v = etaDualObjective rho V F}

/-- PDF pp.3,7, Eq.(16): PPT-state overlap with the actual support projection. -/
def supportOverlap {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sSup {v | ∃ sigma : Matrix (A × B) (A × B) ℂ,
    IsPPT sigma ∧ v = (supportProjection rho * sigma).trace.re}

/-- PDF p.7, Eqs.(16),(18): exactly the two one-sided constraints. -/
def supportDualFeasible {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ)
    (t : ℝ) (Y : Matrix (A × B) (A × B) ℂ) : Prop :=
  Y.IsHermitian ∧ (Y - gamma (supportProjection rho)).PosSemidef ∧
    ((t : ℂ) • (1 : Matrix (A × B) (A × B) ℂ) - gamma Y).PosSemidef

/-- PDF p.7, Eq.(16): one-sided dual infimum, independently defined. -/
def supportDual {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sInf {t | ∃ Y, supportDualFeasible rho t Y}

/-- PDF p.4: E_W, the improved logarithmic-negativity upper bound from Ref.[30].
X>=rho is Loewner order; no normalization of X is imposed. On density inputs
traceNorm(gamma X)>=Tr X>=1, so logarithms have positive arguments. -/
def wangDuanBound {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sInf {e | ∃ X : Matrix (A × B) (A × B) ℂ,
    X.IsHermitian ∧ (X-rho).PosSemidef ∧ e = Real.logb 2 (traceNorm (gamma X))}

/-- PDF pp.1--2,7: range contained in the two-qutrit antisymmetric subspace.
Each column has swap eigenvalue -1, which is exactly that range inclusion. -/
def antisymmetricSupported (rho : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) : Prop :=
  ∀ i j, rho (i.2,i.1) j = -rho i j

/-- PDF pp.1--2: rank is the complex dimension of the matrix's linear-map range. -/
def stateRank {I : Type} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) : ℕ :=
  Module.finrank ℂ (LinearMap.range rho.mulVecLin)

/-- PDF p.2: the normalized antisymmetric ket on basis coordinates 0 and j. -/
def antisymmetricKet (j : Fin 3) : EuclideanSpace ℂ (Fin 3 × Fin 3) :=
  ((Real.sqrt 2 : ℂ)⁻¹) • (ket (0,j) - ket (j,0))

/-- PDF p.2: rho_v is the specified equally weighted mixture, not a free state. -/
def rhoV : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (1/2 : ℂ) • (pureDensity (antisymmetricKet 1) + pureDensity (antisymmetricKet 2))

/-- PDF pp.4,7: arbitrary complex exterior-product spectral vector. Only its
unit norm and orthogonality to u1 are assumed in Proposition 5. -/
def exteriorKet (a b : EuclideanSpace ℂ (Fin 3)) : EuclideanSpace ℂ (Fin 3 × Fin 3) :=
  WithLp.toLp 2 fun i => (a i.1 * b i.2 - b i.1 * a i.2) / (Real.sqrt 2 : ℂ)

/-- PDF p.4: the two disjoint-support unit vectors in the alpha family. -/
def alphaKet (alpha : ℝ) (j : Fin 3) : EuclideanSpace ℂ (Fin 3 × Fin 3) :=
  (Real.sqrt alpha : ℂ) • ket (0,j) - (Real.sqrt (1-alpha) : ℂ) • ket (j,0)

/-- PDF pp.4--5: rho^(alpha); theorems use the exact interval [21/50,1/2]. -/
def alphaState (alpha : ℝ) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (1/2 : ℂ) • (pureDensity (alphaKet alpha 1) + pureDensity (alphaKet alpha 2))

/-- Product-basis check: Bob's transpose sends |01><12| to |02><11|. -/
example (X : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    gamma X (0,1) (1,2) = X (0,2) (1,1) := rfl

/-- The Bell currency has the correct 00:11 coherence and zero cross-sector weight. -/
example : target 2 (0,0) (1,1) = (1/2 : ℂ) ∧ target 2 (0,1) (0,1) = 0 := by
  norm_num [target]

/-- Zero consumed Bell pairs mean a scalar trace-one state, not a zero matrix. -/
example : target (2^0) (0,0) (0,0) = (1 : ℂ) := by norm_num [target]

/-- The tensor power at block length zero is the scalar identity. -/
example {A B : Type} (rho : Matrix (A × B) (A × B) ℂ)
    (i j : (Fin 0 → A) × (Fin 0 → B)) : copies rho 0 i j = 1 := by simp [copies]

/-- The finite zero state has zero support projection. Physical theorems exclude it. -/
example {I : Type} [Fintype I] [DecidableEq I] :
    supportProjection (0 : Matrix I I ℂ) = 0 := by
  simp [supportProjection, cfc_zero]

/-- The support sandwich orientation is the paper's -Y<=P^TB<=Y. -/
example {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho Y : Matrix (A × B) (A × B) ℂ) (h : etaFeasible rho Y) :
    (Y - gamma (supportProjection rho)).PosSemidef ∧
      (Y + gamma (supportProjection rho)).PosSemidef := ⟨h.2.1,h.2.2⟩

/-- Regrouping keeps both input coherences. -/
example {A B C D : Type} (rho : Matrix (A × B) (A × B) ℂ)
    (sigma : Matrix (C × D) (C × D) ℂ) (a a1 : A) (b b1 : B) (c c1 : C) (d d1 : D) :
    regroupProduct rho sigma ((a,c),(b,d)) ((a1,c1),(b1,d1)) =
      rho (a,b) (a1,b1) * sigma (c,d) (c1,d1) := rfl

/-- Antisymmetric means that equal local factors give the zero exterior vector. -/
example (a : EuclideanSpace ℂ (Fin 3)) : exteriorKet a a = 0 := by
  ext i
  simp [exteriorKet]

/-- The accepted rank-three example is (I-swap)/6, with the correct sign. -/
example : antisymmetricQutrit (0,1) (1,0) = -(1/6 : ℂ) := by
  norm_num [antisymmetricQutrit]

end QAlgorithms.Papers.Independent.Intakethird100.P90


