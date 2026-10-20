-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P01
-- name    : QAlgorithms_Papers_Independent_Frontier30_P01
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T17:24:26.516198+00:00
-- url     : https://prove2.me/theorems/9e0caa70-6cfa-4db5-9b31-750d22b954e1
-- title:
--   Definitions for Unifying classical and quantum key distillation
-- statement:
--   The objects the formalized statements of *Unifying classical and quantum key distillation* (arXiv:quant-ph/0608199) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `classicalState`: PDF pp.4,12, Eq.(33): the diagonal density associated with a classical law. Physical uses impose nonnegative weights summing to one.
--   - `qqqVector`: PDF p.12, Eq.(34): the positive-amplitude embedding in the fixed basis. On a probability law this is a unit vector; negative weights are never used.
--   - `intrinsicValues`: PDF p.8, Def.3.4: attainable conditional mutual informations after an arbitrary finite-output CPTP map on E. No measurement-only restriction or output-dimension cap is imposed. The ordering is ((A,B),E).
--   - `intrinsic`: PDF p.8, Def.3.4: quantum intrinsic information. On finite density inputs in positive local dimensions its feasible set is nonempty (identity channel) and bounded below by zero (strong subadditivity).
--   - `IsStochastic`: PDF p.8, Eq.(10): a stochastic channel on Eve's classical alphabet, with the input letter indexing the normalized row.
--   - `processedLaw`: PDF p.8, Eq.(10): joint law after the stochastic processing of E.
--   - `classicalIntrinsicValues`: PDF p.8, Eq.(10): all classical intrinsic-information scores. A stochastic map, rather than an arbitrary decomposition of p, is optimized.
--   - `classicalIntrinsic`: PDF p.8, Eq.(10), and pp.14--15, Theorem 4.3: classical intrinsic information, kept separate from its quantum extension. For probability laws in positive dimensions the score set is nonempty and bounded below by zero.
--   - `EveDetermined`: PDF p.14, Theorem 4.3: only positive-probability (i,j) pairs constrain E; no conditional distribution on a zero-probability pair is formed.
--   - `measureAB`: PDF p.14, following Eq.(39): measure A and B, keeping E quantum.
--   - `CounterIndex`: PDF p.14, Eq.(39): the register order A',((A,B),E).
--   - `counterVector`: PDF p.14, Eq.(39), normalized: the printed expression omits its common factor 1/sqrt(2). Thus the four 00-branch coefficients are sqrt(2)/4 and the two 11-branch coefficients are 1/2. The following displayed mixture in the source has branch probabilities 1/2, fixing this correction.
--   - `plusVector`: PDF p.14: the normalized |+> state on one qubit.
-- source:
--   Unifying classical and quantum key distillation, arXiv:quant-ph/0608199v3, https://arxiv.org/abs/quant-ph/0608199v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34

/-!
Statements from Christandl et al., arXiv:quant-ph/0608199v3.
The operational key-rate nodes are explicitly deferred in this unit's GAPS.json:
no numerical proxy for an evaluated tripartite LOPC key rate is introduced.
All new definitions below are confined to this paper and have complete bodies.
-/

namespace QAlgorithms.Papers.Independent.Frontier30.P01

open scoped Matrix ComplexConjugate

noncomputable section

/-- PDF pp.4,12, Eq.(33): the diagonal density associated with a classical law.
Physical uses impose nonnegative weights summing to one. -/
def classicalState {I : Type} [DecidableEq I] (p : I → ℝ) : Matrix I I ℂ :=
  fun x y => if x = y then (p x : ℂ) else 0

/-- PDF p.12, Eq.(34): the positive-amplitude embedding in the fixed basis.
On a probability law this is a unit vector; negative weights are never used. -/
def qqqVector {I : Type} [Fintype I] (p : I → ℝ) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 fun x => (Real.sqrt (p x) : ℂ)

/-- PDF p.8, Def.3.4: attainable conditional mutual informations after an
arbitrary finite-output CPTP map on E. No measurement-only restriction or
output-dimension cap is imposed. The ordering is ((A,B),E). -/
def intrinsicValues {a b e : ℕ}
    (rho : Matrix ((Fin a × Fin b) × Fin e) ((Fin a × Fin b) × Fin e) ℂ) : Set ℝ :=
  {x | ∃ f : ℕ, 0 < f ∧ ∃ channel : Superop (Fin e) (Fin f),
    IsChannel channel ∧ x = Dependency50.P19.conditionalMutual
      (idTensorSuperop (R := Fin a × Fin b) channel rho)}

/-- PDF p.8, Def.3.4: quantum intrinsic information. On finite density inputs
in positive local dimensions its feasible set is nonempty (identity channel)
and bounded below by zero (strong subadditivity). -/
def intrinsic {a b e : ℕ}
    (rho : Matrix ((Fin a × Fin b) × Fin e) ((Fin a × Fin b) × Fin e) ℂ) : ℝ :=
  sInf (intrinsicValues rho)

/-- PDF p.8, Eq.(10): a stochastic channel on Eve's classical alphabet,
with the input letter indexing the normalized row. -/
def IsStochastic {e f : ℕ} (channel : Fin e → Fin f → ℝ) : Prop :=
  (∀ k l, 0 ≤ channel k l) ∧ ∀ k, ∑ l, channel k l = 1

/-- PDF p.8, Eq.(10): joint law after the stochastic processing of E. -/
def processedLaw {a b e f : ℕ}
    (p : ((Fin a × Fin b) × Fin e) → ℝ) (channel : Fin e → Fin f → ℝ) :
    ((Fin a × Fin b) × Fin f) → ℝ :=
  fun x => ∑ k, p (x.1, k) * channel k x.2

/-- PDF p.8, Eq.(10): all classical intrinsic-information scores. A stochastic
map, rather than an arbitrary decomposition of p, is optimized. -/
def classicalIntrinsicValues {a b e : ℕ}
    (p : ((Fin a × Fin b) × Fin e) → ℝ) : Set ℝ :=
  {x | ∃ f : ℕ, 0 < f ∧ ∃ channel : Fin e → Fin f → ℝ,
    IsStochastic channel ∧ x = Dependency50.P19.conditionalMutual
      (classicalState (processedLaw p channel))}

/-- PDF p.8, Eq.(10), and pp.14--15, Theorem 4.3: classical intrinsic
information, kept separate from its quantum extension. For probability laws
in positive dimensions the score set is nonempty and bounded below by zero. -/
def classicalIntrinsic {a b e : ℕ}
    (p : ((Fin a × Fin b) × Fin e) → ℝ) : ℝ :=
  sInf (classicalIntrinsicValues p)

/-- PDF p.14, Theorem 4.3: only positive-probability (i,j) pairs constrain E;
no conditional distribution on a zero-probability pair is formed. -/
def EveDetermined {a b e : ℕ} (p : ((Fin a × Fin b) × Fin e) → ℝ) : Prop :=
  ∀ i j k l, 0 < p ((i,j),k) → 0 < p ((i,j),l) → k = l

/-- PDF p.14, following Eq.(39): measure A and B, keeping E quantum. -/
def measureAB {a b e : ℕ}
    (rho : Matrix ((Fin a × Fin b) × Fin e) ((Fin a × Fin b) × Fin e) ℂ) :
    Matrix ((Fin a × Fin b) × Fin e) ((Fin a × Fin b) × Fin e) ℂ :=
  fun x y => if x.1 = y.1 then rho x y else 0

/-- PDF p.14, Eq.(39): the register order A',((A,B),E). -/
abbrev CounterIndex := Fin 2 × ((Fin 2 × Fin 2) × Fin 2)

/-- PDF p.14, Eq.(39), normalized: the printed expression omits its common
factor 1/sqrt(2). Thus the four 00-branch coefficients are sqrt(2)/4 and the
two 11-branch coefficients are 1/2. The following displayed mixture in the
source has branch probabilities 1/2, fixing this correction. -/
def counterVector : EuclideanSpace ℂ CounterIndex :=
  WithLp.toLp 2 fun x =>
    if x.2.1 = (0,0) then ((Real.sqrt 2 / 4 : ℝ) : ℂ)
    else if x.2.1 = (1,1) ∧ x.1 = x.2.2 then (1/2 : ℂ) else 0

/-- PDF p.14: the normalized |+> state on one qubit. -/
def plusVector : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 fun _ => ((Real.sqrt 2 / 2 : ℝ) : ℂ)

/-- Sanity: classical embedding has exactly the supplied diagonal. -/
example {I : Type} [DecidableEq I] (p : I → ℝ) (x : I) :
    classicalState p x x = (p x : ℂ) := by simp [classicalState]

/-- Sanity: the one-point probability law has unit embedding coefficient. -/
example : qqqVector (fun _ : Fin 1 => (1 : ℝ)) 0 = 1 := by
  simp [qqqVector]

/-- Sanity: intrinsic-information optimization includes the identity CPTP map. -/
example {a b e : ℕ} (he : 0 < e)
    (rho : Matrix ((Fin a × Fin b) × Fin e) ((Fin a × Fin b) × Fin e) ℂ) :
    Dependency50.P19.conditionalMutual rho ∈ intrinsicValues rho := by
  refine ⟨e, he, (fun X => X), ?_, ?_⟩
  · exact ⟨1, (fun _ => 1), by simp [IsKrausFamily],
      fun X => by simp [krausApply]⟩
  · rfl

/-- Sanity: the one-output classical channel has a normalized row. -/
example (e : ℕ) : IsStochastic (fun (_ : Fin e) (_ : Fin 1) => (1 : ℝ)) := by
  constructor
  · intros; norm_num
  · intro k; simp

/-- Sanity: processing into one output sums over precisely the original E. -/
example {a b e : ℕ} (p : ((Fin a × Fin b) × Fin e) → ℝ) (i : Fin a) (j : Fin b) :
    processedLaw p (fun (_ : Fin e) (_ : Fin 1) => 1) ((i,j),0) =
      ∑ k, p ((i,j),k) := by simp [processedLaw]

/-- Sanity: identity processing is feasible in the classical optimization too. -/
example {a b e : ℕ} (he : 0 < e) (p : ((Fin a × Fin b) × Fin e) → ℝ) :
    Dependency50.P19.conditionalMutual (classicalState p) ∈ classicalIntrinsicValues p := by
  refine ⟨e, he, (fun k l => if k = l then 1 else 0), ?_, ?_⟩
  · constructor
    · intro k l
      change 0 ≤ (if k = l then (1 : ℝ) else 0)
      split_ifs <;> norm_num
    · intro k
      simp
  · have h : processedLaw p (fun k l : Fin e => if k = l then 1 else 0) = p := by
      funext x
      simp [processedLaw]
    rw [h]

/-- Sanity: with one Eve letter, the support promise imposes no restriction. -/
example {a b : ℕ} (p : ((Fin a × Fin b) × Fin 1) → ℝ) : EveDetermined p := by
  intro i j k l hk hl
  exact Subsingleton.elim _ _

/-- Sanity: measuring A,B preserves every E coherence in a fixed A,B block. -/
example {a b e : ℕ}
    (rho : Matrix ((Fin a × Fin b) × Fin e) ((Fin a × Fin b) × Fin e) ℂ)
    (ij : Fin a × Fin b) (k l : Fin e) :
    measureAB rho (ij,k) (ij,l) = rho (ij,k) (ij,l) := by simp [measureAB]

/-- Sanity: full measurement removes coherences between different basis values. -/
example {I : Type} [DecidableEq I] (rho : Matrix I I ℂ) (x y : I) (h : x ≠ y) :
    Information100.P34.dephasing rho x y = 0 := by
  simp [Information100.P34.dephasing, Matrix.diagonal_apply, h]

/-- Sanity: a supported 11 coefficient includes the normalization correction. -/
example : counterVector (0,((1,1),0)) = (1/2 : ℂ) := by
  norm_num [counterVector]

/-- Sanity: both coefficients of |+> agree. -/
example : plusVector 0 = plusVector 1 := rfl

end

end QAlgorithms.Papers.Independent.Frontier30.P01


