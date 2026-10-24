-- Prove2me | Definitions.Def_OAIQWEXF000
-- name    : OAIQWEXF000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T22:02:16.811988+00:00
-- url     : https://prove2.me/theorems/9795c62d-7932-44d4-bb0a-56161acd1420
-- title:
--   OpenAI exact Fourier circuits split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof that exact discrete Fourier transforms have linear circuits of size below $c\,n\log_2 n$, for every $c > 0$, along an unbounded sequence of lengths (`OAI.ExactFourier.main_theorem`, the paper's Theorem 1.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Computability/FourierCircuit` (OpenAI, *Finite tensor savings and exact Fourier circuits*, OpenAI Math Release, September 25, 2026, result family 130, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them are the words of monomial steps and embedded calls and the finite-win statement (`WordStep`, `wordMatrix`, `wordCalls`, `tensorPower`, `FiniteWinStatement`), linear DAGs and their costs, the matrix prices and the comparison packing of the paper's Section 4 (`MonomialMatrix`, `MatrixPrice`), the pivot, triangular, Toeplitz and Taylor matrices (`Pivot.matrix`, `Taylor.matrix`), and the sparse-reflection and graph-reflection objects of Sections 7 and 8 (`SparseReflection.PairTerm`, `GraphReflection.graph`). The bundle also contains the lemmas those definitions use in their bodies.
--
--   The definitions of the published statement (`Circuit`, `fourierMatrix`, `MainStatement` and the rest) are not repeated: the bundle imports them from the published bundle `Def_ExactFourier`. It imports no other bundle of this split.
--
--   Modules: `AmplificationMaster`, `Boundary`, `BoundaryActiveCircuit`, `CascadeLimit`, `CascadeWord`, `CircuitCost`, `CircuitExtensions`, `ClearedCircuit`, `ComparisonRename`, `DiagonalBlocks`, `DisplacementKernel`, `FFTCircuit`, `FiniteSeparation`, `GraphBlocks`, `LinearDAG`, `LiveSectors`, `Main`, `MatrixRelabel`, `MonomialFeedback`, `MonomialTools`, `MultiWord`, `PackedSchedule`, `PairFamilies`, `ParameterAlgebra`, `PiTensor`, `PivotAlgebra`, `PivotJoin`, `PolynomialClearing`, `PortMatrices`, `PositiveReach`, `Prices`, `RationalClearing`, `RawPositive`, `RawWordBound`, `RectStableAlgebra`, `Shears`, `SignedPrice`, `SlotAssembly`, `SparseShear`, `SparseSpectral`, `StreamSeries`, `SumFramed`, `SymmetricLaplacian`, `TensorCostAlgebra`, `TensorTools`, `ToeplitzCross`, `Triangular`, `WordScheduling`, `Words`.
--
--   The theorems of the development that the definitions do not need are proved in the seven solutions of this split: the paper's Theorem 8.3 (`OAI.ExactFourier.finite_win`) from three intermediate statements on matrix prices, the reduction of Section 3 (`OAI.ExactFourier.win_to_fourier`), and `OAI.ExactFourier.main_theorem` from those two. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Finite tensor savings and exact Fourier circuits, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 130; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-tensor-savings-and-exact-Fourier-circuits-September-25-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability/FourierCircuit at commit adc7f12

import Mathlib
import Definitions.Def_ExactFourier

section
-- module Solutions.OAIQW_ExactFourier.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.Words
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier
/-- A permutation matrix times an invertible diagonal matrix, literally P D. -/
def IsMonomial {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) : Prop :=
  ∃ (σ : Equiv.Perm (Fin q)) (d : Fin q → ℂ),
    (∀ j, d j ≠ 0) ∧ ∀ i j, A i j = if i = σ j then d j else 0

/-- A call on an ordered tuple of distinct coordinates; all other values are fixed. -/
noncomputable def embeddedCall {q w : ℕ} (A : Matrix (Fin q) (Fin q) ℂ)
    (e : Fin q ↪ Fin w) : Matrix (Fin w) (Fin w) ℂ := by
  classical
  exact fun u v => (∑ i, ∑ j, if e i = u then (if e j = v then A i j else 0) else 0) +
    if u = v ∧ ¬ ∃ i, e i = u then 1 else 0

/-- Only forward calls to the specified A are allowed. -/
inductive WordStep {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (w : ℕ) where
  | monomial (M : Matrix (Fin w) (Fin w) ℂ) (hM : IsMonomial M)
  | call (e : Fin q ↪ Fin w)

noncomputable def WordStep.matrix {q w : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} :
    WordStep A w → Matrix (Fin w) (Fin w) ℂ
  | .monomial M _ => M
  | .call e => embeddedCall A e

def WordStep.calls {q w : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} : WordStep A w → ℕ
  | .monomial _ _ => 0
  | .call _ => 1

/-- Stored chronologically, so a new step left-multiplies earlier steps. -/
noncomputable def wordMatrix {q w : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (W : List (WordStep A w)) : Matrix (Fin w) (Fin w) ℂ :=
  (W.map WordStep.matrix).reverse.prod

def wordCalls {q w : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (W : List (WordStep A w)) : ℕ := (W.map WordStep.calls).sum

/-- A fixed coordinate relabeling of the ordinary Kronecker tensor power. -/
noncomputable def tensorCoordinates (q b : ℕ) : Fin (q ^ b) ≃ (Fin b → Fin q) := by
  classical
  exact (Equiv.cast (by simp) : Fin (q ^ b) ≃ Fin (Fintype.card (Fin b → Fin q))) |>.trans
    (Fintype.equivFin (Fin b → Fin q)).symm

noncomputable def tensorPower {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (b : ℕ) :
    Matrix (Fin (q ^ b)) (Fin (q ^ b)) ℂ :=
  fun i j => ∏ k : Fin b, A (tensorCoordinates q b i k) (tensorCoordinates q b j k)

def FiniteWinStatement : Prop :=
  ∃ (q : ℕ) (A : Matrix (Fin q) (Fin q) ℂ), IsUnit A ∧ ¬ IsMonomial A ∧
    ∃ b : ℕ, 2 ≤ b ∧ ∃ W : List (WordStep A (q ^ b)),
      wordMatrix W = tensorPower A b ∧ wordCalls W < b * q ^ (b - 1)

end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.Shears
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier

/-- Each internal gate starts at an arbitrary dirty value, and its computed linear
combination is added to that value. The literal zero remains literal zero. -/
def Program.dirtyEval {n : ℕ} : {k : ℕ} → Program n k →
    (Fin n → ℂ) → (Fin k → ℂ) → (Fin (n + 1 + k) → ℂ)
  | 0, .nil, x, _ => Fin.snoc x 0
  | k + 1, .step p g, x, z =>
      let v := p.dirtyEval x (Fin.init z)
      Fin.snoc v (z (Fin.last k) + g.eval v)

structure LinearDAG (n a : ℕ) where
  size : ℕ
  program : Program n size
  outputs : Fin a → Fin (n + 1 + size)

def LinearDAG.eval {n a : ℕ} (C : LinearDAG n a) (x : Fin n → ℂ) : Fin a → ℂ :=
  fun i => C.program.eval x (C.outputs i)

end ExactFourier

namespace ExactFourier

abbrev Shear (ι : Type*) := Matrix.TransvectionStruct ι ℂ

noncomputable def Shear.act {ι : Type*} (t : Shear ι) (v : ι → ℂ) : ι → ℂ := by
  classical
  exact fun i => if i = t.i then v i + t.c * v t.j else v i

noncomputable def runShears {ι : Type*} (W : List (Shear ι)) (v : ι → ℂ) : ι → ℂ :=
  W.foldl (fun v t => t.act v) v

@[simp] theorem runShears_nil {ι : Type*} (v : ι → ℂ) : runShears [] v = v := rfl
@[simp] theorem runShears_cons {ι : Type*} (s : Shear ι) (W : List (Shear ι))
    (v : ι → ℂ) : runShears (s :: W) v = runShears W (s.act v) := rfl
@[simp] theorem runShears_append {ι : Type*} (W V : List (Shear ι)) (v : ι → ℂ) :
    runShears (W ++ V) v = runShears V (runShears W v) := List.foldl_append

@[simp] theorem Shear.act_self {ι : Type*} (s : Shear ι) (v : ι → ℂ) :
    s.act v s.i = v s.i + s.c * v s.j := by simp [Shear.act]

@[simp] theorem Shear.inv_act_act {ι : Type*} (s : Shear ι) (v : ι → ℂ) :
    Shear.act s.inv (s.act v) = v := by
  classical
  funext a
  by_cases h : a = s.i
  · subst a
    simp [Shear.act, Matrix.TransvectionStruct.inv, s.hij.symm]
  · simp [Shear.act, Matrix.TransvectionStruct.inv, h]

noncomputable def reverseShears {ι : Type*} (W : List (Shear ι)) : List (Shear ι) :=
  W.reverse.map Matrix.TransvectionStruct.inv

@[simp] theorem reverseShears_length {ι : Type*} (W : List (Shear ι)) :
    (reverseShears W).length = W.length := by simp [reverseShears]

@[simp] theorem runShears_reverse {ι : Type*} (W : List (Shear ι)) (v : ι → ℂ) :
    runShears (reverseShears W) (runShears W v) = v := by
  induction W generalizing v with
  | nil => rfl
  | cons s W ih =>
      simp only [reverseShears, List.reverse_cons, List.map_append, List.map_singleton,
        runShears_append, runShears_cons, runShears_nil]
      rw [show W.reverse.map Matrix.TransvectionStruct.inv = reverseShears W from rfl,
        ih, Shear.inv_act_act]

/-- `none` is the literal input zero, not a physical workspace coordinate. -/
def readCoord {ι : Type*} (r : Option ι) (v : ι → ℂ) : ℂ := r.elim 0 v

end ExactFourier

namespace ExactFourier

def available {n k : ℕ} (x : Fin n → ℂ) (z : Fin k → ℂ) : Fin (n + 1 + k) → ℂ :=
  Fin.addCases (Fin.snoc x 0) z

def Program.dirtyScratch {n k : ℕ} (p : Program n k)
    (x : Fin n → ℂ) (z : Fin k → ℂ) : Fin k → ℂ :=
  fun i => p.dirtyEval x z (Fin.natAdd (n + 1) i)

@[simp] theorem Program.dirtyScratch_step_cast {n k : ℕ} (p : Program n k)
    (g : Gate (n + 1 + k)) (x : Fin n → ℂ) (z : Fin (k + 1) → ℂ) (i : Fin k) :
    (p.step g).dirtyScratch x z i.castSucc = p.dirtyScratch x (Fin.init z) i := by
  change (Fin.snoc (p.dirtyEval x (Fin.init z)) _ : Fin (n + 1 + k + 1) → ℂ)
    (Fin.castSucc (Fin.natAdd (n + 1) i)) = _
  rw [Fin.snoc_castSucc]
  rfl

@[simp] theorem Program.dirtyScratch_step_last {n k : ℕ} (p : Program n k)
    (g : Gate (n + 1 + k)) (x : Fin n → ℂ) (z : Fin (k + 1) → ℂ) :
    (p.step g).dirtyScratch x z (Fin.last k) =
      z (Fin.last k) + g.eval (p.dirtyEval x (Fin.init z)) := by
  change (Fin.snoc (p.dirtyEval x (Fin.init z)) _ : Fin (n + 1 + k + 1) → ℂ)
    (Fin.last (n + 1 + k)) = _
  rw [Fin.snoc_last]

def replayInputs {ι : Type*} {n : ℕ} (enabled : Bool) (xs : Fin n → ι)
    (v : ι → ℂ) : Fin n → ℂ := fun i => if enabled then v (xs i) else 0

def referenceMap {ι : Type*} {n k : ℕ} (enabled : Bool) (xs : Fin n → ι)
    (zs : Fin k → ι) : Fin (n + 1 + k) → Option ι :=
  Fin.addCases (Fin.snoc (fun i => if enabled then some (xs i) else none) none)
    (fun j => some (zs j))

end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.Prices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ExactFourier

noncomputable def shearMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : List (Shear ι)) : Matrix ι ι ℂ := (W.map Matrix.TransvectionStruct.toMatrix).reverse.prod

/-- Jam the arbitrary dirty memory in an identity summand. The lower-left block
is the designated rectangular map extended by zero on dirty scratch. -/
def replayMatrix {n a k : ℕ} (G : Matrix (Fin a) (Fin n) ℂ) :
    Matrix ((Fin n ⊕ Fin k) ⊕ Fin a) ((Fin n ⊕ Fin k) ⊕ Fin a) ℂ :=
  Matrix.fromBlocks 1 0 (Matrix.fromCols G 0) 1

end ExactFourier

namespace ExactFourier
open scoped Kronecker

/-- Literal permutation-times-invertible-diagonal form on a finite index type. -/
def MonomialMatrix {ι : Type*} [DecidableEq ι] (A : Matrix ι ι ℂ) : Prop :=
  ∃ (σ : Equiv.Perm ι) (d : ι → ℂ),
    (∀ j, d j ≠ 0) ∧ ∀ i j, A i j = if i = σ j then d j else 0

structure MatrixPrice where
  value : ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Matrix ι ι ℂ → ℝ
  nonneg : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ),
    IsUnit A → 0 ≤ value A
  zero_iff : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ),
    IsUnit A → (value A = 0 ↔ MonomialMatrix A)
  reindex : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℂ), IsUnit A →
      value (Matrix.reindex e e A) = value A
  monomial : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (A L R : Matrix ι ι ℂ), IsUnit A → MonomialMatrix L → MonomialMatrix R →
      value (L * A * R) = value A
  mul_le : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ), IsUnit A → IsUnit B → value (A * B) ≤ value A + value B
  tensor : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ), IsUnit A → IsUnit B →
      value (A ⊗ₖ B) = Fintype.card κ * value A + Fintype.card ι * value B
  directSum : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ), IsUnit A → IsUnit B →
      value (Matrix.fromBlocks A 0 0 B) = value A + value B
  inverse : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ),
    IsUnit A → value A⁻¹ = value A
  transpose : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ),
    IsUnit A → value A.transpose = value A
  normalized : value (Matrix.transvection (1 : Fin 2) 0 (1 : ℂ)) = 1

namespace MonomialMatrix

theorem diagonal {ι : Type*} [DecidableEq ι] (d : ι → ℂ) (hd : ∀ i, d i ≠ 0) :
    MonomialMatrix (Matrix.diagonal d) := by
  refine ⟨Equiv.refl ι, d, hd, ?_⟩
  intro i j
  by_cases h : i = j
  · subst j; simp
  · simp [Matrix.diagonal, h]

theorem one {ι : Type*} [DecidableEq ι] : MonomialMatrix (1 : Matrix ι ι ℂ) := by
  simpa using diagonal (fun _ : ι => (1 : ℂ)) (by simp)

end MonomialMatrix

namespace MatrixPrice

@[simp] theorem one (p : MatrixPrice) {ι : Type} [Fintype ι] [DecidableEq ι] :
    p.value (1 : Matrix ι ι ℂ) = 0 :=
  (p.zero_iff 1 isUnit_one).mpr MonomialMatrix.one

theorem transvection_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) (c : ℂ) : IsUnit (Matrix.transvection i j c) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_transvection_of_ne i j hij c]
  exact isUnit_one

/-- An ordered pair and its untouched complement, used for exact identity padding. -/
noncomputable def pairComplement {ι : Type*} (i j : ι) (hij : i ≠ j) :
    (Fin 2 ⊕ {t : ι // t ≠ i ∧ t ≠ j}) ≃ ι := by
  classical
  exact {
    toFun := Sum.elim ![j, i] Subtype.val
    invFun := fun t => if htj : t = j then Sum.inl 0 else
      if hti : t = i then Sum.inl 1 else Sum.inr ⟨t, hti, htj⟩
    left_inv := by
      intro t
      rcases t with a | ⟨t, hti, htj⟩
      · fin_cases a <;> simp [hij]
      · simp [hti, htj]
    right_inv := by
      intro t
      by_cases htj : t = j
      · subst t; simp
      · by_cases hti : t = i
        · subst t; simp [hij]
        · simp [hti, htj] }

@[simp] theorem pairComplement_left₀ {ι : Type*} (i j : ι) (hij : i ≠ j) :
    pairComplement i j hij (Sum.inl 0) = j := rfl

@[simp] theorem pairComplement_left₁ {ι : Type*} (i j : ι) (hij : i ≠ j) :
    pairComplement i j hij (Sum.inl 1) = i := rfl

@[simp] theorem pairComplement_right {ι : Type*} (i j : ι) (hij : i ≠ j)
    (t : {t : ι // t ≠ i ∧ t ≠ j}) : pairComplement i j hij (Sum.inr t) = t := rfl

end MatrixPrice
end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.PortMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe fourierU1 fourierU2

section
namespace ExactFourier
open scoped Kronecker

namespace Reindexed

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

@[simp] theorem symm_apply_apply
    {ι : Type fourierU1} {κ : Type fourierU2} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    Matrix.reindex e.symm e.symm (Matrix.reindex e e A) = A := by
  ext i j
  simp [Matrix.reindex_apply]

@[simp] theorem apply_symm_apply
    {ι : Type fourierU1} {κ : Type fourierU2} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (A : Matrix κ κ ℂ) :
    Matrix.reindex e e (Matrix.reindex e.symm e.symm A) = A := by
  ext i j
  simp [Matrix.reindex_apply]

end Reindexed

namespace OnePort

/-- The shared coordinate is explicitly a single PUnit port, not an unspecified padding block. -/
def splitRight (ι κ : Type*) : ι × (PUnit ⊕ κ) ≃ ι ⊕ (ι × κ) :=
  (Equiv.prodSumDistrib ι PUnit κ).trans
    (Equiv.sumCongr (Equiv.prodPUnit ι) (Equiv.refl (ι × κ)))

def splitLeft (ι κ : Type*) : (ι ⊕ PUnit) × κ ≃ (ι × κ) ⊕ κ :=
  (Equiv.sumProdDistrib ι PUnit κ).trans
    (Equiv.sumCongr (Equiv.refl (ι × κ)) (Equiv.punitProd κ))

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

noncomputable def firstSelected (A : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ) :
    Matrix ((α ⊕ PUnit) × (PUnit ⊕ β)) ((α ⊕ PUnit) × (PUnit ⊕ β)) ℂ :=
  Matrix.reindex (splitRight (α ⊕ PUnit) β).symm (splitRight (α ⊕ PUnit) β).symm
    (Matrix.fromBlocks A 0 0 1)

noncomputable def firstRest (A : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ) :
    Matrix ((α ⊕ PUnit) × (PUnit ⊕ β)) ((α ⊕ PUnit) × (PUnit ⊕ β)) ℂ :=
  Matrix.reindex (splitRight (α ⊕ PUnit) β).symm (splitRight (α ⊕ PUnit) β).symm
    (Matrix.fromBlocks 1 0 0 (A ⊗ₖ (1 : Matrix β β ℂ)))

noncomputable def secondSelected (B : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ) :
    Matrix ((α ⊕ PUnit) × (PUnit ⊕ β)) ((α ⊕ PUnit) × (PUnit ⊕ β)) ℂ :=
  Matrix.reindex (splitLeft α (PUnit ⊕ β)).symm (splitLeft α (PUnit ⊕ β)).symm
    (Matrix.fromBlocks 1 0 0 B)

noncomputable def secondRest (B : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ) :
    Matrix ((α ⊕ PUnit) × (PUnit ⊕ β)) ((α ⊕ PUnit) × (PUnit ⊕ β)) ℂ :=
  Matrix.reindex (splitLeft α (PUnit ⊕ β)).symm (splitLeft α (PUnit ⊕ β)).symm
    (Matrix.fromBlocks ((1 : Matrix α α ℂ) ⊗ₖ B) 0 0 1)

/-- The selected row and column have one shared coordinate. Their complement is
exactly the Cartesian product of the two unshared data sets. -/
def plane : ((α ⊕ PUnit) × (PUnit ⊕ β)) ≃ (((α ⊕ PUnit) ⊕ β) ⊕ (α × β)) where
  toFun
    | (.inl a, .inl _) => .inl (.inl (.inl a))
    | (.inr u, .inl _) => .inl (.inl (.inr u))
    | (.inr _, .inr b) => .inl (.inr b)
    | (.inl a, .inr b) => .inr (a, b)
  invFun
    | .inl (.inl (.inl a)) => (.inl a, .inl PUnit.unit)
    | .inl (.inl (.inr u)) => (.inr u, .inl PUnit.unit)
    | .inl (.inr b) => (.inr PUnit.unit, .inr b)
    | .inr (a, b) => (.inl a, .inr b)
  left_inv := by
    rintro ⟨a | ⟨⟩, ⟨⟩ | b⟩ <;> rfl
  right_inv := by
    rintro (((a | ⟨⟩) | b) | ⟨a, b⟩) <;> rfl

noncomputable def unionFirst (A : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ) :
    Matrix ((α ⊕ PUnit) ⊕ β) ((α ⊕ PUnit) ⊕ β) ℂ := Matrix.fromBlocks A 0 0 1

noncomputable def unionSecond (B : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ) :
    Matrix ((α ⊕ PUnit) ⊕ β) ((α ⊕ PUnit) ⊕ β) ℂ :=
  Matrix.reindex (Equiv.sumAssoc α PUnit β).symm (Equiv.sumAssoc α PUnit β).symm
    (Matrix.fromBlocks 1 0 0 B)

noncomputable def product (A : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ)
    (B : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ) := unionSecond B * unionFirst A

end OnePort
end ExactFourier

namespace ExactFourier

noncomputable def rectangularShear {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (G : Matrix ι κ ℂ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := Matrix.fromBlocks 1 G 0 1

/-- Move the dirty gate memory into a literal identity summand. -/
def replayOrder {n a k : ℕ} : ((Fin a ⊕ Fin n) ⊕ Fin k) ≃ ((Fin n ⊕ Fin k) ⊕ Fin a) where
  toFun := Sum.elim (Sum.elim Sum.inr (Sum.inl ∘ Sum.inl)) (Sum.inl ∘ Sum.inr)
  invFun := Sum.elim (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr) (Sum.inl ∘ Sum.inl)
  left_inv := by rintro ((i | i) | i) <;> rfl
  right_inv := by rintro ((i | i) | i) <;> rfl

end ExactFourier

namespace ExactFourier

noncomputable def lowerShear {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (G : Matrix κ ι ℂ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := Matrix.fromBlocks 1 0 G 1

end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.LinearDAG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier

def Gate.map {w w' : ℕ} (f : Fin w → Fin w') : Gate w → Gate w'
  | .add i j => .add (f i) (f j)
  | .sub i j => .sub (f i) (f j)
  | .scale c i => .scale c (f i)

theorem Gate.eval_map {w w' : ℕ} (f : Fin w → Fin w') (g : Gate w)
    (v : Fin w' → ℂ) : (g.map f).eval v = g.eval (v ∘ f) := by cases g <;> rfl

def appendIndex {n m k l : ℕ} (f : Fin (m + 1) → Fin (n + 1 + k))
    (i : Fin (m + 1 + l)) : Fin (n + 1 + (k + l)) :=
  if h : i.val < m + 1 then ⟨(f ⟨i.val, h⟩).val, by have := (f ⟨i.val, h⟩).isLt; omega⟩
  else ⟨n + 1 + k + (i.val - (m + 1)), by have := i.isLt; omega⟩

def keepIndex {n k l : ℕ} (i : Fin (n + 1 + k)) : Fin (n + 1 + (k + l)) :=
  ⟨i.val, by have := i.isLt; omega⟩

@[simp] theorem appendIndex_last {n m k l : ℕ} (f : Fin (m + 1) → Fin (n + 1 + k)) :
    appendIndex (l := l + 1) f (Fin.last (m + 1 + l)) = Fin.last (n + 1 + (k + l)) := by
  unfold appendIndex
  split_ifs with h
  · have : m + 1 + l < m + 1 := h
    omega
  · apply Fin.ext
    simp only [Fin.val_last]
    omega

@[simp] theorem appendIndex_castSucc {n m k l : ℕ}
    (f : Fin (m + 1) → Fin (n + 1 + k)) (i : Fin (m + 1 + l)) :
    appendIndex (l := l + 1) f i.castSucc = (appendIndex f i).castSucc := by
  unfold appendIndex
  split_ifs <;> first | rfl | (exfalso; simp only [Fin.val_castSucc] at *; contradiction)

@[simp] theorem keepIndex_succ {n k l : ℕ} (i : Fin (n + 1 + k)) :
    keepIndex (l := l + 1) i = (keepIndex (l := l) i).castSucc := rfl

@[simp] theorem keepIndex_zero {n k : ℕ} (i : Fin (n + 1 + k)) :
    keepIndex (l := 0) i = i := rfl

@[simp] theorem appendIndex_zero {n m k : ℕ} (f : Fin (m + 1) → Fin (n + 1 + k))
    (i : Fin (m + 1)) : appendIndex (l := 0) f i = f i := by
  apply Fin.ext
  simp [appendIndex, i.isLt]

def Program.append {n m k : ℕ} (p : Program n k)
    (f : Fin (m + 1) → Fin (n + 1 + k)) : {l : ℕ} → Program m l → Program n (k + l)
  | 0, .nil => p
  | _ + 1, .step q g => .step (p.append f q) (g.map (appendIndex f))

/-- Exact composition: all previous values can be reused without being consumed. -/
noncomputable def LinearDAG.comp {n a b : ℕ} (D : LinearDAG a b) (C : LinearDAG n a) :
    LinearDAG n b where
  size := C.size + D.size
  program := C.program.append (Fin.snoc C.outputs ⟨n, by omega⟩) D.program
  outputs := appendIndex (Fin.snoc C.outputs ⟨n, by omega⟩) ∘ D.outputs

theorem Program.eval_input {n k : ℕ} (p : Program n k) (x : Fin n → ℂ) (j : Fin n) :
    p.eval x ⟨j.val, by have := j.isLt; omega⟩ = x j := by
  induction p with
  | nil => exact Fin.snoc_castSucc _ _ j
  | @step k p g ih =>
      change (Fin.snoc (p.eval x) (g.eval (p.eval x)) : Fin (n + 1 + k + 1) → ℂ)
        (Fin.castSucc (⟨j.val, by have := j.isLt; omega⟩ : Fin (n + 1 + k))) = x j
      rw [Fin.snoc_castSucc, ih]

end ExactFourier

namespace ExactFourier

/-- Index of a newly emitted vector gate. -/
def gateIndex {n k a : ℕ} (i : Fin a) : Fin (n + 1 + (k + a)) :=
  ⟨n + 1 + k + i.val, by have := i.isLt; omega⟩

@[simp] theorem gateIndex_last {n k a : ℕ} :
    gateIndex (n := n) (k := k) (Fin.last a) = Fin.last (n + 1 + (k + a)) := by
  apply Fin.ext
  simp [gateIndex, Nat.add_assoc]

@[simp] theorem gateIndex_castSucc {n k a : ℕ} (i : Fin a) :
    gateIndex (n := n) (k := k) i.castSucc = (gateIndex (n := n) (k := k) i).castSucc := rfl

/-- Emit independent scalar operations, one cost unit per coordinate, with original
operands still available after the whole layer. -/
def Program.emit {n k : ℕ} (p : Program n k) :
    {a : ℕ} → (Fin a → Gate (n + 1 + k)) → Program n (k + a)
  | 0, _ => p
  | a + 1, g => .step (p.emit (g ∘ Fin.castSucc)) ((g (Fin.last a)).map keepIndex)

theorem Program.eval_emit {n k a : ℕ} (p : Program n k)
    (g : Fin a → Gate (n + 1 + k)) (x : Fin n → ℂ) :
    (∀ j, (p.emit g).eval x (keepIndex j) = p.eval x j) ∧
    (∀ i, (p.emit g).eval x (gateIndex i) = (g i).eval (p.eval x)) := by
  induction a with
  | zero =>
      constructor
      · intro j; rfl
      · intro i; exact Fin.elim0 i
  | succ a ih =>
      have ih := ih (g ∘ Fin.castSucc)
      constructor
      · intro j
        simp only [Program.emit, Program.eval, keepIndex_succ, Fin.snoc_castSucc]
        exact ih.1 j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · calc
            _ = (p.emit g).eval x (Fin.last (n + 1 + (k + a))) :=
              congrArg ((p.emit g).eval x) gateIndex_last
            _ = _ := by
              simp only [Program.emit, Program.eval, Nat.add_eq, Fin.snoc_last, Gate.eval_map]
              congr 1
              funext j
              exact ih.1 j
        · simp only [gateIndex_castSucc, Program.emit, Program.eval, Fin.snoc_castSucc]
          exact ih.2 j

/-- Read-only input relabeling and arbitrary fanout are genuinely free. -/
def LinearDAG.wires {n a : ℕ} (f : Fin a → Fin (n + 1)) : LinearDAG n a where
  size := 0
  program := .nil
  outputs := f

@[simp] theorem LinearDAG.eval_wires {n a : ℕ} (f : Fin a → Fin (n + 1))
    (x : Fin n → ℂ) : (LinearDAG.wires f).eval x = fun i => (Fin.snoc x 0 : Fin (n + 1) → ℂ) (f i) := rfl

/-- A rectangular vector layer still charges every scalar gate separately. -/
def LinearDAG.layer {n a : ℕ} (g : Fin a → Gate (n + 1)) : LinearDAG n a where
  size := 0 + a
  program := Program.nil.emit g
  outputs := gateIndex

@[simp] theorem LinearDAG.size_layer {n a : ℕ} (g : Fin a → Gate (n + 1)) :
    (LinearDAG.layer g).size = a := Nat.zero_add _

/-- Append a scaled original input into each existing output accumulator.
The two scalar operations per row are charged even for a zero scalar. -/
def LinearDAG.addColumn {n a : ℕ} (C : LinearDAG n a) (j : Fin n) (c : Fin a → ℂ) :
    LinearDAG n a where
  size := (C.size + a) + a
  program :=
    let p := C.program.emit (fun i => Gate.scale (c i) ⟨j.val, by have := j.isLt; omega⟩)
    p.emit (fun i => Gate.add (keepIndex (C.outputs i)) (gateIndex i))
  outputs := gateIndex

theorem LinearDAG.eval_addColumn {n a : ℕ} (C : LinearDAG n a) (j : Fin n)
    (c : Fin a → ℂ) (x : Fin n → ℂ) :
    (C.addColumn j c).eval x = fun i => C.eval x i + c i * x j := by
  let gs : Fin a → Gate (n + 1 + C.size) := fun i =>
    Gate.scale (c i) ⟨j.val, by have := j.isLt; omega⟩
  have hs := C.program.eval_emit gs x
  have ha := (C.program.emit gs).eval_emit
    (fun i : Fin a => Gate.add (keepIndex (C.outputs i)) (gateIndex i)) x
  funext i
  change (C.program.emit gs |>.emit _).eval x (gateIndex i) = _
  rw [ha.2, Gate.eval, hs.1, hs.2]
  change C.eval x i + c i * C.program.eval x ⟨j.val, by have := j.isLt; omega⟩ = _
  congr 2
  exact C.program.eval_input x j

/-- Direct multiplication: this construction will be used only for the fixed spatial
matrices in the coefficient-boundary comparison, not as a purported FFT saving. -/
def LinearDAG.matrix (n a : ℕ) (G : Matrix (Fin a) (Fin n) ℂ) : LinearDAG n a :=
  (List.finRange n).foldl (fun C j => C.addColumn j (fun i => G i j))
    (LinearDAG.wires (fun _ => Fin.last n))

end ExactFourier

namespace ExactFourier

theorem foldColumns_eval {n a : ℕ} (G : Matrix (Fin a) (Fin n) ℂ)
    (L : List (Fin n)) (C : LinearDAG n a) (x : Fin n → ℂ) (i : Fin a) :
    (L.foldl (fun C j => C.addColumn j (fun r => G r j)) C).eval x i =
      C.eval x i + (L.map (fun j => G i j * x j)).sum := by
  induction L generalizing C with
  | nil => simp
  | cons j L ih =>
      simp only [List.foldl_cons, ih, LinearDAG.eval_addColumn, List.map_cons, List.sum_cons]
      ring

theorem LinearDAG.eval_matrix {n a : ℕ} (G : Matrix (Fin a) (Fin n) ℂ)
    (x : Fin n → ℂ) : (LinearDAG.matrix n a G).eval x = G.mulVec x := by
  funext i
  simp [LinearDAG.matrix, foldColumns_eval, LinearDAG.eval_wires, Matrix.mulVec,
    dotProduct, ← List.ofFn_id, List.map_ofFn, List.sum_ofFn]

end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.TensorTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Exact finite tensor and disjoint-block constructions for the triangular
monotonicity experiment in 05-corners:130–201. -/
namespace ExactFourier
open scoped Kronecker BigOperators
namespace TensorTools

variable {ι κ τ : Type} [Fintype ι] [Fintype κ] [Fintype τ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq τ]

theorem unit_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) (hA : IsUnit A) :
    IsUnit (Matrix.reindex e e A) :=
  hA.map (Matrix.reindexAlgEquiv ℂ ℂ e).toMonoidHom

theorem unit_tensor (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (hA : IsUnit A) (hB : IsUnit B) : IsUnit (A ⊗ₖ B) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_kronecker]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hA).pow _ |>.mul
    (((Matrix.isUnit_iff_isUnit_det _).mp hB).pow _)

def middleEquiv : (ι ⊕ κ) ⊕ τ ≃ (ι ⊕ τ) ⊕ κ where
  toFun := Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr)
  invFun := Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr)
  left_inv := by rintro ((i|k)|t) <;> rfl
  right_inv := by rintro ((i|t)|k) <;> rfl

end TensorTools
end ExactFourier

end

section
/-! Two cell programs sharing only their persistent state space. Unlike the
triangular experiment, no invertibility of the state block is assumed. -/
namespace ExactFourier
open TensorTools
namespace CellJoin
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

abbrev join (X : Matrix (α ⊕ β) (α ⊕ β) ℂ) (Y : Matrix (γ ⊕ β) (γ ⊕ β) ℂ) :
    Matrix ((α ⊕ γ) ⊕ β) ((α ⊕ γ) ⊕ β) ℂ :=
  Matrix.fromBlocks
    (Matrix.fromBlocks X.toBlocks₁₁ 0 (Y.toBlocks₁₂ * X.toBlocks₂₁) Y.toBlocks₁₁)
    (Matrix.fromRows X.toBlocks₁₂ (Y.toBlocks₁₂ * X.toBlocks₂₂))
    (Matrix.fromCols (Y.toBlocks₂₂ * X.toBlocks₂₁) Y.toBlocks₂₁)
    (Y.toBlocks₂₂ * X.toBlocks₂₂)

end CellJoin
end ExactFourier

end

section
namespace ExactFourier.Triangular
open scoped Kronecker BigOperators
open TensorTools

variable {α β σ κ : Type} [Fintype α] [Fintype β] [Fintype σ] [Fintype κ]
  [DecidableEq α] [DecidableEq β] [DecidableEq σ] [DecidableEq κ]

def swapLast : (σ × α) × β ≃ (σ × β) × α where
  toFun x := ((x.1.1,x.2),x.1.2)
  invFun x := ((x.1.1,x.2),x.1.2)
  left_inv := by rintro ⟨⟨s,a⟩,b⟩; rfl
  right_inv := by rintro ⟨⟨s,b⟩,a⟩; rfl

def liftEquiv : ((σ × α) ⊕ κ) × β ≃ ((σ × β) × α) ⊕ (κ × β) :=
  (Equiv.sumProdDistrib _ _ _).trans (Equiv.sumCongr swapLast (Equiv.refl _))

 def oldE (E : Matrix (σ × α) κ ℂ) : Matrix ((σ × β) × α) (κ × β) ℂ :=
   fun i j => E (i.1.1,i.2) j.1 * (1 : Matrix β β ℂ) i.1.2 j.2

 def nextE (E : Matrix (σ × α) κ ℂ) (Y : Matrix κ κ ℂ) (C : Matrix α β ℂ) :
    Matrix (((σ × β) ⊕ κ) × α) (κ × β) ℂ :=
    fun i j => match i.1 with
    | Sum.inl s => E (s.1,i.2) j.1 * (1 : Matrix β β ℂ) s.2 j.2
    | Sum.inr k => Y k j.1 * C i.2 j.2

def mergeEquiv : (((σ × β) × α) ⊕ (κ × α)) ⊕ (κ × β) ≃
    (((σ × β) ⊕ κ) × α) ⊕ (κ × β) :=
  Equiv.sumCongr (Equiv.sumProdDistrib (σ × β) κ α).symm (Equiv.refl _)

end ExactFourier.Triangular

end

section
/-! Whole-row-block compression used in the proof of triangular monotonicity
(05-corners.tex:145–209). Only the block-copy index is changed; individual rows
of a spatial block are never independently mixed. -/
namespace ExactFourier.RowCompression
open scoped BigOperators

section Splitting
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]

/-- A chosen linear right inverse splits a surjection with its kernel. -/
def splitEquiv (f : E →ₗ[K] F) (s : F →ₗ[K] E)
    (hs : f.comp s = LinearMap.id) : E ≃ₗ[K] F × LinearMap.ker f where
  toFun x := (f x, ⟨x-s (f x), by
    change f (x-s (f x)) = 0
    have h := LinearMap.congr_fun hs (f x)
    simpa using sub_eq_zero.mpr h.symm⟩)
  invFun x := s x.1 + x.2
  left_inv x := by simp
  right_inv x := by
    apply Prod.ext
    · have h : f (s x.1) = x.1 := LinearMap.congr_fun hs x.1
      have hx : f (x.2 : E) = 0 := x.2.property
      simp only [map_add, h, hx, add_zero]
    · apply Subtype.ext
      have h : f (s x.1) = x.1 := LinearMap.congr_fun hs x.1
      have hx : f (x.2 : E) = 0 := x.2.property
      simp only [map_add, h, hx, add_zero]
      abel
  map_add' x y := by
    apply Prod.ext
    · exact map_add f x y
    · apply Subtype.ext
      simp only [Prod.snd_add, Submodule.coe_add, map_add]
      abel
  map_smul' c x := by
    apply Prod.ext
    · exact map_smul f c x
    · apply Subtype.ext
      simp [smul_sub]

@[simp] theorem splitEquiv_fst (f : E →ₗ[K] F) (s : F →ₗ[K] E)
    (hs : f.comp s = LinearMap.id) (x : E) : (splitEquiv f s hs x).1 = f x := rfl

end Splitting
end ExactFourier.RowCompression

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.SparseShear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Normalized whole-row-block tensor recursion and its sparse generators.
The change of basis acts only on the call index, as in corner:eq:actual-row-block. -/
namespace ExactFourier.Triangular
open scoped Kronecker BigOperators
open TensorTools
variable {α β σ κ : Type} [Fintype α] [Fintype β] [Fintype σ] [Fintype κ]
  [DecidableEq α] [DecidableEq β] [DecidableEq σ] [DecidableEq κ]

def flat (E : Matrix (σ × α) κ ℂ) : Matrix σ (α × κ) ℂ := fun s j => E (s,j.1) j.2

def liftRows (R : Matrix σ (α × κ) ℂ) (H : Matrix β β ℂ) :
    Matrix (σ × β) (α × (κ × β)) ℂ := fun i j => R i.1 (j.1,j.2.1) * H i.2 j.2.2

def freshRows (T : Matrix α β ℂ) : Matrix κ (α × (κ × β)) ℂ :=
    fun i j => (1 : Matrix κ κ ℂ) i j.2.1 * T j.1 j.2.2

def nextRows (R : Matrix σ (α × κ) ℂ) (T : Matrix α β ℂ) (H : Matrix β β ℂ) :
    Matrix ((σ × β) ⊕ κ) (α × (κ × β)) ℂ :=
    Matrix.fromRows (liftRows R H) (freshRows T)

/-- Number of supported scalar positions. -/
noncomputable def nnz {δ : Type} [Fintype δ] (v : δ → ℂ) : ℕ :=
    (Finset.univ.filter fun i => v i ≠ 0).card

end ExactFourier.Triangular

end

section
namespace ExactFourier.Triangular
open scoped Kronecker BigOperators
open TensorTools

/-- Recursive axis/fiber indexing; no extra workspace is introduced. -/
abbrev Bottom (β : Type) : ℕ → Type
  | 0 => PUnit
  | k+1 => Bottom β k × β

abbrev Calls (β : Type) : ℕ → Type
  | 0 => PEmpty
  | k+1 => (Calls β k × β) ⊕ Bottom β k

@[reducible] noncomputable instance bottomFintype (β : Type) [Fintype β] : (k : ℕ) → Fintype (Bottom β k)
  | 0 => inferInstanceAs (Fintype PUnit)
  | k+1 => letI := bottomFintype β k; inferInstanceAs (Fintype (Bottom β k × β))
@[reducible] noncomputable instance callsFintype (β : Type) [Fintype β] : (k : ℕ) → Fintype (Calls β k)
  | 0 => inferInstanceAs (Fintype PEmpty)
  | k+1 => letI := callsFintype β k; inferInstanceAs (Fintype ((Calls β k × β) ⊕ Bottom β k))
@[reducible] instance bottomDecidableEq (β : Type) [DecidableEq β] : (k : ℕ) → DecidableEq (Bottom β k)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | k+1 => letI := bottomDecidableEq β k; inferInstanceAs (DecidableEq (Bottom β k × β))
@[reducible] instance callsDecidableEq (β : Type) [DecidableEq β] : (k : ℕ) → DecidableEq (Calls β k)
  | 0 => inferInstanceAs (DecidableEq PEmpty)
  | k+1 => letI := callsDecidableEq β k; inferInstanceAs (DecidableEq ((Calls β k × β) ⊕ Bottom β k))

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

@[simp] theorem bottom_card_zero
    {β : Type} [Fintype β] [DecidableEq β] : Fintype.card (Bottom β 0) = 1 := by simp [Bottom]
@[simp] theorem calls_card_zero
    {β : Type} [Fintype β] [DecidableEq β] : Fintype.card (Calls β 0) = 0 := by simp [Calls]
@[simp] theorem bottom_card_succ
    {β : Type} [Fintype β] [DecidableEq β] (k : ℕ) :
    Fintype.card (Bottom β (k+1)) = Fintype.card (Bottom β k) * Fintype.card β := by
  simp only [Bottom, Fintype.card_prod]
@[simp] theorem calls_card_succ
    {β : Type} [Fintype β] [DecidableEq β] (k : ℕ) :
    Fintype.card (Calls β (k+1)) = Fintype.card (Calls β k) * Fintype.card β + Fintype.card (Bottom β k) := by
  simp only [Calls, Fintype.card_sum, Fintype.card_prod]

theorem calls_card_relation (k : ℕ) :
    Fintype.card (Calls β k) * Fintype.card β = k * Fintype.card (Bottom β k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [calls_card_succ, bottom_card_succ]; nlinarith

theorem bottom_card_pos (hβ : 0 < Fintype.card β) (k : ℕ) : 0 < Fintype.card (Bottom β k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [bottom_card_succ]; exact Nat.mul_pos ih hβ

noncomputable def tensorPower (D : Matrix β β ℂ) : (k : ℕ) → Matrix (Bottom β k) (Bottom β k) ℂ
  | 0 => 1
  | k+1 => tensorPower D k ⊗ₖ D
noncomputable def contamination (C : Matrix α β ℂ) (D : Matrix β β ℂ) :
    (k : ℕ) → Matrix (Calls β k × α) (Bottom β k) ℂ
  | 0 => 0
  | k+1 => nextE (contamination C D k) (tensorPower D k) C
noncomputable def generators (C : Matrix α β ℂ) (D : Matrix β β ℂ) :
    (k : ℕ) → Matrix (Calls β k) (α × Bottom β k) ℂ
  | 0 => 0
  | k+1 => nextRows (generators C D k) (C * D⁻¹) 1
noncomputable def rowBasis (D : Matrix β β ℂ) : (k : ℕ) → Matrix (Calls β k) (Calls β k) ℂ
  | 0 => 1
  | k+1 => Matrix.fromBlocks (rowBasis D k ⊗ₖ D) 0 0 1

end ExactFourier.Triangular

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.Triangular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Exact coefficient-basis truncation, as used in the time cascade and feedback
proof on the path to the absent finite-win main theorem. Time comes first. -/

namespace ExactFourier.CoefficientTime
open scoped BigOperators Kronecker

noncomputable def truncMatrix {R : Type*} [Semiring R] (t : ℕ)
    (F : PowerSeries R) : Matrix (Fin t) (Fin t) R :=
  fun a b => if b.val ≤ a.val then PowerSeries.coeff (a.val-b.val) F else 0

@[simp] theorem truncMatrix_one {R : Type*} [Semiring R] (t : ℕ) :
    truncMatrix t (1 : PowerSeries R) = 1 := by
  ext a b
  by_cases h : b.val ≤ a.val
  · simp only [truncMatrix, h, ite_true, PowerSeries.coeff_one, Matrix.one_apply]
    have hh : a.val-b.val = 0 ↔ a=b := by
      constructor
      · intro hh; exact Fin.ext (by omega)
      · intro hh; subst b; omega
    simp only [hh]
  · have hne : a ≠ b := by intro he; subst b; omega
    simp [truncMatrix, h, hne]

@[simp] theorem truncMatrix_zero {R : Type*} [Semiring R] (t : ℕ) :
    truncMatrix t (0 : PowerSeries R) = 0 := by
  ext a b
  simp [truncMatrix]

@[simp] theorem truncMatrix_add {R : Type*} [Semiring R] (t : ℕ)
    (F G : PowerSeries R) : truncMatrix t (F+G) = truncMatrix t F + truncMatrix t G := by
  ext a b
  by_cases h : b.val ≤ a.val <;> simp [truncMatrix, h]

theorem truncMatrix_mul {R : Type*} [Semiring R] (t : ℕ)
    (F G : PowerSeries R) : truncMatrix t (F*G) = truncMatrix t F * truncMatrix t G := by
  classical
  ext a b
  simp only [truncMatrix, Matrix.mul_apply]
  by_cases hab : b.val ≤ a.val
  · rw [ite_eq_left hab, PowerSeries.coeff_mul]
    let S : Finset (Fin t) := Finset.univ.filter (fun k => b.val ≤ k.val ∧ k.val ≤ a.val)
    have hs : (∑ k : Fin t,
        (if k.val ≤ a.val then PowerSeries.coeff (a.val-k.val) F else 0) *
        (if b.val ≤ k.val then PowerSeries.coeff (k.val-b.val) G else 0)) =
        ∑ k ∈ S, PowerSeries.coeff (a.val-k.val) F * PowerSeries.coeff (k.val-b.val) G := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h₁ : k.val ≤ a.val <;> by_cases h₂ : b.val ≤ k.val <;> simp [h₁, h₂]
    rw [hs]
    symm
    apply Finset.sum_bij (fun k _ => (a.val-k.val, k.val-b.val))
    · intro k hk
      have hk' : b.val ≤ k.val ∧ k.val ≤ a.val := (Finset.mem_filter.mp hk).2
      simp only [Finset.HasAntidiagonal.mem_antidiagonal]
      omega
    · intro k hk l hl hkl
      have hk' := (Finset.mem_filter.mp hk).2
      have hl' := (Finset.mem_filter.mp hl).2
      have he := congrArg Prod.snd hkl
      apply Fin.ext
      dsimp at he
      omega
    · intro p hp
      have hp' : p.1+p.2 = a.val-b.val := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have hkt : b.val+p.2 < t := by have := a.isLt; omega
      refine ⟨⟨b.val+p.2, hkt⟩, ?_, ?_⟩
      · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor <;> omega
      · apply Prod.ext
        · change a.val - (b.val + p.2) = p.1; omega
        · change b.val + p.2 - b.val = p.2; omega
    · intro k hk
      rfl
  · rw [ite_eq_right hab]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    by_cases h : k.val ≤ a.val
    · have h' : ¬b.val ≤ k.val := by omega
      simp [h, h']
    · simp [h]

/-- Multiplication modulo z^t in the coefficient basis is a literal ring homomorphism. -/
noncomputable def truncHom {R : Type*} [Semiring R] (t : ℕ) :
    PowerSeries R →+* Matrix (Fin t) (Fin t) R where
  toFun := truncMatrix t
  map_zero' := truncMatrix_zero t
  map_one' := truncMatrix_one t
  map_add' := truncMatrix_add t
  map_mul' := truncMatrix_mul t

noncomputable def blockTruncHom {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℕ) :
    Matrix ι ι (PowerSeries ℂ) →+* Matrix (Fin t × ι) (Fin t × ι) ℂ :=
  (Matrix.reindexRingEquiv ℂ (Equiv.prodComm ι (Fin t))).toRingHom.comp
    ((Matrix.compRingEquiv ι (Fin t) ℂ).toRingHom.comp (truncHom t).mapMatrix)

@[simp] theorem blockTruncHom_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℕ)
    (F : Matrix ι ι (PowerSeries ℂ)) (a b : Fin t × ι) :
    blockTruncHom t F a b =
      if b.1.val ≤ a.1.val then PowerSeries.coeff (a.1.val-b.1.val) (F a.2 b.2) else 0 := rfl

noncomputable def coefficientColumns {ι κ : Type*} (t : ℕ)
    (V : Matrix ι κ (PowerSeries ℂ)) : Matrix (Fin t × ι) κ ℂ :=
  fun a b => PowerSeries.coeff a.1.val (V a.2 b)

/-- The scalar prefix change of basis leaves the suffix literally fixed. Its
prefix-to-suffix block is zero because the convolution is lower triangular. -/
noncomputable def prefixScalar (t T : ℕ) (f : PowerSeries ℂ) :
    Matrix (Fin t) (Fin t) ℂ := fun a b =>
  if a.val < T then truncMatrix t f a b else (1 : Matrix (Fin t) (Fin t) ℂ) a b

@[simp] theorem prefixScalar_one (t T : ℕ) :
    prefixScalar t T 1 = 1 := by
  ext a b
  simp [prefixScalar]

@[simp] theorem prefixScalar_mul (t T : ℕ) (f g : PowerSeries ℂ) :
    prefixScalar t T (f*g) = prefixScalar t T f * prefixScalar t T g := by
  classical
  ext a b
  by_cases ha : a.val < T
  · simp only [prefixScalar, ha, ite_true, Matrix.mul_apply]
    rw [truncMatrix_mul, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkT : k.val < T
    · simp [hkT]
    · have hak : ¬ k.val ≤ a.val := by omega
      simp [hkT, truncMatrix, hak]
  · simp only [prefixScalar, ha, ite_false, Matrix.mul_apply]
    change (1 : Matrix (Fin t) (Fin t) ℂ) a b = ((1 : Matrix (Fin t) (Fin t) ℂ) * prefixScalar t T g) a b
    rw [Matrix.one_mul]
    simp [prefixScalar, ha]

end ExactFourier.CoefficientTime

end

section
namespace ExactFourier
open scoped BigOperators
open TensorTools

def timeSplit (t : ℕ) (α : Type) : (Fin (t+1) × α) ≃ α ⊕ (Fin t × α) where
  toFun x := Fin.cases (Sum.inl x.2) (fun i => Sum.inr (i,x.2)) x.1
  invFun := Sum.elim (fun a => (0,a)) (fun x => (x.1.succ,x.2))
  left_inv := by
    rintro ⟨i,a⟩
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv := by rintro (a|⟨i,a⟩) <;> rfl

end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.StreamSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! The finite-coefficient meaning of the cell transfer H(z). The geometric
resolvent is defined coefficientwise, without assumptions on D. -/
namespace ExactFourier
open scoped BigOperators
namespace CellSeries
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

noncomputable def resolvent (D : Matrix β β ℂ) : Matrix β β (PowerSeries ℂ) :=
  fun i j => PowerSeries.mk (fun m => (D^m) i j)
noncomputable def state (C : Matrix α β ℂ) (D : Matrix β β ℂ) :
    Matrix α β (PowerSeries ℂ) := C.map PowerSeries.C * resolvent D
noncomputable def transfer (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) : Matrix α α (PowerSeries ℂ) :=
  M.map PowerSeries.C + (PowerSeries.X : PowerSeries ℂ) • (state C D * B.map PowerSeries.C)

@[simp] theorem coeff_resolvent (D : Matrix β β ℂ) (n : ℕ) (i j : β) :
    PowerSeries.coeff n (resolvent D i j) = (D^n) i j := by simp [resolvent]
@[simp] theorem coeff_state
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (C : Matrix α β ℂ) (D : Matrix β β ℂ) (n : ℕ) (i : α) (j : β) :
    PowerSeries.coeff n (state C D i j) = (C*D^n) i j := by
  simp [state, Matrix.mul_apply, PowerSeries.coeff_C_mul]
@[simp] theorem coeff_transfer_zero
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (i j : α) :
    PowerSeries.coeff 0 (transfer M C B D i j) = M i j := by
  simp [transfer, Matrix.add_apply, Matrix.smul_apply]
@[simp] theorem coeff_transfer_succ (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (n : ℕ) (i j : α) :
    PowerSeries.coeff (n+1) (transfer M C B D i j) = (C*D^n*B) i j := by
  simp [transfer, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
    PowerSeries.coeff_mul_C]

end CellSeries
end ExactFourier

end

section
/-! Literal finite cell word, one persistent state carried through t fresh data
blocks. All coordinates are allowed arbitrary initial values. -/
namespace ExactFourier
open TensorTools CoefficientTime
open scoped BigOperators
namespace CellStream
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

noncomputable def run (K : Matrix (α ⊕ β) (α ⊕ β) ℂ) : (t : ℕ) →
    Matrix ((Fin t × α) ⊕ β) ((Fin t × α) ⊕ β) ℂ
  | 0 => 1
  | t+1 => Matrix.reindex (Equiv.sumCongr (timeSplit t α).symm (Equiv.refl β))
      (Equiv.sumCongr (timeSplit t α).symm (Equiv.refl β)) (CellJoin.join K (run K t))

variable (M : Matrix α α ℂ) (C : Matrix α β ℂ) (B : Matrix β α ℂ) (D : Matrix β β ℂ)

@[simp] theorem fst_fst
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (C : Matrix α β ℂ) (B : Matrix β α ℂ) (D : Matrix β β ℂ) (t : ℕ) (a b : α) :
    run (Matrix.fromBlocks M C B D) (t+1) (Sum.inl (0,a)) (Sum.inl (0,b)) = M a b := rfl
@[simp] theorem fst_succ
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (C : Matrix α β ℂ) (B : Matrix β α ℂ) (D : Matrix β β ℂ) (t : ℕ) (a b : α) (j : Fin t) :
    run (Matrix.fromBlocks M C B D) (t+1) (Sum.inl (0,a)) (Sum.inl (j.succ,b)) = 0 := rfl
@[simp] theorem succ_succ
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (C : Matrix α β ℂ) (B : Matrix β α ℂ) (D : Matrix β β ℂ) (t : ℕ) (a b : α) (i j : Fin t) :
    run (Matrix.fromBlocks M C B D) (t+1) (Sum.inl (i.succ,a)) (Sum.inl (j.succ,b)) =
      run (Matrix.fromBlocks M C B D) t (Sum.inl (i,a)) (Sum.inl (j,b)) := rfl
@[simp] theorem succ_fst
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (C : Matrix α β ℂ) (B : Matrix β α ℂ) (D : Matrix β β ℂ) (t : ℕ) (a b : α) (i : Fin t) :
    run (Matrix.fromBlocks M C B D) (t+1) (Sum.inl (i.succ,a)) (Sum.inl (0,b)) =
      ∑ w, run (Matrix.fromBlocks M C B D) t (Sum.inl (i,a)) (Sum.inr w) * B w b := rfl
@[simp] theorem fst_state
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (C : Matrix α β ℂ) (B : Matrix β α ℂ) (D : Matrix β β ℂ) (t : ℕ) (a : α) (b : β) :
    run (Matrix.fromBlocks M C B D) (t+1) (Sum.inl (0,a)) (Sum.inr b) = C a b := rfl
@[simp] theorem succ_state
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (C : Matrix α β ℂ) (B : Matrix β α ℂ) (D : Matrix β β ℂ) (t : ℕ) (a : α) (b : β) (i : Fin t) :
    run (Matrix.fromBlocks M C B D) (t+1) (Sum.inl (i.succ,a)) (Sum.inr b) =
      ∑ w, run (Matrix.fromBlocks M C B D) t (Sum.inl (i,a)) (Sum.inr w) * D w b := rfl

end CellStream
end ExactFourier

end

section
/-! Sequential tensor-axis programs share the full data space but have disjoint
persistent state spaces. The ordering of all noncommuting factors is explicit. -/
namespace ExactFourier
open TensorTools
namespace AxisJoin
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def rightOrder : (α ⊕ γ) ⊕ β ≃ α ⊕ (β ⊕ γ) :=
  (middleEquiv (ι := α) (κ := γ) (τ := β)).trans (Equiv.sumAssoc α β γ)

abbrev join (X : Matrix (α ⊕ β) (α ⊕ β) ℂ) (Y : Matrix (α ⊕ γ) (α ⊕ γ) ℂ) :
    Matrix (α ⊕ (β ⊕ γ)) (α ⊕ (β ⊕ γ)) ℂ :=
  Matrix.fromBlocks (Y.toBlocks₁₁ * X.toBlocks₁₁)
    (Matrix.fromCols (Y.toBlocks₁₁ * X.toBlocks₁₂) Y.toBlocks₁₂)
    (Matrix.fromRows X.toBlocks₂₁ (Y.toBlocks₂₁ * X.toBlocks₁₁))
    (Matrix.fromBlocks X.toBlocks₂₂ 0 (Y.toBlocks₂₁ * X.toBlocks₁₂) Y.toBlocks₂₂)

end AxisJoin
end ExactFourier

end

section
/-! Parallel lifts of a finite stream. Time remains outermost, and no additional
coordinates are inserted. -/
namespace ExactFourier
open CoefficientTime TensorTools
open scoped Kronecker
namespace TimeLifts
variable {σ ρ α β : Type} [Fintype σ] [Fintype ρ] [Fintype α] [Fintype β]
  [DecidableEq σ] [DecidableEq ρ] [DecidableEq α] [DecidableEq β]

def rightEquiv (t : ℕ) : (((Fin t × σ) ⊕ ρ) × α) ≃ ((Fin t × (σ × α)) ⊕ (ρ × α)) :=
  (Equiv.sumProdDistrib _ _ _).trans
    (Equiv.sumCongr (Equiv.prodAssoc _ _ _) (Equiv.refl _))
def timeSwap (t : ℕ) : σ × (Fin t × α) ≃ Fin t × (σ × α) where
  toFun x := (x.2.1,(x.1,x.2.2))
  invFun x := (x.2.1,(x.1,x.2.2))
  left_inv := by rintro ⟨s,i,a⟩; rfl
  right_inv := by rintro ⟨i,s,a⟩; rfl
def leftEquiv (t : ℕ) : (σ × ((Fin t × α) ⊕ β)) ≃ ((Fin t × (σ × α)) ⊕ (σ × β)) :=
  (Equiv.prodSumDistrib _ _ _).trans
    (Equiv.sumCongr (timeSwap t) (Equiv.refl _))

noncomputable def right (t : ℕ) (X : Matrix ((Fin t × σ) ⊕ ρ) ((Fin t × σ) ⊕ ρ) ℂ) :
    Matrix ((Fin t × (σ × α)) ⊕ (ρ × α)) ((Fin t × (σ × α)) ⊕ (ρ × α)) ℂ :=
  Matrix.reindex (rightEquiv t) (rightEquiv t) (X ⊗ₖ (1 : Matrix α α ℂ))
noncomputable def left (t : ℕ) (X : Matrix ((Fin t × α) ⊕ β) ((Fin t × α) ⊕ β) ℂ) :
    Matrix ((Fin t × (σ × α)) ⊕ (σ × β)) ((Fin t × (σ × α)) ⊕ (σ × β)) ℂ :=
  Matrix.reindex (leftEquiv t) (leftEquiv t) ((1 : Matrix σ σ ℂ) ⊗ₖ X)

end TimeLifts
end ExactFourier

end

section
/-! The same exact tensor index for scalar, polynomial, and series matrices.
The zero tensor power has one coordinate and is identity. -/
namespace ExactFourier
open scoped Kronecker BigOperators
open Triangular TensorTools
namespace TensorAxis
abbrev Space := Triangular.Bottom
abbrev Fibers := Triangular.Calls

variable {α : Type} [Fintype α] [DecidableEq α]
variable {R S : Type} [CommSemiring R] [CommSemiring S]

noncomputable def power (A : Matrix α α R) : (k : ℕ) → Matrix (Space α k) (Space α k) R
  | 0 => 1
  | k+1 => power A k ⊗ₖ A

@[simp] theorem card_space (k : ℕ) : Fintype.card (Space α k) = Fintype.card α ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [bottom_card_succ,ih,pow_succ]

@[simp] theorem power_one
    {α : Type} [Fintype α] [DecidableEq α] {R : Type} [CommSemiring R] (k : ℕ) : power (1 : Matrix α α R) k = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [power,ih]

theorem unit_power (A : Matrix α α ℂ) (hA : IsUnit A) (k : ℕ) : IsUnit (power A k) := by
  induction k with
  | zero => exact isUnit_one
  | succ k ih => exact unit_tensor _ _ ih hA

end TensorAxis
end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.CascadeWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier
open scoped Kronecker BigOperators
open TensorAxis CoefficientTime TensorTools
namespace Cascade

abbrev States (α β : Type) : ℕ → Type
  | 0 => PEmpty
  | k+1 => (States α β k × α) ⊕ (Space α k × β)
@[reducible] noncomputable instance statesFintype (α β : Type) [Fintype α] [Fintype β] :
    (k : ℕ) → Fintype (States α β k)
  | 0 => inferInstanceAs (Fintype PEmpty)
  | k+1 => letI := statesFintype α β k
           inferInstanceAs (Fintype ((States α β k × α) ⊕ (Space α k × β)))
@[reducible] instance statesDecidableEq (α β : Type) [DecidableEq α] [DecidableEq β] :
    (k : ℕ) → DecidableEq (States α β k)
  | 0 => inferInstanceAs (DecidableEq PEmpty)
  | k+1 => letI := statesDecidableEq α β k
           inferInstanceAs (DecidableEq ((States α β k × α) ⊕ (Space α k × β)))

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

noncomputable def response (H : Matrix α α (PowerSeries ℂ))
    (S : Matrix α β (PowerSeries ℂ)) : (k : ℕ) → Matrix (Space α k) (States α β k) (PowerSeries ℂ)
  | 0 => 0
  | k+1 => Matrix.fromCols (response H S k ⊗ₖ H) ((1 : Matrix (Space α k) (Space α k) _) ⊗ₖ S)

noncomputable def run (K : Matrix (α ⊕ β) (α ⊕ β) ℂ) (t : ℕ) : (k : ℕ) →
    Matrix ((Fin t × Space α k) ⊕ States α β k) ((Fin t × Space α k) ⊕ States α β k) ℂ
  | 0 => 1
  | k+1 => AxisJoin.join (TimeLifts.right (α := α) t (run K t k))
      (TimeLifts.left (σ := Space α k) t (CellStream.run K t))

end Cascade
end ExactFourier

end

section
/-! Polynomial clearing for the cascade (05-corners:327–369). No inverse of D
and no genericity of evaluation points is used. -/
namespace ExactFourier
namespace CellPoly
open Polynomial
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

abbrev ps : Polynomial ℂ →+* PowerSeries ℂ := Polynomial.coeToPowerSeries.ringHom

noncomputable def Z (D : Matrix β β ℂ) : Matrix β β (Polynomial ℂ) :=
  1 - (X : Polynomial ℂ) • D.map Polynomial.C
noncomputable def a (D : Matrix β β ℂ) : Polynomial ℂ := (Z D).det
noncomputable def R (D : Matrix β β ℂ) : Matrix β β (Polynomial ℂ) := (Z D).adjugate
noncomputable def F (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) : Matrix α α (Polynomial ℂ) :=
  a D • M.map Polynomial.C + (X : Polynomial ℂ) •
    (C.map Polynomial.C * R D * B.map Polynomial.C)
noncomputable def b (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) : Polynomial ℂ := (F M C B D).det
noncomputable def J (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) : Matrix α α (Polynomial ℂ) := (F M C B D).adjugate
noncomputable def L (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) : Matrix α α (Polynomial ℂ) := a D • J M C B D
noncomputable def T (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) : Matrix α β (Polynomial ℂ) :=
  J M C B D * C.map Polynomial.C * R D

@[simp] theorem map_const {ι κ : Type} (A : Matrix ι κ ℂ) :
    (A.map Polynomial.C).map ps = A.map PowerSeries.C := by ext i j; simp

end CellPoly
end ExactFourier

end

section
namespace ExactFourier
open scoped Kronecker
open TensorAxis
namespace Cascade
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {R : Type} [CommSemiring R]

noncomputable def cleared (b : R) (L : Matrix α α R) (T : Matrix α β R) :
    (k : ℕ) → Matrix (Space α k) (States α β k) R
  | 0 => 0
  | k+1 => Matrix.fromCols (b • (cleared b L T k ⊗ₖ (1 : Matrix α α R))) (power L k ⊗ₖ T)

end Cascade
end ExactFourier

end

section
namespace ExactFourier
open scoped BigOperators Kronecker
namespace PolynomialMatrix
variable {ι κ τ υ : Type} [Fintype ι] [Fintype κ] [Fintype τ] [Fintype υ]

noncomputable def bound (A : Matrix ι κ (Polynomial ℂ)) : ℕ := ∑ i, ∑ j, (A i j).natDegree

def Bounded (A : Matrix ι κ (Polynomial ℂ)) (d : ℕ) : Prop := ∀ i j, (A i j).natDegree ≤ d

end PolynomialMatrix
end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.CircuitExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier

def LinearDAG.fanout {n a b : ℕ} (C : LinearDAG n a) (D : LinearDAG n b) :
    LinearDAG n (a+b) where
  size := C.size + D.size
  program := C.program.append (Fin.castAdd C.size) D.program
  outputs := Fin.addCases (fun i => keepIndex (C.outputs i))
    (fun j => appendIndex (Fin.castAdd C.size) (D.outputs j))

@[simp] theorem LinearDAG.size_fanout {n a b : ℕ}
    (C : LinearDAG n a) (D : LinearDAG n b) : (C.fanout D).size = C.size+D.size := rfl

/-- Select or duplicate arbitrary existing inputs; these are wire names, not gates. -/
noncomputable def LinearDAG.withInputs {m n a : ℕ} (C : LinearDAG n a)
    (f : Fin n → Fin m) : LinearDAG m a := C.comp (.wires (fun i => (f i).castSucc))

@[simp] theorem LinearDAG.size_withInputs {m n a : ℕ} (C : LinearDAG n a)
    (f : Fin n → Fin m) : (C.withInputs f).size = C.size := by
  simp [LinearDAG.withInputs, LinearDAG.comp, LinearDAG.wires]

/-- Change the ordered output list without performing an arithmetic operation. -/
def LinearDAG.withOutputs {n a b : ℕ} (C : LinearDAG n a) (f : Fin b → Fin a) :
    LinearDAG n b := ⟨C.size, C.program, C.outputs ∘ f⟩

@[simp] theorem LinearDAG.eval_withOutputs {n a b : ℕ} (C : LinearDAG n a)
    (f : Fin b → Fin a) (x : Fin n → ℂ) : (C.withOutputs f).eval x = C.eval x ∘ f := rfl

/-- One butterfly for each of m pairs: charge m scalar multiplications, m additions,
and m subtractions, retaining the scaled terms for both output signs. -/
def LinearDAG.butterflies {n m : ℕ} (C : LinearDAG n (m+m)) (c : Fin m → ℂ) :
    LinearDAG n (m+m) where
  size := (C.size + m) + (m+m)
  program :=
    let p := C.program.emit (fun i => Gate.scale (c i) (C.outputs (Fin.natAdd m i)))
    p.emit (Fin.addCases
      (fun i => Gate.add (keepIndex (C.outputs (Fin.castAdd m i))) (gateIndex i))
      (fun i => Gate.sub (keepIndex (C.outputs (Fin.castAdd m i))) (gateIndex i)))
  outputs := gateIndex

end ExactFourier

end

section
/-! Finite-index wrappers for the exact charged DAG model. These are used for the
state-clearing tensor-axis maps in the cascade and coefficient boundary cost. -/
namespace ExactFourier
open scoped BigOperators Kronecker

structure TypedDAG (ι κ : Type) [Fintype ι] [Fintype κ] where
  circuit : LinearDAG (Fintype.card ι) (Fintype.card κ)

namespace TypedDAG
variable {ι κ τ υ : Type} [Fintype ι] [Fintype κ] [Fintype τ] [Fintype υ]

abbrev size (C : TypedDAG ι κ) : ℕ := C.circuit.size
noncomputable def eval (C : TypedDAG ι κ) (x : ι → ℂ) : κ → ℂ :=
  fun j => C.circuit.eval (x ∘ (Fintype.equivFin ι).symm) (Fintype.equivFin κ j)

noncomputable def comp (D : TypedDAG κ τ) (C : TypedDAG ι κ) : TypedDAG ι τ :=
  ⟨D.circuit.comp C.circuit⟩
@[simp] theorem size_comp (D : TypedDAG κ τ) (C : TypedDAG ι κ) :
    (D.comp C).size = C.size + D.size := rfl

noncomputable def inputs (C : TypedDAG ι κ) (f : ι → τ) : TypedDAG τ κ :=
  ⟨C.circuit.withInputs (fun i => Fintype.equivFin τ (f ((Fintype.equivFin ι).symm i)))⟩
@[simp] theorem size_inputs (C : TypedDAG ι κ) (f : ι → τ) :
    (C.inputs f).size = C.size := LinearDAG.size_withInputs _ _

noncomputable def outputs (C : TypedDAG ι κ) (f : τ → κ) : TypedDAG ι τ :=
  ⟨C.circuit.withOutputs (fun i => Fintype.equivFin κ (f ((Fintype.equivFin τ).symm i)))⟩
@[simp] theorem size_outputs (C : TypedDAG ι κ) (f : τ → κ) :
    (C.outputs f).size = C.size := rfl
@[simp] theorem eval_outputs (C : TypedDAG ι κ) (f : τ → κ) (x : ι → ℂ) :
    (C.outputs f).eval x = C.eval x ∘ f := by
  funext j
  simp [eval, outputs, LinearDAG.eval_withOutputs, Function.comp_def]

noncomputable def fanout (C : TypedDAG ι κ) (D : TypedDAG ι τ) : TypedDAG ι (κ ⊕ τ) :=
  ⟨(C.circuit.fanout D.circuit).withOutputs (fun i =>
    finSumFinEquiv ((Equiv.sumCongr (Fintype.equivFin κ) (Fintype.equivFin τ))
      ((Fintype.equivFin (κ ⊕ τ)).symm i)))⟩
@[simp] theorem size_fanout (C : TypedDAG ι κ) (D : TypedDAG ι τ) :
    (C.fanout D).size = C.size + D.size := rfl

noncomputable def wires (f : κ → Option ι) : TypedDAG ι κ :=
  ⟨LinearDAG.wires (fun j => (f ((Fintype.equivFin κ).symm j)).elim
    (Fin.last _) (fun i => (Fintype.equivFin ι i).castSucc))⟩
@[simp] theorem size_wires (f : κ → Option ι) : (wires f).size = 0 := rfl
@[simp] theorem eval_wires (f : κ → Option ι) (x : ι → ℂ) :
    (wires f).eval x = fun j => (f j).elim 0 x := by
  funext j
  simp only [eval, wires, LinearDAG.eval_wires, Equiv.symm_apply_apply]
  cases f j <;> simp

noncomputable def matrix (A : Matrix κ ι ℂ) : TypedDAG ι κ :=
  ⟨LinearDAG.matrix _ _ (Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin ι) A)⟩
@[simp] theorem eval_matrix (A : Matrix κ ι ℂ) (x : ι → ℂ) :
    (matrix A).eval x = A.mulVec x := by
  funext j
  simp only [eval, matrix, LinearDAG.eval_matrix, Matrix.mulVec, dotProduct,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Function.comp_apply]
  exact (Fintype.equivFin ι).symm.sum_comp (fun i => A j i * x i)

noncomputable def scale (c : κ → ℂ) : TypedDAG κ κ :=
  ⟨LinearDAG.layer (fun i => .scale (c ((Fintype.equivFin κ).symm i)) i.castSucc)⟩
@[simp] theorem size_scale (c : κ → ℂ) : (scale c).size = Fintype.card κ := by simp [size, scale, LinearDAG.layer]

noncomputable def addPair : TypedDAG (κ ⊕ κ) κ :=
  ⟨LinearDAG.layer (fun i => .add
    (Fintype.equivFin (κ ⊕ κ) (Sum.inl ((Fintype.equivFin κ).symm i))).castSucc
    (Fintype.equivFin (κ ⊕ κ) (Sum.inr ((Fintype.equivFin κ).symm i))).castSucc)⟩
@[simp] theorem size_addPair : (addPair (κ := κ)).size = Fintype.card κ := by simp [size, addPair, LinearDAG.layer]

noncomputable def stackFin : (n : ℕ) → (Fin n → TypedDAG ι κ) → TypedDAG ι (Fin n × κ)
  | 0, _ => wires (fun _ => none)
  | n+1, C => ((C 0).fanout (stackFin n (fun i => C i.succ))).outputs
      (fun x => Fin.cases (Sum.inl x.2) (fun i => Sum.inr (i,x.2)) x.1)

noncomputable def stack (C : τ → TypedDAG ι κ) : TypedDAG ι (τ × κ) :=
  (stackFin (Fintype.card τ) (fun i => C ((Fintype.equivFin τ).symm i))).outputs
    (fun x => (Fintype.equivFin τ x.1,x.2))

noncomputable def parallel (C : TypedDAG ι κ) (τ : Type) [Fintype τ] :
    TypedDAG (τ × ι) (τ × κ) := stack (fun t => C.inputs (fun i => (t,i)))

noncomputable def tensor (C : TypedDAG ι κ) (D : TypedDAG τ υ) :
    TypedDAG (ι × τ) (κ × υ) :=
  (((C.parallel υ).inputs Prod.swap).comp (D.parallel ι)).outputs Prod.swap

end TypedDAG
end ExactFourier

end

section
/-! Charged scalar DAGs for the tensor-axis local maps used in the cascade. -/
namespace ExactFourier
open scoped Kronecker
namespace TypedDAG
variable {ι κ τ : Type} [Fintype ι] [Fintype κ] [Fintype τ]

noncomputable def blockCols (C : TypedDAG ι κ) (D : TypedDAG τ κ) : TypedDAG (ι ⊕ τ) κ :=
  addPair.comp ((C.inputs Sum.inl).fanout (D.inputs Sum.inr))
@[simp] theorem size_blockCols (C : TypedDAG ι κ) (D : TypedDAG τ κ) :
    (blockCols C D).size = C.size+D.size+Fintype.card κ := by simp [blockCols]

noncomputable def scalar (c : ℂ) (C : TypedDAG ι κ) : TypedDAG ι κ :=
  (scale (fun _ => c)).comp C
@[simp] theorem size_scalar (c : ℂ) (C : TypedDAG ι κ) :
    (scalar c C).size = C.size+Fintype.card κ := by simp [scalar]

noncomputable def identity : TypedDAG ι ι := wires some
@[simp] theorem size_identity : (identity (ι := ι)).size=0 := rfl
@[simp] theorem eval_identity (x : ι → ℂ) : (identity (ι := ι)).eval x = x := by simp [identity]

variable {α : Type} [Fintype α] [DecidableEq α]
noncomputable def tensorPower (A : Matrix α α ℂ) : (k : ℕ) → TypedDAG (TensorAxis.Space α k) (TensorAxis.Space α k)
  | 0 => identity
  | k+1 => (tensorPower A k).tensor (matrix A)

end TypedDAG
end ExactFourier

end

section
/-! Exact charged reconstruction of coefficient vectors from finitely many
scalar evaluations. All interpolation constants are prechosen and charged;
no pole avoidance or analytic limit is used. -/
namespace ExactFourier
open scoped BigOperators
namespace PolynomialDAG
variable {ι κ : Type} [Fintype ι] [Fintype κ]

noncomputable def nodes (m : ℕ) (i : Fin m) : ℂ := i.val
noncomputable def weights (m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => (Lagrange.basis Finset.univ (nodes m) j).coeff i.val

noncomputable def coefficients (A : Matrix κ ι (Polynomial ℂ)) (t : ℕ) : Matrix (Fin t × κ) ι ℂ :=
  fun i j => (A i.2 j).coeff i.1.val
noncomputable def evalMatrix (A : Matrix κ ι (Polynomial ℂ)) (z : ℂ) : Matrix κ ι ℂ :=
  A.map (Polynomial.evalRingHom z)

noncomputable def reconstruct (m : ℕ) (C : Fin m → TypedDAG ι κ) : TypedDAG ι (Fin m × κ) :=
  ((((TypedDAG.matrix (weights m)).parallel κ).inputs Prod.swap).comp
    (TypedDAG.stackFin m C)).outputs Prod.swap

noncomputable def pad (m t : ℕ) : TypedDAG (Fin m × κ) (Fin t × κ) :=
  TypedDAG.wires (fun i => if h : i.1.val < m then some (⟨i.1.val,h⟩,i.2) else none)
@[simp] theorem size_pad (m t : ℕ) : (pad (κ := κ) m t).size=0 := rfl

end PolynomialDAG
end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.ClearedCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! The O_K(k² n^k) evaluation DAG and O_K((k+1)³ n^k) coefficient
DAG for the literal polynomial state correction, uniform in truncation length. -/
namespace ExactFourier
open scoped Kronecker
open TensorAxis TypedDAG PolynomialDAG
namespace Cascade
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

noncomputable def clearedDAG (b : ℂ) (L : Matrix α α ℂ) (T : Matrix α β ℂ) :
    (k : ℕ) → TypedDAG (States α β k) (Space α k)
  | 0 => wires (fun _ => none)
  | k+1 => blockCols (scalar b ((clearedDAG b L T k).tensor identity))
      ((TypedDAG.tensorPower L k).tensor (matrix T))

end Cascade
end ExactFourier

end

section
/-! Radix-two algebra used by the scalar-convolution bound in the missing main
proof. This is the ordinary O(n log n) support algorithm, NOT a main saving. -/
namespace ExactFourier.RadixTwo
open scoped BigOperators
open Polynomial

def evenIndex (n : ℕ) (i : Fin n) : Fin (n+n) := ⟨2*i.val, by have := i.isLt; omega⟩
def oddIndex (n : ℕ) (i : Fin n) : Fin (n+n) := ⟨2*i.val+1, by have := i.isLt; omega⟩

def parityEquiv (n : ℕ) : Fin n × Fin 2 ≃ Fin (n+n) where
  toFun p := ⟨2*p.1.val+p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩
  invFun j := (⟨j.val/2, by have := j.isLt; omega⟩, ⟨j.val%2, by omega⟩)
  left_inv p := by
    apply Prod.ext <;> apply Fin.ext
    · change (2*p.1.val+p.2.val)/2 = p.1.val
      have := p.2.isLt
      omega
    · change (2*p.1.val+p.2.val)%2 = p.2.val
      have := p.2.isLt
      omega
  right_inv j := by
    apply Fin.ext
    change 2*(j.val/2)+j.val%2=j.val
    omega

noncomputable def evalAt (n : ℕ) (ω : ℂ) (x : Fin n → ℂ) (r : ℕ) : ℂ :=
  ∑ j, ω ^ (r*j.val) * x j

noncomputable def eval (n : ℕ) (ω : ℂ) (x : Fin n → ℂ) : Fin n → ℂ :=
  fun i => evalAt n ω x i.val

end ExactFourier.RadixTwo

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.FFTCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! The uniform scalar-convolution main dependency. All operations are charged;
truncated series and constants may vary with the requested length. -/
namespace ExactFourier.ScalarConvolution
open Polynomial CoefficientTime RadixTwo
open scoped BigOperators

def padIndex (t m : ℕ) (i : Fin m) : Fin (t+1) :=
  if h : i.val < t then (⟨i.val,h⟩ : Fin t).castSucc else Fin.last t

def padded {t m : ℕ} (x : Fin t → ℂ) (i : Fin m) : ℂ :=
  if h : i.val < t then x ⟨i.val,h⟩ else 0

/-- A fixed diagonal layer charges exactly one multiplication per coordinate. -/
def diagonalDAG {m : ℕ} (c : Fin m → ℂ) : LinearDAG m m :=
  LinearDAG.layer (fun i => .scale (c i) i.castSucc)

end ExactFourier.ScalarConvolution

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.Boundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier.Boundary
open Polynomial
open scoped BigOperators

noncomputable def quotientLinear (ℓ : ℂ[X]) (hℓ : ℓ.Monic) : ℂ[X] →ₗ[ℂ] ℂ[X] where
  toFun f := f /ₘ ℓ
  map_add' f g := by
    apply (div_modByMonic_unique (f /ₘ ℓ + g /ₘ ℓ)
      (f %ₘ ℓ + g %ₘ ℓ) hℓ ?_).1
    constructor
    · rw [mul_add]
      linear_combination modByMonic_add_div f ℓ + modByMonic_add_div g ℓ
    · exact lt_of_le_of_lt (degree_add_le _ _) (max_lt
        (degree_modByMonic_lt _ hℓ) (degree_modByMonic_lt _ hℓ))
  map_smul' c f := by
    apply (div_modByMonic_unique (c • (f /ₘ ℓ)) (c • (f %ₘ ℓ)) hℓ ?_).1
    constructor
    · rw [mul_smul_comm, ← smul_add, modByMonic_add_div]
    · exact (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hℓ)

@[simp] theorem quotientLinear_apply (ℓ : ℂ[X]) (hℓ : ℓ.Monic) (f : ℂ[X]) :
    quotientLinear ℓ hℓ f = f /ₘ ℓ := rfl

noncomputable def timeMatrix {ι : Type} (t : ℕ) (G : Matrix ι ι ℂ[X]) :
    Matrix (Fin t × ι) (Fin t × ι) ℂ :=
  fun a b => (G a.2 b.2 * X ^ b.1.val).coeff a.1.val

noncomputable def modulusMatrix {ι : Type} (t : ℕ) (ℓ : ℂ[X])
    (G : Matrix ι ι ℂ[X]) : Matrix (Fin t × ι) (Fin t × ι) ℂ :=
  fun a b => ((G a.2 b.2 * X ^ b.1.val) %ₘ ℓ).coeff a.1.val

/-- Scalar weights for the exact ordered generator formula. Prefix correction uses
η=1. The suffix uses the first t coefficients of ℓ/u^k. -/
noncomputable def orderedWeight (η ℓ : ℂ[X]) (a b i j : ℕ) : ℂ :=
  -(η * X ^ i * ((X ^ (b + j) : ℂ[X]) /ₘ ℓ)).coeff a

noncomputable def coefficientMatrix {ι κ : Type} (G : Matrix ι κ ℂ[X]) (j : ℕ) :
    Matrix ι κ ℂ := fun u v => (G u v).coeff j

/-- Polynomial correction for a single input time b, before taking its output
coefficient. Matrix multiplication is in the original order J then G. -/
noncomputable def weightedCorrection {ι : Type} [Fintype ι] (η ℓ : ℂ[X])
    (J G : Matrix ι ι ℂ[X]) (b : ℕ) : Matrix ι ι ℂ[X] :=
  fun u v => ∑ x, η * J u x * (-((G x v * X ^ b) /ₘ ℓ))

/-- The actual early--suffix formula after the scalar prefix conjugation. -/
noncomputable def activeCorrection {ι : Type} [Fintype ι]
    (t d : ℕ) (η ℓ : ℂ[X]) (J G : Matrix ι ι ℂ[X]) :
    Matrix (Fin t × ι) (Fin t × ι) ℂ := fun a b =>
  if a.1.val < t-d then
    (weightedCorrection 1 ℓ J G b.1.val a.2 b.2).coeff a.1.val
  else (weightedCorrection η ℓ J G b.1.val a.2 b.2).coeff a.1.val

def ActiveTime (t d e a : ℕ) : Prop := a < min (t-d) (e+d) ∨ t-d ≤ a

instance instDecidableActiveTime (t d e a : ℕ) : Decidable (ActiveTime t d e a) := by
  unfold ActiveTime
  infer_instance

end ExactFourier.Boundary

end

section
/-! Literal relation between modulus multiplication and the supported correction.
This is the missing interface at 06-feedback:86--196, not an assumed theorem.
Noncommutative coefficient matrices remain ordered J_i G_j. -/
namespace ExactFourier.Boundary
open Polynomial
open CoefficientTime
open scoped Kronecker BigOperators

noncomputable def seriesMatrix {ι : Type} [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℂ[X] →+* Matrix ι ι (PowerSeries ℂ) :=
  (Polynomial.coeToPowerSeries.ringHom : ℂ[X] →+* PowerSeries ℂ).mapMatrix

@[simp] theorem seriesMatrix_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℂ[X]) (i j : ι) : seriesMatrix G i j = (G i j : PowerSeries ℂ) := rfl

noncomputable def quotientColumns {ι : Type} (t : ℕ) (ℓ : ℂ[X])
    (G : Matrix ι ι ℂ[X]) : Matrix ι (Fin t × ι) (PowerSeries ℂ) :=
  fun i b => (-((G i b.2 * X^b.1.val) /ₘ ℓ) : ℂ[X])

end ExactFourier.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.CascadeLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! The real limit used by the cascade-to-corner argument. Only the fixed real
prices are compared; no continuity of a price functional is used. -/
namespace ExactFourier
open Filter Topology

noncomputable def cascadeError (m : ℕ) : ℝ :=
  Real.log (2*((m:ℝ)+2)^4)/((m:ℝ)+1) +
    ((m:ℝ)+2)^3/(((m:ℝ)+2)^4*((m:ℝ)+1))

end ExactFourier

end

section
/-! Literal arbitrary invertible square submatrix theorem, and its one-way DAG
corollary. Independent permutations use only the standing monomial law. -/
namespace ExactFourier

noncomputable def extendInjection {ι κ : Type} [Fintype ι] [Fintype κ]
    (f : κ → ι) (hf : Function.Injective f) :
    κ ⊕ {i : ι // i ∉ Set.range f} ≃ ι := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective f hf) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range f))

@[simp] theorem extendInjection_inl {ι κ : Type} [Fintype ι] [Fintype κ]
    (f : κ → ι) (hf : Function.Injective f) (j : κ) :
    extendInjection f hf (Sum.inl j) = f j := rfl

end ExactFourier

end

section
/-! Charged common-generator circuits for the active coefficient boundary.
Generator outputs are shared across output times; every scalar weight is charged. -/
namespace ExactFourier
open scoped BigOperators
namespace TypedDAG
variable {α β γ ι : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype ι]

noncomputable def weightedBlocks (W : Matrix α (β × γ) ℂ) (C : γ → TypedDAG ι ι) :
    TypedDAG (β × ι) (α × ι) :=
  ((((matrix W).parallel ι).inputs Prod.swap).outputs Prod.swap).comp
    (stack (fun bg : β × γ => (C bg.2).inputs (fun i => (bg.1,i))))

noncomputable def blockMatrix (W : Matrix α (β × γ) ℂ) (G : γ → Matrix ι ι ℂ) :
    Matrix (α × ι) (β × ι) ℂ := fun a b => ∑ g, W a.1 (b.1,g) * G g a.2 b.2

noncomputable def addIdentity (C : TypedDAG ι ι) : TypedDAG ι ι :=
  addPair.comp (identity.fanout C)
@[simp] theorem size_addIdentity (C : TypedDAG ι ι) :
    C.addIdentity.size=C.size+Fintype.card ι := by simp [addIdentity]

end TypedDAG
end ExactFourier

end

section
/-! The exact disjoint active set and its direct-summand price. -/
namespace ExactFourier.Boundary
open scoped BigOperators

abbrev Times (t d e : ℕ) := {a : Fin t // ActiveTime t d e a.val}

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def timeActiveSplit (t d e : ℕ) :
    ((Times t d e × ι) ⊕ ({a : Fin t // ¬ActiveTime t d e a.val} × ι)) ≃ (Fin t × ι) where
  toFun := Sum.elim (fun x => (x.1.val,x.2)) (fun x => (x.1.val,x.2))
  invFun x := if h : ActiveTime t d e x.1.val then Sum.inl (⟨x.1,h⟩,x.2) else Sum.inr (⟨x.1,h⟩,x.2)
  left_inv := by rintro (⟨a,i⟩|⟨a,i⟩) <;> simp [a.property]
  right_inv := by intro x; dsimp; split_ifs <;> rfl

noncomputable def activeMatrix (t d e : ℕ) (η ℓ : Polynomial ℂ) (J G : Matrix ι ι (Polynomial ℂ)) :
    Matrix (Times t d e × ι) (Times t d e × ι) ℂ :=
  1 + (activeCorrection t d η ℓ J G).submatrix (fun a => (a.1.val,a.2)) (fun a => (a.1.val,a.2))

end ExactFourier.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.BoundaryActiveCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Common ordered spatial generators for the active boundary DAG. Scalar
weights may be arbitrarily large and depend on the modulus; every use is charged. -/
namespace ExactFourier.Boundary
open scoped BigOperators
open TensorAxis PolynomialMatrix
variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def activeWeights (t d e : ℕ) (η ℓ : Polynomial ℂ) :
    Matrix (Times t d e) (Times t d e × (Fin (e+1) × Fin (d+1))) ℂ :=
  fun a b => orderedWeight (if a.val.val<t-d then 1 else η) ℓ a.val.val b.1.val.val b.2.1.val b.2.2.val

end ExactFourier.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.PolynomialClearing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Exact finite Taylor change of coefficient basis. -/
namespace ExactFourier.Taylor
open Polynomial
open scoped BigOperators Kronecker

noncomputable def matrix (t : ℕ) (s : ℂ) : Matrix (Fin t) (Fin t) ℂ :=
  fun a b => (taylor s (X^b.val : Polynomial ℂ)).coeff a.val

@[simp] theorem matrix_zero (t : ℕ) : matrix t 0=1 := by
  ext i j
  simp only [matrix,taylor_zero,coeff_X_pow,Matrix.one_apply]
  simp [Fin.ext_iff]

variable {α : Type} [Fintype α] [DecidableEq α]

noncomputable def translate (s : ℂ) (G : Matrix α α (Polynomial ℂ)) : Matrix α α (Polynomial ℂ) :=
  G.map (taylor s)

end ExactFourier.Taylor

end

section
namespace ExactFourier.Taylor
open Polynomial CoefficientTime
open scoped Kronecker

noncomputable def kernel (s : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun j => s^j/(j.factorial:ℂ))

@[simp] theorem kernel_constant (s : ℂ) : PowerSeries.constantCoeff (kernel s)=1 := by
  simp [kernel]

end ExactFourier.Taylor

end

section
namespace ExactFourier.CellPoly
open Polynomial
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

noncomputable def feedback (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (s : ℂ) : Matrix α α ℂ :=
  M+s•(C*(1-s•D)⁻¹*B)

end ExactFourier.CellPoly

end

section
/-! The real limit used by the boundary comparison argument. Only the fixed real
prices are compared; no continuity of a price functional is used. -/
namespace ExactFourier
open Filter Topology

noncomputable def boundaryError (m : ℕ) : ℝ :=
  Real.log (2*((m:ℝ)+2)^8)/((m:ℝ)+1) +
    ((m:ℝ)+2)^6/(((m:ℝ)+2)^8*((m:ℝ)+1))

end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.PivotAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier.Pivot
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

noncomputable def matrix (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) : Matrix (α⊕β) (α⊕β) ℂ :=
  Matrix.fromBlocks (A-C*D⁻¹*B) (C*D⁻¹) (-D⁻¹*B) D⁻¹

end ExactFourier.Pivot

end

section
namespace ExactFourier
open scoped Kronecker
variable {β : Type} [Fintype β] [DecidableEq β]

def twoProdEquiv (β : Type) : Fin 2×β ≃ β⊕β where
  toFun := fun x => if x.1=0 then Sum.inl x.2 else Sum.inr x.2
  invFun := Sum.elim (fun b => (0,b)) (fun b => (1,b))
  left_inv := by rintro ⟨i,b⟩; fin_cases i <;> simp
  right_inv := by intro b; cases b <;> simp

noncomputable def pairLayer (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (β⊕β) (β⊕β) ℂ :=
  Matrix.reindex (twoProdEquiv β) (twoProdEquiv β) (A ⊗ₖ (1 : Matrix β β ℂ))

end ExactFourier

end

section
namespace ExactFourier.Pivot
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

noncomputable def side (L : Matrix (Fin 2) (Fin 2) ℂ) : Matrix ((α⊕β)⊕β) ((α⊕β)⊕β) ℂ :=
  Matrix.reindex (Equiv.sumAssoc α β β).symm (Equiv.sumAssoc α β β).symm
    (Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 (pairLayer (β := β) L))

noncomputable def middle (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) : Matrix ((α⊕β)⊕β) ((α⊕β)⊕β) ℂ :=
  Matrix.reindex TensorTools.middleEquiv TensorTools.middleEquiv
    (Matrix.fromBlocks (Matrix.fromBlocks A C B D) 0 0 (1 : Matrix β β ℂ))

def P (b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![b,1;1,1]
def Q (b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1,1-b;1,-b]

noncomputable def data (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (b : ℂ) :=
  Matrix.fromBlocks A C ((1-b)•B) (b•1+(1-b)•D)
noncomputable def co (C : Matrix α β ℂ) (D : Matrix β β ℂ) (b : ℂ) :=
  Matrix.fromRows C (1+(1-b)•D)
noncomputable def bo (B : Matrix β α ℂ) (D : Matrix β β ℂ) (b : ℂ) :=
  Matrix.fromCols ((-b)•B) (b•(1-D))
noncomputable def state (D : Matrix β β ℂ) (b : ℂ) := 1-b•D
noncomputable def cell (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (b : ℂ) :=
  Matrix.fromBlocks (data A C B D b) (co C D b) (bo B D b) (state D b)

end ExactFourier.Pivot

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.PivotJoin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier.Pivot
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

noncomputable def ofMatrix (K : Matrix (α⊕β) (α⊕β) ℂ) :=
  matrix K.toBlocks₁₁ K.toBlocks₁₂ K.toBlocks₂₁ K.toBlocks₂₂

@[simp] theorem of_fromBlocks
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) :
    ofMatrix (Matrix.fromBlocks A C B D)=matrix A C B D := rfl

noncomputable def reverseJoin (X : Matrix (α⊕β) (α⊕β) ℂ)
    (Y : Matrix (γ⊕β) (γ⊕β) ℂ) : Matrix ((α⊕γ)⊕β) ((α⊕γ)⊕β) ℂ :=
  Matrix.reindex (Equiv.sumCongr (Equiv.sumComm γ α) (Equiv.refl β))
    (Equiv.sumCongr (Equiv.sumComm γ α) (Equiv.refl β)) (CellJoin.join Y X)

end ExactFourier.Pivot

end

section
namespace ExactFourier.Pivot
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

@[simp] theorem of_one : ofMatrix (1 : Matrix (α⊕β) (α⊕β) ℂ)=1 := by
  have he : (1 : Matrix (α⊕β) (α⊕β) ℂ)=Matrix.fromBlocks 1 0 0 1 := by
    ext i j; cases i <;> cases j <;> simp [Matrix.one_apply,Matrix.fromBlocks]
  rw [he,of_fromBlocks]
  simp [matrix]

end ExactFourier.Pivot

end

section
namespace ExactFourier
namespace BasisExchange
variable {α : Type} [Fintype α] [DecidableEq α]

noncomputable def mix (U V : Matrix (α⊕PUnit) (α⊕PUnit) ℂ) :
    Matrix (α⊕PUnit) (α⊕PUnit) ℂ :=
  Matrix.fromBlocks U.toBlocks₁₁ U.toBlocks₁₂ V.toBlocks₂₁ V.toBlocks₂₂

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def isolate (i : ι) : ι≃{j : ι // j≠i}⊕PUnit where
  toFun j := if h : j=i then Sum.inr PUnit.unit else Sum.inl ⟨j,h⟩
  invFun := Sum.elim Subtype.val (fun _ => i)
  left_inv j := by by_cases h : j=i <;> simp [h]
  right_inv j := by rcases j with ⟨j,h⟩|⟨⟩ <;> simp [*]

end BasisExchange
end ExactFourier

end

section
namespace ExactFourier.DensePair
open scoped Matrix

def J (l : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,1,0,0;0,0,1,0;0,0,0,1;l,0,0,0]
def X (l : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,0,0;0,1,1,0;0,0,1,1;l,0,0,1]
def Xb (l : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,0,0;0,1,0,0;0,0,1,1;l,0,0,1]
def Xd : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,0,0;0,1,1,0;0,0,1,1;0,0,0,1]
def Y1 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,0,0,0;0,1,1,0;0,0,1,0;0,0,0,1]
def Y2 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,1,0;0,1,1,0;0,0,1,0;0,0,0,1]
def Y3 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,1,0;0,1,0,0;0,0,1,0;0,0,0,1]
def Y4 (l : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,1,0;0,1,0,0;0,0,1,0;l,0,0,1]
def Y5 (l : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,1,0;0,1,0,0;l,0,1,1;l,0,0,1]
def Y6 (l : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,1,0;0,1,0,0;l,0,1,1;0,0,0,1]

def cycle : Equiv.Perm (Fin 4) where
  toFun := ![3,0,1,2]
  invFun := ![1,2,3,0]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

end ExactFourier.DensePair

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.MonomialFeedback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.DensePair
open scoped Matrix Kronecker

def rowY : Equiv.Perm (Fin 4) where
  toFun := ![0,1,3,2]
  invFun := ![0,1,3,2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
def rowX : Equiv.Perm (Fin 4) where
  toFun := ![1,0,3,2]
  invFun := ![1,0,3,2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
def delta (l : ℂ) : Fin 4 → ℂ := ![-1,1,l,-l]
def signs : Fin 4 → ℂ := ![1,-1,1,-1]
def rankOne (l : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  1+(Matrix.of fun i j => delta l i*signs j/(1-l))
def scaled (l : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![l,1,1,1;1,l,1,1;1,1,l⁻¹,1;1,1,1,l⁻¹]
def scaled2 (u : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,u,u,1;u,1,u,1;u,u,u^2,1;1,1,1,1]
def B (u : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1,1;1,u]

def left1 (l : ℂ) : Fin 4 → ℂ := fun i => (1-l)/delta l i

def left2 (l : ℂ) : Fin 4 → ℂ := ![l⁻¹,l⁻¹,l⁻¹,1]
def right2 (l : ℂ) : Fin 4 → ℂ := ![1,1,1,l]

def bitsRow : (Fin 4)≃(Fin 2×Fin 2) where
  toFun := ![(1,0),(0,1),(1,1),(0,0)]
  invFun := fun p => if p.1=0 then (if p.2=0 then 3 else 1) else (if p.2=0 then 0 else 2)
  left_inv i := by fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨a,b⟩; fin_cases a <;> fin_cases b <;> rfl

def bitsCol : (Fin 4)≃(Fin 2×Fin 2) where
  toFun := ![(0,1),(1,0),(1,1),(0,0)]
  invFun := fun p => if p.1=0 then (if p.2=0 then 3 else 0) else (if p.2=0 then 1 else 2)
  left_inv i := by fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨a,b⟩; fin_cases a <;> fin_cases b <;> rfl

end ExactFourier.DensePair

end
end

section
noncomputable section
namespace ExactFourier.Embedded
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

abbrev complement (e : β ↪ α) := {a : α // a∉Set.range e}
instance instFintypeComplement (e : β ↪ α) : Fintype (complement e) := Fintype.ofFinite _
instance instDecidableEqComplement (e : β ↪ α) : DecidableEq (complement e) := Classical.decEq _

def coordinates (e : β ↪ α) : β⊕complement e ≃ α := by
  classical
  letI : DecidablePred (fun a => a∈Set.range e) := Classical.decPred _
  exact (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range e))

@[simp] theorem coordinates_inl
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : β ↪ α) (i : β) : coordinates e (Sum.inl i)=e i := rfl
@[simp] theorem coordinates_inr
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : β ↪ α) (i : complement e) : coordinates e (Sum.inr i)=i.val := rfl

def matrix (e : β ↪ α) (A : Matrix β β ℂ) : Matrix α α ℂ :=
  Matrix.reindex (coordinates e) (coordinates e) (Matrix.fromBlocks A 0 0 (1 : Matrix (complement e) (complement e) ℂ))

theorem unit (e : β ↪ α) (A : Matrix β β ℂ) (hA : IsUnit A) : IsUnit (matrix e A) :=
  TensorTools.unit_reindex _ _ (Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨hA,isUnit_one⟩)

def pair (i j : α) (hij : i≠j) : Fin 2 ↪ α where
  toFun := fun a => if a=0 then i else j
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

@[simp] theorem pair_zero
    {α : Type} [Fintype α] [DecidableEq α] (i j : α) (hij : i≠j) : pair i j hij 0=i := rfl
@[simp] theorem pair_one
    {α : Type} [Fintype α] [DecidableEq α] (i j : α) (hij : i≠j) : pair i j hij 1=j := by change (if (1 : Fin 2)=0 then i else j)=j; simp

end ExactFourier.Embedded

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.MonomialTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier.MonomialMatrix
open scoped Kronecker
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem mul {A B : Matrix α α ℂ} (hA : MonomialMatrix A) (hB : MonomialMatrix B) :
    MonomialMatrix (A*B) := by
  classical
  obtain ⟨σ,d,hd,ha⟩ := hA
  obtain ⟨τ,e,he,hb⟩ := hB
  refine ⟨τ.trans σ,fun j => d (τ j)*e j,fun j => mul_ne_zero (hd _) (he _),?_⟩
  intro i j
  rw [Matrix.mul_apply]
  simp_rw [hb,mul_ite,mul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,ha,Equiv.trans_apply]
  split_ifs <;> simp_all

theorem unit (A : Matrix α α ℂ) (hA : MonomialMatrix A) : IsUnit A := by
  classical
  obtain ⟨σ,d,hd,ha⟩ := hA
  have he : A=(Matrix.diagonal d).submatrix σ.symm (Equiv.refl _) := by
    ext i j
    rw [ha]
    simp only [Matrix.submatrix_apply,Matrix.diagonal_apply,Equiv.refl_apply]
    by_cases h : i=σ j
    · subst i; simp
    · have hj : σ.symm i≠j := by intro hj; apply h; simpa using congrArg σ hj
      simp [h,hj]
  rw [he]
  exact (Matrix.isUnit_submatrix_equiv σ.symm (Equiv.refl _)).mpr
    (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr (fun i => isUnit_iff_ne_zero.mpr (hd i))))

end ExactFourier.MonomialMatrix

end

section
noncomputable section
namespace ExactFourier
variable {α : Type} [Fintype α] [DecidableEq α]

def permM (e : Equiv.Perm α) : Matrix α α ℂ := fun i j=>if i=e j then 1 else 0

theorem permM_monomial
    {α : Type} [Fintype α] [DecidableEq α] (e : Equiv.Perm α) : MonomialMatrix (permM e) :=
  ⟨e,fun _=>1,by simp,by intro i j; rfl⟩

theorem permM_mul_apply (e : Equiv.Perm α) (X : Matrix α α ℂ) (i j : α) :
    (permM e*X) i j=X (e.symm i) j := by
  rw [Matrix.mul_apply]
  have he : ∀ k,i=e k ↔ k=e.symm i := by
    intro k
    constructor
    · intro h; simpa using (congrArg e.symm h).symm
    · intro h; simpa using (congrArg e h).symm
  simp only [permM,he,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem mul_permM_apply (e : Equiv.Perm α) (X : Matrix α α ℂ) (i j : α) :
    (X*permM e) i j=X i (e j) := by
  rw [Matrix.mul_apply]
  simp only [permM,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem permM_inv (e : Equiv.Perm α) : (permM e)⁻¹=permM e.symm := by
  apply Matrix.inv_eq_left_inv
  ext i j
  rw [permM_mul_apply]
  simp [permM,Matrix.one_apply]

theorem permM_conj (e : Equiv.Perm α) (X : Matrix α α ℂ) :
    permM e*X*(permM e)⁻¹=X.submatrix e.symm e.symm := by
  rw [permM_inv]
  ext i j
  rw [mul_permM_apply,permM_mul_apply]
  rfl

theorem permM_conj_single (e : Equiv.Perm α) (i j : α) :
    permM e*Matrix.single i j (1:ℂ)*(permM e)⁻¹=Matrix.single (e i) (e j) 1 := by
  rw [permM_conj]
  ext a b
  simp only [Matrix.submatrix_apply,Matrix.single]
  have hi : i=e.symm a ↔ e i=a := e.eq_symm_apply
  have hj : j=e.symm b ↔ e j=b := e.eq_symm_apply
  simp [hi,hj]

theorem exists_perm_pair
    {α : Type} [Fintype α] [DecidableEq α] (i j a b : α) (hij : i≠j) (hab : a≠b) :
    ∃ e : Equiv.Perm α,e i=a ∧ e j=b := by
  let s := Equiv.swap i a
  have hs : s j≠a := by
    have he : s i=a := Equiv.swap_apply_left i a
    rw [← he]
    exact s.injective.ne hij.symm
  let e := s.trans (Equiv.swap (s j) b)
  refine ⟨e,?_,?_⟩
  · change Equiv.swap (s j) b (s i)=a
    rw [show s i=a from Equiv.swap_apply_left i a,Equiv.swap_apply_of_ne_of_ne hs.symm hab]
  · exact Equiv.swap_apply_left (s j) b

end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier.Embedded
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

@[simp] theorem matrix_coordinates
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : β ↪ α) (A : Matrix β β ℂ)
    (i j : β⊕complement e) :
    matrix e A (coordinates e i) (coordinates e j)=
      Matrix.fromBlocks A 0 0 (1 : Matrix (complement e) (complement e) ℂ) i j := by
  simp [matrix,Matrix.reindex_apply]

@[simp] theorem matrix_on (e : β ↪ α) (A : Matrix β β ℂ) (i j : β) :
    matrix e A (e i) (e j)=A i j := by
  exact matrix_coordinates e A (Sum.inl i) (Sum.inl j)

theorem matrix_off_row (e : β ↪ α) (A : Matrix β β ℂ) (i j : α)
    (hi : i∉Set.range e) : matrix e A i j=if i=j then 1 else 0 := by
  obtain ⟨j,rfl⟩ := (coordinates e).surjective j
  have he : i=coordinates e (Sum.inr ⟨i,hi⟩) := rfl
  rw [he,matrix_coordinates]
  cases j with
  | inl j =>
    have hn : i≠e j := fun h=>hi ⟨j,h.symm⟩
    simp [hn]
  | inr j => simp [Matrix.one_apply,Subtype.ext_iff] ; rfl

theorem matrix_off_col (e : β ↪ α) (A : Matrix β β ℂ) (i j : α)
    (hj : j∉Set.range e) : matrix e A i j=if i=j then 1 else 0 := by
  obtain ⟨i,rfl⟩ := (coordinates e).surjective i
  have he : j=coordinates e (Sum.inr ⟨j,hj⟩) := rfl
  rw [he,matrix_coordinates]
  cases i with
  | inl i =>
    have hn : e i≠j := fun h=>hj ⟨i,h⟩
    simp [hn]
  | inr i => simp [Matrix.one_apply,Subtype.ext_iff] ; rfl

@[simp] theorem matrix_one (e : β ↪ α) : matrix e (1 : Matrix β β ℂ)=1 := by
  rw [matrix,Matrix.fromBlocks_one]
  exact (Matrix.reindexAlgEquiv ℂ ℂ (coordinates e)).map_one

theorem matrix_mul (e : β ↪ α) (A B : Matrix β β ℂ) :
    matrix e (A*B)=matrix e A*matrix e B := by
  let φ := Matrix.reindexAlgEquiv ℂ ℂ (coordinates e)
  change φ (Matrix.fromBlocks (A*B) 0 0 1)=φ (Matrix.fromBlocks A 0 0 1)*φ (Matrix.fromBlocks B 0 0 1)
  rw [← map_mul]
  congr 1
  simp [Matrix.fromBlocks_multiply]

theorem matrix_comp (e : γ ↪ β) (f : β ↪ α) (A : Matrix γ γ ℂ) :
    matrix f (matrix e A)=matrix (e.trans f) A := by
  classical
  ext i j
  by_cases hi : i∈Set.range f
  · obtain ⟨a,rfl⟩ := hi
    by_cases hj : j∈Set.range f
    · obtain ⟨b,rfl⟩ := hj
      rw [matrix_on]
      by_cases ha : a∈Set.range e
      · obtain ⟨a,rfl⟩ := ha
        by_cases hb : b∈Set.range e
        · obtain ⟨b,rfl⟩ := hb
          exact (matrix_on e A a b).trans (matrix_on (e.trans f) A a b).symm
        · rw [matrix_off_col e A _ _ hb,matrix_off_col (e.trans f) A]
          · simp only [f.injective.eq_iff]
          · rintro ⟨b',hb'⟩; exact hb ⟨b',f.injective hb'⟩
      · rw [matrix_off_row e A _ _ ha,matrix_off_row (e.trans f) A]
        · simp only [f.injective.eq_iff]
        · rintro ⟨a',ha'⟩; exact ha ⟨a',f.injective ha'⟩
    · rw [matrix_off_col f _ _ _ hj,matrix_off_col (e.trans f) A]
      rintro ⟨b,hb⟩; exact hj ⟨e b,hb⟩
  · rw [matrix_off_row f _ _ _ hi,matrix_off_row (e.trans f) A]
    rintro ⟨a,ha⟩; exact hi ⟨e a,ha⟩

@[simp] theorem matrix_equiv (e : β≃α) (A : Matrix β β ℂ) :
    matrix e.toEmbedding A=Matrix.reindex e e A := by
  ext i j
  obtain ⟨i,rfl⟩ := e.surjective i
  obtain ⟨j,rfl⟩ := e.surjective j
  change matrix e.toEmbedding A (e.toEmbedding i) (e.toEmbedding j)=_
  rw [matrix_on]
  simp [Matrix.reindex_apply]

end ExactFourier.Embedded

end
end

section
noncomputable section
namespace ExactFourier.MonomialMatrix
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem reindex
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : α≃β) {A : Matrix α α ℂ} (hA : MonomialMatrix A) :
    MonomialMatrix (Matrix.reindex e e A) := by
  obtain ⟨s,d,hd,hs⟩ := hA
  refine ⟨e.symm.trans (s.trans e),fun j=>d (e.symm j),fun j=>hd _,?_⟩
  intro i j
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,hs,Equiv.trans_apply]
  have hh : e.symm i=s (e.symm j) ↔ i=e (s (e.symm j)) := e.symm_apply_eq
  simp only [hh]
  rfl

theorem directSum
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] {A : Matrix α α ℂ} {B : Matrix β β ℂ}
    (hA : MonomialMatrix A) (hB : MonomialMatrix B) :
    MonomialMatrix (Matrix.fromBlocks A 0 0 B) := by
  obtain ⟨s,d,hd,hs⟩ := hA
  obtain ⟨t,e,he,ht⟩ := hB
  refine ⟨s.sumCongr t,Sum.elim d e,?_,?_⟩
  · intro j; cases j <;> simp [hd,he]
  · intro i j; cases i <;> cases j <;> simp [hs,ht]

theorem blockDiagonal' {π : Type} [Fintype π] [DecidableEq π]
    {β : π→Type} [∀ i,Fintype (β i)] [∀ i,DecidableEq (β i)]
    (A : ∀ i,Matrix (β i) (β i) ℂ) (hA : ∀ i,MonomialMatrix (A i)) :
    MonomialMatrix (Matrix.blockDiagonal' A) := by
  classical
  choose s d hd hs using hA
  refine ⟨Equiv.sigmaCongrRight s,fun j=>d j.1 j.2,fun j=>hd _ _,?_⟩
  rintro ⟨i,a⟩ ⟨j,b⟩
  by_cases h : i=j
  · subst j
    simp [hs]
  · simp [Matrix.blockDiagonal'_apply,h,Equiv.sigmaCongrRight_apply]

theorem embed (e : β ↪ α) {A : Matrix β β ℂ} (hA : MonomialMatrix A) :
    MonomialMatrix (Embedded.matrix e A) :=
  reindex _ (hA.directSum one)

end ExactFourier.MonomialMatrix

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
variable {α : Type} [Fintype α] [DecidableEq α]

/-- Exact positive pattern: k forward calls, interleaved with arbitrary monomials. -/
inductive Pattern (A : Matrix α α ℂ) : ℕ → Matrix α α ℂ → Prop
  | zero (M) (hM : MonomialMatrix M) : Pattern A 0 M
  | succ {k H} (hH : Pattern A k H) (M) (hM : MonomialMatrix M) : Pattern A (k+1) (H*A*M)

theorem pattern_unit {A H : Matrix α α ℂ} {k : ℕ} (hA : IsUnit A) (h : Pattern A k H) : IsUnit H := by
  induction h with
  | zero M hM => exact MonomialMatrix.unit M hM
  | succ h M hM ih => exact (ih.mul hA).mul (MonomialMatrix.unit M hM)

/-- If every column projector is diagonal, the matrix is monomial. -/
theorem monomial_of_projectors (A : Matrix α α ℂ) (hA : IsUnit A)
    (hp : ∀ k i j,i≠j → A i k*A⁻¹ k j=0) : MonomialMatrix A := by
  classical
  have hdet := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hi := Matrix.nonsing_inv_mul A hdet
  have hc : ∀ k,∃ i,A⁻¹ k i*A i k≠0 := by
    intro k
    have he := congrArg (fun M : Matrix α α ℂ=>M k k) hi
    simp only [Matrix.mul_apply,Matrix.one_apply,ite_true] at he
    by_contra hn
    push Not at hn
    rw [Finset.sum_eq_zero (fun i _=>hn i)] at he
    exact zero_ne_one he
  choose σ hσ using hc
  have hc₁ : ∀ k,A⁻¹ k (σ k)≠0 := fun k => (mul_ne_zero_iff.mp (hσ k)).1
  have hc₂ : ∀ k,A (σ k) k≠0 := fun k => (mul_ne_zero_iff.mp (hσ k)).2
  have hz : ∀ k i,i≠σ k → A i k=0 := by
    intro k i hik
    exact (mul_eq_zero.mp (hp k i (σ k) hik)).resolve_right (hc₁ k)
  have he : ∀ i k,A i k=if i=σ k then A (σ k) k else 0 := by
    intro i k; split_ifs with h
    · subst i; rfl
    · exact hz k i h
  have hinj : Function.Injective σ := by
    intro k l hkl
    by_contra hne
    have hh := congrArg (fun M : Matrix α α ℂ=>M k l) hi
    simp only [Matrix.mul_apply,Matrix.one_apply,ite_eq_right hne] at hh
    have hsum : (∑ i,A⁻¹ k i*A i l)=A⁻¹ k (σ l)*A (σ l) l := by
      apply Finset.sum_eq_single (σ l)
      · intro i _ hne; rw [hz l i hne,mul_zero]
      · simp
    rw [hsum] at hh
    apply (mul_ne_zero (hc₁ k) (hc₂ l))
    simpa only [hkl] using hh
  let e : Equiv.Perm α := Equiv.ofBijective σ (⟨hinj,Finite.surjective_of_injective hinj⟩)
  exact ⟨e,fun k=>A (σ k) k,hc₂,he⟩

theorem exists_nondiagonal_projector (A : Matrix α α ℂ) (hA : IsUnit A) (hn : ¬MonomialMatrix A) :
    ∃ k i j,i≠j ∧ A i k*A⁻¹ k j≠0 := by
  by_contra h
  apply hn
  apply monomial_of_projectors A hA
  push Not at h
  exact h

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
variable {α : Type} [Fintype α] [DecidableEq α]

def changeSign (i : α) : Matrix α α ℂ := Matrix.diagonal (fun j=>if j=i then -1 else 1)
def doubleCoord (i : α) : Matrix α α ℂ := Matrix.diagonal (fun j=>if j=i then 2 else 1)

theorem changeSign_square (i : α) : changeSign i*changeSign i=1 := by
  rw [changeSign,Matrix.diagonal_mul_diagonal]
  ext a b; by_cases h : a=i <;> simp [Matrix.diagonal_apply,Matrix.one_apply,h]

theorem changeSign_inv (i : α) : (changeSign i)⁻¹=changeSign i := Matrix.inv_eq_left_inv (changeSign_square i)

theorem changeSign_monomial
    {α : Type} [Fintype α] [DecidableEq α] (i : α) : MonomialMatrix (changeSign i) :=
  MonomialMatrix.diagonal _ (by intro j; split_ifs <;> norm_num)

theorem doubleCoord_monomial
    {α : Type} [Fintype α] [DecidableEq α] (i : α) : MonomialMatrix (doubleCoord i) :=
  MonomialMatrix.diagonal _ (by intro j; split_ifs <;> norm_num)

theorem doubleCoord_inv (i : α) : (doubleCoord i)⁻¹=Matrix.diagonal (fun j=>if j=i then (1/2:ℂ) else 1) := by
  apply Matrix.inv_eq_left_inv
  rw [doubleCoord,Matrix.diagonal_mul_diagonal]
  ext a b; by_cases h : a=i <;> simp [Matrix.diagonal_apply,Matrix.one_apply,h]

def cut (i : α) (X : Matrix α α ℂ) := X-changeSign i*X*changeSign i

theorem cut_apply (i a b : α) (X : Matrix α α ℂ) :
    cut i X a b=if (a=i ∧ b≠i) ∨ (a≠i ∧ b=i) then 2*X a b else 0 := by
  simp only [cut,Matrix.sub_apply,changeSign,Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases ha : a=i <;> by_cases hb : b=i <;> simp [ha,hb] <;> ring

theorem double_cut (i j : α) (hij : i≠j) (X : Matrix α α ℂ) :
    cut i (cut j X)=(4:ℂ)•(X i j•Matrix.single i j 1+X j i•Matrix.single j i 1) := by
  ext a b
  simp only [cut_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.single]
  by_cases hai : a=i <;> by_cases haj : a=j <;> by_cases hbi : b=i <;> by_cases hbj : b=j <;>
    simp_all [eq_comm] <;> ring

theorem isolate_identity (i j : α) (hij : i≠j) (X : Matrix α α ℂ) :
    doubleCoord i*cut i (cut j X)*(doubleCoord i)⁻¹-(1/2:ℂ)•cut i (cut j X)=
      (6*X i j)•Matrix.single i j 1 := by
  rw [double_cut i j hij X,doubleCoord_inv]
  ext a b
  simp only [doubleCoord,Matrix.sub_apply,Matrix.mul_diagonal,Matrix.diagonal_mul,
    Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.single]
  by_cases hai : a=i <;> by_cases haj : a=j <;> by_cases hbi : b=i <;> by_cases hbj : b=j <;>
    simp_all [eq_comm] <;> ring

theorem single_mem_of_offdiagonal (V : Submodule ℂ (Matrix α α ℂ))
    (hc : ∀ M : Matrix α α ℂ,MonomialMatrix M → ∀ X∈V,M*X*M⁻¹∈V)
    {X : Matrix α α ℂ} (hX : X∈V) (i j : α) (hij : i≠j) (hx : X i j≠0) :
    Matrix.single i j (1:ℂ)∈V := by
  have hcut : ∀ i X,X∈V → cut i X∈V := by
    intro i X hX
    apply V.sub_mem hX
    simpa only [changeSign_inv] using hc (changeSign i) (changeSign_monomial i) X hX
  have hy := hcut i _ (hcut j X hX)
  have hz := V.sub_mem (hc (doubleCoord i) (doubleCoord_monomial i) _ hy) (V.smul_mem (1/2:ℂ) hy)
  rw [isolate_identity i j hij X] at hz
  have hh := V.smul_mem ((6*X i j)⁻¹) hz
  have hn : (6:ℂ)*X i j≠0 := mul_ne_zero (by norm_num) hx
  simpa only [smul_smul,inv_mul_cancel₀ hn,one_smul] using hh

end ExactFourier.PositiveGeneration

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.PositiveReach
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.PositiveGeneration
variable {α : Type} [Fintype α] [DecidableEq α]

theorem Pattern.monomial_right {A H : Matrix α α ℂ} {k : ℕ} (h : Pattern A k H)
    (M : Matrix α α ℂ) (hM : MonomialMatrix M) : Pattern A k (H*M) := by
  induction h with
  | zero N hN => exact .zero _ (hN.mul hM)
  | succ h N hN ih => simpa only [mul_assoc] using Pattern.succ h (N*M) (hN.mul hM)

theorem Pattern.mul {A H K : Matrix α α ℂ} {k l : ℕ} (hH : Pattern A k H) (hK : Pattern A l K) :
    Pattern A (k+l) (H*K) := by
  induction hK with
  | zero M hM => simpa using hH.monomial_right M hM
  | @succ l K h M hM ih => simpa only [Nat.add_assoc,mul_assoc] using Pattern.succ ih M hM

def Reach (A H : Matrix α α ℂ) : Prop := ∃ k,Pattern A k H

theorem Reach.one (A : Matrix α α ℂ) : Reach A 1 := ⟨0,.zero 1 MonomialMatrix.one⟩
theorem Reach.monomial (A M : Matrix α α ℂ) (hM : MonomialMatrix M) : Reach A M := ⟨0,.zero M hM⟩
theorem Reach.self (A : Matrix α α ℂ) : Reach A A := by
  refine ⟨1,?_⟩
  simpa using Pattern.succ (Pattern.zero (A := A) 1 MonomialMatrix.one) 1 MonomialMatrix.one

theorem Reach.mul {A H K : Matrix α α ℂ} (hH : Reach A H) (hK : Reach A K) : Reach A (H*K) := by
  obtain ⟨k,hk⟩ := hH
  obtain ⟨l,hl⟩ := hK
  exact ⟨k+l,hk.mul hl⟩

theorem Reach.unit {A H : Matrix α α ℂ} (hA : IsUnit A) (hH : Reach A H) : IsUnit H := by
  obtain ⟨k,hk⟩ := hH
  exact pattern_unit hA hk

def directions (A : Matrix α α ℂ) : Set (Matrix α α ℂ) :=
  {X | ∃ (s : Matrix α α ℂ),Reach A s ∧ ∃ d : α→ℂ,X=s*Matrix.diagonal d*s⁻¹}

def tangentSpan (A : Matrix α α ℂ) : Submodule ℂ (Matrix α α ℂ) := Submodule.span ℂ (directions A)

theorem direction_mem (A s : Matrix α α ℂ) (hs : Reach A s) (d : α→ℂ) :
    s*Matrix.diagonal d*s⁻¹∈tangentSpan A := Submodule.subset_span ⟨s,hs,d,rfl⟩

theorem diagonal_mem (A : Matrix α α ℂ) (d : α→ℂ) : Matrix.diagonal d∈tangentSpan A := by
  simpa using direction_mem A 1 (Reach.one A) d

theorem tangent_conj (A s : Matrix α α ℂ) (hs : Reach A s) {X : Matrix α α ℂ}
    (hX : X∈tangentSpan A) : s*X*s⁻¹∈tangentSpan A := by
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨t,ht,d,rfl⟩ := hX
    have hh := direction_mem A (s*t) (hs.mul ht) d
    simpa only [Matrix.mul_inv_rev,mul_assoc] using hh
  | zero => simp
  | add X Y hX hY ihX ihY => simpa only [mul_add,add_mul] using (tangentSpan A).add_mem ihX ihY
  | smul c X hX ih => simpa only [Matrix.mul_smul,Matrix.smul_mul] using (tangentSpan A).smul_mem c ih

theorem tangent_monomial_conj (A M : Matrix α α ℂ) (hM : MonomialMatrix M)
    (X : Matrix α α ℂ) (hX : X∈tangentSpan A) : M*X*M⁻¹∈tangentSpan A :=
  tangent_conj A M (Reach.monomial A M hM) hX

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
variable {α : Type} [Fintype α] [DecidableEq α]

theorem single_diagonal
    {α : Type} [Fintype α] [DecidableEq α] (k : α) : Matrix.diagonal (Pi.single k (1:ℂ))=Matrix.single k k 1 := by
  ext i j
  by_cases hi : i=k <;> by_cases hj : j=k <;>
    simp [Matrix.diagonal_apply,Matrix.single,hi,hj] <;> aesop

theorem projector_apply (A : Matrix α α ℂ) (k i j : α) :
    (A*Matrix.single k k (1:ℂ)*A⁻¹) i j=A i k*A⁻¹ k j := by
  simp [Matrix.mul_apply,Matrix.single,ite_and]

theorem tangent_top (A : Matrix α α ℂ) (hA : IsUnit A) (hn : ¬MonomialMatrix A) :
    tangentSpan A=⊤ := by
  obtain ⟨k,i,j,hij,hx⟩ := exists_nondiagonal_projector A hA hn
  have hp := direction_mem A A (Reach.self A) (Pi.single k 1)
  rw [single_diagonal] at hp
  have hx' : (A*Matrix.single k k (1:ℂ)*A⁻¹) i j≠0 := by rw [projector_apply]; exact hx
  have he := single_mem_of_offdiagonal (tangentSpan A) (tangent_monomial_conj A) hp i j hij hx'
  have hall : ∀ a b,Matrix.single a b (1:ℂ)∈tangentSpan A := by
    intro a b
    by_cases hab : a=b
    · subst b
      rw [← single_diagonal]
      exact diagonal_mem A _
    · obtain ⟨e,hei,hej⟩ := exists_perm_pair i j a b hij hab
      have ht := tangent_monomial_conj A (permM e) (permM_monomial e) _ he
      rwa [permM_conj_single,hei,hej] at ht
  apply Submodule.eq_top_iff'.mpr
  intro X
  have hdec : X=∑ a,∑ b,X a b•Matrix.single a b (1:ℂ) := by
    ext i j
    simp [Matrix.sum_apply,Matrix.single,ite_and]
  rw [hdec]
  exact (tangentSpan A).sum_mem (fun a _ => (tangentSpan A).sum_mem (fun b _ => (tangentSpan A).smul_mem _ (hall a b)))

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
variable {α : Type} [Fintype α] [DecidableEq α]

def conjLinear (p : Matrix α α ℂ) : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ where
  toFun X := p*X*p⁻¹
  map_add' _ _ := by simp [mul_add,add_mul]
  map_smul' _ _ := by simp

def diagLinear : (α→ℂ) →ₗ[ℂ] Matrix α α ℂ where
  toFun := Matrix.diagonal
  map_add' _ _ := (Matrix.diagonal_add _ _).symm
  map_smul' _ _ := Matrix.diagonal_smul _ _

def diagConj (p : Matrix α α ℂ) : Submodule ℂ (Matrix α α ℂ) :=
  LinearMap.range ((conjLinear p).comp diagLinear)

@[simp] theorem mem_diagConj (p X : Matrix α α ℂ) :
    X∈diagConj p ↔ ∃ d : α→ℂ,p*Matrix.diagonal d*p⁻¹=X := Iff.rfl

inductive Chain (A : Matrix α α ℂ) : Matrix α α ℂ → Submodule ℂ (Matrix α α ℂ) → Prop
 | nil : Chain A 1 (diagConj 1)
 | snoc {p U s} : Chain A p U → Reach A s → Chain A (p*s) (U⊔diagConj (p*s))

theorem Chain.reach {A p : Matrix α α ℂ} {U} (h : Chain A p U) : Reach A p := by
  induction h with
  | nil => exact Reach.one A
  | snoc h hs ih => exact ih.mul hs

theorem directions_after_span (A p : Matrix α α ℂ) (hA : IsUnit A)
    (hn : ¬MonomialMatrix A) (hp : IsUnit p) (U : Submodule ℂ (Matrix α α ℂ))
    (h : ∀ s,Reach A s → diagConj (p*s)≤U) : U=⊤ := by
  have hh : ∀ X∈tangentSpan A,p*X*p⁻¹∈U := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem X hX =>
      obtain ⟨s,hs,d,rfl⟩ := hX
      have he : (p*s)*Matrix.diagonal d*(p*s)⁻¹∈U := h s hs ⟨d,rfl⟩
      simpa only [Matrix.mul_inv_rev,mul_assoc] using he
    | zero => simp
    | add X Y hX hY ihX ihY => simpa only [mul_add,add_mul] using U.add_mem ihX ihY
    | smul c X hX ih => simpa only [Matrix.mul_smul,Matrix.smul_mul] using U.smul_mem c ih
  rw [tangent_top A hA hn] at hh
  apply Submodule.eq_top_iff'.mpr
  intro X
  have ht := hh (p⁻¹*X*p) (Submodule.mem_top)
  have hi := Matrix.mul_nonsing_inv p ((Matrix.isUnit_iff_isUnit_det _).mp hp)
  have he : p*(p⁻¹*X*p)*p⁻¹=X := by
    calc
      _ = (p*p⁻¹)*X*(p*p⁻¹) := by noncomm_ring
      _ = X := by rw [hi]; simp
  rwa [he] at ht

theorem exists_full_chain (A : Matrix α α ℂ) (hA : IsUnit A) (hn : ¬MonomialMatrix A) :
    ∃ p,Chain A p ⊤ := by
  let P : Submodule ℂ (Matrix α α ℂ) → Prop := fun U=>∃ p,Chain A p U
  obtain ⟨U,hU,hmax⟩ := exists_maximal_of_wellFoundedGT P ⟨diagConj 1,1,Chain.nil⟩
  obtain ⟨p,hp⟩ := hU
  have htop : U=⊤ := by
    apply directions_after_span A p hA hn (hp.reach.unit hA) U
    intro s hs
    have hh : P (U⊔diagConj (p*s)) := ⟨p*s,Chain.snoc hp hs⟩
    exact le_trans le_sup_right (hmax hh le_sup_left)
  exact ⟨p,htop ▸ hp⟩

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
open Topology
variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]

def genericPoint (R : Type*) [CommRing R] [IsDomain R] : PrimeSpectrum R := ⟨⊥,inferInstance⟩

theorem generic_mem_open {U : Set (PrimeSpectrum R)} (hU : IsOpen U) (hne : U.Nonempty) :
    genericPoint R∈U := by
  obtain ⟨x,hx⟩ := hne
  rw [PrimeSpectrum.eq_biUnion_of_isOpen hU] at hx
  obtain ⟨p,hp,hxp⟩ := Set.mem_iUnion₂.mp hx
  apply hp
  change p∉(⊥ : Ideal R)
  intro hz
  have hpz : p=0 := hz
  exact hxp (hpz ▸ x.asIdeal.zero_mem)

theorem constructible_generic_nhds {T : Set (PrimeSpectrum R)} (hT : IsConstructible T) :
    ∃ U : Set (PrimeSpectrum R),IsOpen U ∧ genericPoint R∈U ∧
      ∀ x∈U,(x∈T ↔ genericPoint R∈T) := by
  induction hT using IsConstructible.empty_union_induction with
  | open_retrocompact V hV hc =>
    by_cases hg : genericPoint R∈V
    · exact ⟨V,hV,hg,fun x hx=>⟨fun _=>hg,fun _=>hx⟩⟩
    · have hv : V=∅ := Set.eq_empty_iff_forall_notMem.mpr (fun x hx=>hg (generic_mem_open hV ⟨x,hx⟩))
      subst V
      exact ⟨Set.univ,isOpen_univ,Set.mem_univ _,by simp⟩
  | union V hV W hW ihV ihW =>
    obtain ⟨U,hU,hg,hue⟩ := ihV
    obtain ⟨Z,hZ,hgz,hze⟩ := ihW
    exact ⟨U∩Z,hU.inter hZ,⟨hg,hgz⟩,fun x hx=>or_congr (hue x hx.1) (hze x hx.2)⟩
  | compl V hV ih =>
    obtain ⟨U,hU,hg,he⟩ := ih
    exact ⟨U,hU,hg,fun x hx=>not_congr (he x hx)⟩

theorem constructible_contains_basic {T : Set (PrimeSpectrum R)} (hT : IsConstructible T)
    (hg : genericPoint R∈T) : ∃ g : R,g≠0 ∧ (PrimeSpectrum.basicOpen g : Set _)⊆T := by
  obtain ⟨U,hU,hu,he⟩ := constructible_generic_nhds hT
  rw [PrimeSpectrum.eq_biUnion_of_isOpen hU] at hu
  obtain ⟨g,hgU,hgg⟩ := Set.mem_iUnion₂.mp hu
  refine ⟨g,?_,fun x hx=>(he x (hgU hx)).mpr hg⟩
  simpa [genericPoint] using hgg

/-- A dominant finite-presentation map meets an actual nonempty basic open,
not merely its closure. This is the open-image step in positive generation. -/
theorem dominant_open_image (f : R →+* S) (hf : f.FinitePresentation)
    (hinj : Function.Injective f) (p : S) (hp : p≠0) :
    ∃ g : R,g≠0 ∧ (PrimeSpectrum.basicOpen g : Set _)⊆
      PrimeSpectrum.comap f '' (PrimeSpectrum.basicOpen p : Set _) := by
  apply constructible_contains_basic
    (PrimeSpectrum.isConstructible_comap_image hf PrimeSpectrum.isConstructible_basicOpen)
  refine ⟨genericPoint S,?_,?_⟩
  · simpa [genericPoint] using hp
  · apply PrimeSpectrum.ext
    change Ideal.comap f ⊥=⊥
    ext x
    change f x=0 ↔ x=0
    exact map_eq_zero_iff f hinj

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
open MvPolynomial
variable {ι κ : Type} [Finite ι] [Finite κ]

theorem polynomial_hom_finitePresentation
    (f : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial κ ℂ) : f.toRingHom.FinitePresentation := by
  apply RingHom.FinitePresentation.of_finiteType.mp
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (MvPolynomial ι ℂ))
  change (f.toRingHom.comp (algebraMap ℂ (MvPolynomial ι ℂ))).FiniteType
  have he : f.toRingHom.comp (algebraMap ℂ (MvPolynomial ι ℂ)) =
      algebraMap ℂ (MvPolynomial κ ℂ) := by ext1 c; exact f.commutes c
  rw [he]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

theorem maximal_avoiding {R : Type*} [CommRing R] [IsJacobsonRing R]
    (I : Ideal R) (hI : I.IsPrime) (p : R) (hp : p∉I) :
    ∃ J : Ideal R,J.IsMaximal ∧ I≤J ∧ p∉J := by
  by_contra h
  push Not at h
  apply hp
  rw [← IsJacobsonRing.out (inferInstance : IsJacobsonRing R) hI.isRadical]
  rw [Ideal.jacobson,Ideal.mem_sInf]
  intro J hJ
  exact h J hJ.2 hJ.1

/-- Point-level consequence of Chevalley and the Nullstellensatz. -/
theorem polynomial_open_image (f : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial κ ℂ)
    (hinj : Function.Injective f) (p : MvPolynomial κ ℂ) (hp : p≠0) :
    ∃ g : MvPolynomial ι ℂ,g≠0 ∧ ∀ y : ι→ℂ,aeval y g≠0 →
      ∃ x : κ→ℂ,aeval x p≠0 ∧ ∀ i,aeval x (f (X i))=y i := by
  obtain ⟨g,hg,hgi⟩ := dominant_open_image f.toRingHom (polynomial_hom_finitePresentation f) hinj p hp
  refine ⟨g,hg,?_⟩
  intro y hy
  have hyp : pointToPoint (k := ℂ) y∈PrimeSpectrum.basicOpen g := by
    change g∉vanishingIdeal ℂ {y}
    simpa only [mem_vanishingIdeal_singleton_iff] using hy
  obtain ⟨q,hqp,hq⟩ := hgi hyp
  obtain ⟨J,hJ,hqJ,hpJ⟩ := maximal_avoiding q.asIdeal q.isPrime p hqp
  have hcontract : Ideal.comap f.toRingHom J=vanishingIdeal ℂ {y} := by
    symm
    apply Ideal.IsMaximal.eq_of_le (inferInstance : (vanishingIdeal ℂ {y}).IsMaximal)
      (Ideal.comap_ne_top _ hJ.ne_top)
    have he := congrArg PrimeSpectrum.asIdeal hq
    change Ideal.comap f.toRingHom q.asIdeal=vanishingIdeal ℂ {y} at he
    rw [← he]
    exact Ideal.comap_mono hqJ
  obtain ⟨x,hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal ℂ hJ
  refine ⟨x,?_,?_⟩
  · rw [hx] at hpJ
    simpa only [mem_vanishingIdeal_singleton_iff] using hpJ
  · intro i
    have hpoly : X i-C (y i)∈vanishingIdeal ℂ {y} := by
      rw [mem_vanishingIdeal_singleton_iff]; simp
    rw [← hcontract] at hpoly
    change f (X i-C (y i))∈J at hpoly
    rw [hx,mem_vanishingIdeal_singleton_iff] at hpoly
    apply sub_eq_zero.mp
    simpa using hpoly

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
open MvPolynomial Filter Topology
variable {ι κ : Type} [Fintype ι] [Fintype κ]

def polynomialMap (f : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial κ ℂ) (x : κ→ℂ) : ι→ℂ :=
  fun i=>aeval x (f (X i))

theorem eval_polynomialMap
    {ι : Type} {κ : Type} [Fintype ι] [Fintype κ] (f : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial κ ℂ)
    (x : κ→ℂ) (p : MvPolynomial ι ℂ) :
    aeval (polynomialMap f x) p=aeval x (f p) := by
  have he : (aeval x).comp f=aeval (polynomialMap f x) := by ext; simp [polynomialMap]
  exact (AlgHom.congr_fun he p).symm

/-- A surjective strict derivative certifies dominance, with no dimension
reduction or extra algebraic hypotheses. -/
theorem injective_of_submersion (f : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial κ ℂ)
    (x : κ→ℂ) (d : (κ→ℂ) →L[ℂ] (ι→ℂ))
    (hd : HasStrictFDerivAt (polynomialMap f) d x) (hs : d.range=⊤) :
    Function.Injective f := by
  apply (injective_iff_map_eq_zero f).mpr
  intro p hp
  have hzero : (fun y : ι→ℂ=>aeval y p)=ᶠ[𝓝 (polynomialMap f x)] 0 := by
    rw [← hd.map_nhds_eq_of_surj hs]
    change ∀ᶠ y in 𝓝 x,aeval (polynomialMap f y) p=0
    exact Filter.Eventually.of_forall (fun y=>by rw [eval_polynomialMap,hp,map_zero])
  have hall := (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) p).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ (polynomialMap f x)) hzero
  apply MvPolynomial.funext
  intro y
  simpa using hall (Set.mem_univ y)

end ExactFourier.PositiveGeneration

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.ParameterAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.PositiveGeneration
open MvPolynomial
open scoped Matrix.Norms.Operator
variable {α κ : Type} [Fintype α] [DecidableEq α]

def evalMatrix (F : Matrix α α (MvPolynomial κ ℂ)) (x : κ→ℂ) : Matrix α α ℂ :=
  (aeval x).mapMatrix F

@[simp] theorem evalMatrix_apply (F : Matrix α α (MvPolynomial κ ℂ)) (x : κ→ℂ) (i j : α) :
    evalMatrix F x i j=aeval x (F i j) := rfl

@[simp] theorem evalMatrix_mul (F G : Matrix α α (MvPolynomial κ ℂ)) (x : κ→ℂ) :
    evalMatrix (F*G) x=evalMatrix F x*evalMatrix G x := map_mul _ _ _

@[simp] theorem evalMatrix_const (M : Matrix α α ℂ) (x : κ→ℂ) :
    evalMatrix (C.mapMatrix M) x=M := by ext i j; simp [evalMatrix]

@[simp] theorem evalMatrix_rename {τ : Type} (e : κ→τ)
    (F : Matrix α α (MvPolynomial κ ℂ)) (x : τ→ℂ) :
    evalMatrix ((rename e).mapMatrix F) x=evalMatrix F (x∘e) := by
  ext i j
  exact aeval_rename e x (F i j)

@[simp] theorem evalMatrix_diag (d : α→MvPolynomial κ ℂ) (x : κ→ℂ) :
    evalMatrix (Matrix.diagonal d) x=Matrix.diagonal (fun i=>aeval x (d i)) := by
  exact Matrix.diagonal_map (map_zero _)

def diagCLM : (α→ℂ) →L[ℂ] Matrix α α ℂ := diagLinear.toContinuousLinearMap
@[simp] theorem diagCLM_apply (x : α→ℂ) : diagCLM x=Matrix.diagonal x := rfl

def leftProj [Fintype κ] : (κ⊕α→ℂ) →L[ℂ] (κ→ℂ) :=
  ContinuousLinearMap.pi (fun i=>ContinuousLinearMap.proj (Sum.inl i))
def rightProj [Fintype κ] : (κ⊕α→ℂ) →L[ℂ] (α→ℂ) :=
  ContinuousLinearMap.pi (fun i=>ContinuousLinearMap.proj (Sum.inr i))
@[simp] theorem leftProj_apply
    {α : Type} {κ : Type} [Fintype α] [DecidableEq α] [Fintype κ] (x : κ⊕α→ℂ) : leftProj x=x∘Sum.inl := rfl
@[simp] theorem rightProj_apply
    {α : Type} {κ : Type} [Fintype α] [DecidableEq α] [Fintype κ] (x : κ⊕α→ℂ) : rightProj x=x∘Sum.inr := rfl

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
open MvPolynomial
open scoped Matrix.Norms.Operator
variable {α : Type} [Fintype α] [DecidableEq α]

/-- A fixed positive word with polynomial diagonal parameters and its exact derivative. -/
structure Param (A p : Matrix α α ℂ) (U : Submodule ℂ (Matrix α α ℂ)) where
  Vars : Type
  finiteVars : Fintype Vars
  poly : Matrix α α (MvPolynomial Vars ℂ)
  calls : ℕ
  base : evalMatrix poly (fun _=>1)=p
  pattern : ∀ x : Vars→ℂ,(∀ i,x i≠0) → Pattern A calls (evalMatrix poly x)
  derivative : letI := finiteVars; (Vars→ℂ) →L[ℂ] Matrix α α ℂ
  deriv : letI := finiteVars; HasStrictFDerivAt (evalMatrix poly) derivative (fun _=>1)
  spans : ∀ X∈U,∃ x : Vars→ℂ,derivative x=X*p

attribute [instance] Param.finiteVars

def Param.nil (A : Matrix α α ℂ) : Param A 1 (diagConj 1) where
  Vars := α
  finiteVars := inferInstance
  poly := Matrix.diagonal X
  calls := 0
  base := by simp
  pattern x hx := by simpa using Pattern.zero (A := A) (Matrix.diagonal x) (MonomialMatrix.diagonal x hx)
  derivative := diagCLM
  deriv := by
    convert! (diagCLM (α := α)).hasStrictFDerivAt (x := fun _=>1) using 1
    funext x
    change evalMatrix (Matrix.diagonal X) x=Matrix.diagonal x
    simp only [evalMatrix_diag,aeval_X]
  spans X hX := by
    obtain ⟨d,hd⟩ := hX
    refine ⟨d,?_⟩
    change 1*Matrix.diagonal d*1⁻¹=X at hd
    simpa using hd

def Param.nextPoly {A p U} (P : Param (α := α) A p U) (s : Matrix α α ℂ) :
    Matrix α α (MvPolynomial (P.Vars⊕α) ℂ) :=
  (rename Sum.inl).mapMatrix P.poly*C.mapMatrix s*Matrix.diagonal (fun i=>X (Sum.inr i))

@[simp] theorem Param.eval_nextPoly {A p U} (P : Param (α := α) A p U) (s : Matrix α α ℂ)
    (x : P.Vars⊕α→ℂ) :
    evalMatrix (P.nextPoly s) x=evalMatrix P.poly (x∘Sum.inl)*s*Matrix.diagonal (x∘Sum.inr) := by
  simp only [Param.nextPoly,evalMatrix_mul,evalMatrix_rename,evalMatrix_const,evalMatrix_diag,aeval_X]
  rfl

def Param.nextDerivative {A p U} (P : Param (α := α) A p U) (s : Matrix α α ℂ) :
    (P.Vars⊕α→ℂ) →L[ℂ] Matrix α α ℂ :=
  ((ContinuousLinearMap.mulLeftRight ℂ (Matrix α α ℂ) 1 s).comp P.derivative).comp leftProj +
  ((ContinuousLinearMap.mulLeftRight ℂ (Matrix α α ℂ) (p*s) 1).comp diagCLM).comp rightProj

@[simp] theorem Param.nextDerivative_apply {A p U} (P : Param (α := α) A p U)
    (s : Matrix α α ℂ) (x : P.Vars⊕α→ℂ) :
    P.nextDerivative s x=P.derivative (x∘Sum.inl)*s+(p*s)*Matrix.diagonal (x∘Sum.inr) := by
  change 1*P.derivative (x∘Sum.inl)*s+(p*s)*Matrix.diagonal (x∘Sum.inr)*1=_
  simp only [one_mul,mul_one]

theorem Param.next_deriv {A p U} (P : Param (α := α) A p U) (s : Matrix α α ℂ) :
    HasStrictFDerivAt (evalMatrix (P.nextPoly s)) (P.nextDerivative s) (fun _=>1) := by
  have h1 := (P.deriv.comp (fun _ : P.Vars⊕α=> (1:ℂ))
    (leftProj (κ := P.Vars) (α := α)).hasStrictFDerivAt).mul_const' s
  have h2 := (diagCLM (α := α)).hasStrictFDerivAt.comp (fun _ : P.Vars⊕α=> (1:ℂ))
    (rightProj (κ := P.Vars) (α := α)).hasStrictFDerivAt
  convert! h1.mul' h2 using 1
  · funext x
    change evalMatrix (P.nextPoly s) x=evalMatrix P.poly (x∘Sum.inl)*s*Matrix.diagonal (x∘Sum.inr)
    exact P.eval_nextPoly s x
  · ext1 x
    change P.nextDerivative s x=(evalMatrix P.poly (fun _=>1)*s)*Matrix.diagonal (x∘Sum.inr)+
      (P.derivative (x∘Sum.inl)*s)*Matrix.diagonal (fun _=>1)
    rw [P.base,Matrix.diagonal_one,mul_one,P.nextDerivative_apply,add_comm]

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
open MvPolynomial
open scoped Matrix.Norms.Operator
variable {α : Type} [Fintype α] [DecidableEq α]

theorem Param.base_unit {A p U} (P : Param (α := α) A p U) (hA : IsUnit A) : IsUnit p := by
  have hu := pattern_unit hA (P.pattern (fun _=>1) (by simp))
  rwa [P.base] at hu

def Param.snoc {A p U} (P : Param (α := α) A p U) (hA : IsUnit A)
    (s : Matrix α α ℂ) (hs : Reach A s) : Param A (p*s) (U⊔diagConj (p*s)) where
  Vars := P.Vars⊕α
  finiteVars := inferInstance
  poly := P.nextPoly s
  calls := P.calls+Classical.choose hs
  base := by simp only [Param.eval_nextPoly,Function.comp_def,P.base,Matrix.diagonal_one,mul_one]
  pattern x hx := by
    rw [Param.eval_nextPoly]
    exact ((P.pattern (x∘Sum.inl) (fun i=>hx (Sum.inl i))).mul (Classical.choose_spec hs)).monomial_right
      _ (MonomialMatrix.diagonal _ (fun i=>hx (Sum.inr i)))
  derivative := P.nextDerivative s
  deriv := P.next_deriv s
  spans X hX := by
    obtain ⟨Y,hY,Z,hZ,rfl⟩ := Submodule.mem_sup.mp hX
    obtain ⟨u,hu⟩ := P.spans Y hY
    obtain ⟨d,hd⟩ := mem_diagConj _ _ |>.mp hZ
    refine ⟨Sum.elim u d,?_⟩
    rw [Param.nextDerivative_apply]
    have hu' : (Sum.elim u d)∘Sum.inl=u := rfl
    have hd' : (Sum.elim u d)∘Sum.inr=d := rfl
    rw [hu',hd',hu]
    have hi := Matrix.nonsing_inv_mul (p*s)
      ((Matrix.isUnit_iff_isUnit_det _).mp ((P.base_unit hA).mul (hs.unit hA)))
    calc
      _ = Y*(p*s)+(p*s)*Matrix.diagonal d := by noncomm_ring
      _ = Y*(p*s)+Z*(p*s) := by
        congr 1
        rw [← hd]
        simp only [mul_assoc,hi,mul_one]
      _ = (Y+Z)*(p*s) := (add_mul _ _ _).symm

theorem Chain.parameterization {A p U} (h : Chain (α := α) A p U) (hA : IsUnit A) :
    Nonempty (Param A p U) := by
  induction h with
  | nil => exact ⟨Param.nil A⟩
  | @snoc p U s h hs ih =>
    obtain ⟨P⟩ := ih
    exact ⟨P.snoc hA s hs⟩

theorem Param.derivative_surjective {A p} (P : Param (α := α) A p ⊤) (hA : IsUnit A) :
    Function.Surjective P.derivative := by
  intro X
  obtain ⟨x,hx⟩ := P.spans (X*p⁻¹) Submodule.mem_top
  refine ⟨x,?_⟩
  rw [mul_assoc,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (P.base_unit hA)),mul_one] at hx
  exact hx

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
open MvPolynomial
open scoped Matrix.Norms.Operator
variable {α : Type} [Fintype α] [DecidableEq α]

def flatten : Matrix α α ℂ ≃ₗ[ℂ] (α×α→ℂ) where
  toFun M ij := M ij.1 ij.2
  invFun x i j := x (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def flatCLM : Matrix α α ℂ ≃L[ℂ] (α×α→ℂ) := flatten.toContinuousLinearEquiv

@[simp] theorem flatCLM_apply
    {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ) (ij : α×α) : flatCLM M ij=M ij.1 ij.2 := rfl

def Param.hom {A p U} (P : Param (α := α) A p U) :
    MvPolynomial (α×α) ℂ →ₐ[ℂ] MvPolynomial P.Vars ℂ := aeval (fun ij=>P.poly ij.1 ij.2)

@[simp] theorem Param.polynomialMap_hom {A p U} (P : Param (α := α) A p U) (x : P.Vars→ℂ) :
    polynomialMap P.hom x=flatCLM (evalMatrix P.poly x) := by
  funext ij
  simp [polynomialMap,Param.hom]

theorem Param.hom_injective {A p} (P : Param (α := α) A p ⊤) (hA : IsUnit A) :
    Function.Injective P.hom := by
  let d := flatCLM.toContinuousLinearMap.comp P.derivative
  apply injective_of_submersion P.hom (fun _=>1) d
  · have hh := (flatCLM (α := α)).toContinuousLinearMap.hasStrictFDerivAt.comp (fun _ : P.Vars=> (1:ℂ)) P.deriv
    convert! hh using 1
    funext x
    exact P.polynomialMap_hom x
  · apply LinearMap.range_eq_top.mpr
    exact flatCLM.surjective.comp (P.derivative_surjective hA)

theorem Param.open_word {A p} (P : Param (α := α) A p ⊤) (hA : IsUnit A) :
    ∃ g : MvPolynomial (α×α) ℂ,g≠0 ∧ ∀ H : Matrix α α ℂ,
      aeval (flatCLM H) g≠0 → Pattern A P.calls H := by
  classical
  let q : MvPolynomial P.Vars ℂ := ∏ i,X i
  have hq : q≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>X_ne_zero i)
  obtain ⟨g,hg,hgi⟩ := polynomial_open_image P.hom (P.hom_injective hA) q hq
  refine ⟨g,hg,?_⟩
  intro H hH
  obtain ⟨x,hx,hxH⟩ := hgi (flatCLM H) hH
  have hxn : ∀ i,x i≠0 := by
    have hh : (∏ i,x i)≠0 := by simpa [q,map_prod,aeval_X] using hx
    exact fun i=>Finset.prod_ne_zero_iff.mp hh i (Finset.mem_univ i)
  have he : evalMatrix P.poly x=H := by
    ext i j
    have ht := hxH (i,j)
    simpa [Param.hom] using ht
  rw [← he]
  exact P.pattern x hxn

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
open MvPolynomial Filter Topology
variable {ι : Type} [Fintype ι]

/-- Nonempty Zariski basic opens in complex affine space are Euclidean dense. -/
theorem polynomial_nonzero_dense (g : MvPolynomial ι ℂ) (hg : g≠0) :
    Dense {y : ι→ℂ | aeval y g≠0} := by
  rw [dense_iff_inter_open]
  intro U hU hne
  by_contra h
  obtain ⟨z,hz⟩ := hne
  have hzero : (fun y : ι→ℂ=>aeval y g)=ᶠ[𝓝 z] 0 := by
    filter_upwards [hU.mem_nhds hz] with y hy
    by_contra hn
    exact h ⟨y,hy,hn⟩
  have hall := (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) g).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ z) hzero
  apply hg
  apply MvPolynomial.funext
  intro y
  simpa using hall (Set.mem_univ y)

theorem polynomial_nonzero_open (g : MvPolynomial ι ℂ) :
    IsOpen {y : ι→ℂ | aeval y g≠0} := by
  apply isOpen_ne_fun _ continuous_const
  exact continuousOn_univ.mp (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) g).continuousOn

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
open MvPolynomial Filter Topology
open scoped Matrix.Norms.Operator
variable {α : Type} [Fintype α] [DecidableEq α]

theorem Pattern.zero_iff (A H : Matrix α α ℂ) : Pattern A 0 H ↔ MonomialMatrix H := by
  constructor
  · intro h; cases h with | zero M hM => exact hM
  · exact Pattern.zero H

/-- Positive generation, with a common strictly positive number of forward calls. -/
theorem positive_generation (A : Matrix α α ℂ) (hA : IsUnit A) (hn : ¬MonomialMatrix A) :
    ∃ h : ℕ,0<h ∧ ∀ H : Matrix α α ℂ,IsUnit H → Pattern A h H := by
  obtain ⟨p,hp⟩ := exists_full_chain A hA hn
  obtain ⟨P⟩ := hp.parameterization hA
  obtain ⟨g,hg,hgi⟩ := P.open_word hA
  let S : Set (Matrix α α ℂ) := {H | aeval (flatCLM H) g≠0}
  have hSd : Dense S := (polynomial_nonzero_dense g hg).preimage flatCLM.toHomeomorph.isOpenMap
  have hSo : IsOpen S := (polynomial_nonzero_open g).preimage flatCLM.continuous
  have hpat : ∀ H∈S,Pattern A P.calls H := hgi
  obtain ⟨W,hW⟩ := hSd.nonempty
  have hWu : IsUnit W := pattern_unit hA (hpat W hW)
  have hall : ∀ H : Matrix α α ℂ,IsUnit H → Pattern A (P.calls+P.calls) H := by
    intro H hH
    let V₀ := H*W⁻¹
    have hVu : IsUnit V₀ := hH.mul (Matrix.isUnit_nonsing_inv_iff.mpr hWu)
    let f : Matrix α α ℂ → Matrix α α ℂ := fun V=>Ring.inverse V*H
    have hf : ContinuousAt f V₀ := by
      exact ((hVu.unit_spec ▸ NormedRing.inverse_continuousAt hVu.unit)).mul continuousAt_const
    have hfV : f V₀=W := by
      change Ring.inverse (H*W⁻¹)*H=W
      rw [← Matrix.nonsing_inv_eq_ringInverse,Matrix.mul_inv_rev,Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hWu)]
      rw [mul_assoc,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hH),mul_one]
    have hnh : f⁻¹' S∈𝓝 V₀ := hf.preimage_mem_nhds (hSo.mem_nhds (hfV ▸ hW))
    obtain ⟨V,hV,hfVS⟩ := hSd.inter_nhds_nonempty hnh
    have hVp := hpat V hV
    have hVi := Matrix.mul_nonsing_inv V ((Matrix.isUnit_iff_isUnit_det _).mp (pattern_unit hA hVp))
    have hh := hVp.mul (hpat (f V) hfVS)
    have he : V*f V=H := by
      change V*(Ring.inverse V*H)=H
      rw [← Matrix.nonsing_inv_eq_ringInverse,← mul_assoc,hVi,one_mul]
    rwa [he] at hh
  refine ⟨P.calls+P.calls,?_,hall⟩
  by_contra h
  have hz : P.calls+P.calls=0 := Nat.eq_zero_of_not_pos h
  exact hn ((Pattern.zero_iff A A).mp (hz ▸ hall A hA))

end ExactFourier.PositiveGeneration

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.MultiWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} (D : τ→Type) [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
  (A : ∀ t,Matrix (D t) (D t) ℂ)

inductive Step (D : τ→Type) [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
    (A : ∀ t,Matrix (D t) (D t) ℂ) (α : Type) [Fintype α] [DecidableEq α] where
 | mono (M : Matrix α α ℂ) (hm : MonomialMatrix M)
 | call (t : τ) (e : D t ↪ α)

variable {D A} {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def Step.matrix : Step D A α → Matrix α α ℂ
 | .mono M _ => M
 | .call t e => Embedded.matrix e (A t)

def Step.kind : Step D A α → Option τ
 | .mono _ _ => none
 | .call t _ => some t

def Step.embed (e : α ↪ β) : Step D A α → Step D A β
 | .mono M hM => .mono (Embedded.matrix e M) (hM.embed e)
 | .call t f => .call t (f.trans e)

@[simp] theorem Step.matrix_embed (e : α ↪ β) (s : Step D A α) :
    (s.embed e).matrix=Embedded.matrix e s.matrix := by
  cases s with
  | mono M hM => rfl
  | call t f => exact (Embedded.matrix_comp f e (A t)).symm

@[simp] theorem Step.kind_embed (e : α ↪ β) (s : Step D A α) : (s.embed e).kind=s.kind := by cases s <;> rfl

abbrev Word (D : τ→Type) [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
    (A : ∀ t,Matrix (D t) (D t) ℂ) (α : Type) [Fintype α] [DecidableEq α] := List (Step D A α)

def Word.matrix (W : Word D A α) : Matrix α α ℂ := (W.map Step.matrix).prod

def Word.calls (W : Word D A α) : List τ := W.filterMap Step.kind

def Word.count [DecidableEq τ] (W : Word D A α) (t : τ) : ℕ := W.calls.count t

def Word.embed (e : α ↪ β) (W : Word D A α) : Word D A β := W.map (Step.embed e)

@[simp] theorem Word.matrix_nil : (Word.matrix ([] : Word D A α))=1 := rfl
@[simp] theorem Word.matrix_cons (s : Step D A α) (W : Word D A α) :
    Word.matrix (s::W)=s.matrix*W.matrix := rfl
@[simp] theorem Word.matrix_append (W V : Word D A α) : (W++V).matrix=W.matrix*V.matrix := by
  simp [Word.matrix,List.map_append,List.prod_append]
@[simp] theorem Word.calls_append (W V : Word D A α) : (W++V).calls=W.calls++V.calls := by
  simp [Word.calls]
@[simp] theorem Word.count_append [DecidableEq τ] (W V : Word D A α) (t : τ) :
    (W++V).count t=W.count t+V.count t := by simp [Word.count]

@[simp] theorem Word.matrix_embed (e : α ↪ β) (W : Word D A α) :
    (W.embed e).matrix=Embedded.matrix e W.matrix := by
  induction W with
  | nil => simp [Word.embed]
  | cons w W ih =>
    simp only [Word.embed,List.map_cons,Word.matrix_cons,Step.matrix_embed]
    rw [← Word.embed,ih,← Embedded.matrix_mul]

@[simp] theorem Word.calls_embed (e : α ↪ β) (W : Word D A α) : (W.embed e).calls=W.calls := by
  simp [Word.embed,Word.calls,List.filterMap_map]

@[simp] theorem Word.count_embed [DecidableEq τ] (e : α ↪ β) (W : Word D A α) (t : τ) :
    (W.embed e).count t=W.count t := by simp [Word.count]

theorem Word.unit (hA : ∀ t,IsUnit (A t)) (W : Word D A α) : IsUnit W.matrix := by
  induction W with
  | nil => exact isUnit_one
  | cons s W ih =>
    apply IsUnit.mul _ ih
    cases s with
    | mono M hm => exact hm.unit _
    | call t e => exact Embedded.unit e _ (hA t)

def monoWord (M : Matrix α α ℂ) (hm : MonomialMatrix M) : Word D A α := [.mono M hm]
def callWord (t : τ) (e : D t ↪ α) : Word D A α := [.call t e]
@[simp] theorem matrix_monoWord (M : Matrix α α ℂ) (hm : MonomialMatrix M) :
    (monoWord (D := D) (A := A) M hm).matrix=M := by simp [monoWord,Word.matrix,Step.matrix]
@[simp] theorem matrix_callWord (t : τ) (e : D t ↪ α) :
    (callWord (A := A) t e).matrix=Embedded.matrix e (A t) := by simp [callWord,Word.matrix,Step.matrix]
@[simp] theorem calls_monoWord (M : Matrix α α ℂ) (hm : MonomialMatrix M) :
    (monoWord (D := D) (A := A) M hm).calls=[] := rfl
@[simp] theorem calls_callWord (t : τ) (e : D t ↪ α) :
    (callWord (A := A) t e).calls=[t] := rfl

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Embedded
variable {π : Type} [Fintype π] [DecidableEq π]
  {β : π→Type} [∀ i,Fintype (β i)] [∀ i,DecidableEq (β i)]

def sigmaIn (p : π) : β p ↪ (Σ p,β p) := ⟨Sigma.mk p,by intro a b h; exact eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩

theorem matrix_sigmaIn (A : ∀ p,Matrix (β p) (β p) ℂ) (p : π) :
    matrix (sigmaIn p) (A p)=Matrix.blockDiagonal' (Function.update 1 p (A p)) := by
  classical
  ext ⟨i,a⟩ ⟨j,b⟩
  by_cases hi : i=p
  · subst i
    by_cases hj : j=p
    · subst j
      change matrix (sigmaIn p) (A p) (sigmaIn p a) (sigmaIn p b)=_
      rw [matrix_on]
      simp
    · rw [matrix_off_col]
      · simp [Matrix.blockDiagonal'_apply,Ne.symm hj]
      · rintro ⟨b',hb⟩; exact hj (congrArg Sigma.fst hb).symm
  · rw [matrix_off_row]
    · by_cases hij : i=j
      · subst j; simp [Matrix.one_apply,hi]
      · simp [Matrix.blockDiagonal'_apply,hij]
    · rintro ⟨a',ha⟩; exact hi (congrArg Sigma.fst ha).symm

theorem list_update_prod
    {π : Type} [Fintype π] [DecidableEq π] {R : π→Type} [∀ i,Monoid (R i)] (A : ∀ i,R i)
    (L : List π) (hL : L.Nodup) (p : π) :
    ((L.map (fun i=>Function.update (1 : ∀ i,R i) i (A i))).prod) p=if p∈L then A p else 1 := by
  classical
  induction L with
  | nil => simp
  | cons i L ih =>
    have hi := List.nodup_cons.mp hL
    rw [List.map_cons,List.prod_cons,Pi.mul_apply,ih hi.2]
    by_cases hp : p=i
    · subst p; simp [hi.1]
    · simp [hp]

theorem blockDiagonal'_product (A : ∀ p,Matrix (β p) (β p) ℂ) :
    ((Finset.univ.toList.map (fun p=>matrix (sigmaIn p) (A p))).prod)=Matrix.blockDiagonal' A := by
  classical
  let φ := Matrix.blockDiagonal'RingHom (m' := β) (α := ℂ)
  have he : (fun p=>matrix (sigmaIn p) (A p))=fun p=>φ (Function.update 1 p (A p)) := by
    funext p; exact matrix_sigmaIn A p
  rw [he]
  let upd := fun p=>Function.update (1 : ∀ p,Matrix (β p) (β p) ℂ) p (A p)
  have hmap : Finset.univ.toList.map (fun p=>φ (upd p))=(Finset.univ.toList.map upd).map φ :=
    (List.map_map ..).symm
  change (Finset.univ.toList.map (fun p=>φ (upd p))).prod=_
  rw [hmap,← map_list_prod]
  change φ ((Finset.univ.toList.map upd).prod)=φ A
  apply congrArg φ
  funext p
  rw [list_update_prod A _ (Finset.nodup_toList _)]
  simp

end ExactFourier.Embedded

end
end

section
noncomputable section
namespace ExactFourier.Embedded
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable {π : Type} [Fintype π] [DecidableEq π]
 {δ ε : π→Type} [∀ p,Fintype (δ p)] [∀ p,Fintype (ε p)]
 [∀ p,DecidableEq (δ p)] [∀ p,DecidableEq (ε p)]

def sigmaEmbed (e : ∀ p,δ p ↪ ε p) : (Σ p,δ p) ↪ (Σ p,ε p) where
  toFun i := ⟨i.1,e i.1 i.2⟩
  inj' := by
    rintro ⟨p,a⟩ ⟨q,b⟩ h
    have hp := congrArg Sigma.fst h
    dsimp at hp
    subst q
    have hab := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    exact congrArg (Sigma.mk p) ((e p).injective hab)

end ExactFourier.Embedded

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
  {A : ∀ t,Matrix (D t) (D t) ℂ}
  {α : Type} [Fintype α] [DecidableEq α]

theorem Word.matrix_flatten (L : List (Word D A α)) :
    Word.matrix L.flatten=(L.map Word.matrix).prod := by
  induction L with
  | nil => rfl
  | cons W L ih => simp only [List.flatten_cons,Word.matrix_append,ih,List.map_cons,List.prod_cons]

theorem Word.calls_flatten (L : List (Word D A α)) :
    Word.calls L.flatten=(L.map Word.calls).flatten := by
  induction L with
  | nil => rfl
  | cons W L ih => simp only [List.flatten_cons,Word.calls_append,ih,List.map_cons]

def Word.reindex {β : Type} [Fintype β] [DecidableEq β] (e : α≃β) (W : Word D A α) : Word D A β :=
  W.embed e.toEmbedding

@[simp] theorem Word.matrix_reindex {β : Type} [Fintype β] [DecidableEq β]
    (e : α≃β) (W : Word D A α) : (W.reindex e).matrix=Matrix.reindex e e W.matrix := by
  rw [Word.reindex,Word.matrix_embed,Embedded.matrix_equiv]
@[simp] theorem Word.calls_reindex {β : Type} [Fintype β] [DecidableEq β]
    (e : α≃β) (W : Word D A α) : (W.reindex e).calls=W.calls := by simp [Word.reindex]

variable {π : Type} [Fintype π] [DecidableEq π]
  {β : π→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]

def Word.blockSum (W : ∀ p,Word D A (β p)) : Word D A (Σ p,β p) :=
  (Finset.univ.toList.map (fun p=>(W p).embed (Embedded.sigmaIn p))).flatten

@[simp] theorem Word.matrix_blockSum (W : ∀ p,Word D A (β p)) :
    (Word.blockSum W).matrix=Matrix.blockDiagonal' (fun p=>(W p).matrix) := by
  rw [Word.blockSum,Word.matrix_flatten,List.map_map]
  simp only [Function.comp_def,Word.matrix_embed]
  exact Embedded.blockDiagonal'_product _

@[simp] theorem Word.calls_blockSum (W : ∀ p,Word D A (β p)) :
    (Word.blockSum W).calls=(Finset.univ.toList.map (fun p=>(W p).calls)).flatten := by
  rw [Word.blockSum,Word.calls_flatten,List.map_map]
  simp only [Function.comp_def,Word.calls_embed]

theorem Word.count_blockSum [DecidableEq τ] (W : ∀ p,Word D A (β p)) (t : τ) :
    (Word.blockSum W).count t=∑ p,(W p).count t := by
  rw [Word.count,Word.calls_blockSum,List.count_flatten]
  simp [List.map_map,Word.count]

end ExactFourier.Packing

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.WordScheduling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Packing
variable {τ σ : Type}
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {E : σ→Type} [∀ t,Fintype (E t)] [∀ t,DecidableEq (E t)]
 {B : ∀ t,Matrix (E t) (E t) ℂ}
 {α : Type} [Fintype α] [DecidableEq α]

def Word.weight (p : τ→ℝ) (W : Word D A α) : ℝ := (W.calls.map p).sum

@[simp] theorem Word.weight_nil (p : τ→ℝ) : Word.weight p ([] : Word D A α)=0 := rfl
@[simp] theorem Word.weight_cons_mono (p : τ→ℝ) (M : Matrix α α ℂ) (h : MonomialMatrix M) (W : Word D A α) :
 Word.weight p (.mono M h::W)=W.weight p := rfl
@[simp] theorem Word.weight_cons_call (p : τ→ℝ) (t : τ) (e : D t ↪ α) (W : Word D A α) :
 Word.weight p (.call t e::W)=p t+W.weight p := rfl
@[simp] theorem Word.weight_append (p : τ→ℝ) (W V : Word D A α) :
 (W++V).weight p=W.weight p+V.weight p := by simp [Word.weight]
@[simp] theorem Word.weight_embed {β : Type} [Fintype β] [DecidableEq β]
 (p : τ→ℝ) (e : α ↪ β) (W : Word D A α) : (W.embed e).weight p=W.weight p := by simp [Word.weight]
@[simp] theorem Word.weight_reindex {β : Type} [Fintype β] [DecidableEq β]
 (p : τ→ℝ) (e : α≃β) (W : Word D A α) : (W.reindex e).weight p=W.weight p := by
 simp [Word.weight,Word.reindex]

theorem Word.weight_count [Fintype τ] [DecidableEq τ] (p : τ→ℝ) (W : Word D A α) :
 W.weight p=∑ t,(W.count t : ℝ)*p t := by
 induction W with
 | nil => simp [Word.weight,Word.count,Word.calls]
 | cons s W ih =>
  cases s with
  | mono M h =>
   change Word.weight p W=∑ t : τ,(Word.count W t : ℝ)*p t
   exact ih
  | call t e =>
   rw [Word.weight_cons_call,ih]
   simp only [Word.count,Word.calls,List.filterMap_cons,Step.kind,List.count_eq_countP,
     List.countP_cons,Nat.cast_add,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,add_mul,Finset.sum_add_distrib]
   simp [mul_comm,add_comm]

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.MonomialMatrix
variable {α : Type} [Fintype α] [DecidableEq α]

theorem inverse {A : Matrix α α ℂ} (hA : MonomialMatrix A) : MonomialMatrix A⁻¹ := by
 obtain ⟨s,d,hd,hs⟩ := hA
 let B : Matrix α α ℂ := fun i j=>if i=s.symm j then (d (s.symm j))⁻¹ else 0
 have hB : MonomialMatrix B := ⟨s.symm,fun j=>(d (s.symm j))⁻¹,fun j=>inv_ne_zero (hd _),fun _ _=>rfl⟩
 have he : A*B=1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [B,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,hs,s.apply_symm_apply]
  by_cases h : i=j
  · subst j; simp [hd]
  · simp [h]
 rw [Matrix.inv_eq_right_inv he]
 exact hB

/-- A unit square submatrix of a monomial matrix is monomial. -/
theorem submatrix_unit {β : Type} [Fintype β] [DecidableEq β]
 {B : Matrix β β ℂ} (hB : MonomialMatrix B) (e f : α ↪ β)
 (hA : IsUnit (B.submatrix e f)) : MonomialMatrix (B.submatrix e f) := by
 let A := B.submatrix e f
 have hi := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
 have hc : ∀ k,∃ i,A⁻¹ k i*A i k≠0 := by
  intro k
  have he := congrArg (fun M : Matrix α α ℂ=>M k k) hi
  simp only [Matrix.mul_apply,Matrix.one_apply,ite_true] at he
  by_contra hn
  push Not at hn
  rw [Finset.sum_eq_zero (fun i _=>hn i)] at he
  exact zero_ne_one he
 choose σ hσ using hc
 have hc₁ : ∀ k,A⁻¹ k (σ k)≠0 := fun k=>(mul_ne_zero_iff.mp (hσ k)).1
 have hc₂ : ∀ k,A (σ k) k≠0 := fun k=>(mul_ne_zero_iff.mp (hσ k)).2
 obtain ⟨s,d,hd,hs⟩ := hB
 have hz : ∀ k i,i≠σ k → A i k=0 := by
  intro k i hik
  have he : e (σ k)=s (f k) := by
   by_contra h
   exact hc₂ k (by simp [A,Matrix.submatrix_apply,hs,h])
  have hn : e i≠s (f k) := by intro hh; exact hik (e.injective (hh.trans he.symm))
  simp [A,Matrix.submatrix_apply,hs,hn]
 have hinj : Function.Injective σ := by
  intro k l hkl
  by_contra hne
  have hh := congrArg (fun M : Matrix α α ℂ=>M k l) hi
  simp only [Matrix.mul_apply,Matrix.one_apply,ite_eq_right hne] at hh
  have hsum : (∑ i,A⁻¹ k i*A i l)=A⁻¹ k (σ l)*A (σ l) l := by
   apply Finset.sum_eq_single (σ l)
   · intro i _ hne; rw [hz l i hne,mul_zero]
   · simp
  rw [hsum] at hh
  apply mul_ne_zero (hc₁ k) (hc₂ l)
  simpa only [hkl] using hh
 let g : Equiv.Perm α := Equiv.ofBijective σ ⟨hinj,Finite.surjective_of_injective hinj⟩
 refine ⟨g,fun k=>A (σ k) k,hc₂,?_⟩
 intro i k
 change A i k=if i=σ k then A (σ k) k else 0
 split_ifs with h
 · subst i; rfl
 · exact hz k i h

end ExactFourier.MonomialMatrix

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type}
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {α : Type} [Fintype α] [DecidableEq α]

theorem pattern_from_word (V : Word D A α) {H : Matrix α α ℂ} {h : ℕ}
 (hp : PositiveGeneration.Pattern V.matrix h H) :
 ∃ W : Word D A α,W.matrix=H ∧ ∀ p : τ→ℝ,W.weight p=(h : ℝ)*V.weight p := by
 induction hp with
 | zero M hm => exact ⟨monoWord M hm,by simp,fun p=>by simp [Word.weight]⟩
 | @succ h H hp M hm ih =>
  obtain ⟨W,hW,hp⟩ := ih
  refine ⟨W++V++monoWord M hm,by simp [hW,mul_assoc],?_⟩
  intro p
  rw [Word.weight_append,Word.weight_append,hp]
  change (h : ℝ)*V.weight p+V.weight p+0=_
  push_cast
  ring

theorem word_generates (V : Word D A α) (hu : IsUnit V.matrix) (hn : ¬MonomialMatrix V.matrix)
 (H : Matrix α α ℂ) (hH : IsUnit H) :
 ∃ h : ℕ,0<h ∧ ∃ W : Word D A α,W.matrix=H ∧ ∀ p : τ→ℝ,W.weight p=(h : ℝ)*V.weight p := by
 obtain ⟨h,hh,hg⟩ := PositiveGeneration.positive_generation V.matrix hu hn
 exact ⟨h,hh,pattern_from_word V (hg H hH)⟩

theorem monomial_of_subsingleton [Subsingleton α] (H : Matrix α α ℂ) (hH : IsUnit H) : MonomialMatrix H := by
 have he : H=Matrix.diagonal (fun i=>H i i) := by
  ext i j
  have h : i=j := Subsingleton.elim _ _
  subst j
  simp
 have hu : ∀ i,H i i≠0 := by
  rw [he] at hH
  have hh := Pi.isUnit_iff.mp (Matrix.isUnit_diagonal.mp hH)
  intro i
  exact isUnit_iff_ne_zero.mp (hh i)
 rw [he]
 exact MonomialMatrix.diagonal _ hu

def shearU : Matrix (Fin 2) (Fin 2) ℂ := Matrix.transvection 1 0 1

theorem shearU_unit : IsUnit shearU := MatrixPrice.transvection_isUnit 1 0 (by decide) 1

theorem shearU_not_monomial : ¬MonomialMatrix shearU := by
 rintro ⟨s,d,hd,hs⟩
 have h0 : (0 : Fin 2)=s 0 := by
  by_contra h
  have hh := hs 0 0
  simp [shearU,Matrix.transvection,h] at hh
 have h1 : (1 : Fin 2)=s 0 := by
  by_contra h
  have hh := hs 1 0
  simp [shearU,Matrix.transvection,h] at hh
 have hh : (0 : Fin 2)=1 := h0.trans h1.symm
 exact (by decide : (0 : Fin 2)≠1) hh

theorem shear_word_exists (u : τ) (eu : D u≃Fin 2)
 (hAu : Matrix.reindex eu eu (A u)=shearU)
 (H : Matrix α α ℂ) (hH : IsUnit H) :
 ∃ C : ℕ,∃ W : Word D A α,W.matrix=H ∧ ∀ p : τ→ℝ,W.weight p=(C : ℝ)*p u := by
 classical
 by_cases hc : 2≤Fintype.card α
 · let e : D u ↪ α := eu.toEmbedding.trans
    ((Fin.castLEEmb hc).trans (Fintype.equivFin α).symm.toEmbedding)
   let V : Word D A α := callWord u e
   have hu : IsUnit (A u) := by
    have hh := TensorTools.unit_reindex eu.symm _ shearU_unit
    rw [← hAu] at hh
    convert hh using 1
    ext i j
    simp [Matrix.reindex_apply]
   have hn : ¬MonomialMatrix (A u) := by
    intro hh; exact shearU_not_monomial (hAu ▸ hh.reindex eu)
   have hV : V.matrix=Embedded.matrix e (A u) := matrix_callWord u e
   have hVm : ¬MonomialMatrix V.matrix := by
    intro hh
    rw [hV] at hh
    have he : (Embedded.matrix e (A u)).submatrix e e=A u := by
     ext i j; exact Embedded.matrix_on e _ i j
    apply hn
    rw [← he]
    exact hh.submatrix_unit e e (he.symm ▸ hu)
   obtain ⟨h,hh,W,hm,hp⟩ := word_generates V (hV.symm ▸ Embedded.unit e _ hu) hVm H hH
   exact ⟨h,W,hm,fun p=>by simpa [V,Word.weight] using hp p⟩
 · have hcard : Fintype.card α≤1 := by omega
   let : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp hcard
   have hm := monomial_of_subsingleton H hH
   exact ⟨0,monoWord H hm,by simp,fun p=>by simp [Word.weight]⟩

end ExactFourier.Packing

end
end

section
namespace ExactFourier
variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

theorem reindex_tensor
    {α : Type} {β : Type} {γ : Type} {δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ] (e : α≃β) (f : γ≃δ) (M : Matrix α α ℂ) (N : Matrix γ γ ℂ) :
 Matrix.reindex (e.prodCongr f) (e.prodCongr f) (Matrix.kronecker M N)=
 Matrix.kronecker (Matrix.reindex e e M) (Matrix.reindex f f N) := by
 ext x y
 rfl

theorem reindex_inverse
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : α≃β) (M : Matrix α α ℂ) :
 Matrix.reindex e.symm e.symm (Matrix.reindex e e M)=M := by
 ext i j; simp [Matrix.reindex_apply]
end ExactFourier

end

section
noncomputable section
namespace ExactFourier
namespace Embedded
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ]
theorem matrix_domain (e : α≃β) (f : α ↪ γ) (M : Matrix α α ℂ) :
 matrix (e.symm.toEmbedding.trans f) (Matrix.reindex e e M)=matrix f M := by
 classical
 ext i j
 by_cases hi : ∃ a,f a=i
 · obtain ⟨a,rfl⟩ := hi
   by_cases hj : ∃ b,f b=j
   · obtain ⟨b,rfl⟩ := hj
     have ha : (e.symm.toEmbedding.trans f) (e a)=f a := by simp
     have hb : (e.symm.toEmbedding.trans f) (e b)=f b := by simp
     rw [← ha,← hb,matrix_on]
     simp only [ha,hb,matrix_on,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
   · have hj' : ¬∃ b,(e.symm.toEmbedding.trans f) b=j := by
      rintro ⟨b,hb⟩; exact hj ⟨e.symm b,hb⟩
     rw [matrix_off_col _ _ _ _ hj',matrix_off_col _ _ _ _ hj]
 · have hi' : ¬∃ a,(e.symm.toEmbedding.trans f) a=i := by
    rintro ⟨a,ha⟩; exact hi ⟨e.symm a,ha⟩
   rw [matrix_off_row _ _ _ _ hi',matrix_off_row _ _ _ _ hi]
end Embedded
namespace Packing
variable {τ σ : Type}
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {E : σ→Type} [∀ t,Fintype (E t)] [∀ t,DecidableEq (E t)]
 {B : ∀ t,Matrix (E t) (E t) ℂ}
 {α : Type} [Fintype α] [DecidableEq α]

def Step.rename (f : τ→σ) (e : ∀ t,D t≃E (f t)) : Step D A α→Step E B α
 | .mono M h => .mono M h
 | .call t a => .call (f t) ((e t).symm.toEmbedding.trans a)
def Word.rename (f : τ→σ) (e : ∀ t,D t≃E (f t)) (W : Word D A α) : Word E B α :=
 W.map (Step.rename f e)
theorem Word.matrix_rename (f : τ→σ) (e : ∀ t,D t≃E (f t))
 (he : ∀ t,Matrix.reindex (e t) (e t) (A t)=B (f t)) (W : Word D A α) :
 (W.rename (B := B) f e).matrix=W.matrix := by
 induction W with
 | nil => rfl
 | cons s W ih =>
  simp only [Word.rename,List.map_cons,Word.matrix_cons]
  rw [← Word.rename,ih]
  congr 1
  cases s with
  | mono M h => rfl
  | call t a =>
   change Embedded.matrix _ (B (f t))=Embedded.matrix a (A t)
   rw [← he t,Embedded.matrix_domain]
@[simp] theorem Word.weight_rename (f : τ→σ) (e : ∀ t,D t≃E (f t))
 (p : σ→ℝ) (W : Word D A α) : (W.rename (B := B) f e).weight p=W.weight (p∘f) := by
 induction W with
 | nil => rfl
 | cons s W ih =>
  cases s with
  | mono M h => simpa only [Word.rename,List.map_cons,Step.rename,Word.weight_cons_mono] using ih
  | call t a => simpa only [Word.rename,List.map_cons,Step.rename,Word.weight_cons_call,Function.comp_apply] using congrArg (fun x=>p (f t)+x) ih
end Packing
end ExactFourier

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.PiTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.PiTensor
variable {ι : Type} [Fintype ι] [DecidableEq ι]
 {D : ι→Type} [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]

def matrix (A : ∀ i,Matrix (D i) (D i) ℂ) : Matrix (∀ i,D i) (∀ i,D i) ℂ :=
 fun x y=>∏ i,A i (x i) (y i)

@[simp] theorem one
    {ι : Type} [Fintype ι] [DecidableEq ι] {D : ι → Type} [(i : ι) → Fintype (D i)] [(i : ι) → DecidableEq (D i)] : matrix (1 : ∀ i,Matrix (D i) (D i) ℂ)=1 := by
 classical
 ext x y
 by_cases h : x=y
 · subst y; simp [matrix]
 · rw [Matrix.one_apply,ite_eq_right h]
   obtain ⟨i,hi⟩ := Function.ne_iff.mp h
   exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

def axisCoordinates (i : ι) : (Σ _ : ∀ j : {j // j≠i},D j,D i) ≃ (∀ j,D j) :=
 (Equiv.sigmaEquivProd _ _).trans ((Equiv.prodComm _ _).trans (Equiv.piSplitAt i D).symm)

@[simp] theorem axisCoordinates_symm
    {ι : Type} [Fintype ι] [DecidableEq ι] {D : ι → Type} [(i : ι) → Fintype (D i)] [(i : ι) → DecidableEq (D i)] (i : ι) (x : ∀ j,D j) :
 (axisCoordinates i).symm x=⟨fun j=>x j,x i⟩ := rfl

end ExactFourier.PiTensor

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {ι : Type} [Fintype ι] [DecidableEq ι]
 {E : ι→Type} [∀ i,Fintype (E i)] [∀ i,DecidableEq (E i)]

def Word.axis (i : ι) (W : Word D A (E i)) : Word D A (∀ i,E i) :=
 (Word.blockSum (fun _ : ∀ j : {j // j≠i},E j=>W)).reindex (PiTensor.axisCoordinates i)

def Word.tensor (W : ∀ i,Word D A (E i)) : Word D A (∀ i,E i) :=
 (Finset.univ.toList.map (fun i=>(W i).axis i)).flatten

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def Word.leftTensor (W : Word D A α) : Word D A (α×β) :=
 (Word.blockSum (fun _ : β=>W)).reindex ((Equiv.sigmaEquivProd β α).trans (Equiv.prodComm β α))
def Word.rightTensor (V : Word D A β) : Word D A (α×β) :=
 (Word.blockSum (fun _ : α=>V)).reindex (Equiv.sigmaEquivProd α β)

theorem Word.matrix_leftTensor (W : Word D A α) :
 (W.leftTensor (β := β)).matrix=Matrix.kronecker W.matrix (1 : Matrix β β ℂ) := by
 rw [Word.leftTensor,Word.matrix_reindex,Word.matrix_blockSum]
 ext ⟨a,b⟩ ⟨c,d⟩
 by_cases h : b=d
 · subst d; simp [Matrix.reindex_apply]
 · simp [Matrix.reindex_apply,Matrix.blockDiagonal'_apply,h]

theorem Word.matrix_rightTensor (V : Word D A β) :
 (V.rightTensor (α := α)).matrix=Matrix.kronecker (1 : Matrix α α ℂ) V.matrix := by
 rw [Word.rightTensor,Word.matrix_reindex,Word.matrix_blockSum]
 ext ⟨a,b⟩ ⟨c,d⟩
 by_cases h : a=c
 · subst c; simp [Matrix.reindex_apply]
 · simp [Matrix.reindex_apply,Matrix.blockDiagonal'_apply,h]

theorem Word.count_leftTensor [DecidableEq τ] (W : Word D A α) (t : τ) :
 (W.leftTensor (β := β)).count t=Fintype.card β*W.count t := by
 rw [Word.leftTensor,Word.count,Word.calls_reindex,← Word.count,Word.count_blockSum]
 simp

theorem Word.count_rightTensor [DecidableEq τ] (V : Word D A β) (t : τ) :
 (V.rightTensor (α := α)).count t=Fintype.card α*V.count t := by
 rw [Word.rightTensor,Word.count,Word.calls_reindex,← Word.count,Word.count_blockSum]
 simp

def Word.kronecker (W : Word D A α) (V : Word D A β) : Word D A (α×β) :=
 W.leftTensor++V.rightTensor

@[simp] theorem Word.matrix_kronecker (W : Word D A α) (V : Word D A β) :
 (W.kronecker V).matrix=Matrix.kronecker W.matrix V.matrix := by
 rw [Word.kronecker,Word.matrix_append,Word.matrix_leftTensor,Word.matrix_rightTensor]
 simpa using (Matrix.mul_kronecker_mul W.matrix (1 : Matrix α α ℂ)
   (1 : Matrix β β ℂ) V.matrix).symm

theorem Word.count_kronecker [DecidableEq τ] (W : Word D A α) (V : Word D A β) (t : τ) :
 (W.kronecker V).count t=Fintype.card β*W.count t+Fintype.card α*V.count t := by
 rw [Word.kronecker,Word.count_append,Word.count_leftTensor,Word.count_rightTensor]

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {σ : Type} [Fintype σ] [DecidableEq σ]
 {E : σ→Type} [∀ s,Fintype (E s)] [∀ s,DecidableEq (E s)]

/-- The two tensor axes choose block-copy labels independently, even for repeated species. -/
def sectorCoordinates (k : σ→ℕ) :
 (Σ p : σ×σ,(Fin (k p.1)×Fin (k p.2))×(E p.1×E p.2)) ≃
 ((Σ s,Fin (k s)×E s)×(Σ s,Fin (k s)×E s)) where
 toFun x := (⟨x.1.1,x.2.1.1,x.2.2.1⟩,⟨x.1.2,x.2.1.2,x.2.2.2⟩)
 invFun x := ⟨(x.1.1,x.2.1),(x.1.2.1,x.2.2.1),(x.1.2.2,x.2.2.2)⟩
 left_inv := by rintro ⟨⟨s,t⟩,⟨i,j⟩,a,b⟩; rfl
 right_inv := by rintro ⟨⟨s,i,a⟩,⟨t,j,b⟩⟩; rfl

def speciesInventory (k : σ→ℕ) (B : ∀ s,Matrix (E s) (E s) ℂ) :
 Matrix (Σ s,Fin (k s)×E s) (Σ s,Fin (k s)×E s) ℂ :=
 Matrix.blockDiagonal' fun s=>Matrix.kronecker (1 : Matrix (Fin (k s)) (Fin (k s)) ℂ) (B s)

def sectorMatrix (k : σ→ℕ) (B : ∀ s,Matrix (E s) (E s) ℂ) :
 Matrix (Σ p : σ×σ,(Fin (k p.1)×Fin (k p.2))×(E p.1×E p.2))
   (Σ p : σ×σ,(Fin (k p.1)×Fin (k p.2))×(E p.1×E p.2)) ℂ :=
 Matrix.blockDiagonal' fun p=>Matrix.kronecker (1 : Matrix (Fin (k p.1)×Fin (k p.2)) _ ℂ)
   (Matrix.kronecker (B p.1) (B p.2))

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ π ρ : Type} [Fintype π] [Fintype ρ] [DecidableEq π] [DecidableEq ρ]
  {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
  {A : ∀ t,Matrix (D t) (D t) ℂ}

def colorEquiv (u : π→τ) (v : ρ→τ) (e : π≃ρ) (he : ∀ p,u p=v (e p)) :
    (Σ p,D (u p))≃(Σ r,D (v r)) :=
  Equiv.sigmaCongr e (fun p=>Equiv.cast (congrArg D (he p)))

@[simp] theorem colorEquiv_fst
    {τ : Type} {π : Type} {ρ : Type} [Fintype π] [Fintype ρ] [DecidableEq π] [DecidableEq ρ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] (u : π→τ) (v : ρ→τ) (e : π≃ρ) (he : ∀ p,u p=v (e p))
    (x : Σ p,D (u p)) : (colorEquiv u v e he x).1=e x.1 := rfl

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
  {A : ∀ t,Matrix (D t) (D t) ℂ}

abbrev optionalDomain (D : τ→Type) : Option τ→Type
 | none => Empty
 | some t => D t
instance optionalDomain_fintype (t : Option τ) : Fintype (optionalDomain D t) := by
  cases t <;> dsimp [optionalDomain] <;> infer_instance
instance optionalDomain_decEq (t : Option τ) : DecidableEq (optionalDomain D t) := by
  cases t <;> dsimp [optionalDomain] <;> infer_instance

def optionalMatrix (A : ∀ t,Matrix (D t) (D t) ℂ) : ∀ t,Matrix (optionalDomain D t) (optionalDomain D t) ℂ
 | none => 1
 | some t => A t

variable {α : Type} [Fintype α] [DecidableEq α]

def Step.activeTuple : (s : Step D A α) → optionalDomain D s.kind ↪ α
 | .mono _ _ => ⟨Empty.elim,by intro a; exact a.elim⟩
 | .call _ e => e

def Step.monoPart : Step D A α→Matrix α α ℂ
 | .mono M _ => M
 | .call _ _ => 1

variable {π : Type} [Fintype π] [DecidableEq π]

abbrev CallIndex (u : π→Option τ) := Σ t,{p // u p=some t}

def activeTo (u : π→Option τ) (x : Σ c : CallIndex u,D c.1) : Σ p,optionalDomain D (u p) :=
 ⟨x.1.2.1,cast (congrArg (optionalDomain D) x.1.2.2.symm) x.2⟩

theorem activeTo_injective
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {π : Type} [Fintype π] [DecidableEq π] (u : π→Option τ) : Function.Injective (activeTo (D := D) u) := by
 rintro ⟨⟨i,p,hp⟩,a⟩ ⟨⟨j,q,hq⟩,b⟩ h
 have hpq := congrArg Sigma.fst h
 change p=q at hpq
 subst q
 have hij : i=j := Option.some.inj (hp.symm.trans hq)
 subst j
 have hab := eq_of_heq (Sigma.mk.inj_iff.mp h).2
 have ha : a=b := (Equiv.cast (congrArg (optionalDomain D) hp.symm)).injective hab
 subst b
 rfl

theorem activeTo_surjective
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {π : Type} [Fintype π] [DecidableEq π] (u : π→Option τ) : Function.Surjective (activeTo (D := D) u) := by
 rintro ⟨p,a⟩
 have hh : ∃ t,u p=some t := by
  cases h : u p with
  | none => exact (cast (congrArg (optionalDomain D) h) a : Empty).elim
  | some t => exact ⟨t,rfl⟩
 obtain ⟨t,hp⟩ := hh
 refine ⟨⟨⟨t,p,hp⟩,cast (congrArg (optionalDomain D) hp) a⟩,?_⟩
 simp [activeTo]

def activeEquiv (u : π→Option τ) :
    (Σ c : CallIndex u,D c.1)≃(Σ p,optionalDomain D (u p)) :=
 Equiv.ofBijective (activeTo u) ⟨activeTo_injective u,activeTo_surjective u⟩

@[simp] theorem activeEquiv_fst (u : π→Option τ) (x : Σ c : CallIndex u,D c.1) :
    (activeEquiv u x).1=x.1.2.1 := rfl

end ExactFourier.Packing

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.SlotAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {π : Type} [Fintype π] [DecidableEq π]
 {β : π→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]

abbrev Inventory (k : τ→ℕ) := Σ t,Fin (k t)
abbrev ActiveSpace (D : τ→Type) (k : τ→ℕ) := Σ i : Inventory k,D i.1

def inventoryMatrix (k : τ→ℕ) : Matrix (ActiveSpace D k) (ActiveSpace D k) ℂ :=
 Matrix.blockDiagonal' (fun i : Inventory k=>A i.1)

variable {ν : Type} [Fintype ν] [DecidableEq ν]

def inventoryWithIdentity (k : τ→ℕ) : Matrix (ActiveSpace D k ⊕ ν) (ActiveSpace D k ⊕ ν) ℂ :=
 Matrix.fromBlocks (inventoryMatrix (A := A) k) 0 0 1

end ExactFourier.Packing

end
end
section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}

abbrev SpeciesDomain (D : τ→Type) : Option τ→Type
 | none => Unit
 | some t => D t
instance SpeciesDomain_fintype (s : Option τ) : Fintype (SpeciesDomain D s) := by
 cases s <;> dsimp [SpeciesDomain] <;> infer_instance
instance SpeciesDomain_decEq (s : Option τ) : DecidableEq (SpeciesDomain D s) := by
 cases s <;> dsimp [SpeciesDomain] <;> infer_instance

def speciesMatrix : ∀ s,Matrix (SpeciesDomain D s) (SpeciesDomain D s) ℂ
 | none => 1
 | some t => A t

abbrev speciesCopies (k : τ→ℕ) (I : ℕ) : Option τ→ℕ
 | none => I
 | some t => k t

abbrev SpeciesSpace (D : τ→Type) (k : τ→ℕ) (I : ℕ) :=
 Σ s,Fin (speciesCopies k I s)×SpeciesDomain D s

def speciesCoordinates (k : τ→ℕ) (I : ℕ) :
 (ActiveSpace D k⊕Fin I)≃SpeciesSpace D k I where
 toFun
  | .inl ⟨⟨t,i⟩,a⟩ => ⟨some t,i,a⟩
  | .inr i => ⟨none,i,()⟩
 invFun
  | ⟨some t,i,a⟩ => .inl ⟨⟨t,i⟩,a⟩
  | ⟨none,i,_⟩ => .inr i
 left_inv := by rintro (⟨⟨t,i⟩,a⟩|i) <;> rfl
 right_inv := by
  rintro ⟨s,i,a⟩
  cases s with
  | none => cases a; rfl
  | some t => rfl

abbrev LivePair (τ : Type) := {p : Option τ×Option τ // p≠(none,none)}
abbrev PairDomain (D : τ→Type) (p : LivePair τ) := SpeciesDomain D p.1.1×SpeciesDomain D p.1.2

def pairMatrix (p : LivePair τ) : Matrix (PairDomain D p) (PairDomain D p) ℂ :=
 Matrix.kronecker (speciesMatrix (A := A) p.1.1) (speciesMatrix (A := A) p.1.2)

abbrev LiveSpace (D : τ→Type) (k : τ→ℕ) (I : ℕ) :=
 Σ p : LivePair τ,(Fin (speciesCopies k I p.1.1)×Fin (speciesCopies k I p.1.2))×PairDomain D p

def liveCoordinates (k : τ→ℕ) (I : ℕ) :
 (LiveSpace D k I⊕(Fin I×Fin I))≃(SpeciesSpace D k I×SpeciesSpace D k I) where
 toFun
  | .inl ⟨p,⟨i,j⟩,a,b⟩ => (⟨p.1.1,i,a⟩,⟨p.1.2,j,b⟩)
  | .inr (i,j) => (⟨none,i,()⟩,⟨none,j,()⟩)
 invFun
  | (⟨none,i,_⟩,⟨none,j,_⟩) => .inr (i,j)
  | (⟨some s,i,a⟩,⟨t,j,b⟩) => .inl ⟨⟨(some s,t),by simp⟩,⟨i,j⟩,a,b⟩
  | (⟨none,i,a⟩,⟨some t,j,b⟩) => .inl ⟨⟨(none,some t),by simp⟩,⟨i,j⟩,a,b⟩
 left_inv := by
  rintro (⟨⟨⟨s,t⟩,hp⟩,⟨i,j⟩,a,b⟩|⟨i,j⟩)
  · cases s <;> cases t <;> try rfl
    exact (hp rfl).elim
  · rfl
 right_inv := by
  rintro ⟨⟨s,i,a⟩,⟨t,j,b⟩⟩
  cases s <;> cases t <;> rfl

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
  {A : ∀ t,Matrix (D t) (D t) ℂ} {α : Type} [Fintype α] [DecidableEq α]

structure Frame (D : τ→Type) [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
    (α : Type) [Fintype α] [DecidableEq α] where
  mono : Matrix α α ℂ
  monomial : MonomialMatrix mono
  type : τ
  tuple : D type ↪ α

def Frame.matrix (f : Frame D α) : Matrix α α ℂ := f.mono * Embedded.matrix f.tuple (A f.type)

def Frame.pre (M : Matrix α α ℂ) (hm : MonomialMatrix M) (f : Frame D α) : Frame D α :=
  {f with mono := M*f.mono,monomial := hm.mul f.monomial}

structure FramedWord (D : τ→Type) [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
    (α : Type) [Fintype α] [DecidableEq α] where
  frames : List (Frame D α)
  tail : Matrix α α ℂ
  tail_monomial : MonomialMatrix tail

def FramedWord.matrix (W : FramedWord D α) : Matrix α α ℂ :=
  (W.frames.map (Frame.matrix (A := A))).prod * W.tail

def FramedWord.types (W : FramedWord D α) : List τ := W.frames.map Frame.type

def FramedWord.pre (M : Matrix α α ℂ) (hm : MonomialMatrix M) (W : FramedWord D α) : FramedWord D α :=
  match W.frames with
  | [] => ⟨[],M*W.tail,hm.mul W.tail_monomial⟩
  | f::fs => ⟨f.pre M hm::fs,W.tail,W.tail_monomial⟩

@[simp] theorem FramedWord.matrix_pre (M : Matrix α α ℂ) (hm : MonomialMatrix M) (W : FramedWord D α) :
    (W.pre M hm).matrix (A := A)=M*W.matrix (A := A) := by
  cases W with
  | mk fs N hn => cases fs <;> simp [FramedWord.pre,FramedWord.matrix,Frame.pre,Frame.matrix,mul_assoc]

@[simp] theorem FramedWord.types_pre (M : Matrix α α ℂ) (hm : MonomialMatrix M) (W : FramedWord D α) :
    (W.pre M hm).types=W.types := by
  cases W with
  | mk fs N hn => cases fs <;> rfl

def Word.framed : Word D A α → FramedWord D α
  | [] => ⟨[],1,MonomialMatrix.one⟩
  | .mono M hm::W => (Word.framed W).pre M hm
  | .call t e::W => ⟨⟨1,MonomialMatrix.one,t,e⟩::(Word.framed W).frames,(Word.framed W).tail,(Word.framed W).tail_monomial⟩

@[simp] theorem Word.matrix_framed (W : Word D A α) : (Word.framed W).matrix (A := A)=W.matrix := by
  induction W with
  | nil => simp [Word.framed,FramedWord.matrix]
  | cons s W ih =>
    cases s with
    | mono M hm => simpa [Word.framed,Step.matrix] using congrArg (M*·) ih
    | call t e => simpa [Word.framed,FramedWord.matrix,Frame.matrix,Step.matrix,mul_assoc] using (congrArg (fun X=>Embedded.matrix e (A t)*X) ih)

@[simp] theorem Word.types_framed (W : Word D A α) : (Word.framed W).types=Word.calls W := by
  induction W with
  | nil => rfl
  | cons s W ih =>
    cases s with
    | mono M hm =>
      change ((Word.framed W).pre M hm).types=Word.calls W
      rw [FramedWord.types_pre,ih]
    | call t e =>
      change t::(Word.framed W).types=t::Word.calls W
      exact congrArg (List.cons t) ih

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}

def speciesWord : ∀ s,Word D A (SpeciesDomain D s)
 | none => []
 | some t => callWord t (Function.Embedding.refl _)

@[simp] theorem speciesWord_matrix
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} (s : Option τ) :
 (speciesWord (A := A) s).matrix=speciesMatrix (A := A) s := by
 cases s with
 | none => rfl
 | some t =>
  rw [speciesWord,matrix_callWord]
  ext i j
  exact Embedded.matrix_on (Function.Embedding.refl _) (A t) i j

def standardPair (p : LivePair τ) : Word D A (PairDomain D p) :=
 (speciesWord p.1.1).kronecker (speciesWord p.1.2)

@[simp] theorem standardPair_matrix (p : LivePair τ) :
 (standardPair (A := A) p).matrix=pairMatrix (A := A) p := by
 simp [standardPair,pairMatrix]

def pairBaseline (p : LivePair τ) (t : τ) : ℕ :=
 Fintype.card (SpeciesDomain D p.1.2)*(if p.1.1=some t then 1 else 0)+
 Fintype.card (SpeciesDomain D p.1.1)*(if p.1.2=some t then 1 else 0)

@[simp] theorem speciesWord_count
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} (s : Option τ) (t : τ) :
 (speciesWord (A := A) s).count t=if s=some t then 1 else 0 := by
 cases s with
 | none => simp [speciesWord,Word.count,Word.calls]
 | some s =>
  by_cases h : s=t
  · subst s; simp [speciesWord,Word.count]
  · simp [speciesWord,Word.count,h]

@[simp] theorem standardPair_count (p : LivePair τ) (t : τ) :
 (standardPair (A := A) p).count t=pairBaseline (D := D) p t := by
 simp [standardPair,Word.count_kronecker,pairBaseline]

/-- Exact two-factor comparison; identity factors have width one and zero price. -/
structure PairComparison where
 pair : LivePair τ
 word : Word D A (PairDomain D pair)
 correct : word.matrix=pairMatrix (A := A) pair

def PairComparison.delta (c : PairComparison (A := A)) (t : τ) : ℤ :=
 (pairBaseline (D := D) c.pair t : ℤ)-(c.word.count t : ℤ)

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}

abbrev speciesPrice (p : τ→ℝ) : Option τ→ℝ
 | none => 0
 | some t => p t

def pairPrice (p : τ→ℝ) (s : LivePair τ) : ℝ :=
 Fintype.card (SpeciesDomain D s.1.2)*speciesPrice p s.1.1+
 Fintype.card (SpeciesDomain D s.1.1)*speciesPrice p s.1.2

abbrev singlePair (t : τ) : LivePair τ := ⟨(some t,none),by simp⟩
def singleCoordinates (α : Type) : α≃(α×Unit) where
 toFun := fun a=>(a,())
 invFun := Prod.fst
 left_inv := fun _=>rfl
 right_inv := by rintro ⟨a,u⟩; cases u; rfl

def singleComparison (t : τ) (W : Word D A (D t)) (hW : W.matrix=A t) : PairComparison (A := A) where
 pair := singlePair t
 word := W.reindex (singleCoordinates (D t))
 correct := by
  rw [Word.matrix_reindex,hW]
  ext ⟨i,u⟩ ⟨j,v⟩
  cases u; cases v
  simp [singleCoordinates,pairMatrix,singlePair,speciesMatrix,Matrix.reindex_apply]

@[simp] theorem singleComparison_price
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} (p : τ→ℝ) (t : τ) (W : Word D A (D t)) (hW : W.matrix=A t) :
 pairPrice (D := D) p (singleComparison t W hW).pair=p t := by
 change (Fintype.card (SpeciesDomain D (none : Option τ)) : ℝ)*p t+
   (Fintype.card (D t) : ℝ)*0=p t
 have hc : Fintype.card (SpeciesDomain D (none : Option τ))=1 := Fintype.card_ofSubsingleton ()
 rw [hc]
 ring
@[simp] theorem singleComparison_weight
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} (p : τ→ℝ) (t : τ) (W : Word D A (D t)) (hW : W.matrix=A t) :
 (singleComparison t W hW).word.weight p=W.weight p := by
 exact Word.weight_reindex p _ W

end ExactFourier.Packing

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.ComparisonRename
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Kronecker
namespace ExactFourier.Packing
variable {τ σ : Type}
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {E : σ→Type} [∀ t,Fintype (E t)] [∀ t,DecidableEq (E t)]
 {B : ∀ t,Matrix (E t) (E t) ℂ}

abbrev mapPair (f : τ→σ) (p : LivePair τ) : LivePair σ :=
 ⟨(p.1.1.map f,p.1.2.map f),by
   rcases p with ⟨⟨a,b⟩,h⟩
   cases a with
   | none => cases b with
     | none => exact (h rfl).elim
     | some b => simp
   | some a => simp⟩
def speciesEquiv (f : τ→σ) (e : ∀ t,D t≃E (f t)) :
 ∀ s : Option τ,SpeciesDomain D s≃SpeciesDomain E (s.map f)
 | none => Equiv.refl _
 | some t => e t
abbrev pairEquiv (f : τ→σ) (e : ∀ t,D t≃E (f t)) (p : LivePair τ) :
 PairDomain D p≃PairDomain E (mapPair f p) :=
 (speciesEquiv f e p.1.1).prodCongr (speciesEquiv f e p.1.2)

theorem speciesEquiv_matrix
    {τ : Type} {σ : Type} {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} {E : σ → Type} [(t : σ) → Fintype (E t)] [(t : σ) → DecidableEq (E t)] {B : (t : σ) → Matrix (E t) (E t) ℂ} (f : τ→σ) (e : ∀ t,D t≃E (f t))
 (he : ∀ t,Matrix.reindex (e t) (e t) (A t)=B (f t)) (s : Option τ) :
 Matrix.reindex (speciesEquiv f e s) (speciesEquiv f e s) (speciesMatrix (A := A) s)=
 speciesMatrix (A := B) (s.map f) := by
 cases s with
 | none => rfl
 | some t => exact he t

theorem pairEquiv_matrix (f : τ→σ) (e : ∀ t,D t≃E (f t))
 (he : ∀ t,Matrix.reindex (e t) (e t) (A t)=B (f t)) (p : LivePair τ) :
 Matrix.reindex (pairEquiv f e p) (pairEquiv f e p) (pairMatrix (A := A) p)=
 pairMatrix (A := B) (mapPair f p) := by
 dsimp only [pairEquiv,pairMatrix]
 rw [ExactFourier.reindex_tensor,speciesEquiv_matrix f e he,speciesEquiv_matrix f e he]

abbrev PairComparison.rename (f : τ→σ) (e : ∀ t,D t≃E (f t))
 (he : ∀ t,Matrix.reindex (e t) (e t) (A t)=B (f t)) (c : PairComparison (A := A)) :
 PairComparison (A := B) where
 pair := mapPair f c.pair
 word := (c.word.rename f e).reindex (pairEquiv f e c.pair)
 correct := by
  rw [Word.matrix_reindex,Word.matrix_rename f e he,c.correct,pairEquiv_matrix f e he]

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
structure GMatrix where
 width : ℕ
 mat : Matrix (Fin width) (Fin width) ℂ
 unit : IsUnit mat
abbrev GMatrix.domain (g : GMatrix) := Fin g.width

def shearG : GMatrix := ⟨2,shearU,shearU_unit⟩
abbrev shearD (_ : Unit) := Fin 2
abbrev shearA (_ : Unit) := shearU

theorem GMatrix.upper_exists (g : GMatrix) :
 ∃ C : ℕ,∃ W : Word shearD shearA g.domain,W.matrix=g.mat ∧
 ∀ p : Unit→ℝ,W.weight p=(C : ℝ)*p () :=
 shear_word_exists () (Equiv.refl _) (by rfl) g.mat g.unit

def GMatrix.upperCost (g : GMatrix) : ℕ := g.upper_exists.choose
def GMatrix.upperWord (g : GMatrix) : Word shearD shearA g.domain := g.upper_exists.choose_spec.choose
@[simp] theorem GMatrix.upperWord_matrix (g : GMatrix) : g.upperWord.matrix=g.mat :=
 g.upper_exists.choose_spec.choose_spec.1
@[simp] theorem GMatrix.upperWord_weight (g : GMatrix) (p : Unit→ℝ) :
 g.upperWord.weight p=(g.upperCost : ℝ)*p () := g.upper_exists.choose_spec.choose_spec.2 p

structure GlobalComparison where
 num : ℕ
 family : Fin num→GMatrix
 comparison : PairComparison (D := fun t=>(family t).domain) (A := fun t=>(family t).mat)

def GlobalComparison.holds (c : GlobalComparison) (p : GMatrix→ℝ) : Prop :=
 pairPrice (D := fun t=>(c.family t).domain) (p∘c.family) c.comparison.pair≤
 c.comparison.word.weight (p∘c.family)

def GlobalConstraints (p : GMatrix→ℝ) : Prop := ∀ c : GlobalComparison,c.holds p

variable {τ : Type} [Fintype τ] [DecidableEq τ]
 (f : τ→GMatrix)

theorem family_cast_matrix
    {τ : Type} [Fintype τ] [DecidableEq τ] (f : τ → ExactFourier.Packing.GMatrix) {t u : τ} (h : t=u) :
 Matrix.reindex (Equiv.cast (congrArg (fun t=>(f t).domain) h))
  (Equiv.cast (congrArg (fun t=>(f t).domain) h)) (f t).mat=(f u).mat := by
 cases h
 rfl

abbrev toGlobalComparison (c : PairComparison (D := fun t=>(f t).domain) (A := fun t=>(f t).mat)) : GlobalComparison where
 num := Fintype.card τ
 family := f∘(Fintype.equivFin τ).symm
 comparison := c.rename (Fintype.equivFin τ)
  (fun t=>Equiv.cast (congrArg (fun t=>(f t).domain) ((Fintype.equivFin τ).symm_apply_apply t).symm))
  (fun t=>family_cast_matrix f ((Fintype.equivFin τ).symm_apply_apply t).symm)

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {ρ : Type} [Fintype ρ] [DecidableEq ρ]

abbrev familyKey (c : ρ→PairComparison (A := A)) : LivePair τ⊕ρ→LivePair τ
 | .inl p => p
 | .inr r => (c r).pair

def familyProgram (c : ρ→PairComparison (A := A)) :
 ∀ p : LivePair τ⊕ρ,FramedWord D (PairDomain D (familyKey c p))
 | .inl p => (standardPair (A := A) p).framed
 | .inr r => (c r).word.framed

def familyMultiplicity (c : ρ→PairComparison (A := A)) (n : LivePair τ→ℕ) (a : ρ→ℕ) :
 LivePair τ⊕ρ→ℕ
 | .inl p => n p-∑ r,if (c r).pair=p then a r else 0
 | .inr r => a r

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {α : Type} [Fintype α] [DecidableEq α]

def framedSlot (W : FramedWord D α) {T : ℕ} (time : Fin W.frames.length→Fin T) (t : Fin T) : Option (Frame D α) :=
 Function.extend time (fun i=>some (W.frames.get i)) (fun _=>none) t

def slotCall : Option (Frame D α)→Step D A α
 | none => .mono 1 MonomialMatrix.one
 | some f => .call f.type f.tuple

def slotMono : Option (Frame D α)→Matrix α α ℂ
 | none => 1
 | some f => f.mono

def slotMatrix (f : Option (Frame D α)) : Matrix α α ℂ := slotMono f*(slotCall (A := A) f).matrix

variable {π : Type} [Fintype π] [DecidableEq π]
 {β : π→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]

def framedLayer (W : ∀ p,FramedWord D (β p)) {T : ℕ}
 (time : ∀ p,Fin (W p).frames.length→Fin T) (t : Fin T) : Matrix (Σ p,β p) (Σ p,β p) ℂ :=
 Matrix.blockDiagonal' (fun p=>slotMatrix (A := A) (framedSlot (W p) (time p) t))

end ExactFourier.Packing

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.PackedSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier.Packing

/-- Sectors with identical programs start cyclically at the F possible starts. -/
def cyclicStart (F : ℕ) {m : ℕ} (j : Fin m) : ℕ := j.val % F

variable {π τ : Type*} [Fintype π] [DecidableEq τ]

/-- Positions of calls of type i within a fixed sector program. -/
def occurrences (P : List τ) (i : τ) : Finset (Fin P.length) :=
  Finset.univ.filter (fun o => P.get o = i)

/-- Exact number of calls of a given type at a given time in the cyclic schedule. -/
def scheduledLoad (P : π → List τ) (m : π → ℕ) (F : ℕ) (i : τ) (t : ℕ) : ℕ :=
  ∑ p, ∑ o ∈ occurrences (P p) i,
    (Finset.univ.filter (fun j : Fin (m p) => cyclicStart F j + o.val = t)).card

/-- Total calls of a type before scheduling. -/
def totalCalls (P : π → List τ) (m : π → ℕ) (i : τ) : ℕ :=
  ∑ p, m p * (occurrences (P p) i).card

/-- No occurrence is placed outside the allocated F+L-1 slots. -/
theorem schedule_in_range {F L m : ℕ} (hF : 0 < F) (j : Fin m) (o : Fin L) :
    cyclicStart F j + o.val < F + L - 1 := by
  have hs := Nat.mod_lt j.val hF
  have ho := o.isLt
  unfold cyclicStart
  omega

end ExactFourier.Packing

end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {α : Type} [Fintype α] [DecidableEq α]

def subtypeSigmaAll {π : Type} {β : π→Type} (P : ∀ p,β p→Prop) :
 {x : Σ p,β p // P x.1 x.2}≃(Σ p,{x : β p // P p x}) where
 toFun x := ⟨x.1.1,x.1.2,x.2⟩
 invFun x := ⟨⟨x.1,x.2.1⟩,x.2.2⟩
 left_inv _ := rfl
 right_inv _ := rfl

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
open Finset

def sigmaFiberEquiv {ι : Type} {β : ι→Type} (t : ι) :
    {x : Σ i,β i // x.1=t}≃β t where
 toFun x := x.2 ▸ x.1.2
 invFun a := ⟨⟨t,a⟩,rfl⟩
 left_inv := by rintro ⟨⟨s,a⟩,h⟩; dsimp at h; subst s; rfl
 right_inv _ := rfl

end ExactFourier.Packing

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.SumFramed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {π ρ : Type} [Fintype π] [Fintype ρ] [DecidableEq π] [DecidableEq ρ]
 {β : π→Type} {γ : ρ→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]
 [∀ r,Fintype (γ r)] [∀ r,DecidableEq (γ r)]

abbrev SumDomain (β : π→Type) (γ : ρ→Type) : π⊕ρ→Type
 | .inl p => β p
 | .inr r => γ r
instance SumDomain_fintype (v : π⊕ρ) : Fintype (SumDomain β γ v) := by
 cases v <;> dsimp [SumDomain] <;> infer_instance
instance SumDomain_decEq (v : π⊕ρ) : DecidableEq (SumDomain β γ v) := by
 cases v <;> dsimp [SumDomain] <;> infer_instance

def sumFramed (W : ∀ p,FramedWord D (β p)) (V : ∀ r,FramedWord D (γ r)) :
 ∀ v : π⊕ρ,FramedWord D (SumDomain β γ v)
 | .inl p => W p
 | .inr r => V r

def sumTime (W : ∀ p,FramedWord D (β p)) (V : ∀ r,FramedWord D (γ r)) {T : ℕ}
 (timeW : ∀ p,Fin (W p).frames.length→Fin T)
 (timeV : ∀ r,Fin (V r).frames.length→Fin T) :
 ∀ v,Fin (sumFramed W V v).frames.length→Fin T
 | .inl p => timeW p
 | .inr r => timeV r

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {π ρ : Type} [Fintype π] [Fintype ρ] [DecidableEq π] [DecidableEq ρ]
 {β : π→Type} {γ : ρ→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]
 [∀ r,Fintype (γ r)] [∀ r,DecidableEq (γ r)]

variable (D) (α : Type) [Fintype α] [DecidableEq α]

def emptyFramed : FramedWord D α := ⟨[],1,MonomialMatrix.one⟩

@[simp] theorem emptyFramed_matrix
    {τ : Type} [Fintype τ] [DecidableEq τ] (D : τ → Type) [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} (α : Type) [Fintype α] [DecidableEq α] : (emptyFramed D α).matrix (A := A)=1 := by
 simp [emptyFramed,FramedWord.matrix]

def emptyTime (T : ℕ) : Fin (emptyFramed D α).frames.length→Fin T := Fin.elim0

@[simp] theorem empty_slot_card
    {τ : Type} [Fintype τ] [DecidableEq τ] (D : τ → Type) [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} (α : Type) [Fintype α] [DecidableEq α] (T : ℕ) (s : Fin T) (t : τ) :
 Fintype.card {_unused : Unit //
   (slotCall (A := A) (framedSlot (emptyFramed D α) (emptyTime D α T) s)).kind=some t}=0 := by
 have hn : ¬∃ i,emptyTime D α T i=s := by rintro ⟨i,_⟩; exact Fin.elim0 i
 simp [framedSlot,Function.extend_apply' _ _ _ hn,slotCall,Step.kind]

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {π : Type} [Fintype π] [DecidableEq π]
 {β : π→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]

def cyclicTime (W : ∀ p,FramedWord D (β p)) (m : π→ℕ) (F L : ℕ)
 (hF : 0<F) (hL : ∀ p,(W p).frames.length≤L) :
 ∀ v : Σ p,Fin (m p),Fin (W v.1).frames.length→Fin (F+L-1) :=
 fun v o=>⟨cyclicStart F v.2+o.val,
   schedule_in_range hF v.2 (⟨o.val,lt_of_lt_of_le o.isLt (hL v.1)⟩ : Fin L)⟩

end ExactFourier.Packing

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.LiveSectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}

def liveMatrix (k : τ→ℕ) (I : ℕ) : Matrix (LiveSpace D k I) (LiveSpace D k I) ℂ :=
 Matrix.blockDiagonal' fun p : LivePair τ=>
   Matrix.kronecker (1 : Matrix (Fin (speciesCopies k I p.1.1)×Fin (speciesCopies k I p.1.2))
         (Fin (speciesCopies k I p.1.1)×Fin (speciesCopies k I p.1.2)) ℂ)
     (pairMatrix (A := A) p)

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {σ π : Type} [Fintype σ] [DecidableEq σ] [Fintype π] [DecidableEq π]
 {E : σ→Type} [∀ s,Fintype (E s)] [∀ s,DecidableEq (E s)]
 {B : ∀ s,Matrix (E s) (E s) ℂ}

def sigmaFstFiber (κ : σ→Type) (s : σ) : {v : Σ t,κ t // v.1=s}≃κ s where
 toFun x := cast (congrArg κ x.property) x.val.2
 invFun y := ⟨⟨s,y⟩,rfl⟩
 left_inv := by rintro ⟨⟨t,x⟩,h⟩; dsimp at h; subst s; rfl
 right_inv := by intro y; rfl

def copyCoordinates (κ : σ→Type) : (Σ v : Σ s,κ s,E v.1)≃(Σ s,κ s×E s) where
 toFun x := ⟨x.1.1,x.1.2,x.2⟩
 invFun x := ⟨⟨x.1,x.2.1⟩,x.2.2⟩
 left_inv := by rintro ⟨⟨s,i⟩,a⟩; rfl
 right_inv := by rintro ⟨s,i,a⟩; rfl

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {α : Type} [Fintype α] [DecidableEq α]

def singleStepFin (e : α≃Fin (Fintype.card α))
 (f : (α×α)≃Fin (Fintype.card α^2)) (A : Matrix α α ℂ) :
 Step (fun _ : Unit=>α) (fun _=>A) (α×α) →
 WordStep (Matrix.reindex e e A) (Fintype.card α^2)
 | .mono M hM => .monomial (Matrix.reindex f f M) (hM.reindex f)
 | .call _ g => .call (e.symm.toEmbedding.trans (g.trans f.toEmbedding))

def squareFinEquiv (e : α≃Fin (Fintype.card α)) : (α×α)≃Fin (Fintype.card α^2) :=
 ((e.prodCongr e).trans (finTwoArrowEquiv _).symm).trans
  (tensorCoordinates (Fintype.card α) 2).symm

end ExactFourier.Packing

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.FiniteSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Packing

def GMatrix.of {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ) (hM : IsUnit M) : GMatrix :=
 ⟨Fintype.card α,Matrix.reindex (Fintype.equivFin α) (Fintype.equivFin α) M,
  TensorTools.unit_reindex _ _ hM⟩
def rawValue (p : GMatrix→ℝ) {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ) : ℝ := by
 classical
 exact if h:IsUnit M then p (GMatrix.of M h) else 0

structure RawPrice where
 value : ∀ {α : Type} [Fintype α] [DecidableEq α],Matrix α α ℂ→ℝ
 nonneg : ∀ {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ),IsUnit M→0≤value M
 comparison : ∀ {τ : Type} [Fintype τ] [DecidableEq τ]
  {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
  {A : ∀ t,Matrix (D t) (D t) ℂ},(∀ t,IsUnit (A t))→
  ∀ c : PairComparison (A := A),pairPrice (D := D) (fun t=>value (A t)) c.pair≤
    c.word.weight (fun t=>value (A t))
 normalized : value shearU=1

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier
namespace Embedded
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
theorem matrix_inl (M : Matrix α α ℂ) :
 matrix (Function.Embedding.inl : α ↪ α⊕β) M=Matrix.fromBlocks M 0 0 1 := by
 ext i j
 cases i with
 | inl i => cases j with
  | inl j => exact matrix_on Function.Embedding.inl M i j
  | inr j =>
   rw [matrix_off_col _ _ _ _ (by rintro ⟨a,h⟩; cases h)]
   simp
 | inr i =>
  rw [matrix_off_row _ _ _ _ (by rintro ⟨a,h⟩; cases h)]
  cases j <;> simp [Matrix.one_apply]
theorem matrix_inr (M : Matrix β β ℂ) :
 matrix (Function.Embedding.inr : β ↪ α⊕β) M=Matrix.fromBlocks 1 0 0 M := by
 ext i j
 cases i with
 | inr i => cases j with
  | inr j => exact matrix_on Function.Embedding.inr M i j
  | inl j =>
   rw [matrix_off_col _ _ _ _ (by rintro ⟨a,h⟩; cases h)]
   simp
 | inl i =>
  rw [matrix_off_row _ _ _ _ (by rintro ⟨a,h⟩; cases h)]
  cases j <;> simp [Matrix.one_apply]
@[simp] theorem matrix_refl (M : Matrix α α ℂ) : matrix (Function.Embedding.refl α) M=M := by
 ext i j; exact matrix_on (Function.Embedding.refl _) _ i j
end Embedded
namespace Packing
variable {τ : Type} {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def Word.sum (W : Word D A α) (V : Word D A β) : Word D A (α⊕β) :=
 W.embed Function.Embedding.inl++V.embed Function.Embedding.inr
@[simp] theorem Word.matrix_sum (W : Word D A α) (V : Word D A β) :
 (W.sum V).matrix=Matrix.fromBlocks W.matrix 0 0 V.matrix := by
 rw [Word.sum,Word.matrix_append,Word.matrix_embed,Word.matrix_embed,Embedded.matrix_inl,Embedded.matrix_inr]
 simp [Matrix.fromBlocks_multiply]
@[simp] theorem Word.weight_sum (p : τ→ℝ) (W : Word D A α) (V : Word D A β) :
 (W.sum V).weight p=W.weight p+V.weight p := by
 rw [Word.sum,Word.weight_append,Word.weight_embed,Word.weight_embed]

theorem Word.weight_kronecker [Fintype τ] [DecidableEq τ] (p : τ→ℝ) (W : Word D A α) (V : Word D A β) :
 (W.kronecker V).weight p=(Fintype.card β : ℝ)*W.weight p+(Fintype.card α : ℝ)*V.weight p := by
 rw [Word.weight_count,Word.weight_count,Word.weight_count]
 simp only [Word.count_kronecker,Nat.cast_add,Nat.cast_mul,add_mul,Finset.sum_add_distrib,mul_assoc,Finset.mul_sum]
end Packing
end ExactFourier

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.RawWordBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Packing
namespace RawPrice
variable (p : RawPrice)
 {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem word_le (hA : ∀ t,IsUnit (A t)) (W : Word D A α) :
 p.value W.matrix≤W.weight (fun t=>p.value (A t)) := by
 let E : Option τ→Type := fun t=>t.elim α D
 let : ∀ t,Fintype (E t) := fun t=>by cases t <;> dsimp [E] <;> infer_instance
 let : ∀ t,DecidableEq (E t) := fun t=>by cases t <;> dsimp [E] <;> infer_instance
 let B : ∀ t,Matrix (E t) (E t) ℂ := fun t=>by
  cases t with
  | none => exact W.matrix
  | some t => exact A t
 let V : Word E B α := W.rename some (fun _=>Equiv.refl _)
 have hV : V.matrix=B none := Word.matrix_rename (D := D) (A := A) (E := E) (B := B) some (fun _=>Equiv.refl _) (fun _=>rfl) W
 have hB : ∀ t,IsUnit (B t) := by
  intro t; cases t with
  | none => exact W.unit hA
  | some t => exact hA t
 have hh := p.comparison hB (singleComparison none V hV)
 have hl := singleComparison_price (D := E) (A := B) (fun t=>p.value (B t)) none V hV
 have hr := singleComparison_weight (D := E) (A := B) (fun t=>p.value (B t)) none V hV
 rw [hl,hr] at hh
 change p.value W.matrix≤V.weight (fun t=>p.value (B t)) at hh
 have hw := Word.weight_rename (D := D) (A := A) (E := E) (B := B)
   some (fun _=>Equiv.refl _) (fun t=>p.value (B t)) W
 exact hh.trans_eq hw

theorem word_bound (hA : ∀ t,IsUnit (A t)) (W : Word D A α)
 (H : Matrix α α ℂ) (hW : W.matrix=H) : p.value H≤W.weight (fun t=>p.value (A t)) :=
 hW ▸ p.word_le hA W

theorem monomial_zero (M : Matrix α α ℂ) (hM : MonomialMatrix M) : p.value M=0 := by
 let W : Word (fun _:Unit=>α) (fun _=>(1 : Matrix α α ℂ)) α := monoWord M hM
 have hh := p.word_bound (fun _ : Unit=>isUnit_one) W M (matrix_monoWord M hM)
 change p.value M≤0 at hh
 exact le_antisymm hh (p.nonneg _ (hM.unit _))

@[simp] theorem one : p.value (1 : Matrix α α ℂ)=0 := p.monomial_zero 1 MonomialMatrix.one

theorem reindex_le (e : α≃β) (M : Matrix α α ℂ) (hM : IsUnit M) :
 p.value (Matrix.reindex e e M)≤p.value M := by
 let W : Word (fun _:Unit=>α) (fun _=>M) β := callWord () e.toEmbedding
 have hh := p.word_le (fun _:Unit=>hM) W
 have he : W.matrix=Matrix.reindex e e M := by rw [matrix_callWord,Embedded.matrix_equiv]
 rw [he] at hh
 simpa [W,Word.weight] using hh

theorem reindex (e : α≃β) (M : Matrix α α ℂ) (hM : IsUnit M) :
 p.value (Matrix.reindex e e M)=p.value M := by
 apply le_antisymm (p.reindex_le e M hM)
 have hh := p.reindex_le e.symm _ (TensorTools.unit_reindex e M hM)
 rw [ExactFourier.reindex_inverse] at hh
 exact hh

theorem mul_le (M N : Matrix α α ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.value (M*N)≤p.value M+p.value N := by
 let A : Bool→Matrix α α ℂ := fun b=>cond b M N
 let W : Word (fun _:Bool=>α) A α := callWord (D := fun _:Bool=>α) (A := A) true (Function.Embedding.refl _)++callWord (D := fun _:Bool=>α) (A := A) false (Function.Embedding.refl _)
 have hA : ∀ b,IsUnit (A b) := by intro b; cases b <;> assumption
 have hm : W.matrix=M*N := by
  dsimp only [W]
  rw [Word.matrix_append,matrix_callWord,matrix_callWord,Embedded.matrix_refl,Embedded.matrix_refl]
  rfl
 have hh := p.word_bound hA W (M*N) hm
 simpa [W,Word.weight,A] using hh

theorem monomial (M L R : Matrix α α ℂ) (hM : IsUnit M)
 (hL : MonomialMatrix L) (hR : MonomialMatrix R) : p.value (L*M*R)=p.value M := by
 have one_side : ∀ (M L R : Matrix α α ℂ),IsUnit M→MonomialMatrix L→MonomialMatrix R→
   p.value (L*M*R)≤p.value M := by
  intro M L R hM hL hR
  have h1 := p.mul_le L M (hL.unit _) hM
  have h2 := p.mul_le (L*M) R ((hL.unit _).mul hM) (hR.unit _)
  rw [p.monomial_zero L hL] at h1
  rw [p.monomial_zero R hR] at h2
  linarith
 apply le_antisymm (one_side M L R hM hL hR)
 have hh := one_side (L*M*R) L⁻¹ R⁻¹ (((hL.unit _).mul hM).mul (hR.unit _)) hL.inverse hR.inverse
 have he : L⁻¹*(L*M*R)*R⁻¹=M := by
  simp only [← mul_assoc,Matrix.nonsing_inv_mul L ((Matrix.isUnit_iff_isUnit_det L).mp (hL.unit _)),one_mul]
  rw [mul_assoc,Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).mp (hR.unit _)),mul_one]
 rw [he] at hh
 exact hh
end RawPrice
end ExactFourier.Packing

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier.Packing
abbrev BiDomain (α β : Type) : Bool→Type
 | false => α
 | true => β
instance instFintypeBiDomain {α β : Type} [Fintype α] [Fintype β] (b : Bool) : Fintype (BiDomain α β b) := by
 cases b <;> dsimp [BiDomain] <;> infer_instance
instance instDecidableEqBiDomain {α β : Type} [DecidableEq α] [DecidableEq β] (b : Bool) : DecidableEq (BiDomain α β b) := by
 cases b <;> dsimp [BiDomain] <;> infer_instance
abbrev biMatrix {α β : Type} (M : Matrix α α ℂ) (N : Matrix β β ℂ) :
 ∀ b,Matrix (BiDomain α β b) (BiDomain α β b) ℂ
 | false => M
 | true => N
namespace RawPrice
variable (p : RawPrice) {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem tensor_le (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.value (M⊗ₖN)≤(Fintype.card β : ℝ)*p.value M+(Fintype.card α : ℝ)*p.value N := by
 let A := biMatrix M N
 let W : Word (BiDomain α β) A α := callWord false (Function.Embedding.refl _)
 let V : Word (BiDomain α β) A β := callWord true (Function.Embedding.refl _)
 have hA : ∀ b,IsUnit (A b) := by intro b; cases b <;> assumption
 have hW : W.matrix=M := by rw [matrix_callWord,Embedded.matrix_refl]
 have hV : V.matrix=N := by rw [matrix_callWord,Embedded.matrix_refl]
 have hh := p.word_bound hA (W.kronecker V) (M⊗ₖN) (by rw [Word.matrix_kronecker,hW,hV]; rfl)
 rw [Word.weight_kronecker] at hh
 simpa [W,V,Word.weight,A] using hh

theorem tensor_ge (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 (Fintype.card β : ℝ)*p.value M+(Fintype.card α : ℝ)*p.value N≤p.value (M⊗ₖN) := by
 let D : Option Bool→Type := fun s=>s.elim (α×β) (BiDomain α β)
 let : ∀ s,Fintype (D s) := fun s=>by cases s <;> dsimp [D] <;> infer_instance
 let : ∀ s,DecidableEq (D s) := fun s=>by cases s <;> dsimp [D] <;> infer_instance
 let A : ∀ s,Matrix (D s) (D s) ℂ
  | none => M⊗ₖN
  | some b => biMatrix M N b
 let q : LivePair (Option Bool) := ⟨(some (some false),some (some true)),by simp⟩
 let W : Word D A (PairDomain D q) := callWord none (Function.Embedding.refl _)
 have hW : W.matrix=pairMatrix (A := A) q := by
  change (callWord (A := A) none (Function.Embedding.refl _)).matrix=_
  exact (matrix_callWord _ _).trans (Embedded.matrix_refl _)
 have hA : ∀ s,IsUnit (A s) := by
  intro s; cases s with
  | none => exact TensorTools.unit_tensor M N hM hN
  | some b => cases b <;> assumption
 have hh := p.comparison hA ⟨q,W,hW⟩
 change pairPrice (D := D) (fun s=>p.value (A s)) q≤W.weight (fun s=>p.value (A s)) at hh
 simp [pairPrice,q,speciesPrice,SpeciesDomain,D,A,W,Word.weight,callWord,Word.calls,Step.kind,BiDomain,biMatrix] at hh
 convert hh using 1 ; congr 1

theorem tensor (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.value (M⊗ₖN)=(Fintype.card β : ℝ)*p.value M+(Fintype.card α : ℝ)*p.value N :=
 le_antisymm (p.tensor_le M N hM hN) (p.tensor_ge M N hM hN)

theorem directSum_le (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.value (Matrix.fromBlocks M 0 0 N)≤p.value M+p.value N := by
 let A := biMatrix M N
 let W : Word (BiDomain α β) A α := callWord false (Function.Embedding.refl _)
 let V : Word (BiDomain α β) A β := callWord true (Function.Embedding.refl _)
 have hA : ∀ b,IsUnit (A b) := by intro b; cases b <;> assumption
 have hW : W.matrix=M := by rw [matrix_callWord,Embedded.matrix_refl]
 have hV : V.matrix=N := by rw [matrix_callWord,Embedded.matrix_refl]
 have hh := p.word_bound hA (W.sum V) (Matrix.fromBlocks M 0 0 N) (by rw [Word.matrix_sum,hW,hV])
 rw [Word.weight_sum] at hh
 simpa [W,V,Word.weight,A] using hh
end RawPrice
end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def Word.Pure (W : Word D A α) : Prop := ∀ s∈W,s.kind≠none
@[simp] theorem Word.pure_nil : Word.Pure ([] : Word D A α) := by simp [Word.Pure]
@[simp] theorem Word.pure_cons (s : Step D A α) (W : Word D A α) :
 Word.Pure (s::W) ↔ s.kind≠none ∧ W.Pure := by simp [Word.Pure]
@[simp] theorem Word.pure_append (W V : Word D A α) : (W++V).Pure ↔ W.Pure ∧ V.Pure := by
 simp only [Word.Pure,List.mem_append]
 aesop
theorem Word.Pure.embed {W : Word D A α} (h : W.Pure) (e : α ↪ β) : (W.embed e).Pure := by
 intro s hs
 change s∈W.map (Step.embed e) at hs
 obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hs
 simpa using h x hx
theorem Word.Pure.reindex {W : Word D A α} (h : W.Pure) (e : α≃β) : (W.reindex e).Pure := h.embed e.toEmbedding

theorem Word.pure_blockSum {π : Type} [Fintype π] [DecidableEq π]
 {E : π→Type} [∀ t,Fintype (E t)] [∀ t,DecidableEq (E t)]
 (W : ∀ t,Word D A (E t)) (h : ∀ t,(W t).Pure) : (Word.blockSum W).Pure := by
 intro s hs
 obtain ⟨V,hV,hs⟩ := List.mem_flatten.mp hs
 obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hV
 exact (h t).embed (Embedded.sigmaIn t) s hs

theorem Word.Pure.leftTensor {W : Word D A α} (h : W.Pure) : (W.leftTensor (β := β)).Pure :=
 (Word.pure_blockSum (fun _:β=>W) (fun _=>h)).reindex _
theorem Word.Pure.rightTensor {W : Word D A β} (h : W.Pure) : (W.rightTensor (α := α)).Pure :=
 (Word.pure_blockSum (fun _:α=>W) (fun _=>h)).reindex _
theorem Word.Pure.kronecker {W : Word D A α} {V : Word D A β} (hW : W.Pure) (hV : V.Pure) :
 (W.kronecker V).Pure := Word.pure_append _ _ |>.mpr ⟨hW.leftTensor,hV.rightTensor⟩

@[simp] theorem pure_callWord (t : τ) (e : D t ↪ α) : (callWord (A := A) t e).Pure := by
 simp [callWord,Step.kind]

theorem Word.Pure.length_eq_count {M : Matrix α α ℂ}
 {W : Word (fun _:Unit=>α) (fun _=>M) β} (hW : W.Pure) : W.length=W.count () := by
 induction W with
 | nil => rfl
 | cons s W ih =>
  have hh := Word.pure_cons s W |>.mp hW
  cases s with
  | mono M h => exact (hh.1 rfl).elim
  | call t e =>
   cases t
   simp only [List.length_cons,Word.count,Word.calls,List.filterMap_cons,Step.kind,List.count_cons_self]
   congr 1
   exact ih hh.2

variable (M : Matrix α α ℂ)
def purePower (M : Matrix α α ℂ) : (k : ℕ)→Word (fun _:Unit=>α) (fun _=>M) (TensorAxis.Space α k)
 | 0 => []
 | k+1 => (purePower M k).kronecker (callWord () (Function.Embedding.refl _))
@[simp] theorem purePower_matrix (k : ℕ) : (purePower M k).matrix=TensorAxis.power M k := by
 induction k with
 | zero => rfl
 | succ k ih => rw [purePower,Word.matrix_kronecker,ih,matrix_callWord,Embedded.matrix_refl]; rfl
@[simp] theorem purePower_pure (k : ℕ) : (purePower M k).Pure := by
 induction k with
 | zero => exact Word.pure_nil
 | succ k ih => exact ih.kronecker (pure_callWord _ _)
theorem purePower_count (k : ℕ) : (purePower M k).count ()=Fintype.card (TensorAxis.Fibers α k) := by
 induction k with
 | zero => simp [purePower,Word.count,Word.calls]
 | succ k ih =>
  rw [purePower,Word.count_kronecker,ih,Triangular.calls_card_succ]
  simp [Word.count,mul_comm]
end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Embedded
variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
theorem matrix_sumMap (e : α ↪ γ) (f : β ↪ δ) (M : Matrix α α ℂ) (N : Matrix β β ℂ) :
 matrix (e.sumMap f) (Matrix.fromBlocks M 0 0 N)=
 Matrix.fromBlocks (matrix e M) 0 0 (matrix f N) := by
 have he : (Function.Embedding.inl : α ↪ α⊕β).trans (e.sumMap f)=e.trans Function.Embedding.inl := rfl
 have hf : (Function.Embedding.inr : β ↪ α⊕β).trans (e.sumMap f)=f.trans Function.Embedding.inr := rfl
 have hJ : Matrix.fromBlocks M 0 0 N=
  matrix (Function.Embedding.inl : α ↪ α⊕β) M*matrix Function.Embedding.inr N := by
  rw [matrix_inl,matrix_inr]; simp [Matrix.fromBlocks_multiply]
 rw [hJ,matrix_mul,matrix_comp,matrix_comp,he,hf,← matrix_comp,← matrix_comp,matrix_inl,matrix_inr]
 simp [Matrix.fromBlocks_multiply]
end ExactFourier.Embedded

end
end

section
noncomputable section
namespace ExactFourier.Packing.RawPrice
variable (p : RawPrice) {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

theorem embedded_le (e : α ↪ β) (M : Matrix α α ℂ) (hM : IsUnit M) :
 p.value (Embedded.matrix e M)≤p.value M := by
 have hh := p.word_le (fun _:Unit=>hM) (callWord () e)
 simpa [Word.weight] using hh

theorem paired_le (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N)
 (W : Word (fun _:Unit=>α) (fun _=>M) γ) (V : Word (fun _:Unit=>β) (fun _=>N) δ)
 (hW : W.Pure) (hV : V.Pure) (hlen : W.length=V.length) :
 p.value (Matrix.fromBlocks (Word.matrix W) 0 0 (Word.matrix V))≤(W.length : ℝ)*p.value (Matrix.fromBlocks M 0 0 N) := by
 induction W generalizing V with
 | nil =>
  have hv : V=[] := List.length_eq_zero_iff.mp hlen.symm
  subst V
  simp
 | cons s W ih =>
  cases V with
  | nil => simp at hlen
  | cons t V =>
   obtain ⟨hs,hW'⟩ := (Word.pure_cons s W).mp hW
   obtain ⟨ht,hV'⟩ := (Word.pure_cons t V).mp hV
   cases s with
   | mono X hX => exact (hs rfl).elim
   | call a e =>
    cases t with
    | mono X hX => exact (ht rfl).elim
    | call b f =>
     cases a; cases b
     have hl : W.length=V.length := by simpa using hlen
     have hi := ih V hW' hV' hl
     have hJ : IsUnit (Matrix.fromBlocks M 0 0 N) := Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hM,hN⟩
     have he := p.embedded_le (e.sumMap f) (Matrix.fromBlocks M 0 0 N) hJ
     rw [Embedded.matrix_sumMap] at he
     have hu : IsUnit (Matrix.fromBlocks (Embedded.matrix e M) 0 0 (Embedded.matrix f N)) :=
      Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨Embedded.unit _ _ hM,Embedded.unit _ _ hN⟩
     have hv : IsUnit (Matrix.fromBlocks (Word.matrix W) 0 0 (Word.matrix V)) :=
      Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨Word.unit (fun _=>hM) W,Word.unit (fun _=>hN) V⟩
     have hh := p.mul_le _ _ hu hv
     simp only [Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add] at hh
     change p.value (Matrix.fromBlocks (Embedded.matrix e M*(Word.matrix W)) 0 0
      (Embedded.matrix f N*(Word.matrix V)))≤_ at hh
     change p.value (Matrix.fromBlocks (Embedded.matrix e M*(Word.matrix W)) 0 0
      (Embedded.matrix f N*(Word.matrix V)))≤_
     simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
     nlinarith
end ExactFourier.Packing.RawPrice

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier.Packing.RawPrice
variable (p : RawPrice) {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem sum_swap (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.value (Matrix.fromBlocks N 0 0 M)=p.value (Matrix.fromBlocks M 0 0 N) := by
 have hh := p.reindex (Equiv.sumComm α β) (Matrix.fromBlocks M 0 0 N)
   (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hM,hN⟩)
 have he : Matrix.reindex (Equiv.sumComm α β) (Equiv.sumComm α β) (Matrix.fromBlocks M 0 0 N)=Matrix.fromBlocks N 0 0 M := by
  ext i j
  cases i <;> cases j <;> rfl
 rw [he] at hh
 exact hh

theorem duplicate (M : Matrix α α ℂ) (hM : IsUnit M) :
 p.value (Matrix.fromBlocks M 0 0 M)=2*p.value M := by
 have he : Matrix.reindex (Equiv.boolProdEquivSum α) (Equiv.boolProdEquivSum α)
   ((1 : Matrix Bool Bool ℂ)⊗ₖM)=Matrix.fromBlocks M 0 0 M := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.reindex_apply,Equiv.boolProdEquivSum]
 rw [← he,p.reindex _ _ (TensorTools.unit_tensor _ _ isUnit_one hM),p.tensor _ _ isUnit_one hM,p.one]
 simp

theorem power (M : Matrix α α ℂ) (hM : IsUnit M) (k : ℕ) :
 p.value (TensorAxis.power M k)=(Fintype.card (TensorAxis.Fibers α k) : ℝ)*p.value M := by
 induction k with
 | zero => simp [TensorAxis.power]
 | succ k ih =>
  rw [TensorAxis.power,p.tensor _ _ (TensorAxis.unit_power M hM k) hM,ih,Triangular.calls_card_succ]
  push_cast
  ring

theorem balanced_calls (hα : 0<Fintype.card α) :
 Fintype.card (TensorAxis.Fibers α (Fintype.card α))=Fintype.card (TensorAxis.Space α (Fintype.card α)) := by
 have hh := Triangular.calls_card_relation (β := α) (Fintype.card α)
 nlinarith

theorem directSum_ge_nonempty (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N)
 (hα : 0<Fintype.card α) (hβ : 0<Fintype.card β) :
 p.value M+p.value N≤p.value (Matrix.fromBlocks M 0 0 N) := by
 let a := Fintype.card α
 let b := Fintype.card β
 let U := TensorAxis.Space α a
 let V := TensorAxis.Space β b
 let W : Word (fun _:Unit=>α) (fun _=>M) (U×V) := (purePower M a).leftTensor
 let Z : Word (fun _:Unit=>β) (fun _=>N) (U×V) := (purePower N b).rightTensor
 let X := TensorAxis.power M a⊗ₖTensorAxis.power N b
 let Q := Fintype.card U*Fintype.card V
 have hW : W.Pure := (purePower_pure M a).leftTensor
 have hZ : Z.Pure := (purePower_pure N b).rightTensor
 have hw : W.length=Q := by
  rw [hW.length_eq_count,Word.count_leftTensor,purePower_count,balanced_calls hα]
  exact Nat.mul_comm _ _
 have hz : Z.length=Q := by
  rw [hZ.length_eq_count,Word.count_rightTensor,purePower_count,balanced_calls hβ]
 have hwu := W.unit (fun _=>hM)
 have hzu := Z.unit (fun _=>hN)
 have hX : IsUnit X := TensorTools.unit_tensor _ _ (TensorAxis.unit_power M hM _) (TensorAxis.unit_power N hN _)
 have h1 := p.paired_le M N hM hN W Z hW hZ (hw.trans hz.symm)
 have h2 := p.paired_le M N hM hN W Z hW hZ (hw.trans hz.symm)
 rw [← p.sum_swap W.matrix Z.matrix hwu hzu] at h2
 rw [hw] at h1 h2
 have ht := p.mul_le (Matrix.fromBlocks W.matrix 0 0 Z.matrix)
   (Matrix.fromBlocks Z.matrix 0 0 W.matrix)
   (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hwu,hzu⟩)
   (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hzu,hwu⟩)
 have hwz : W.matrix*Z.matrix=X := by
  rw [Word.matrix_leftTensor,Word.matrix_rightTensor,purePower_matrix,purePower_matrix]
  change (TensorAxis.power M a⊗ₖ(1 : Matrix V V ℂ))*((1 : Matrix U U ℂ)⊗ₖTensorAxis.power N b)=X
  rw [← Matrix.mul_kronecker_mul,mul_one,one_mul]
 have hzw : Z.matrix*W.matrix=X := by
  rw [Word.matrix_leftTensor,Word.matrix_rightTensor,purePower_matrix,purePower_matrix]
  change ((1 : Matrix U U ℂ)⊗ₖTensorAxis.power N b)*(TensorAxis.power M a⊗ₖ(1 : Matrix V V ℂ))=X
  rw [← Matrix.mul_kronecker_mul,mul_one,one_mul]
 simp only [Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,hwz,hzw] at ht
 rw [p.duplicate X hX] at ht
 have hpX : p.value X=(Q : ℝ)*(p.value M+p.value N) := by
  rw [p.tensor _ _ (TensorAxis.unit_power M hM _) (TensorAxis.unit_power N hN _),p.power M hM,p.power N hN,
   balanced_calls hα,balanced_calls hβ]
  dsimp [Q]
  push_cast
  ring
 rw [hpX] at ht
 have hQ : 0<(Q : ℝ) := by
  exact_mod_cast Nat.mul_pos (Triangular.bottom_card_pos hα a) (Triangular.bottom_card_pos hβ b)
 nlinarith

theorem directSum (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.value (Matrix.fromBlocks M 0 0 N)=p.value M+p.value N := by
 apply le_antisymm (p.directSum_le M N hM hN)
 by_cases hα : 0<Fintype.card α
 · by_cases hβ : 0<Fintype.card β
   · exact p.directSum_ge_nonempty M N hM hN hα hβ
   · have : IsEmpty β := Fintype.card_eq_zero_iff.mp (by omega)
     have hNm : N=1 := Subsingleton.elim _ _
     have he : Matrix.reindex (Equiv.sumEmpty α β).symm (Equiv.sumEmpty α β).symm M=
       Matrix.fromBlocks M 0 0 N := by
      ext i j; cases i with
      | inl i => cases j with
       | inl j => rfl
       | inr j => exact isEmptyElim j
      | inr i => exact isEmptyElim i
     rw [← he,p.reindex _ _ hM,hNm,p.one,add_zero]
 · have : IsEmpty α := Fintype.card_eq_zero_iff.mp (by omega)
   have hMm : M=1 := Subsingleton.elim _ _
   have he : Matrix.reindex (Equiv.emptySum α β).symm (Equiv.emptySum α β).symm N=
       Matrix.fromBlocks M 0 0 N := by
    ext i j; cases i with
    | inl i => exact isEmptyElim i
    | inr i => cases j with
     | inl j => exact isEmptyElim j
     | inr j => rfl
   rw [← he,p.reindex _ _ hN,hMm,p.one,zero_add]
end ExactFourier.Packing.RawPrice

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.RawPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Packing.RawPrice
variable (p : RawPrice) {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem embedded (e : α ↪ β) (M : Matrix α α ℂ) (hM : IsUnit M) :
 p.value (Embedded.matrix e M)=p.value M := by
 rw [Embedded.matrix,p.reindex _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hM,isUnit_one⟩),
  p.directSum _ _ hM isUnit_one,p.one,add_zero]

theorem zero_iff (M : Matrix α α ℂ) (hM : IsUnit M) : p.value M=0 ↔ MonomialMatrix M := by
 refine ⟨?_,p.monomial_zero M⟩
 intro hz
 by_contra hn
 have ha : 2≤Fintype.card α := by
  by_contra h
  have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  exact hn (monomial_of_subsingleton M hM)
 let e : Fin 2 ↪ α := (Fin.castLEEmb ha).trans (Fintype.equivFin α).symm.toEmbedding
 let V : Word (fun _:Unit=>α) (fun _=>M) α := callWord () (Function.Embedding.refl _)
 have hv : V.matrix=M := by rw [matrix_callWord,Embedded.matrix_refl]
 obtain ⟨h,hh,W,hW,hw⟩ := word_generates V (hv.symm ▸ hM) (hv.symm ▸ hn)
  (Embedded.matrix e shearU) (Embedded.unit e shearU shearU_unit)
 have hb := p.word_bound (fun _:Unit=>hM) W (Embedded.matrix e shearU) hW
 rw [hw] at hb
 have hweight : V.weight (fun _:Unit=>p.value M)=p.value M := by simp [V,Word.weight]
 rw [hweight,hz,mul_zero,p.embedded e shearU shearU_unit,p.normalized] at hb
 norm_num at hb
end ExactFourier.Packing.RawPrice

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier
namespace MonomialMatrix
variable {α : Type} [Fintype α] [DecidableEq α]
theorem transpose
    {α : Type} [Fintype α] [DecidableEq α] {M : Matrix α α ℂ} (hM : MonomialMatrix M) : MonomialMatrix M.transpose := by
 obtain ⟨s,d,hd,hs⟩ := hM
 refine ⟨s.symm,fun j=>d (s.symm j),fun j=>hd _,?_⟩
 intro i j
 change M j i=_
 rw [hs]
 by_cases h : i=s.symm j
 · subst i; simp
 · have hh : j≠s i := by intro he; exact h (by rw [he,s.symm_apply_apply])
   simp [h,hh]
end MonomialMatrix
namespace MatrixSymmetry
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
theorem unit_transpose (M : Matrix α α ℂ) (hM : IsUnit M) : IsUnit M.transpose := by
 apply (Matrix.isUnit_iff_isUnit_det _).mpr
 simpa using (Matrix.isUnit_iff_isUnit_det M).mp hM

theorem inverse_tensor (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 (M⊗ₖN)⁻¹=M⁻¹⊗ₖN⁻¹ := by
 apply Matrix.inv_eq_right_inv
 rw [← Matrix.mul_kronecker_mul,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM),
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hN),Matrix.one_kronecker_one]

theorem inverse_sum (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 (Matrix.fromBlocks M 0 0 N)⁻¹=Matrix.fromBlocks M⁻¹ 0 0 N⁻¹ := by
 apply Matrix.inv_eq_right_inv
 simp only [Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM),
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hN),Matrix.fromBlocks_one]

theorem inverse_reindex (e : α≃β) (M : Matrix α α ℂ) (hM : IsUnit M) :
 (Matrix.reindex e e M)⁻¹=Matrix.reindex e e M⁻¹ := by
 apply Matrix.inv_eq_right_inv
 change (Matrix.reindexAlgEquiv ℂ ℂ e) M*(Matrix.reindexAlgEquiv ℂ ℂ e) M⁻¹=1
 rw [← map_mul,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM)]
 exact (Matrix.reindexAlgEquiv ℂ ℂ e).map_one
theorem transpose_tensor
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (N : Matrix β β ℂ) :
 (M⊗ₖN).transpose=M.transpose⊗ₖN.transpose := rfl

end MatrixSymmetry
end ExactFourier

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier.Packing.RawPrice
open MatrixSymmetry
variable (p : RawPrice) {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def symValue (M : Matrix α α ℂ) : ℝ :=
 (p.value M+p.value M⁻¹+p.value M.transpose+p.value M.transpose⁻¹)/4

theorem sym_nonneg (M : Matrix α α ℂ) (hM : IsUnit M) : 0≤p.symValue M := by
 have h1 := p.nonneg M hM
 have h2 := p.nonneg M⁻¹ (Matrix.isUnit_nonsing_inv_iff.mpr hM)
 have h3 := p.nonneg M.transpose (unit_transpose M hM)
 have h4 := p.nonneg M.transpose⁻¹ (Matrix.isUnit_nonsing_inv_iff.mpr (unit_transpose M hM))
 dsimp [symValue]
 positivity

theorem sym_zero (M : Matrix α α ℂ) (hM : IsUnit M) : p.symValue M=0 ↔ MonomialMatrix M := by
 constructor
 · intro hz
   have h1 := p.nonneg M hM
   have h2 := p.nonneg M⁻¹ (Matrix.isUnit_nonsing_inv_iff.mpr hM)
   have h3 := p.nonneg M.transpose (unit_transpose M hM)
   have h4 := p.nonneg M.transpose⁻¹ (Matrix.isUnit_nonsing_inv_iff.mpr (unit_transpose M hM))
   apply (p.zero_iff M hM).mp
   dsimp [symValue] at hz
   linarith
 · intro hm
   simp only [symValue,p.monomial_zero M hm,p.monomial_zero _ hm.inverse,
    p.monomial_zero _ hm.transpose,p.monomial_zero _ hm.transpose.inverse]
   norm_num

theorem sym_reindex (e : α≃β) (M : Matrix α α ℂ) (hM : IsUnit M) :
 p.symValue (Matrix.reindex e e M)=p.symValue M := by
 simp only [symValue,inverse_reindex e M hM,Matrix.transpose_reindex,
  inverse_reindex e M.transpose (unit_transpose M hM)]
 rw [p.reindex e M hM,p.reindex e M⁻¹ (Matrix.isUnit_nonsing_inv_iff.mpr hM),
  p.reindex e M.transpose (unit_transpose M hM),
  p.reindex e M.transpose⁻¹ (Matrix.isUnit_nonsing_inv_iff.mpr (unit_transpose M hM))]

theorem sym_mul (M N : Matrix α α ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.symValue (M*N)≤p.symValue M+p.symValue N := by
 have hiM := Matrix.isUnit_nonsing_inv_iff.mpr hM
 have hiN := Matrix.isUnit_nonsing_inv_iff.mpr hN
 have htM := unit_transpose M hM
 have htN := unit_transpose N hN
 have hitM := Matrix.isUnit_nonsing_inv_iff.mpr htM
 have hitN := Matrix.isUnit_nonsing_inv_iff.mpr htN
 have h1 := p.mul_le M N hM hN
 have h2 := p.mul_le N⁻¹ M⁻¹ hiN hiM
 have h3 := p.mul_le N.transpose M.transpose htN htM
 have h4 := p.mul_le M.transpose⁻¹ N.transpose⁻¹ hitM hitN
 simp only [symValue,Matrix.mul_inv_rev,Matrix.transpose_mul]
 linarith

theorem sym_monomial (M L R : Matrix α α ℂ) (hM : IsUnit M)
 (hL : MonomialMatrix L) (hR : MonomialMatrix R) : p.symValue (L*M*R)=p.symValue M := by
 have hm := (hL.unit _).mul hM |>.mul (hR.unit _)
 have one_side : ∀ (M L R : Matrix α α ℂ),IsUnit M→MonomialMatrix L→MonomialMatrix R→
  p.symValue (L*M*R)≤p.symValue M := by
  intro M L R hM hL hR
  have h1 := p.sym_mul L M (hL.unit _) hM
  have h2 := p.sym_mul (L*M) R ((hL.unit _).mul hM) (hR.unit _)
  rw [(p.sym_zero L (hL.unit _)).mpr hL] at h1
  rw [(p.sym_zero R (hR.unit _)).mpr hR] at h2
  linarith
 apply le_antisymm (one_side M L R hM hL hR)
 have hh := one_side (L*M*R) L⁻¹ R⁻¹ hm hL.inverse hR.inverse
 have he : L⁻¹*(L*M*R)*R⁻¹=M := by
  simp only [← mul_assoc,Matrix.nonsing_inv_mul L ((Matrix.isUnit_iff_isUnit_det L).mp (hL.unit _)),one_mul]
  rw [mul_assoc,Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).mp (hR.unit _)),mul_one]
 rw [he] at hh
 exact hh

theorem sym_tensor (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.symValue (M⊗ₖN)=(Fintype.card β : ℝ)*p.symValue M+(Fintype.card α : ℝ)*p.symValue N := by
 have hiM := Matrix.isUnit_nonsing_inv_iff.mpr hM
 have hiN := Matrix.isUnit_nonsing_inv_iff.mpr hN
 have htM := unit_transpose M hM
 have htN := unit_transpose N hN
 have hitM := Matrix.isUnit_nonsing_inv_iff.mpr htM
 have hitN := Matrix.isUnit_nonsing_inv_iff.mpr htN
 simp only [symValue,inverse_tensor M N hM hN,transpose_tensor,inverse_tensor _ _ htM htN]
 rw [p.tensor M N hM hN,p.tensor M⁻¹ N⁻¹ hiM hiN,p.tensor M.transpose N.transpose htM htN,
  p.tensor M.transpose⁻¹ N.transpose⁻¹ hitM hitN]
 ring

theorem sym_sum (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.symValue (Matrix.fromBlocks M 0 0 N)=p.symValue M+p.symValue N := by
 have hiM := Matrix.isUnit_nonsing_inv_iff.mpr hM
 have hiN := Matrix.isUnit_nonsing_inv_iff.mpr hN
 have htM := unit_transpose M hM
 have htN := unit_transpose N hN
 have hitM := Matrix.isUnit_nonsing_inv_iff.mpr htM
 have hitN := Matrix.isUnit_nonsing_inv_iff.mpr htN
 simp only [symValue,inverse_sum M N hM hN,Matrix.fromBlocks_transpose,Matrix.transpose_zero,
  inverse_sum _ _ htM htN]
 rw [p.directSum M N hM hN,p.directSum M⁻¹ N⁻¹ hiM hiN,p.directSum M.transpose N.transpose htM htN,
  p.directSum M.transpose⁻¹ N.transpose⁻¹ hitM hitN]
 ring

theorem sym_inverse (M : Matrix α α ℂ) (hM : IsUnit M) : p.symValue M⁻¹=p.symValue M := by
 have hdet := (Matrix.isUnit_iff_isUnit_det M).mp hM
 have htdet := (Matrix.isUnit_iff_isUnit_det M.transpose).mp (unit_transpose M hM)
 simp only [symValue,Matrix.nonsing_inv_nonsing_inv M hdet,Matrix.transpose_nonsing_inv,
  Matrix.nonsing_inv_nonsing_inv M.transpose htdet]
 ring

theorem sym_transpose (M : Matrix α α ℂ) : p.symValue M.transpose=p.symValue M := by
 simp only [symValue,Matrix.transpose_transpose]
 ring
end ExactFourier.Packing.RawPrice

end
end

section
noncomputable section
namespace ExactFourier.Packing.RawPrice
variable (p : RawPrice)

theorem shear_inverse : p.value shearU⁻¹=1 := by
 let d : Fin 2→ℂ := ![1,-1]
 let L := Matrix.diagonal d
 have hL : MonomialMatrix L := MonomialMatrix.diagonal d (by intro i; fin_cases i <;> norm_num [d])
 have he : shearU⁻¹=L*shearU*L := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
   norm_num [L,d,shearU,Matrix.mul_apply,Fin.sum_univ_two,Matrix.transvection,
    Matrix.diagonal,Matrix.single,Matrix.one_apply]
 rw [he,p.monomial _ L L shearU_unit hL hL,p.normalized]

theorem shear_transpose : p.value shearU.transpose=1 := by
 have he : Matrix.reindex (Fin.revPerm (n := 2)) (Fin.revPerm (n := 2)) shearU=shearU.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.reindex_apply,shearU,Matrix.transvection,Fin.revPerm,Fin.rev,Matrix.single]
 rw [← he,p.reindex _ _ shearU_unit,p.normalized]

theorem shear_transpose_inverse : p.value shearU.transpose⁻¹=1 := by
 have he : Matrix.reindex (Fin.revPerm (n := 2)) (Fin.revPerm (n := 2)) shearU=shearU.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.reindex_apply,shearU,Matrix.transvection,Fin.revPerm,Fin.rev,Matrix.single]
 rw [← he,MatrixSymmetry.inverse_reindex _ _ shearU_unit,
  p.reindex _ _ (Matrix.isUnit_nonsing_inv_iff.mpr shearU_unit),p.shear_inverse]

theorem sym_normalized : p.symValue shearU=1 := by
 rw [symValue,p.normalized,p.shear_inverse,p.shear_transpose,p.shear_transpose_inverse]
 norm_num

def toMatrixPrice : MatrixPrice where
 value := p.symValue
 nonneg := p.sym_nonneg
 zero_iff := p.sym_zero
 reindex := p.sym_reindex
 monomial := p.sym_monomial
 mul_le := p.sym_mul
 tensor := p.sym_tensor
 directSum := p.sym_sum
 inverse := p.sym_inverse
 transpose := fun M _=>p.sym_transpose M
 normalized := p.sym_normalized
end ExactFourier.Packing.RawPrice

end
end

section
namespace ExactFourier.BasisExchange
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def rows (K : Matrix ι ι ℂ) (H : Finset ι) : Matrix ι ι ℂ :=
  fun i j => if i∈H then K i j else (1 : Matrix ι ι ℂ) i j

end ExactFourier.BasisExchange

end

section
noncomputable section
namespace ExactFourier.SignedBits
open scoped Matrix Kronecker

abbrev Bits : ℕ → Type
  | 0 => PUnit
  | m+1 => Bits m ⊕ Bits m
@[reducible] instance bitsFintype : (m : ℕ) → Fintype (Bits m)
  | 0 => inferInstanceAs (Fintype PUnit)
  | m+1 => letI := bitsFintype m; inferInstanceAs (Fintype (Bits m ⊕ Bits m))
@[reducible] instance bitsDecidableEq : (m : ℕ) → DecidableEq (Bits m)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | m+1 => letI := bitsDecidableEq m; inferInstanceAs (DecidableEq (Bits m ⊕ Bits m))
@[reducible] instance bitsLinearOrder : (m : ℕ) → LinearOrder (Bits m)
  | 0 => inferInstanceAs (LinearOrder PUnit)
  | m+1 => @Sum.Lex.linearOrder (Bits m) (Bits m) (bitsLinearOrder m) (bitsLinearOrder m)

@[reducible] instance (priority := 2000) bitsLT (m : ℕ) : LT (Bits m) :=
  (bitsLinearOrder m).toLT

@[simp] theorem bits_card (m : ℕ) : Fintype.card (Bits m)=2^m := by
  induction m with
  | zero => simp [Bits]
  | succ m ih => simpa [Bits,pow_succ,mul_two] using congrArg (fun n => n+n) ih

def D : (m : ℕ) → Matrix (Bits m) (Bits m) ℂ
  | 0 => 0
  | m+1 => Matrix.fromBlocks (D m) 0 1 (-D m)
def T (m : ℕ) : Matrix (Bits m) (Bits m) ℂ := 1+D m

end ExactFourier.SignedBits

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.SignedPrice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.SignedBits
open scoped Matrix Kronecker

local instance instLinearOrderSumBits (m : ℕ) : LinearOrder (Bits m ⊕ Bits m) := bitsLinearOrder (m+1)
local instance instLTSumBits (m : ℕ) : LT (Bits m ⊕ Bits m) := (bitsLinearOrder (m+1)).toLT

def start (m : ℕ) : Matrix (Bits (m+1)) (Bits (m+1)) ℂ :=
  Matrix.fromBlocks (T m) 0 (T m) (T m)
def oldInputs (m : ℕ) : Matrix (Bits (m+1)) (Bits (m+1)) ℂ :=
  Matrix.fromBlocks (1 : Matrix (Bits m) (Bits m) ℂ) 0 (T m) (T m)
def oldOutputs (m : ℕ) : Matrix (Bits (m+1)) (Bits (m+1)) ℂ :=
  Matrix.fromBlocks (T m) 0 0 (1 : Matrix (Bits m) (Bits m) ℂ)
def transition (m : ℕ) : Matrix (Bits (m+1)) (Bits (m+1)) ℂ :=
  Matrix.fromBlocks (T m) 0 (-1) (T m)⁻¹

def bottom (m : ℕ) : Finset (Bits (m+1)) := Finset.univ.filter (fun i => i.isRight = true)

def zdiag (m : ℕ) : Matrix (Bits (m+1)) (Bits (m+1)) ℂ :=
  Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))

end ExactFourier.SignedBits

end
end

section
noncomputable section
namespace ExactFourier.SignedBits
open scoped Matrix Kronecker

def J : (m : ℕ) → Bool → Matrix (Bits m) (Bits m) ℂ
  | 0, _ => 1
  | m+1, false => Matrix.fromBlocks 0 (J m true) (J m true) 0
  | m+1, true => Matrix.fromBlocks 0 (J m false) (-J m false) 0

def Gamma (m : ℕ) : Matrix (Bits (m+1)) (Bits (m+1)) ℂ :=
  Matrix.fromBlocks (D m) 1 1 (-D m)

end ExactFourier.SignedBits

end
end

section
noncomputable section
namespace ExactFourier
open scoped Kronecker
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def support (A : Matrix α β ℂ) : Finset (α×β) := Finset.univ.filter (fun ij=>A ij.1 ij.2≠0)
def nnz (A : Matrix α β ℂ) : ℕ := (support A).card

@[simp] theorem mem_support
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (A : Matrix α β ℂ) (ij : α×β) : ij∈support A ↔ A ij.1 ij.2≠0 := by simp [support]
@[simp] theorem nnz_zero
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] : nnz (0 : Matrix α β ℂ)=0 := by simp [nnz,support]

@[simp] theorem nnz_neg
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (A : Matrix α β ℂ) : nnz (-A)=nnz A := by simp [nnz,support]

@[simp] theorem nnz_one : nnz (1 : Matrix α α ℂ)=Fintype.card α := by
  have he : support (1 : Matrix α α ℂ)=Finset.univ.image (fun i : α => (i,i)) := by
    ext ⟨i,j⟩; simp [support,Matrix.one_apply]
  rw [nnz,he,Finset.card_image_of_injective _ (by intro i j h; exact (Prod.mk.inj h).1)]
  exact Finset.card_univ

end ExactFourier

end
end

section
namespace ExactFourier.Similarity
variable {α : Type} [Fintype α] [DecidableEq α]

noncomputable def conj (U A : Matrix α α ℂ) : Matrix α α ℂ := U*A*U⁻¹

end ExactFourier.Similarity

end

section
noncomputable section
namespace ExactFourier.RealMatrix
variable {α : Type} [Fintype α] [DecidableEq α]

def complex (A : Matrix α α ℝ) : Matrix α α ℂ := A.map Complex.ofReal

@[simp] theorem map_one
    {α : Type} [Fintype α] [DecidableEq α] : complex (1 : Matrix α α ℝ)=1 := by ext i j; by_cases h : i=j <;> simp [complex,Matrix.one_apply,h]
@[simp] theorem map_zero
    {α : Type} [Fintype α] [DecidableEq α] : complex (0 : Matrix α α ℝ)=0 := rfl
@[simp] theorem map_transpose
    {α : Type} [Fintype α] [DecidableEq α] (A : Matrix α α ℝ) : complex A.transpose=(complex A).transpose := rfl
@[simp] theorem map_diagonal
    {α : Type} [Fintype α] [DecidableEq α] (d : α → ℝ) : complex (Matrix.diagonal d)=Matrix.diagonal (fun i => (d i : ℂ)) := by
  ext i j; by_cases h : i=j <;> simp [complex,Matrix.diagonal,h]
@[simp] theorem map_add
    {α : Type} [Fintype α] [DecidableEq α] (A B : Matrix α α ℝ) : complex (A+B)=complex A+complex B := by
  ext i j; simp [complex]
@[simp] theorem map_sub
    {α : Type} [Fintype α] [DecidableEq α] (A B : Matrix α α ℝ) : complex (A-B)=complex A-complex B := by
  ext i j; simp [complex]

end ExactFourier.RealMatrix

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.SymmetricLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.SymLap
open scoped Kronecker
variable {α : Type} [Fintype α] [DecidableEq α]

def lap (G : Matrix α α ℂ) : Matrix (α×α) (α×α) ℂ := G⊗ₖ1-(1 : Matrix α α ℂ)⊗ₖG
def tensor (G : Matrix α α ℂ) : Matrix (α×α) (α×α) ℂ := G⊗ₖG
def symmetrized (G J : Matrix α α ℂ) : Matrix (α×α) (α×α) ℂ := (J⊗ₖJ)*lap G

end ExactFourier.SymLap

end
end

section
noncomputable section
namespace ExactFourier.LinearProduct
open Polynomial
variable {α : Type} [Fintype α] [DecidableEq α]

def factor (A : Matrix α α ℂ) : Matrix α α (Polynomial ℂ) := 1+(X : Polynomial ℂ)•A.map Polynomial.C

def product : List (Matrix α α ℂ) → Matrix α α (Polynomial ℂ)
  | [] => 1
  | a::L => factor a*product L

@[simp] theorem coeff_one_factor
    {α : Type} [Fintype α] [DecidableEq α] (A : Matrix α α ℂ) :
    (factor A).map (fun f => f.coeff 1)=A := by
  ext i j
  by_cases h : i=j
  · subst j; simp [factor,Polynomial.coeff_one]
  · simp [factor,h]

def quotient (L : List (Matrix α α ℂ)) : Matrix α α (Polynomial ℂ) := (product L).map Polynomial.divX

end ExactFourier.LinearProduct

end
end

section
noncomputable section
namespace ExactFourier.SparseReflection
open Polynomial
variable {α : Type} [Fintype α] [DecidableEq α]

structure PairTerm (α : Type) where
  i : α
  j : α
  hij : i≠j
  a : ℂ
  b : ℂ
  ha : a≠0
  hb : b≠0

def PairTerm.direction (u : PairTerm α) : Matrix α α ℂ :=
  Matrix.single u.i u.j u.a+Matrix.single u.j u.i u.b

def PairTerm.den (u : PairTerm α) : Polynomial ℂ := 1-X^2*Polynomial.C (u.a*u.b)

def PairTerm.bad (u : PairTerm α) : Finset ℂ := insert 0 u.den.roots.toFinset

end ExactFourier.SparseReflection

end
end

section
noncomputable section
namespace ExactFourier.MatrixPrice
open scoped Matrix
variable {α : Type} [Fintype α] [DecidableEq α]

def cayley (A : Matrix α α ℂ) (t : ℂ) : Matrix α α ℂ :=
  (1+t•A)*(1-t•A)⁻¹

end ExactFourier.MatrixPrice

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.DiagonalBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier
open scoped BigOperators
variable {α : Type} [Fintype α] [DecidableEq α]

noncomputable def diagonalBlocks {t : ℕ} (A : Fin t → Matrix α α ℂ) :
    Matrix (Fin t × α) (Fin t × α) ℂ :=
  fun i j => if i.1=j.1 then A i.1 i.2 j.2 else 0

end ExactFourier

end

section
namespace ExactFourier.RootEvaluation
open Polynomial
open scoped BigOperators Kronecker
noncomputable def fourier (t : ℕ) (ω : ℂ) : Matrix (Fin t) (Fin t) ℂ :=
  fun i j => ω^(i.val*j.val)

@[simp] theorem fourier_mulVec (t : ℕ) (ω : ℂ) (x : Fin t → ℂ) :
    (fourier t ω).mulVec x=RadixTwo.eval t ω x := rfl

noncomputable def matrix (t : ℕ) (ω a : ℂ) : Matrix (Fin t) (Fin t) ℂ :=
  fun i j => (a*ω^i.val)^j.val

end ExactFourier.RootEvaluation

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.RationalClearing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.CayleyLimit
open Polynomial
variable {α : Type} [Fintype α] [DecidableEq α]

def active (a : α → ℂ) : Finset α := Finset.univ.filter (fun i=>a i≠0)
def denominator (a : α → ℂ) : Polynomial ℂ := ∏ i∈active a,(X-Polynomial.C (a i))
def except (a : α → ℂ) (i : α) : Polynomial ℂ := ∏ j∈(active a).erase i,(X-Polynomial.C (a j))
def numerator (a : α → ℂ) (i : α) : Polynomial ℂ :=
  if a i=0 then denominator a else (X+Polynomial.C (a i))*except a i
def sign (a : α → ℂ) (i : α) : ℂ := if a i=0 then 1 else -1


def polynomial (U : Matrix α α ℂ) (a : α → ℂ) : Matrix α α (Polynomial ℂ) :=
  U.map Polynomial.C*Matrix.diagonal (numerator a)*(U⁻¹).map Polynomial.C

def bad (a : α → ℂ) : Finset ℂ := insert 0 (Finset.univ.image a∪Finset.univ.image (fun i=>-a i))

end ExactFourier.CayleyLimit

end
end

section
noncomputable section
namespace ExactFourier.CayleyLimit
variable {α : Type} [Fintype α] [DecidableEq α]

def reciprocal (a : α → ℂ) (i : α) : ℂ := if a i=0 then 0 else 2/(a i)

end ExactFourier.CayleyLimit

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.SparseSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.SparseReflection
variable {α : Type} [Fintype α] [LinearOrder α]

def pairs (A : Matrix α α ℂ) : Finset (α×α) := Finset.univ.filter (fun ij=>ij.1 < ij.2 ∧ A ij.1 ij.2≠0)

@[simp] theorem mem_pairs (A : Matrix α α ℂ) (ij : α×α) : ij∈pairs A ↔ ij.1 < ij.2 ∧ A ij.1 ij.2≠0 := by simp [pairs]

def term (A : Matrix α α ℂ) (hA : A.IsSymm) (ij : {ij // ij∈pairs A}) : PairTerm α :=
  ⟨ij.1.1,ij.1.2,ne_of_lt ((mem_pairs A ij).mp ij.2).1,A ij.1.1 ij.1.2,A ij.1.2 ij.1.1,
   ((mem_pairs A ij).mp ij.2).2,by
     have hh : A ij.1.2 ij.1.1=A ij.1.1 ij.1.2 := congrFun (congrFun hA ij.1.1) ij.1.2
     rw [hh]; exact ((mem_pairs A ij).mp ij.2).2⟩

def terms (A : Matrix α α ℂ) (hA : A.IsSymm) : List (PairTerm α) :=
  (pairs A).attach.toList.map (term A hA)

@[simp] theorem terms_length (A : Matrix α α ℂ) (hA : A.IsSymm) : (terms A hA).length=(pairs A).card := by simp [terms]

end ExactFourier.SparseReflection

end
end

section
noncomputable section
namespace ExactFourier.SignedBits

def parity : (m : ℕ) → Bits m → Bool
  | 0, _ => false
  | m+1, .inl i => parity m i
  | m+1, .inr i => !(parity m i)

def paritySwitch (m : ℕ) : Bits (m+1) → Bits (m+1)
  | .inl i => if parity m i then .inr i else .inl i
  | .inr i => if parity m i then .inl i else .inr i

theorem paritySwitch_involutive (m : ℕ) : Function.Involutive (paritySwitch m) := by
  intro i; rcases i with i|i <;> cases he : parity m i <;> simp [paritySwitch,he]

def parityEquiv (m : ℕ) : (Bits m⊕Bits m) ≃ Bits (m+1) :=
  (paritySwitch_involutive m).toPerm

end ExactFourier.SignedBits

end
end

section
noncomputable section
namespace ExactFourier.GraphReflection
open scoped ComplexOrder
variable {α : Type} [Fintype α] [DecidableEq α]

def swap : Matrix (α⊕α) (α⊕α) ℂ := Matrix.fromBlocks 0 1 1 0

def hadamard : Matrix (α⊕α) (α⊕α) ℂ := Matrix.fromBlocks 1 1 1 (-1)

noncomputable def graph (B : Matrix α α ℂ) : Matrix (α⊕α) (α⊕α) ℂ := Matrix.fromBlocks 0 B B⁻¹ 0

end ExactFourier.GraphReflection

end
end

section
noncomputable section
namespace ExactFourier.SignedBits
open scoped Kronecker

abbrev Half (m : ℕ) := Bits m × Bits (m+1)
def tensorParityEquiv (m : ℕ) : (Half m⊕Half m) ≃ Bits (m+1)×Bits (m+1) :=
  (Equiv.sumProdDistrib (Bits m) (Bits m) (Bits (m+1))).symm.trans
    (Equiv.prodCongr (parityEquiv m) (Equiv.refl _))

def parityTensor (m : ℕ) : Matrix (Half m⊕Half m) (Half m⊕Half m) ℂ :=
  (SymLap.tensor (Gamma m)).submatrix (tensorParityEquiv m) (tensorParityEquiv m)

def graphB (m : ℕ) : Matrix (Half m) (Half m) ℂ := (parityTensor m).toBlocks₁₂

end ExactFourier.SignedBits

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.GraphBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.SignedBits
open scoped Matrix Kronecker

def weight : (m : ℕ) → Bits m → ℕ
  | 0, _ => 0
  | m+1, .inl i => weight m i
  | m+1, .inr i => weight m i+1

def V : Matrix (Fin 2) (Fin 2) ℂ := !![0,-1;1,0]
def Vi : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;-1,0]
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]

def gauge (m : ℕ) : Matrix (Fin 2×Bits m) (Fin 2×Bits m) ℂ :=
  Matrix.blockDiagonal (fun i => Vi^(weight m i))
def Q (m : ℕ) : Matrix (Fin 2×Bits m) (Fin 2×Bits m) ℂ := 1+V⊗ₖD m

end ExactFourier.SignedBits

end
end

section
noncomputable section
namespace ExactFourier
/-- Exact-width mixed rounds. Monomial rounds are counted, not silently free
scalar multiplications. Disjoint parallel blocks share a round. -/
inductive Layered : {α : Type} → [Fintype α] → [DecidableEq α] → Matrix α α ℂ → ℕ → Prop
 | identity {α : Type} [Fintype α] [DecidableEq α] : Layered (1 : Matrix α α ℂ) 0
 | mono {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ)
   (hM : MonomialMatrix M) : Layered M 1
 | pair (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : IsUnit M) : Layered M 1
 | mul {α : Type} [Fintype α] [DecidableEq α] {M N : Matrix α α ℂ} {d e : ℕ}
   (hM : Layered M d) (hN : Layered N e) : Layered (M*N) (d+e)
 | reindex {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
   (f : α≃β) {M : Matrix α α ℂ} {d : ℕ} (hM : Layered M d) :
   Layered (Matrix.reindex f f M) d
 | sum {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
   {M : Matrix α α ℂ} {N : Matrix β β ℂ} {d : ℕ}
   (hM : Layered M d) (hN : Layered N d) : Layered (Matrix.fromBlocks M 0 0 N) d
 | weaken {α : Type} [Fintype α] [DecidableEq α] {M : Matrix α α ℂ} {d e : ℕ}
   (h : Layered M d) (hde : d≤e) : Layered M e

end ExactFourier

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.CircuitCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Kronecker
namespace ExactFourier
namespace CircuitCost
variable {α β : Type} [Fintype α] [Fintype β]

abbrev Realizes (C : TypedDAG α β) (M : Matrix β α ℂ) : Prop := ∀ x,C.eval x=M.mulVec x

theorem exists_size (M : Matrix β α ℂ) : ∃ n : ℕ,∃ C : TypedDAG α β,C.size=n ∧ Realizes C M :=
 ⟨_,TypedDAG.matrix M,rfl,TypedDAG.eval_matrix M⟩

def cost (M : Matrix β α ℂ) : ℕ := by
 classical
 exact Nat.find (exists_size M)

end CircuitCost
end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier
/-- Separating the first output block, without inserting extra coordinates. -/
def sigmaFinSucc {n : ℕ} (D : Fin (n+1)→Type) : (Σ i,D i)≃(D 0⊕Σ i : Fin n,D i.succ) where
 toFun x := Fin.cases (fun z=>Sum.inl z) (fun i z=>Sum.inr ⟨i,z⟩) x.1 x.2
 invFun x := match x with
  | .inl z => ⟨0,z⟩
  | .inr ⟨i,z⟩ => ⟨i.succ,z⟩
 left_inv := by rintro ⟨i,z⟩; refine Fin.cases ?_ (fun i=>?_) i z <;> intro z <;> rfl
 right_inv := by rintro (z|⟨i,z⟩) <;> rfl

end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier.Layered
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem transpose {M : Matrix α α ℂ} {d : ℕ} (h : Layered M d) : Layered M.transpose d := by
 induction h with
 | identity => simpa using (Layered.identity (α := _))
 | mono M hM => exact Layered.mono _ hM.transpose
 | pair M hM => exact Layered.pair _ ((Matrix.isUnit_transpose M).mpr hM)
 | mul hM hN ihM ihN => simpa only [Matrix.transpose_mul,Nat.add_comm] using ihN.mul ihM
 | reindex f hM ih => exact ih.reindex f
 | sum hM hN ihM ihN =>
  rw [Matrix.fromBlocks_transpose]
  simpa using ihM.sum ihN
 | weaken h hde ih => exact ih.weaken hde

end ExactFourier.Layered

end
end

section
noncomputable section
namespace ExactFourier
inductive Round : {α : Type}→ [Fintype α]→ [DecidableEq α]→Matrix α α ℂ→Prop
 | mono {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ) (h : MonomialMatrix M) : Round M
 | pair (M : Matrix (Fin 2) (Fin 2) ℂ) (h : IsUnit M) : Round M
 | reindex {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
   (e : α≃β) {M : Matrix α α ℂ} (h : Round M) : Round (Matrix.reindex e e M)
 | sum {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
   {M : Matrix α α ℂ} {N : Matrix β β ℂ} (hM : Round M) (hN : Round N) :
   Round (Matrix.fromBlocks M 0 0 N)

namespace Round
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def joint (M : List (Matrix α α ℂ)) (N : List (Matrix β β ℂ)) : List (Matrix (α⊕β) (α⊕β) ℂ) :=
 List.zipWith (fun X Y=>Matrix.fromBlocks X 0 0 Y) M N

end Round

end ExactFourier

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.TensorCostAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Kronecker
namespace ExactFourier

namespace TensorAxis
variable {α : Type} [Fintype α] [DecidableEq α]
def funCoordinates : (k : ℕ)→Space α k≃(Fin k→α)
 | 0 => {toFun:=fun _ i=>Fin.elim0 i,invFun:=fun _=>PUnit.unit,
         left_inv:=by intro x; cases x; rfl,right_inv:=by intro x; funext i; exact Fin.elim0 i}
 | k+1 => {toFun:=fun z=>Fin.snoc (funCoordinates k z.1) z.2,
           invFun:=fun f=>((funCoordinates k).symm (Fin.init f),f (Fin.last k)),
           left_inv:=by rintro ⟨x,y⟩; simp,
           right_inv:=by intro f; simp}

/-- Grouping changes coordinate indexing only, not the scalar operation. -/
def appendCoordinates (k : ℕ) : (l : ℕ)→Space α (k+l)≃(Space α k×Space α l)
 | 0 => (Equiv.prodPUnit _).symm
 | l+1 => ((appendCoordinates k l).prodCongr (Equiv.refl α)).trans (Equiv.prodAssoc _ _ _)

end TensorAxis
end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier.Amplification
/-- Finite dimension-weighted sector average; no random choices enter a circuit. -/
def avg (p : ℝ) (f : ℕ→ℝ) : ℕ→ℕ→ℝ
 | 0,r => f r
 | j+1,r => p*avg p f j (r+1)+(1-p)*avg p f j r

end ExactFourier.Amplification

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier.Amplification
open CircuitCost TensorAxis

def sectorCost (l : ℕ→ℕ) (s : ℕ) : ℕ→ℕ→ℕ
 | 0,r => l r
 | j+1,r => sectorCost l s j (r+1)+s*sectorCost l s j r

end ExactFourier.Amplification

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier.Amplification
open CircuitCost TensorAxis

def normalizedCost {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (k : ℕ) : ℝ :=
 (cost (power A k) : ℝ)/(q : ℝ)^k

end ExactFourier.Amplification

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.AmplificationMaster
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier
variable {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ)
/-- A disjoint union of forward calls and untouched coordinates. -/
inductive AParallel : {α : Type}→ [Fintype α]→ [DecidableEq α]→Matrix α α ℂ→Prop
 | identity {α : Type} [Fintype α] [DecidableEq α] : AParallel (1 : Matrix α α ℂ)
 | atom : AParallel A
 | reindex {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
   (e : α≃β) {M : Matrix α α ℂ} (h : AParallel M) : AParallel (Matrix.reindex e e M)
 | sum {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
   {M : Matrix α α ℂ} {N : Matrix β β ℂ} (hM : AParallel M) (hN : AParallel N) :
   AParallel (Matrix.fromBlocks M 0 0 N)

variable {A} {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

structure AFrame (A : Matrix (Fin q) (Fin q) ℂ) (M : Matrix α α ℂ) : Prop where
 exists_factors : ∃ B Q : Matrix α α ℂ,AParallel A B ∧ MonomialMatrix Q ∧ M=B*Q

namespace AFrame
theorem reindex {M : Matrix α α ℂ} (h : AFrame A M) (e : α≃β) :
 AFrame A (Matrix.reindex e e M) := by
 obtain ⟨B,Q,hB,hQ,rfl⟩ := h.exists_factors
 exact ⟨_,_,hB.reindex e,hQ.reindex e,(Matrix.reindexAlgEquiv ℂ ℂ e).map_mul B Q⟩
end AFrame

def AGenerated (A : Matrix (Fin q) (Fin q) ℂ) (M : Matrix α α ℂ) (d : ℕ) : Prop :=
 ∃ L : List (Matrix α α ℂ),L.length=d ∧ L.prod=M ∧ ∀ X∈L,AFrame A X

end ExactFourier

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier
namespace ParallelTensorCost
open CircuitCost TensorAxis
variable {q : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} {a C : ℝ}
 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def Good (M : Matrix α α ℂ) (m : ℕ) : Prop := ∀ k,
 (cost (M⊗ₖpower A k) : ℝ)≤C*Fintype.card α*(q : ℝ)^k*(m+k+1 : ℝ)^a

end ParallelTensorCost
end ExactFourier

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier
namespace PiTensor

def splitFirst {n : ℕ} (D : Fin (n+1)→Type) : (∀ i,D i) ≃ (D 0×∀ i : Fin n,D i.succ) where
 toFun f := (f 0,fun i=>f i.succ)
 invFun p := Fin.cases p.1 p.2
 left_inv := by intro f; funext i; refine Fin.cases rfl (fun i=>rfl) i
 right_inv := by intro p; rfl

end PiTensor

end ExactFourier

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.PairFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier
namespace PairFamily
variable {σ τ α β : Type} [Fintype σ] [Fintype τ] [Fintype α] [Fintype β]
 [DecidableEq σ] [DecidableEq τ] [DecidableEq α] [DecidableEq β]

def sumEquiv : (Σ _ : σ⊕τ,Fin 2) ≃ ((Σ _ : σ,Fin 2)⊕(Σ _ : τ,Fin 2)) where
 toFun := fun ⟨i,x⟩ => match i with | .inl s => .inl ⟨s,x⟩ | .inr t => .inr ⟨t,x⟩
 invFun := Sum.elim (fun ⟨s,x⟩=>⟨.inl s,x⟩) (fun ⟨t,x⟩=>⟨.inr t,x⟩)
 left_inv := by rintro ⟨i,x⟩; cases i <;> rfl
 right_inv := by intro i; cases i <;> rfl

def subEmbedding (S : Set σ) : (Σ _ : S,Fin 2) ↪ (Σ _ : σ,Fin 2) where
 toFun i := ⟨i.1.1,i.2⟩
 inj' := by rintro ⟨⟨i,hi⟩,x⟩ ⟨⟨j,hj⟩,y⟩ h; cases h; rfl

end PairFamily

/-- A simultaneous pair family retains its actual disjoint ordered coordinate tuples. -/
structure PairFamily (α : Type) [Fintype α] [DecidableEq α] where
 index : Type
 finite : Fintype index
 dec : DecidableEq index
 pairs : index→Matrix (Fin 2) (Fin 2) ℂ
 unit : ∀ i,IsUnit (pairs i)
 position : (Σ _ : index,Fin 2) ↪ α
attribute [instance] PairFamily.finite PairFamily.dec
namespace PairFamily
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
def matrix (P : PairFamily α) := Embedded.matrix P.position (Matrix.blockDiagonal' P.pairs)
def empty : PairFamily α where
 index := Fin 0
 finite := inferInstance
 dec := inferInstance
 pairs i := Fin.elim0 i
 unit i := Fin.elim0 i
 position := ⟨fun i=>Fin.elim0 i.1,by intro i; exact Fin.elim0 i.1⟩

def pair (H : Matrix (Fin 2) (Fin 2) ℂ) (hu : IsUnit H) : PairFamily (Fin 2) where
 index := Fin 1
 finite := inferInstance
 dec := inferInstance
 pairs _ := H
 unit _ := hu
 position := ⟨fun i=>i.2,by rintro ⟨i,x⟩ ⟨j,y⟩ h; dsimp at h; subst y; have : i=j := Subsingleton.elim _ _; subst j; rfl⟩

def reindex (P : PairFamily α) (e : α≃β) : PairFamily β :=
 { P with position := P.position.trans e.toEmbedding }

def sum (P : PairFamily α) (Q : PairFamily β) : PairFamily (α⊕β) where
 index := P.index⊕Q.index
 finite := inferInstance
 dec := inferInstance
 pairs := Sum.elim P.pairs Q.pairs
 unit := by intro i; cases i with | inl i=>exact P.unit i | inr i=>exact Q.unit i
 position := sumEquiv.toEmbedding.trans (P.position.sumMap Q.position)
end PairFamily

end ExactFourier

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.MatrixRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.RadixTwo

def dft (n : ℕ) (ω : ℂ) : Matrix (Fin n) (Fin n) ℂ := fun i j=>ω^(i.val*j.val)

 def butterfly (n : ℕ) (ω : ℂ) : Matrix (Fin n⊕Fin n) (Fin n⊕Fin n) ℂ :=
 Matrix.fromBlocks 1 (Matrix.diagonal (fun i=>ω^i.val)) 1 (-Matrix.diagonal (fun i=>ω^i.val))

def paritySumEquiv (n : ℕ) : (Fin n⊕Fin n)≃Fin (n+n) :=
 ((twoProdEquiv (Fin n)).symm.trans (Equiv.prodComm _ _)).trans (parityEquiv n)

@[simp] theorem paritySumEquiv_inl (n : ℕ) (i : Fin n) : paritySumEquiv n (.inl i)=evenIndex n i := by
 apply Fin.ext; simp [paritySumEquiv,twoProdEquiv,parityEquiv,evenIndex]
@[simp] theorem paritySumEquiv_inr (n : ℕ) (i : Fin n) : paritySumEquiv n (.inr i)=oddIndex n i := by
 apply Fin.ext; simp [paritySumEquiv,twoProdEquiv,parityEquiv,oddIndex]

end ExactFourier.RadixTwo

end
end

section
noncomputable section
namespace ExactFourier.NewtonFourier
open scoped BigOperators
open Polynomial

def newton (ω : ℂ) (k : ℕ) : ℂ[X] := ∏ j∈Finset.range k,(X-C (ω^j))
def H (ω : ℂ) (i : ℕ) : ℂ := ∏ j∈Finset.range i,(1-ω^(j+1))
def scale (ω : ℂ) (k : ℕ) : ℂ := ∏ j∈Finset.range k,(-ω^j)
def N (n : ℕ) (ω : ℂ) : Matrix (Fin n) (Fin n) ℂ := fun i k=>(newton ω k.val).eval (ω^i.val)
def P (n : ℕ) (ω : ℂ) : Matrix (Fin n) (Fin n) ℂ := fun i k=>(newton ω k.val).coeff i.val

@[simp] theorem newton_zero (ω : ℂ) : newton ω 0=1 := by simp [newton]
@[simp] theorem H_zero (ω : ℂ) : H ω 0=1 := by simp [H]
@[simp] theorem scale_zero (ω : ℂ) : scale ω 0=1 := by simp [scale]
end ExactFourier.NewtonFourier

end
end

section
noncomputable section
namespace ExactFourier.Layered
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def swapLast : ((α⊕γ)⊕β)≃(α⊕(β⊕γ)) :=
 (Equiv.sumAssoc α γ β).trans (Equiv.sumCongr (Equiv.refl α) (Equiv.sumComm γ β))

end ExactFourier.Layered

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.RectStableAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Layered
variable {α β γ σ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype σ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq σ]

def splitRowsLeft : ((α⊕γ)⊕(β⊕σ))≃(((α⊕β)⊕γ)⊕σ) where
 toFun := fun x=>match x with
  | .inl (.inl a)=>.inl (.inl (.inl a))
  | .inl (.inr c)=>.inl (.inr c)
  | .inr (.inl b)=>.inl (.inl (.inr b))
  | .inr (.inr s)=>.inr s
 invFun := fun x=>match x with
  | .inl (.inl (.inl a))=>.inl (.inl a)
  | .inl (.inl (.inr b))=>.inr (.inl b)
  | .inl (.inr c)=>.inl (.inr c)
  | .inr s=>.inr (.inr s)
 left_inv := by rintro ((a|c)|(b|s)) <;> rfl
 right_inv := by rintro (((a|b)|c)|s) <;> rfl

def splitRowsRight : ((β⊕γ)⊕(α⊕σ))≃(((α⊕β)⊕γ)⊕σ) :=
 (splitRowsLeft (α := β) (β := α) (γ := γ) (σ := σ)).trans
 (((Equiv.sumComm β α).sumCongr (Equiv.refl γ)).sumCongr (Equiv.refl σ))

end ExactFourier.Layered

end
end

section
noncomputable section
namespace ExactFourier
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def SumLayered (M : Matrix α α ℂ) (d c : ℕ) : Prop :=
 ∃ L : List (Matrix α α ℂ), L.length≤c ∧ L.sum=M ∧ ∀ N∈L,Layered N d

end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier.RadixTwo
open Polynomial
open scoped BigOperators

def convolutionMatrix (k : ℕ) (f : ℂ[X]) : Matrix (Fin (2^k)) (Fin (2^k)) ℂ :=
 let ω := zeta (2^k)
 dft (2^k) ω⁻¹ * Matrix.diagonal (fun i=>((2^k : ℕ) : ℂ)⁻¹*f.eval (ω^i.val)) * dft (2^k) ω

end ExactFourier.RadixTwo

end
end

section
noncomputable section
namespace ExactFourier
open scoped BigOperators

def initialEmbedding {a n : ℕ} (h : a≤n) : Fin a↪Fin n :=
 ⟨fun i=>⟨i.val,lt_of_lt_of_le i.isLt h⟩,by intro i j he; exact Fin.ext (congrArg (fun x : Fin n=>x.val) he)⟩

@[simp] theorem initialEmbedding_val {a n : ℕ} (h : a≤n) (i : Fin a) :
 (initialEmbedding h i).val=i.val := rfl

end ExactFourier

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.DisplacementKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Displacement
open scoped BigOperators

def kernel (v w : ℕ→ℂ) (i j : ℕ) : ℂ :=
 ∑ l∈Finset.range (min i j+1),v (i-l)*w (j-l)

@[simp] theorem kernel_zero_left (v w : ℕ→ℂ) (j : ℕ) : kernel v w 0 j=v 0*w j := by
 simp [kernel]
@[simp] theorem kernel_zero_right (v w : ℕ→ℂ) (i : ℕ) : kernel v w i 0=v i*w 0 := by
 simp [kernel]

def lower (v : ℕ→ℂ) (a e : ℕ) : Matrix (Fin a) (Fin e) ℂ :=
 fun i j=>if j.val ≤ i.val then v (i.val-j.val) else 0

def delta : ℕ→ℂ := fun i=>if i=0 then 1 else 0

end ExactFourier.Displacement

end
end

section
noncomputable section
namespace ExactFourier.Displacement
open Polynomial RadixTwo

def extendVector {a : ℕ} (v : Fin a→ℂ) : ℕ→ℂ :=
 fun i=>if hi : i < a then v ⟨i,hi⟩ else 0

def fullKernel (k a e : ℕ) (v : Fin a→ℂ) (w : Fin e→ℂ) : Matrix (Fin (2^k)) (Fin (2^k)) ℂ :=
 convolutionMatrix k (Polynomial.ofFn a v) *
 Matrix.diagonal (fun i : Fin (2^k)=>if i.val < e then 1 else 0) *
 (convolutionMatrix k (Polynomial.ofFn e w)).transpose

end ExactFourier.Displacement

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.ToeplitzCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.ToeplitzLayers
open scoped BigOperators
open CoefficientTime

def cross (s : ℕ) (h g : ℕ→ℂ) (i j : ℕ) : ℂ :=
 ∑ l∈Finset.range (s-j),h (i-j-l)*g l

def lowerCross (s a : ℕ) (h : ℕ→ℂ) : Matrix (Fin a) (Fin s) ℂ :=
 fun i j=>h (s+i.val-j.val)

end ExactFourier.ToeplitzLayers

end
end

section
noncomputable section
namespace ExactFourier.NewtonFourier
open Layered CoefficientTime

def invH (ω : ℂ) : PowerSeries ℂ := PowerSeries.mk (fun i=>(H ω i)⁻¹)

@[simp] theorem invH_constant (ω : ℂ) : PowerSeries.constantCoeff (invH ω)=1 := by
 simp [invH,PowerSeries.constantCoeff_mk]

end ExactFourier.NewtonFourier

end
end

section
noncomputable section
namespace ExactFourier
namespace FourierCRT
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def finZMod (n : ℕ) [NeZero n] : Fin n ≃ ZMod n where
 toFun i := (i.val : ZMod n)
 invFun x := ⟨x.val,ZMod.val_lt x⟩
 left_inv i := Fin.ext (by simp [ZMod.val_natCast,Nat.mod_eq_of_lt i.isLt])
 right_inv := ZMod.natCast_zmod_val

def singleAdd (r : ι→ℕ) (i : ι) : ZMod (r i) →+ (∀ j,ZMod (r j)) where
 toFun x := Function.update 0 i x
 map_zero' := by simp
 map_add' := by
  intro x y; funext j
  rcases eq_or_ne j i with rfl|h
  · simp
  · simp [h,Function.update_of_ne]

def component (r : ι→ℕ) (hn : Pairwise (fun i j=>Nat.Coprime (r i) (r j)))
 [NeZero (∏ i,r i)] (i : ι) : AddChar (ZMod (r i)) ℂ :=
 ZMod.stdAddChar.compAddMonoidHom ((ZMod.prodEquivPi r hn).symm.toAddMonoidHom.comp (singleAdd r i))

end FourierCRT
end ExactFourier

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.PrimeInventory
open Nat Real

def upper (q m : ℕ) : ℕ := (m+2*q+10)^4

end ExactFourier.PrimeInventory

end
end

section
noncomputable section
namespace ExactFourier.FourierTransfer
open CircuitCost

def depth (q m : ℕ) : ℕ := 8388608*(Nat.log 2 (PrimeInventory.upper q m)+2)^2+5

end ExactFourier.FourierTransfer

end
end

end OAI
end


