-- Prove2me | Definitions.Def_OAIQWWLI001
-- name    : OAIQWWLI001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T21:17:05.895868+00:00
-- url     : https://prove2.me/theorems/5e8e9acd-aa4a-454d-926c-19fb8cd7377a
-- title:
--   OpenAI Weisfeiler–Leman identification split: definitions bundle OAIQWWLI001
-- statement:
--   A definitions bundle of the split of OpenAI's proof that deciding whether Weisfeiler–Leman refinement of a given dimension identifies a graph is EXPTIME-complete (`OAI.WLIdentification.main`, the paper's Theorem 1.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Computability/WLIdentification` (OpenAI, *The complexity of identifying a graph by Weisfeiler–Leman refinement*, OpenAI Math Release, September 25, 2026, result family 133, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies.
--
--   This bundle holds the padding and dimension bookkeeping of the reduction (`paddedEquiv`, `paddedExponent`, `addressWidth`, `reductionDimension`) and the command language and numeric kernel tables of OpenAI's word machines (`Command`, `Control`, `kernel`, `table`, `registers`).
--
--   The definitions of the published statement (`Graph`, `WLdim`, `dimensionLanguage`, `InEXPTIME`, `PolytimeManyOne`, `EXPTIMEComplete` and the rest) are not repeated: the bundle imports them from the published bundle `Def_WLIdentification`. It imports no other bundle of this split.
--
--   Modules: `CircuitReduction`, `ExpressionCompiler`, `FiniteRefinement`, `MachineCells`, `MachineReduction`, `NumericKernel`, `Refinement`, `RefinementCorrectness`, `StackCommands`, `WordCommands`.
--
--   The theorems of the development that the definitions do not need are proved in the single solution of this split, which imports the bundle `OAIQWWLI002` (and through it the other two) and proves `OAI.WLIdentification.main`. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The complexity of identifying a graph by Weisfeiler–Leman refinement, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 133; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complexity-of-identifying-a-graph-by-Weisfeiler-Leman-refinement-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability/WLIdentification at commit adc7f12

import Mathlib
import Definitions.Def_WLIdentification

section
-- module Solutions.OAIQW_WLIdentification.Refinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

def diagonalEquiv {k : ℕ} (i : Fin k) (α : Type) :
    α ≃ {v : Fin k → α // ∀ j, v j = v i} where
  toFun x := ⟨fun _ => x, fun _ => rfl⟩
  invFun v := v.val i
  left_inv _ := rfl
  right_inv v := by
    apply Subtype.ext
    funext j
    exact (v.property j).symm

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.CircuitReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

/-- Restricting a joint color retains an entire replacement vector at once. -/
def restrictTupleColor {j k : ℕ} (q : Fin j → Fin k) :
    (s : ℕ) → TupleColor k s → TupleColor j s
  | 0, c => (fun i l => c.1 (q i) (q l), fun i l => c.2 (q i) (q l))
  | s + 1, c => (restrictTupleColor q s c.1,
      c.2.map (fun v i => restrictTupleColor q s (v (q i))))

def padIndex {j k : ℕ} (hj : 0 < j) (_hjk : j ≤ k) (i : Fin k) : Fin j :=
  if hi : i.val < j then ⟨i.val, hi⟩ else ⟨0, hj⟩

@[simp] theorem padIndex_castLE {j k : ℕ} (hj : 0 < j) (hjk : j ≤ k) (i : Fin j) :
    padIndex hj hjk (Fin.castLE hjk i) = i := by
  simp [padIndex, i.isLt]

def paddedEquiv {j k : ℕ} (hj : 0 < j) (hjk : j ≤ k) (α : Type) :
    (Fin j → α) ≃ {v : Fin k → α // ∀ i, v i = v (Fin.castLE hjk (padIndex hj hjk i))} where
  toFun v := ⟨v ∘ padIndex hj hjk, fun i => by simp⟩
  invFun v := v.val ∘ Fin.castLE hjk
  left_inv v := by funext i; simp
  right_inv v := by
    apply Subtype.ext
    funext i
    exact (v.property i).symm

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.MachineCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace Machine

/-- The literal bounded input segment, with one head marker. -/
abbrev inputSpan (w : Word) := max 1 w.length

end Machine

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.MachineReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace Machine

def paddedExponent (C e m : ℕ) : ℕ := C * (m + 1) ^ e + m + 32

def addressWidth (C e m : ℕ) : ℕ := paddedExponent C e m + 2

def reductionDimension (C e m : ℕ) : ℕ := addressWidth C e m + addressWidth C e m

theorem reductionDimension_ge (C e m : ℕ) : 68 ≤ reductionDimension C e m := by
  simp only [reductionDimension, addressWidth, paddedExponent]
  omega

end Machine

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.StackCommands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace StackModel

/-- Finite structured source code. Tests and registers have fixed finite range;
all unbounded data remain in the explicitly named bit stacks. -/
inductive Command (K R : Type) where
  | skip
  | push (k : K) (value : R → Bool)
  | pop (k : K) (store : R → Option Bool → R)
  | modify (store : R → R)
  | seq (first second : Command K R)
  | branch (test : R → Bool) (yes no : Command K R)
  | while (test : R → Bool) (body : Command K R)

namespace Command
variable {K R : Type}

abbrev Control : Command K R → Type
  | .skip | .push _ _ | .pop _ _ | .modify _ => Unit
  | .seq c d => Control c ⊕ Control d
  | .branch _ c d => Unit ⊕ (Control c ⊕ Control d)
  | .while _ c => Unit ⊕ Control c

noncomputable instance controlFintype (c : Command K R) : Fintype (Control c) := by
  induction c <;> simp only [Control] <;> infer_instance

def entry : (c : Command K R) → Control c
  | .skip | .push _ _ | .pop _ _ | .modify _ => ()
  | .seq c _ => .inl (entry c)
  | .branch _ _ _ | .while _ _ => .inl ()

end Command

end StackModel

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.FiniteRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace FiniteRefinement

variable {A : Type} [Fintype A] {C : ℕ → Type} (color : (s : ℕ) → A → C s)

def KernelEq (s t : ℕ) : Prop := ∀ a b, color s a = color s b ↔ color t a = color t b

noncomputable def kernel (s : ℕ) : Finset (A × A) := by
  classical exact Finset.univ.filter (fun ab => color s ab.1 = color s ab.2)

end FiniteRefinement
namespace FiniteRefinement

variable {A I : Type} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]

def vectorMatch (R : A → A → Bool) (v w : I → A) : Bool :=
  decide (∀ i, R (v i) (w i) = true)

def tableStep (N : A → Multiset (I → A)) (R : A → A → Bool) (a b : A) : Bool :=
  R a b && decide (∀ v : I → A,
    (N a).countP (fun w => vectorMatch R w v = true) =
    (N b).countP (fun w => vectorMatch R w v = true))

/-- Literal finite Boolean relation iteration. -/
def table (N : A → Multiset (I → A)) (initial : A → A → Bool) (rounds : ℕ) : A → A → Bool :=
  (tableStep N)^[rounds] initial

end FiniteRefinement

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.WordCommands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace StackModel
namespace Command
variable {K : Type} [DecidableEq K]

abbrev read (k : K) : Command K (Option Bool) := .pop k (fun _ b => b)
abbrev emit (k : K) : Command K (Option Bool) := .push k (fun b => b.getD false)

def drain (k : K) (body : Command K (Option Bool)) : Command K (Option Bool) :=
  .seq (read k) (.while Option.isSome (.seq body (read k)))

def clear (k : K) : Command K (Option Bool) := drain k .skip

def pushMany (ks : List K) : Command K (Option Bool) :=
  ks.foldr (fun k c => .seq (emit k) c) .skip

/-- Copy a complete word, preserving its order and the source, using one private work stack. -/
def copy (a b tmp : K) : Command K (Option Bool) :=
  .seq (clear b) (.seq (clear tmp) (.seq (drain a (pushMany [tmp]))
    (drain tmp (pushMany [a,b]))))

end Command
end StackModel
namespace StackModel.Command
variable {K L R : Type}

def rename (e : K → L) : Command K R → Command L R
  | .skip => .skip
  | .push k f => .push (e k) f
  | .pop k f => .pop (e k) f
  | .modify f => .modify f
  | .seq c d => .seq (rename e c) (rename e d)
  | .branch t c d => .branch t (rename e c) (rename e d)
  | .while t c => .while t (rename e c)

@[simp] theorem rename_rename {N : Type} (e : K → L) (f : L → N) (c : Command K R) :
    rename f (rename e c) = rename (f ∘ e) c := by
  induction c <;> simp_all [rename]

end StackModel.Command

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.ExpressionCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace StackModel.Command
variable {R : Type}

def registers : Command ℕ R → Finset ℕ
  | .skip | .modify _ => ∅
  | .push k _ | .pop k _ => {k}
  | .seq c d | .branch _ c d => c.registers ∪ d.registers
  | .while _ c => c.registers

def small (c : Command ℕ R) (N : ℕ) : Prop := ∀ k ∈ c.registers, k < N

def finiteIndex (N : ℕ) (h : 0 < N) (k : ℕ) : Fin N := ⟨k % N, Nat.mod_lt _ h⟩

@[simp] theorem finiteIndex_val {N k} (h : 0 < N) (hk : k < N) :
    (finiteIndex N h k).val = k := Nat.mod_eq_of_lt hk

end StackModel.Command

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.NumericKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace NumericKernel

structure Data (N width branch : ℕ) where
  active : Fin N → Fin branch → Bool
  next : Fin N → Fin branch → Fin width → Fin N

variable {N width branch : ℕ} (D : Data N width branch)

def Data.vectors (a : Fin N) : Multiset (Fin width → Fin N) :=
  ((Finset.univ : Finset (Fin branch)).filter (fun z => D.active a z = true)).val.map (D.next a)

end NumericKernel

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.RefinementCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace NumericWL
open NumericKernel

abbrev sides (t : ℕ) : Fin t ⊕ Fin t ≃ Fin (t+t) := finSumFinEquiv

@[simp] theorem sides_inl (t : ℕ) (x : Fin t) : (sides t (.inl x)).val = x.val := rfl
@[simp] theorem sides_inr (t : ℕ) (x : Fin t) : (sides t (.inr x)).val = t+x.val := rfl

end NumericWL

namespace NumericWL
open NumericKernel

abbrev tuples (n k : ℕ) := (Fin k → Fin n) ⊕ (Fin k → Fin n)

end NumericWL

end WLIdentification

end OAI
end


