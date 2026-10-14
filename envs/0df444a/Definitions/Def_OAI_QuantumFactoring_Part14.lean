-- Prove2me | Definitions.Def_OAI_QuantumFactoring_Part14
-- name    : OAI_QuantumFactoring_Part14
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T07:48:35.018533+00:00
-- url     : https://prove2.me/theorems/b738b104-0617-47c6-a0a9-1902e960fbd8
-- title:
--   Exact quantum factoring, part 14 of 38 (port of OpenAI's formalization)
-- statement:
--   Part 14 of 38 of a port of OpenAI's Lean formalization of the manuscript *Exact quantum factoring over a fixed finite gate set* (OpenAI, September 25, 2026). This part contains the modules `PhysicalSplit`, `SamplerDecodeCircuit`, `RawTrialFields`, `RawTrialLabelCircuit`, `RetrospectiveOrder`, `RetrospectiveCircuit`, `LabelValidationCircuit`, `RationalConditionals`, `ProgressionEvaluation`, `ProgressionExpressions`, `PolynomialFilterExpressions`, `DynamicMajorantExpressions`, `RetentionExpressions`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/QuantumFactoring`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `ExactQuantumFactoring`, which is identical to upstream `Basic.lean`.
--
--   The development is split into 38 parts only so that each compiles within the platform's time limit. Together the parts supply the circuit family `PhysicalTree.finalCircuit` and its specification, used to prove `OAI.ExactQuantumFactoring.zero_amplitude_core`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/QuantumFactoring: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhysicalSplit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/SamplerDecodeCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/RawTrialFields.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/RawTrialLabelCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/RetrospectiveOrder.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/RetrospectiveCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/LabelValidationCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/RationalConditionals.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ProgressionEvaluation.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ProgressionExpressions.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PolynomialFilterExpressions.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/DynamicMajorantExpressions.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/RetentionExpressions.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf

/-
Exact quantum factoring development (port of OpenAI's formalization), part 14 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: PhysicalSplit.lean, SamplerDecodeCircuit.lean, RawTrialFields.lean, RawTrialLabelCircuit.lean, RetrospectiveOrder.lean, RetrospectiveCircuit.lean, LabelValidationCircuit.lean, RationalConditionals.lean, ProgressionEvaluation.lean, ProgressionExpressions.lean, PolynomialFilterExpressions.lean, DynamicMajorantExpressions.lean, RetentionExpressions.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part13

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalSplit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness
namespace FixedSplit

abbrev ordersWidth (n : ℕ) := tensorWidth (OrderSlots.width n) (n^5)
def ordersLayout (n : ℕ) : (Fin (n^5)→OrderSlots.Result n)≃Basis (ordersWidth n) :=
  (Equiv.piCongrRight (fun _ => OrderSlots.layout n)).trans (tensorLayout (OrderSlots.width n) (n^5))
def ordersProgram (n : ℕ) : List (Instruction (ordersWidth n)) := tensorProgram (OrderSlots.program n) (n^5)

lemma ordersProgram_state {n : ℕ} (m : Basis n) (aa : Fin (n^5)→Basis n) :
    (programMatrix (ordersProgram n)).mulVec
      (basisVector (ordersLayout n (fun i=>OrderSlots.zero (aa i) m)))=
    encodeState (ordersLayout n) (productState (fun i=>OrderSlots.fresh n (aa i) m)) := by
  funext x
  obtain ⟨y,rfl⟩ := (ordersLayout n).surjective x
  rw [encodeState_at _ (ordersLayout n).injective]
  change (programMatrix (tensorProgram (OrderSlots.program n) (n^5))).mulVec
    (basisVector (tensorLayout _ _ (fun i=>OrderSlots.layout n (OrderSlots.zero (aa i) m))))
    (tensorLayout _ _ (fun i=>OrderSlots.layout n (y i)))= _
  rw [tensorProgram_entry]
  simp only [OrderSlots.program_entry,productState]

def listWires (n : ℕ) : BooleanNetwork (PhysicalListSlots.launchWidth n) (PhysicalListSlots.width n) :=
  select (targetRegister n (PhysicalListSlots.width n) (PhysicalListSlots.work n))
def modulusWires (n : ℕ) : BooleanNetwork (PhysicalListSlots.launchWidth n) n :=
  select (firstRegister n (PhysicalListSlots.width n) (PhysicalListSlots.work n))
def listEncoding {n : ℕ} (m : Basis n) (l : PhysicalListSlots.Result n) : Basis (PhysicalListSlots.launchWidth n) :=
  packed (PhysicalListSlots.work n) m (PhysicalListSlots.layout n l)
lemma listWires_eval {n : ℕ} (m : Basis n) (l : PhysicalListSlots.Result n) :
    (listWires n).eval (listEncoding m l)=PhysicalListSlots.layout n l := by
  exact packed_targetRegister m _
lemma modulusWires_eval {n : ℕ} (m : Basis n) (l : PhysicalListSlots.Result n) :
    (modulusWires n).eval (listEncoding m l)=m := packed_first m _

def baseNet {n : ℕ} (i : Fin (n^5)) : BooleanNetwork (PhysicalListSlots.launchWidth n) n :=
  ((listWires n).comp (PhysicalListSlots.outputNet n)).rewire
    (fun j=>Fin.cast (Nat.mul_comm _ _) (finProdFinEquiv (i.castSucc,j)))
lemma baseNet_eval {n : ℕ} (i : Fin (n^5)) (m : Basis n) (l : PhysicalListSlots.Result n) :
    (baseNet i).eval (listEncoding m l)=bases l i := by
  rw [baseNet,eval_rewire,eval_comp,listWires_eval,PhysicalListSlots.outputNet_eval]
  rfl
lemma baseNet_count {n : ℕ} (i : Fin (n^5)) :
    (baseNet i).net.count=(PhysicalListSlots.outputNet n).net.count := by
  simp only [baseNet,count_rewire,count_comp,listWires,count_select,zero_add]

def orderInitialNet {n : ℕ} (i : Fin (n^5)) :
    BooleanNetwork (PhysicalListSlots.launchWidth n) (OrderSlots.width n) :=
  ((baseNet i).pair (modulusWires n)).comp (OrderSlots.initialNet n)
lemma orderInitialNet_eval {n : ℕ} (i : Fin (n^5)) (m : Basis n) (l : PhysicalListSlots.Result n) :
    (orderInitialNet i).eval (listEncoding m l)=OrderSlots.layout n (OrderSlots.zero (bases l i) m) := by
  rw [orderInitialNet,eval_comp,eval_pair,baseNet_eval,modulusWires_eval,OrderSlots.initialNet_eval]
lemma orderInitialNet_count {n : ℕ} (i : Fin (n^5)) :
    (orderInitialNet i).net.count=(PhysicalListSlots.outputNet n).net.count+(OrderSlots.initialNet n).net.count := by
  simp only [orderInitialNet,count_comp,count_pair,baseNet_count,modulusWires,count_select,add_zero]

def ordersInitialNet (n : ℕ) : BooleanNetwork (PhysicalListSlots.launchWidth n) (ordersWidth n) :=
  tensorNetwork (fun i=>orderInitialNet (n:=n) i)
lemma ordersInitialNet_eval {n : ℕ} (m : Basis n) (l : PhysicalListSlots.Result n) :
    (ordersInitialNet n).eval (listEncoding m l)=ordersLayout n (fun i=>OrderSlots.zero (bases l i) m) := by
  rw [ordersInitialNet,tensorNetwork_eval]
  simp only [orderInitialNet_eval]
  rfl
lemma ordersInitialNet_count (n : ℕ) : (ordersInitialNet n).net.count=
    n^5*((PhysicalListSlots.outputNet n).net.count+(OrderSlots.initialNet n).net.count) := by
  rw [ordersInitialNet,tensorNetwork_count]
  simp only [orderInitialNet_count,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

abbrev work (n : ℕ) := (ordersInitialNet n).net.count
abbrev width (n : ℕ) := PhysicalListSlots.launchWidth n+ordersWidth n+work n
/-- One actual fixed-gate circuit: the completed random list is generated first;
only that same list supplies the bases for the ensuing order slots. -/
def program (n : ℕ) : List (Instruction (width n)) :=
  appendPrepared (PhysicalListSlots.launch n) (ordersInitialNet n) le_rfl (ordersProgram n)
def encoding {n : ℕ} (m : Basis n) (r : Raw n) : Basis (width n) :=
  packed (work n) (listEncoding m r.1) (ordersLayout n r.2)
def zero {n : ℕ} (m : Basis n) : Basis (width n) :=
  packed (work n) (packed (PhysicalListSlots.work n) m (fun _=>false)) (fun _=>false)

theorem program_state {n : ℕ} (m : Basis n) :
    (programMatrix (program n)).mulVec (basisVector (zero m))=encodeState (encoding m) (fresh m) := by
  apply appendPrepared_state (listEncoding m) (ordersLayout n) (PhysicalListSlots.fresh m)
    (fun l=>productState (fun i=>OrderSlots.fresh n (bases l i) m))
    (PhysicalListSlots.launch n) (packed (PhysicalListSlots.work n) m (fun _=>false))
    (PhysicalListSlots.launch_state m) (ordersInitialNet n) le_rfl (ordersProgram n)
  intro l
  rw [ordersInitialNet_eval,ordersProgram_state]

lemma encoding_injective {n : ℕ} (m : Basis n) : Function.Injective (encoding m) := by
  intro a b hh
  have he : (listEncoding m a.1,ordersLayout n a.2)=(listEncoding m b.1,ordersLayout n b.2) :=
    packed_pair_injective _ _ _ hh
  apply Prod.ext
  · apply (PhysicalListSlots.layout n).injective
    have h : (m,PhysicalListSlots.layout n a.1)=(m,PhysicalListSlots.layout n b.1) :=
      packed_pair_injective _ _ _ (congrArg Prod.fst he)
    exact congrArg Prod.snd h
  · exact (ordersLayout n).injective (congrArg Prod.snd he)

lemma program_length (n : ℕ) : (program n).length ≤
    (PhysicalListSlots.launch n).length+4*work n+2*ordersWidth n+n^5*(OrderSlots.program n).length := by
  have h := appendPrepared_length (PhysicalListSlots.launch n) (ordersInitialNet n) le_rfl (ordersProgram n)
  simpa only [program,work,ordersProgram,tensorProgram_length] using h

end FixedSplit
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/SamplerDecodeCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace BooleanNetwork

def leftNet (u v : ℕ) : BooleanNetwork (u+v) u := select (Fin.castAdd v)
def rightNet (u v : ℕ) : BooleanNetwork (u+v) v := select (Fin.natAdd u)
lemma leftNet_eval {u v : ℕ} (x : Basis u) (y : Basis v) :
    (leftNet u v).eval (Fin.append x y)=x := by
  funext i
  exact Fin.append_left x y i
lemma rightNet_eval {u v : ℕ} (x : Basis u) (y : Basis v) :
    (rightNet u v).eval (Fin.append x y)=y := by
  funext i
  exact Fin.append_right x y i
lemma equalOn_basis {k w : ℕ} (a b : BooleanNetwork k w) (x : Basis k) :
    (equalOn a b).eval x 0=true ↔ a.eval x=b.eval x := by
  rw [equalOn_value]
  constructor
  · intro h
    exact (bitsEquiv w).injective (BitVec.eq_of_toNat_eq h)
  · intro h; rw [h]

end BooleanNetwork
namespace OrderTrial

def sampleYNet (u b : ℕ) : BooleanNetwork (OrderSample.width u b) b :=
  select (fun i => (((Fin.natAdd (u+u) (Triangular.dataWire i)).castAdd u).castAdd (OrderSample.scratch u b)))
def sampleUNet (u b : ℕ) : BooleanNetwork (OrderSample.width u b) u :=
  select (fun i => ((Fin.natAdd (OrderSample.inputWidth u b) i).castAdd (OrderSample.scratch u b)))
lemma sampleYNet_eval {u b : ℕ} (x : Basis (OrderSample.width u b)) :
    (sampleYNet u b).eval x=sampleY x := rfl
lemma sampleUNet_eval {u b : ℕ} (x : Basis (OrderSample.width u b)) :
    (sampleUNet u b).eval x=sampleU x := rfl

def triangularSelectedNet {k b : ℕ} (y : BooleanNetwork k b) : BooleanNetwork k (Triangular.width b) :=
  packNet (Triangular.work b) (y.pair (Completion.zeros k b)) (Completion.zeros k (b+b))
lemma triangularSelectedNet_eval {k b : ℕ} (y : BooleanNetwork k b) (x : Basis k) :
    (triangularSelectedNet y).eval x=Triangular.encode b (y.eval x,0) := by
  have h := (basisResidue b).symm_apply_eq.mpr (basisResidue_zero b).symm
  rw [triangularSelectedNet,packNet_eval,eval_pair,Completion.zeros_eval,Completion.zeros_eval]
  simp only [Triangular.encode,h]

/-- Full selection compares retained read-only inputs and every sampler scratch
bit, not only the apparent phase and modular residue fields. -/
def samplerSelectedNet {k u b : ℕ} (a m : BooleanNetwork k u)
    (z : BooleanNetwork k (OrderSample.width u b)) : BooleanNetwork k 1 :=
  equalOn z (packNet (OrderSample.scratch u b)
    ((a.pair m).pair (triangularSelectedNet (z.comp (sampleYNet u b))))
    (z.comp (sampleUNet u b)))
lemma samplerSelectedNet_eval {k u b : ℕ} (a m : BooleanNetwork k u)
    (z : BooleanNetwork k (OrderSample.width u b)) (x : Basis k) :
    (samplerSelectedNet a m z).eval x 0=true ↔ SampleSelected (a.eval x) (m.eval x) (z.eval x) := by
  rw [samplerSelectedNet,equalOn_basis,packNet_eval,eval_pair,eval_pair,
    triangularSelectedNet_eval]
  simp only [eval_comp,sampleYNet_eval,sampleUNet_eval,SampleSelected,OrderSample.word,OrderSample.inputWord]
lemma samplerSelectedNet_count {k u b : ℕ} (a m : BooleanNetwork k u)
    (z : BooleanNetwork k (OrderSample.width u b)) :
    (samplerSelectedNet a m z).net.count ≤
      3*z.net.count+a.net.count+m.net.count+3*b+Triangular.work b+
        OrderSample.scratch u b+98*OrderSample.width u b+21 := by
  have h := equalOn_count z (packNet (OrderSample.scratch u b)
    ((a.pair m).pair (triangularSelectedNet (z.comp (sampleYNet u b))))
    (z.comp (sampleUNet u b)))
  simp only [packNet_count,count_pair,triangularSelectedNet,Completion.zeros_count,
    count_comp,sampleYNet,sampleUNet,count_select] at h
  dsimp only [samplerSelectedNet,triangularSelectedNet,sampleYNet,sampleUNet]
  omega

end OrderTrial
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RawTrialFields.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

def rawMode {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k 2 :=
  r.comp (leftNet 2 (OrderSample.width u (s+2)+guessWidth n))
def rawSample {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    BooleanNetwork k (OrderSample.width u (s+2)) :=
  (r.comp (rightNet 2 (OrderSample.width u (s+2)+guessWidth n))).comp
    (leftNet (OrderSample.width u (s+2)) (guessWidth n))
def rawGuesses {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k (guessWidth n) :=
  (r.comp (rightNet 2 (OrderSample.width u (s+2)+guessWidth n))).comp
    (rightNet (OrderSample.width u (s+2)) (guessWidth n))
def rawDen {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k n :=
  (rawGuesses r).comp (leftNet n (n+(n+retentionBits n)))
def rawNum {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k n :=
  ((rawGuesses r).comp (rightNet n (n+(n+retentionBits n)))).comp (leftNet n (n+retentionBits n))
def rawResidue {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k n :=
  (((rawGuesses r).comp (rightNet n (n+(n+retentionBits n)))).comp
    (rightNet n (n+retentionBits n))).comp (leftNet n (retentionBits n))
def rawCoin {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k (retentionBits n) :=
  (((rawGuesses r).comp (rightNet n (n+(n+retentionBits n)))).comp
    (rightNet n (n+retentionBits n))).comp (rightNet n (retentionBits n))

lemma rawMode_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawMode r).eval x=y.1 := by
  simp only [rawMode,eval_comp,h,rawLayout,productLayout_apply,Equiv.refl_apply,leftNet_eval]
lemma rawSample_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawSample r).eval x=y.2.1 := by
  simp only [rawSample,eval_comp,h,rawLayout,productLayout_apply,Equiv.refl_apply,leftNet_eval,rightNet_eval]
lemma rawGuesses_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawGuesses r).eval x=guessLayout n y.2.2 := by
  simp only [rawGuesses,eval_comp,h,rawLayout,productLayout_apply,Equiv.refl_apply,rightNet_eval]
lemma rawDen_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawDen r).eval x=y.2.2.1 := by
  rw [rawDen,eval_comp,rawGuesses_eval r x y h]
  simp only [guessLayout,productLayout_apply,Equiv.refl_apply,leftNet_eval]
lemma rawNum_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawNum r).eval x=y.2.2.2.1 := by
  rw [rawNum,eval_comp,eval_comp,rawGuesses_eval r x y h]
  simp only [guessLayout,productLayout_apply,Equiv.refl_apply,leftNet_eval,rightNet_eval]
lemma rawResidue_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawResidue r).eval x=y.2.2.2.2.1 := by
  rw [rawResidue,eval_comp,eval_comp,eval_comp,rawGuesses_eval r x y h]
  simp only [guessLayout,productLayout_apply,Equiv.refl_apply,leftNet_eval,rightNet_eval]
lemma rawCoin_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawCoin r).eval x=y.2.2.2.2.2 := by
  rw [rawCoin,eval_comp,eval_comp,eval_comp,rawGuesses_eval r x y h]
  simp only [guessLayout,productLayout_apply,Equiv.refl_apply,rightNet_eval]

def toWidth {k u : ℕ} (w : ℕ) (a : BooleanNetwork k u) : BooleanNetwork k w :=
  a.comp (resizeWord u w)
lemma toWidth_value {k u w : ℕ} (a : BooleanNetwork k u) (h : u≤w) (x : Basis k) :
    (bitsValue ((toWidth w a).eval x)).toNat=(bitsValue (a.eval x)).toNat := by
  rw [toWidth,eval_comp,resizeWord_toNat h]
lemma toWidth_count {k u w : ℕ} (a : BooleanNetwork k u) :
    (toWidth w a).net.count≤a.net.count+w := by
  rw [toWidth,count_comp]
  exact Nat.add_le_add_left (resizeWord_count u w) _

end ExactQuantumFactoring.OrderTrial


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RawTrialLabelCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

abbrev decodeSteps (s : ℕ) := 2*(s+3)+1
abbrev decodeWidth (u s n : ℕ) := cfWidth (s+3) (decodeSteps s)+u+n+retentionBits n+(s+3)+3

def recoveredPairNet {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    BooleanNetwork k (decodeWidth u s n+decodeWidth u s n) :=
  recoveryNet (wordConstant (BitVec.ofNat (decodeWidth u s n) (2^(s+2))))
    (wordConstant (BitVec.ofNat (decodeWidth u s n) (2^n)))
    (toWidth (decodeWidth u s n) ((rawSample r).comp (sampleYNet u (s+2)))) (decodeSteps s)

def trialPairNet {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    BooleanNetwork k (decodeWidth u s n+decodeWidth u s n) :=
  wordMux (wordLt (toWidth (decodeWidth u s n) (rawMode r))
      (wordConstant (BitVec.ofNat (decodeWidth u s n) 2)))
    (recoveredPairNet r)
    ((toWidth (decodeWidth u s n) (rawDen r)).pair (toWidth (decodeWidth u s n) (rawNum r)))
def trialDenNet {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    BooleanNetwork k (decodeWidth u s n) :=
  (trialPairNet r).comp (leftNet (decodeWidth u s n) (decodeWidth u s n))
def trialNumNet {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    BooleanNetwork k (decodeWidth u s n) :=
  (trialPairNet r).comp (rightNet (decodeWidth u s n) (decodeWidth u s n))

lemma recoveredPairNet_value {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n))
    (x : Basis k) (y : Raw u s n) (h : r.eval x=rawLayout u s n y) :
    ∃ d j : Basis (decodeWidth u s n),
      (recoveredPairNet r).eval x=Fin.append d j ∧
      ((bitsValue d).toNat,(bitsValue j).toNat)=
        scanPairs (2^(s+2)) (2^n) (Triangular.outputNumber (sampleY y.2.1)) (decodeSteps s) := by
  have hw : cfWidth (s+3) (decodeSteps s)≤decodeWidth u s n := by unfold decodeWidth; omega
  have hs : s+2<decodeWidth u s n := by unfold decodeWidth; omega
  have hn : n<decodeWidth u s n := by unfold decodeWidth; omega
  have hQ : (bitsValue ((wordConstant (n:=k) (BitVec.ofNat (decodeWidth u s n) (2^(s+2)))).eval x)).toNat=2^(s+2) := by
    rw [wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hs)]
  have hB : (bitsValue ((wordConstant (n:=k) (BitVec.ofNat (decodeWidth u s n) (2^n))).eval x)).toNat=2^n := by
    rw [wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hn)]
  have hy : (bitsValue ((toWidth (decodeWidth u s n) ((rawSample r).comp (sampleYNet u (s+2)))).eval x)).toNat =
      Triangular.outputNumber (sampleY y.2.1) := by
    rw [toWidth_value _ hs.le,eval_comp,rawSample_eval r x y h,sampleYNet_eval,bitsValue_toNat]
    rfl
  obtain ⟨d,j,hd,hv⟩ := recoveryNet_value
    (wordConstant (n:=k) (BitVec.ofNat (decodeWidth u s n) (2^(s+2))))
    (wordConstant (n:=k) (BitVec.ofNat (decodeWidth u s n) (2^n)))
    (toWidth (decodeWidth u s n) ((rawSample r).comp (sampleYNet u (s+2)))) (decodeSteps s) hw x
    (by rw [hQ]; exact Nat.pow_lt_pow_right (by decide) (by omega))
    (by rw [hy,Triangular.outputNumber,← bitsValue_toNat]
        exact (bitsValue (sampleY y.2.1)).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
  exact ⟨d,j,hd,by simpa only [hQ,hB,hy] using hv⟩

lemma trialPairNet_value {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n))
    (x : Basis k) (y : Raw u s n) (h : r.eval x=rawLayout u s n y) :
    ∃ d j : Basis (decodeWidth u s n),
      (trialPairNet r).eval x=Fin.append d j ∧
      ((bitsValue d).toNat,(bitsValue j).toNat)=labelPair s n y := by
  have hw : 2≤decodeWidth u s n := by unfold decodeWidth; omega
  have hn : n≤decodeWidth u s n := by unfold decodeWidth; omega
  have h2 : 2<2^(decodeWidth u s n) := lt_of_lt_of_le (by decide : 2<2^2)
    (Nat.pow_le_pow_right (by decide) hw)
  have hm : (wordLt (toWidth (decodeWidth u s n) (rawMode r))
      (wordConstant (BitVec.ofNat (decodeWidth u s n) 2))).eval x 0=
      decide ((bitsValue y.1).toNat<2) := by
    rw [wordLt_eval,toWidth_value _ hw,rawMode_eval r x y h,wordConstant_eval,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt h2]
  by_cases ht : (bitsValue y.1).toNat<2
  · obtain ⟨d,j,hd,hv⟩ := recoveredPairNet_value r x y h
    refine ⟨d,j,?_,?_⟩
    · rw [trialPairNet,wordMux_eval,hm,ite_eq_left (by simpa only [decide_eq_true_eq] using ht),hd]
    · rw [labelPair,ite_eq_left ht]
      exact hv
  · refine ⟨(toWidth (decodeWidth u s n) (rawDen r)).eval x,
      (toWidth (decodeWidth u s n) (rawNum r)).eval x,?_,?_⟩
    · rw [trialPairNet,wordMux_eval,hm,ite_eq_right (by simpa only [decide_eq_true_eq] using ht),eval_pair]
    · rw [toWidth_value _ hn,toWidth_value _ hn,rawDen_eval r x y h,rawNum_eval r x y h,
        labelPair,ite_eq_right ht]

lemma trialDenNet_value {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n))
    (x : Basis k) (y : Raw u s n) (h : r.eval x=rawLayout u s n y) :
    (bitsValue ((trialDenNet r).eval x)).toNat=(labelPair s n y).1 := by
  obtain ⟨d,j,hd,hv⟩ := trialPairNet_value r x y h
  rw [trialDenNet,eval_comp,hd,leftNet_eval]
  exact congrArg Prod.fst hv
lemma trialNumNet_value {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n))
    (x : Basis k) (y : Raw u s n) (h : r.eval x=rawLayout u s n y) :
    (bitsValue ((trialNumNet r).eval x)).toNat=(labelPair s n y).2 := by
  obtain ⟨d,j,hd,hv⟩ := trialPairNet_value r x y h
  rw [trialNumNet,eval_comp,hd,rightNet_eval]
  exact congrArg Prod.snd hv

end ExactQuantumFactoring.OrderTrial


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetrospectiveOrder.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

/-- One occurrence of the source's prime-stripping loop. A repeated prime
factor list supplies exactly as many attempts as its known multiplicity. -/
def stripOrderPrime {G : Type*} [Monoid G] [DecidableEq G] (a : G) (q v : ℕ) : ℕ :=
  if q ∣ v ∧ a^(v/q)=1 then v/q else v

def stripOrderFactors {G : Type*} [Monoid G] [DecidableEq G] (a : G) : List ℕ→ℕ→ℕ
  | [], v => v
  | q::qs, v => stripOrderFactors a qs (stripOrderPrime a q v)

lemma stripOrderPrime_multiple {G : Type*} [Monoid G] [DecidableEq G]
    (a : G) (hr : 0 < orderOf a) (q k : ℕ) :
    stripOrderPrime a q (orderOf a*k)=orderOf a*(if q∣k then k/q else k) := by
  let r := orderOf a
  have hcond : (q∣r*k ∧ a^((r*k)/q)=1) ↔ q∣k := by
    constructor
    · rintro ⟨hq,hpow⟩
      have h := orderOf_dvd_iff_pow_eq_one.mpr hpow
      have hh : r*q∣r*k := by simpa only [Nat.mul_comm q] using (Nat.dvd_div_iff_mul_dvd hq).mp h
      exact (Nat.mul_dvd_mul_iff_left hr).mp hh
    · intro hk
      refine ⟨hk.mul_left r,?_⟩
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [Nat.mul_div_assoc r hk]
      exact dvd_mul_right r (k/q)
  change (if q∣r*k ∧ a^((r*k)/q)=1 then (r*k)/q else r*k)=_
  simp only [hcond]
  split_ifs with hq
  · exact Nat.mul_div_assoc r hq
  · rfl

lemma quotient_dvd_tail {k q v : ℕ} (hq : 0 < q) (hk : q∣k) (hkv : k∣q*v) : k/q ∣ v := by
  obtain ⟨c,hc⟩ := hkv
  refine ⟨c,?_⟩
  apply Nat.eq_of_mul_eq_mul_left hq
  rw [← Nat.mul_assoc,Nat.mul_div_cancel' hk]
  exact hc

/-- Complete factor stripping: no excess prime can survive a scan of a known
factorization of a multiple of the initial quotient. There is no call to an
order oracle in this algorithm. -/
theorem stripOrderFactors_exact {G : Type*} [Monoid G] [DecidableEq G]
    (a : G) (hr : 0 < orderOf a) (qs : List ℕ)
    (hp : ∀ q∈qs, q.Prime) (k : ℕ) (hk : k∣qs.prod) :
    stripOrderFactors a qs (orderOf a*k)=orderOf a := by
  induction qs generalizing k with
  | nil =>
    have he : k=1 := Nat.dvd_one.mp hk
    simp [stripOrderFactors,he]
  | cons q qs ih =>
    have hq := hp q (by simp)
    have htail : ∀ p∈qs, p.Prime := fun p hh => hp p (by simp [hh])
    simp only [stripOrderFactors,stripOrderPrime_multiple a hr]
    apply ih htail
    by_cases hdiv : q∣k
    · rw [ite_eq_left hdiv]
      exact quotient_dvd_tail hq.pos hdiv hk
    · rw [ite_eq_right hdiv]
      exact (hq.coprime_iff_not_dvd.mpr hdiv).symm.dvd_of_dvd_mul_left hk

/-- Specializing to the known factorization of phi(m), as in source §5. The
factor list is explicit input produced by the completed auxiliary tree. -/
theorem strip_totient_factors {m : ℕ} (hm : 2 ≤ m) (a : (ZMod m)ˣ)
    (qs : List ℕ) (hp : ∀ q∈qs,q.Prime) (hprod : qs.prod=m.totient) :
    stripOrderFactors a qs m.totient=orderOf a := by
  let : NeZero m := ⟨by omega⟩
  have hd : orderOf a ∣ m.totient := by simpa [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient] using orderOf_dvd_natCard a
  have hr : 0 < orderOf a := orderOf_pos a
  have he := Nat.mul_div_cancel' hd
  have hq : m.totient/orderOf a ∣ qs.prod := by
    rw [hprod]
    exact (dvd_mul_left (m.totient/orderOf a) (orderOf a)).trans (dvd_of_eq he)
  rw [← he]
  exact stripOrderFactors_exact a hr qs hp _ hq

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetrospectiveCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

def stripPrimeNat (a m q v : ℕ) : ℕ :=
  if v%q=0 ∧ a^(v/q)%m=1 then v/q else v

lemma stripPrimeNat_unit {m a : ℕ} (hm : 2 ≤ m) (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) (q v : ℕ) :
    stripPrimeNat a m q v=stripOrderPrime u q v := by
  let : NeZero m := ⟨by omega⟩
  have he : a^(v/q)%m=1 ↔ u^(v/q)=1 := by
    rw [show a^(v/q)%m=((u^(v/q) : (ZMod m)ˣ) : ZMod m).val by
      rw [Units.val_pow_eq_pow_val,← ha,← Nat.cast_pow,ZMod.val_natCast]]
    constructor
    · intro h
      apply Units.ext
      apply ZMod.val_injective
      simpa only [Units.val_one,ZMod.val_one'' (by omega : m≠1)] using h
    · intro h
      rw [h,Units.val_one,ZMod.val_one'' (by omega : m≠1)]
  simp only [stripPrimeNat,stripOrderPrime,← Nat.dvd_iff_mod_eq_zero,he]

namespace BitArithmetic

def liftInput {k l w : ℕ} (a : BooleanNetwork k w) (f : Fin k → Fin l) : BooleanNetwork l w :=
  (select f).comp a

@[simp] lemma liftInput_eval {k l w : ℕ} (a : BooleanNetwork k w) (f : Fin k → Fin l) (x : Basis l) :
    (liftInput a f).eval x=a.eval (x∘f) := by simp [liftInput,eval_comp]

@[simp] lemma liftInput_count {k l w : ℕ} (a : BooleanNetwork k w) (f : Fin k → Fin l) :
    (liftInput a f).net.count=a.net.count := by simp [liftInput,count_comp]

def powOn {k w : ℕ} (a m e : BooleanNetwork k w) : BooleanNetwork k w :=
  ((a.pair m).pair (e.rewire Fin.rev)).comp (modularPower w w)

lemma powOn_value {k w : ℕ} (a m e : BooleanNetwork k w) (x : Basis k)
    (hm : 2 ≤ (bitsValue (m.eval x)).toNat) :
    (bitsValue ((powOn a m e).eval x)).toNat=
      (bitsValue (a.eval x)).toNat^(bitsValue (e.eval x)).toNat%(bitsValue (m.eval x)).toNat := by
  have hh : horner ((e.rewire Fin.rev).eval x) w le_rfl=(bitsValue (e.eval x)).toNat := by
    rw [horner_full,Triangular.inputNumber_reverse]
    congr 2
    funext i
    simp [reverseBits,eval_rewire]
  rw [powOn,eval_comp,eval_pair,eval_pair,modularPower_value _ _ _ hm,hh]

lemma powOn_count {k w : ℕ} (a m e : BooleanNetwork k w) :
    (powOn a m e).net.count ≤ a.net.count+m.net.count+e.net.count+
      w+w*(3672*w*w+436*w+36) := by
  have h := modularPower_count w w
  simp only [powOn,count_comp,count_pair,count_rewire]
  omega

def stripOn {k w : ℕ} (a m q v : BooleanNetwork k w) : BooleanNetwork k w :=
  let d := (v.pair q).comp (div w)
  let cond := (equalOn ((v.pair q).comp (mod w)) (wordConstant (BitVec.ofNat w 0))).band
    (equalOn (powOn a m d) (wordConstant (BitVec.ofNat w 1)))
  wordMux cond d v

lemma stripOn_value {k w : ℕ} (a m q v : BooleanNetwork k w) (x : Basis k)
    (hm : 2 ≤ (bitsValue (m.eval x)).toNat) :
    (bitsValue ((stripOn a m q v).eval x)).toNat=stripPrimeNat
      (bitsValue (a.eval x)).toNat (bitsValue (m.eval x)).toNat
      (bitsValue (q.eval x)).toNat (bitsValue (v.eval x)).toNat := by
  have h1 : 1 < 2^w := lt_of_lt_of_le (by omega : 1 < (bitsValue (m.eval x)).toNat)
    (bitsValue (m.eval x)).isLt.le
  have hd : (bitsValue (((v.pair q).comp (div w)).eval x)).toNat=
      (bitsValue (v.eval x)).toNat/(bitsValue (q.eval x)).toNat := by
    rw [eval_comp,eval_pair,div_word,BitVec.toNat_udiv]
  have hc : ((equalOn ((v.pair q).comp (mod w)) (wordConstant (BitVec.ofNat w 0))).band
      (equalOn (powOn a m ((v.pair q).comp (div w))) (wordConstant (BitVec.ofNat w 1)))).eval x 0=true ↔
      (bitsValue (v.eval x)).toNat%(bitsValue (q.eval x)).toNat=0 ∧
      (bitsValue (a.eval x)).toNat^((bitsValue (v.eval x)).toNat/(bitsValue (q.eval x)).toNat)%
        (bitsValue (m.eval x)).toNat=1 := by
    rw [eval_band,Bool.and_eq_true,equalOn_value,equalOn_value,powOn_value _ _ _ _ hm,hd,
      eval_comp,eval_pair,mod_word,BitVec.toNat_umod,wordConstant_eval,wordConstant_eval,
      BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.zero_mod,Nat.mod_eq_of_lt h1]
  simp only [stripOn,wordMux_eval]
  split_ifs with hh
  · rw [hd,stripPrimeNat,ite_eq_left (hc.mp hh)]
  · rw [stripPrimeNat,ite_eq_right (fun h => hh (hc.mpr h))]

def stripStepBound (w c : ℕ) : ℕ := 9*c+4000*w^3+1500*w^2+500*w+100

lemma stripOn_count {k w c : ℕ} (a m q v : BooleanNetwork k w)
    (ha : a.net.count ≤ c) (hm : m.net.count ≤ c) (hq : q.net.count ≤ c) (hv : v.net.count ≤ c) :
    (stripOn a m q v).net.count ≤ stripStepBound w c := by
  have hdiv := div_count w
  have hmod := mod_count w
  have hpow := powOn_count a m ((v.pair q).comp (div w))
  have he0 := equalOn_count ((v.pair q).comp (mod w)) (wordConstant (n:=k) (BitVec.ofNat w 0))
  have he1 := equalOn_count (powOn a m ((v.pair q).comp (div w))) (wordConstant (n:=k) (BitVec.ofNat w 1))
  simp only [count_comp,count_pair,wordConstant_count] at hpow he0 he1
  simp only [stripOn,wordMux_count,count_band,count_comp,count_pair]
  dsimp [stripStepBound]
  nlinarith

/-- The original input stays read-only; the accumulator is updated once. -/
def stripUpdate {k w : ℕ} (a m q : BooleanNetwork k w) : BooleanNetwork (k+w) (k+w) :=
  (select (Fin.castAdd w)).pair (stripOn (liftInput a (Fin.castAdd w))
    (liftInput m (Fin.castAdd w)) (liftInput q (Fin.castAdd w)) (select (Fin.natAdd k)))

lemma stripUpdate_value {k w : ℕ} (a m q : BooleanNetwork k w) (x : Basis k) (z : Basis w)
    (hm : 2 ≤ (bitsValue (m.eval x)).toNat) :
    ∃ z', (stripUpdate a m q).eval (Fin.append x z)=Fin.append x z' ∧
      (bitsValue z').toNat=stripPrimeNat (bitsValue (a.eval x)).toNat (bitsValue (m.eval x)).toNat
        (bitsValue (q.eval x)).toNat (bitsValue z).toNat := by
  let v := stripOn (liftInput a (Fin.castAdd w)) (liftInput m (Fin.castAdd w))
      (liftInput q (Fin.castAdd w)) (select (Fin.natAdd k))
  have hx : Fin.append x z ∘ Fin.castAdd w=x := by funext i; exact Fin.append_left _ _ i
  have hz : Fin.append x z ∘ Fin.natAdd k=z := by funext i; exact Fin.append_right _ _ i
  refine ⟨v.eval (Fin.append x z),?_,?_⟩
  · simp only [stripUpdate,eval_pair,eval_select,hx]
    rfl
  · have hh := stripOn_value (liftInput a (Fin.castAdd w)) (liftInput m (Fin.castAdd w))
      (liftInput q (Fin.castAdd w)) (select (Fin.natAdd k)) (Fin.append x z)
      (by simpa only [liftInput_eval,hx] using hm)
    simpa only [liftInput_eval,eval_select,hx,hz] using hh

lemma stripUpdate_count {k w c : ℕ} (a m q : BooleanNetwork k w)
    (ha : a.net.count ≤ c) (hm : m.net.count ≤ c) (hq : q.net.count ≤ c) :
    (stripUpdate a m q).net.count ≤ stripStepBound w c := by
  simp only [stripUpdate,count_pair,count_select,zero_add]
  exact stripOn_count _ _ _ _ (by simpa using ha) (by simpa using hm) (by simpa using hq) (by simp)

def stripScan {k w : ℕ} (a m : BooleanNetwork k w) : List (BooleanNetwork k w)→BooleanNetwork (k+w) (k+w)
  | [] => select id
  | q::qs => (stripUpdate a m q).comp (stripScan a m qs)

lemma stripScan_count {k w c : ℕ} (a m : BooleanNetwork k w) (qs : List (BooleanNetwork k w))
    (ha : a.net.count ≤ c) (hm : m.net.count ≤ c) (hq : ∀ q∈qs,q.net.count ≤ c) :
    (stripScan a m qs).net.count ≤ qs.length*stripStepBound w c := by
  induction qs with
  | nil => simp [stripScan]
  | cons q qs ih =>
    have hh := stripUpdate_count a m q ha hm (hq q (by simp))
    have ht := ih (fun r hr => hq r (by simp [hr]))
    simp only [stripScan,count_comp,List.length_cons]
    nlinarith

lemma stripScan_unit {k w m : ℕ} (hm : 2 ≤ m) (aN mN : BooleanNetwork k w)
    (u : (ZMod m)ˣ) (qs : List (BooleanNetwork k w)) (x : Basis k) (z : Basis w)
    (ha : ((bitsValue (aN.eval x)).toNat : ZMod m)=(u : ZMod m))
    (hmN : (bitsValue (mN.eval x)).toNat=m) :
    ∃ z', (stripScan aN mN qs).eval (Fin.append x z)=Fin.append x z' ∧
      (bitsValue z').toNat=stripOrderFactors u (qs.map (fun q => (bitsValue (q.eval x)).toNat)) (bitsValue z).toNat := by
  induction qs generalizing z with
  | nil => exact ⟨z,by simp [stripScan],rfl⟩
  | cons q qs ih =>
    obtain ⟨z₁,hz₁,hv₁⟩ := stripUpdate_value aN mN q x z (by omega)
    obtain ⟨z₂,hz₂,hv₂⟩ := ih z₁
    refine ⟨z₂,?_,?_⟩
    · rw [stripScan,eval_comp,hz₁,hz₂]
    · rw [hv₂,hv₁,hmN,stripPrimeNat_unit hm u ha]
      rfl

/-- Exact order from the completed data, by explicit polynomial-size Boolean
networks of division and repeated modular squaring. -/
theorem stripScan_exact {k w m : ℕ} (hm : 2 ≤ m) (aN mN : BooleanNetwork k w)
    (u : (ZMod m)ˣ) (qs : List (BooleanNetwork k w)) (x : Basis k) (z : Basis w)
    (ha : ((bitsValue (aN.eval x)).toNat : ZMod m)=(u : ZMod m))
    (hmN : (bitsValue (mN.eval x)).toNat=m) (hz : (bitsValue z).toNat=m.totient)
    (hp : ∀ q∈qs, ((bitsValue (q.eval x)).toNat).Prime)
    (hprod : (qs.map (fun q => (bitsValue (q.eval x)).toNat)).prod=m.totient) :
    ∃ z', (stripScan aN mN qs).eval (Fin.append x z)=Fin.append x z' ∧ (bitsValue z').toNat=orderOf u := by
  obtain ⟨z',he,hv⟩ := stripScan_unit hm aN mN u qs x z ha hmN
  refine ⟨z',he,?_⟩
  rw [hv,hz]
  apply strip_totient_factors hm u _ _ hprod
  intro p hp'
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp'
  exact hp q hq

end BitArithmetic
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/LabelValidationCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

/-- Every returned denominator, in EVERY mode, undergoes the full arithmetic
check. No primality or order oracle appears in the network. -/
def labelValidNet {k w : ℕ} (n : ℕ) (a m d j : BooleanNetwork k w) : BooleanNetwork k 1 :=
  (wordLt (wordConstant (BitVec.ofNat w 0)) d).band
    ((wordLt d (wordConstant (BitVec.ofNat w (2^n)))).band
      ((wordLt j d).band
        ((equalOn ((j.pair d).comp (gcdNet w)) (wordConstant (BitVec.ofNat w 1))).band
          (equalOn (powOn a m d) (wordConstant (BitVec.ofNat w 1))))))

lemma labelValidNet_value {k w : ℕ} (n : ℕ) (a m d j : BooleanNetwork k w)
    (hn : n<w) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (labelValidNet n a m d j).eval x 0=true ↔
      ValidLabel n (bitsValue (a.eval x)).toNat (bitsValue (m.eval x)).toNat
        (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat := by
  have hp : 1<2^w := Nat.one_lt_two_pow (by omega)
  have hB : 2^n<2^w := Nat.pow_lt_pow_right (by decide) hn
  simp only [labelValidNet,eval_band,Bool.and_eq_true,wordLt_eval,decide_eq_true_eq,
    equalOn_value,eval_comp,eval_pair,gcdNet_value,powOn_value a m d x hm,
    wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod,Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt hB,
    ValidLabel,Nat.Coprime]

lemma labelValidNet_count {k w c : ℕ} (n : ℕ) (a m d j : BooleanNetwork k w)
    (ha : a.net.count≤c) (hm : m.net.count≤c) (hd : d.net.count≤c) (hj : j.net.count≤c) :
    (labelValidNet n a m d j).net.count ≤
      9*c+2*w*(216*w*w+300*w+100)+w+w*(3672*w*w+436*w+36)+344*w+70 := by
  have h0 := wordLt_count (wordConstant (n:=k) (BitVec.ofNat w 0)) d
  have hB := wordLt_count d (wordConstant (n:=k) (BitVec.ofNat w (2^n)))
  have hjd := wordLt_count j d
  have hg := equalOn_count ((j.pair d).comp (gcdNet w)) (wordConstant (n:=k) (BitVec.ofNat w 1))
  have hp := equalOn_count (powOn a m d) (wordConstant (n:=k) (BitVec.ofNat w 1))
  have hgc := gcdNet_count w
  have hpow := powOn_count a m d
  simp only [count_comp,count_pair,wordConstant_count] at h0 hB hjd hg hp
  simp only [labelValidNet,count_band]
  omega

end ExactQuantumFactoring.OrderTrial


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RationalConditionals.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace IntExpr
variable {v : Type*}

def ifLe (a b c d : IntExpr v) : IntExpr v :=
  iteLe (.add a.pos b.neg) (.add b.pos a.neg) c d
@[simp] lemma eval_ifLe (x : v → ℕ) (a b c d : IntExpr v) :
    (ifLe a b c d).eval x = if a.eval x ≤ b.eval x then c.eval x else d.eval x := by
  simp only [ifLe,eval_iteLe,NatExpr.eval]
  have he : a.pos.eval x+b.neg.eval x ≤ b.pos.eval x+a.neg.eval x ↔ a.eval x ≤ b.eval x := by
    simp only [eval]
    omega
  simp only [he]
end IntExpr

namespace RatExpr
variable {v : Type*}

def ifNatLe (a b : NatExpr v) (c d : RatExpr v) : RatExpr v :=
  ⟨IntExpr.iteLe a b c.num d.num,.iteLe a b c.den d.den⟩
@[simp] lemma eval_ifNatLe (x : v → ℕ) (a b : NatExpr v) (c d : RatExpr v) :
    (ifNatLe a b c d).eval x = if a.eval x ≤ b.eval x then c.eval x else d.eval x := by
  by_cases h : a.eval x ≤ b.eval x
  · simp [ifNatLe,eval,NatExpr.eval,h]
  · simp [ifNatLe,eval,NatExpr.eval,h]

def ifIntLe (a b : IntExpr v) (c d : RatExpr v) : RatExpr v :=
  ifNatLe (.add a.pos b.neg) (.add b.pos a.neg) c d
@[simp] lemma eval_ifIntLe (x : v → ℕ) (a b : IntExpr v) (c d : RatExpr v) :
    (ifIntLe a b c d).eval x = if a.eval x ≤ b.eval x then c.eval x else d.eval x := by
  rw [ifIntLe,eval_ifNatLe]
  simp only [NatExpr.eval]
  have hh : a.pos.eval x+b.neg.eval x ≤ b.pos.eval x+a.neg.eval x ↔ a.eval x ≤ b.eval x := by
    simp only [IntExpr.eval]
    omega
  simp only [hh]

def ifLe (a b c d : RatExpr v) : RatExpr v :=
  let a := a.normalize
  let b := b.normalize
  ifIntLe (a.num.scale b.den) (b.num.scale a.den) c d
@[simp] lemma eval_ifLe (x : v → ℕ) (a b c d : RatExpr v) :
    (ifLe a b c d).eval x = if a.eval x ≤ b.eval x then c.eval x else d.eval x := by
  rw [ifLe,eval_ifIntLe]
  simp only [IntExpr.eval_scale]
  have ha : (0 : ℚ) < a.normalize.den.eval x := by exact_mod_cast normalize_den_pos x a
  have hb : (0 : ℚ) < b.normalize.den.eval x := by exact_mod_cast normalize_den_pos x b
  have he : a.normalize.num.eval x * b.normalize.den.eval x ≤
      b.normalize.num.eval x * a.normalize.den.eval x ↔ a.eval x ≤ b.eval x := by
    rw [← eval_normalize x a,← eval_normalize x b,eval,eval,div_le_div_iff₀ ha hb]
    norm_cast
  simp only [he]

def ifLt (a b c d : RatExpr v) : RatExpr v := ifLe b a d c
def ifEq (a b c d : RatExpr v) : RatExpr v := ifLe a b (ifLe b a c d) d
def max (a b : RatExpr v) : RatExpr v := ifLe a b b a
def min (a b : RatExpr v) : RatExpr v := ifLe a b a b
@[simp] lemma eval_ifLt (x : v → ℕ) (a b c d : RatExpr v) :
    (ifLt a b c d).eval x = if a.eval x < b.eval x then c.eval x else d.eval x := by
  simp only [ifLt,eval_ifLe]
  by_cases h : a.eval x < b.eval x
  · simp [h,not_le.mpr h]
  · simp [h,le_of_not_gt h]
@[simp] lemma eval_ifEq (x : v → ℕ) (a b c d : RatExpr v) :
    (ifEq a b c d).eval x = if a.eval x = b.eval x then c.eval x else d.eval x := by
  simp only [ifEq,eval_ifLe]
  by_cases h : a.eval x = b.eval x
  · simp [h]
  · by_cases h₁ : a.eval x ≤ b.eval x
    · have h₂ : ¬b.eval x ≤ a.eval x := fun hh => h (le_antisymm h₁ hh)
      simp [h,h₁,h₂]
    · simp [h,h₁]
@[simp] lemma eval_max (x : v → ℕ) (a b : RatExpr v) : (max a b).eval x=Max.max (a.eval x) (b.eval x) := by
  simp [max,_root_.max_def]
@[simp] lemma eval_min (x : v → ℕ) (a b : RatExpr v) : (min a b).eval x=Min.min (a.eval x) (b.eval x) := by
  simp [min,_root_.min_def]
end RatExpr
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ProgressionEvaluation.lean =====
namespace OAI

section
open scoped BigOperators


/-! Constant-length exact evaluation of the selected arithmetic progression.
The exponentially many progression points are replaced by seven truncated
arithmetic sums. This is the explicit arithmetic behind source Lemma 4.1. -/
namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Five fixed terms, of which only the constant and linear ones are nonzero. -/
def linearSum (a b : ℚ) (lo hi : ℕ) : ℚ :=
  fiveTermSum (fun q => if q=0 then a else if q=1 then b else 0) lo hi

lemma linearSum_correct (a b : ℚ) (lo hi : ℕ) :
    linearSum a b lo hi = ∑ i ∈ Finset.Ico lo hi, (a+b*i) := by
  rw [linearSum,fiveTermSum_correct]
  apply Finset.sum_congr rfl
  intro i _
  norm_num [Finset.sum_range_succ]

/-- A ramp can change sign only once along an arithmetic progression. -/
def rampSum (a b : ℚ) (M : ℕ) : ℚ :=
  if 0 < b then linearSum a b (Int.ceil (-a/b)).toNat M
  else if b < 0 then linearSum a b 0 (min M (Int.ceil (-a/b)).toNat)
  else M*max 0 a

lemma sum_ramp_filter_nonneg (a b : ℚ) (M : ℕ) :
    (∑ i ∈ Finset.range M, max 0 (a+b*i)) =
      ∑ i ∈ (Finset.range M).filter (fun i : ℕ => 0 ≤ a+b*(i:ℚ)), (a+b*i) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 ≤ a+b*i
  · rw [ite_eq_left h,max_eq_right h]
  · rw [ite_eq_right h,max_eq_left (le_of_not_ge h)]

lemma sum_ramp_filter_pos (a b : ℚ) (M : ℕ) :
    (∑ i ∈ Finset.range M, max 0 (a+b*i)) =
      ∑ i ∈ (Finset.range M).filter (fun i : ℕ => 0 < a+b*(i:ℚ)), (a+b*i) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 < a+b*i
  · rw [ite_eq_left h,max_eq_right h.le]
  · rw [ite_eq_right h,max_eq_left (le_of_not_gt h)]

lemma rampSum_correct (a b : ℚ) (M : ℕ) :
    rampSum a b M = ∑ i ∈ Finset.range M, max 0 (a+b*i) := by
  unfold rampSum
  split_ifs with hp hn
  · rw [linearSum_correct,sum_ramp_filter_nonneg]
    congr 1
    ext i
    simp only [Finset.mem_Ico,Finset.mem_filter,Finset.mem_range,
      Int.toNat_le,Int.ceil_le,Int.cast_natCast,div_le_iff₀ hp]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  · rw [linearSum_correct,sum_ramp_filter_pos]
    congr 1
    ext i
    simp only [Finset.mem_Ico,Finset.mem_filter,Finset.mem_range,
      zero_le, true_and,lt_min_iff,Int.lt_toNat,Int.lt_ceil,Int.cast_natCast,
      lt_div_iff_of_neg hn]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  · have hb : b=0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
    simp [hb]

/-- The real coordinate of the seven-ramp spline derivative summed exactly. -/
def phaseSumRe (a b : ℚ) (M : ℕ) : ℚ :=
  -(M:ℚ)+4*linearSum (a+1/2) b 0 M-8*rampSum a b M+
    8*rampSum (a-1/2) b M-8*rampSum (a-1) b M

def phaseSumIm (a b : ℚ) (M : ℕ) : ℚ :=
  4*linearSum (a+1/2) b 0 M-8*rampSum (a+1/4) b M+
    8*rampSum (a-1/4) b M-8*rampSum (a-3/4) b M+
    8*rampSum (a-5/4) b M

lemma phaseSumRe_correct (a b : ℚ) (M : ℕ) :
    (phaseSumRe a b M : ℝ) =
      ∑ i ∈ Finset.range M, splineReDeriv ((a:ℝ)+(b:ℝ)*i) := by
  simp only [phaseSumRe,linearSum_correct,rampSum_correct,
    Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_neg,Rat.cast_natCast,
    Rat.cast_ofNat,Rat.cast_div,Rat.cast_one,Rat.cast_sum,Rat.cast_max,Rat.cast_zero,
    Nat.Ico_zero_eq_range,splineReDeriv,sub_add_eq_add_sub,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    Finset.sum_neg_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  ring

lemma phaseSumIm_correct (a b : ℚ) (M : ℕ) :
    (phaseSumIm a b M : ℝ) =
      ∑ i ∈ Finset.range M, splineImDeriv ((a:ℝ)+(b:ℝ)*i) := by
  have hh' (i : ℕ) : (a:ℝ)+1/4+(b:ℝ)*i = (a:ℝ)+(b:ℝ)*i+1/4 := by ring
  simp only [phaseSumIm,linearSum_correct,rampSum_correct,
    Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,
    Rat.cast_ofNat,Rat.cast_div,Rat.cast_one,Rat.cast_sum,Rat.cast_max,Rat.cast_zero,
    Nat.Ico_zero_eq_range,splineImDeriv,hh',sub_add_eq_add_sub,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  ring

lemma phaseSum_correct (a b : ℚ) (M : ℕ)
    (h : ∀ i < M, -(1/2:ℝ) ≤ (a:ℝ)+(b:ℝ)*i ∧ (a:ℝ)+(b:ℝ)*i ≤ 3/2) :
    ((phaseSumRe a b M : ℚ):ℂ)+((phaseSumIm a b M : ℚ):ℂ)*Complex.I =
      ∑ i ∈ Finset.range M, phase ((a:ℝ)+(b:ℝ)*i) := by
  apply Complex.ext
  · simp only [Complex.add_re,Complex.mul_re,Complex.I_re,Complex.I_im,
      Complex.ratCast_re,Complex.ratCast_im,mul_zero,zero_mul,sub_self,add_zero,
      Complex.re_sum,phase]
    rw [phaseSumRe_correct]
    apply Finset.sum_congr rfl
    intro i hi
    exact splineReDeriv_eq (h i (Finset.mem_range.mp hi)).1 (h i (Finset.mem_range.mp hi)).2
  · simp only [Complex.add_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ratCast_re,Complex.ratCast_im,mul_zero,mul_one,add_zero,zero_add,
      Complex.im_sum,phase]
    rw [phaseSumIm_correct]
    apply Finset.sum_congr rfl
    intro i hi
    exact splineImDeriv_eq (h i (Finset.mem_range.mp hi)).1 (h i (Finset.mem_range.mp hi)).2

/-- Offset and slope are rational values of polynomial bit length, evaluated
using the arithmetic nearest-bin rule rather than any transcendental oracle. -/
def sampleOffset (Q d j t : ℕ) : ℚ :=
  (((j*t)%d:ℕ):ℚ)/d+binErrorRat Q d j*t/Q

def sampleSlope (Q d j : ℕ) : ℚ := binErrorRat Q d j*d/Q

lemma sampleLine_cast (Q d j t i : ℕ) :
    (sampleOffset Q d j t:ℝ)+(sampleSlope Q d j:ℝ)*i =
      ((j*t)%d:ℕ)/(d:ℝ)+binError Q d j*((t:ℝ)/Q+(i:ℝ)*((d:ℝ)/Q)) := by
  simp only [sampleOffset,sampleSlope,Rat.cast_add,Rat.cast_div,Rat.cast_mul,
    Rat.cast_natCast,binErrorRat_cast]
  ring

lemma sampleLine_bounds {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j i : ℕ) (hi : i < sampleCount Q d t) :
    -(1/2:ℝ) ≤ (sampleOffset Q d j t:ℝ)+(sampleSlope Q d j:ℝ)*i ∧
      (sampleOffset Q d j t:ℝ)+(sampleSlope Q d j:ℝ)*i ≤ 3/2 := by
  rw [sampleLine_cast]
  have hQ : (0:ℝ) < Q := by exact_mod_cast lt_of_lt_of_le hd hdQ
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hu : (0:ℝ) ≤ ((j*t)%d:ℕ)/(d:ℝ) := by positivity
  have hu' : ((j*t)%d:ℕ)/(d:ℝ) < 1 := by
    rw [div_lt_one hd']
    exact_mod_cast Nat.mod_lt (j*t) hd
  have hv : (0:ℝ) ≤ (t:ℝ)/Q+(i:ℝ)*((d:ℝ)/Q) := by positivity
  have hv' : (t:ℝ)/Q+(i:ℝ)*((d:ℝ)/Q) ≤ 1 := by
    have h := (lt_sampleCount_iff hd hdQ ht).mp hi
    have h' : (t:ℝ)+i*d ≤ Q := by exact_mod_cast h.le
    have he : (t:ℝ)/Q+(i:ℝ)*((d:ℝ)/Q) = ((t:ℝ)+i*d)/Q := by ring
    rw [he,div_le_one hQ]
    exact h'
  rcases abs_le.mp (binError_bound (Q:=Q) (j:=j) hd) with ⟨he₀,he₁⟩
  have hm₀ := mul_le_mul_of_nonneg_right he₀ hv
  have hm₁ := mul_le_mul_of_nonneg_right he₁ hv
  constructor <;> nlinarith

/-- Constant-piece rational P: seven ramp sums, hence no loop of length Q or d. -/
def fastResidueProbability (Q d j t : ℕ) : ℚ :=
  let a := sampleOffset Q d j t
  let b := sampleSlope Q d j
  let M := sampleCount Q d t
  (phaseSumRe a b M ^ 2 + phaseSumIm a b M ^ 2)/(Q:ℚ)^2

lemma residueAmplitude_fast {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j : ℕ) :
    residueAmplitude Q d j t = (Q:ℂ)⁻¹ *
      ((phaseSumRe (sampleOffset Q d j t) (sampleSlope Q d j) (sampleCount Q d t):ℂ)+
        (phaseSumIm (sampleOffset Q d j t) (sampleSlope Q d j) (sampleCount Q d t):ℂ)*Complex.I) := by
  rw [phaseSum_correct _ _ _ (fun i hi => sampleLine_bounds hd hdQ ht j i hi),
    residueAmplitude_samples hd hdQ ht]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [sampleLine_cast]

lemma fastResidueProbability_correct {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j : ℕ) :
    (fastResidueProbability Q d j t:ℝ) = residueProbability Q d j t := by
  rw [residueProbability,residueAmplitude_fast hd hdQ ht]
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_mul,Complex.normSq_inv]
  simp [fastResidueProbability,Complex.normSq_apply,div_eq_mul_inv,pow_two]
  ring

lemma fastResidueProbability_eq {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j : ℕ) :
    fastResidueProbability Q d j t = residueProbabilityRat Q d j t := by
  apply Rat.cast_injective (α:=ℝ)
  rw [fastResidueProbability_correct hd hdQ ht,
    residueProbabilityRat_cast (lt_of_lt_of_le hd hdQ)]

end ExactQuantumFactoring.OrderTrial


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ProgressionExpressions.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace NatExpr
variable {v : Type*}
def min (a b : NatExpr v) : NatExpr v := .iteLe a b a b
def max (a b : NatExpr v) : NatExpr v := .iteLe a b b a
@[simp] lemma eval_min (x : v → ℕ) (a b : NatExpr v) : (min a b).eval x=Min.min (a.eval x) (b.eval x) := by
  simp [min,eval,min_def]
@[simp] lemma eval_max (x : v → ℕ) (a b : NatExpr v) : (max a b).eval x=Max.max (a.eval x) (b.eval x) := by
  simp [max,eval,max_def]
end NatExpr

namespace OrderTrial.Expressions
variable {v : Type*}
open RatExpr

def powerSum (q : ℕ) (M : RatExpr v) : RatExpr v := match q with
  | 0 => M
  | 1 => M*(M-1)/2
  | 2 => M*(M-1)*(2*M-1)/6
  | 3 => (M*(M-1)/2)^2
  | 4 => M*(M-1)*(2*M-1)*(3*M^2-3*M-1)/30
  | _ => 0
lemma powerSum_correct (x : v → ℕ) (q : ℕ) (M : RatExpr v) :
    (powerSum q M).eval x=powerSumValue q (M.eval x) := by
  rcases q with _|_|_|_|_|q <;> simp [powerSum,powerSumValue]

def fiveTerm (a : ℕ → RatExpr v) (lo hi : NatExpr v) : RatExpr v :=
  ifNatLe lo hi (RatExpr.sum (fun q => a q*(powerSum q (ofNat hi)-powerSum q (ofNat lo))) 5) 0
lemma fiveTerm_correct (x : v → ℕ) (a : ℕ → RatExpr v) (lo hi : NatExpr v) :
    (fiveTerm a lo hi).eval x=fiveTermSum (fun q => (a q).eval x) (lo.eval x) (hi.eval x) := by
  simp [fiveTerm,fiveTermSum,powerSum_correct]

def linear (a b : RatExpr v) (lo hi : NatExpr v) : RatExpr v :=
  fiveTerm (fun q => if q=0 then a else if q=1 then b else 0) lo hi
lemma linear_correct (x : v → ℕ) (a b : RatExpr v) (lo hi : NatExpr v) :
    (linear a b lo hi).eval x=linearSum (a.eval x) (b.eval x) (lo.eval x) (hi.eval x) := by
  rw [linear,fiveTerm_correct,linearSum]
  congr 1
  funext q
  split_ifs <;> simp

def ramp (a b : RatExpr v) (M : NatExpr v) : RatExpr v :=
  ifLt 0 b (linear a b ((-a/b).ceilNat) M)
    (ifLt b 0 (linear a b (.const 0) (NatExpr.min M (-a/b).ceilNat))
      (ofNat M*RatExpr.max 0 a))
lemma ramp_correct (x : v → ℕ) (a b : RatExpr v) (M : NatExpr v) :
    (ramp a b M).eval x=rampSum (a.eval x) (b.eval x) (M.eval x) := by
  simp [ramp,rampSum,linear_correct,NatExpr.eval]

def phaseRe (a b : RatExpr v) (M : NatExpr v) : RatExpr v :=
  -ofNat M+4*linear (a+1/2) b (.const 0) M-8*ramp a b M+
    8*ramp (a-1/2) b M-8*ramp (a-1) b M
lemma phaseRe_correct (x : v → ℕ) (a b : RatExpr v) (M : NatExpr v) :
    (phaseRe a b M).eval x=phaseSumRe (a.eval x) (b.eval x) (M.eval x) := by
  simp [phaseRe,phaseSumRe,linear_correct,ramp_correct,NatExpr.eval]

def phaseIm (a b : RatExpr v) (M : NatExpr v) : RatExpr v :=
  4*linear (a+1/2) b (.const 0) M-8*ramp (a+1/4) b M+
    8*ramp (a-1/4) b M-8*ramp (a-3/4) b M+8*ramp (a-5/4) b M
lemma phaseIm_correct (x : v → ℕ) (a b : RatExpr v) (M : NatExpr v) :
    (phaseIm a b M).eval x=phaseSumIm (a.eval x) (b.eval x) (M.eval x) := by
  simp [phaseIm,phaseSumIm,linear_correct,ramp_correct,NatExpr.eval]

def binE (Q d j : NatExpr v) : NatExpr v :=
  .div (.add (.mul (.mul (.const 2) j) Q) d) (.mul (.const 2) d)
lemma binE_correct (x : v → ℕ) (Q d j : NatExpr v) :
    (binE Q d j).eval x=bin (Q.eval x) (d.eval x) (j.eval x) := rfl

def error (Q d j : NatExpr v) : RatExpr v := ofNat (binE Q d j)-ofNat j*ofNat Q/ofNat d
lemma error_correct (x : v → ℕ) (Q d j : NatExpr v) :
    (error Q d j).eval x=binErrorRat (Q.eval x) (d.eval x) (j.eval x) := by
  simp [error,binErrorRat,binE_correct]

def offset (Q d j t : NatExpr v) : RatExpr v :=
  ofNat (.mod (.mul j t) d)/ofNat d+error Q d j*ofNat t/ofNat Q
lemma offset_correct (x : v → ℕ) (Q d j t : NatExpr v) :
    (offset Q d j t).eval x=sampleOffset (Q.eval x) (d.eval x) (j.eval x) (t.eval x) := by
  simp [offset,sampleOffset,error_correct,NatExpr.eval]

def slope (Q d j : NatExpr v) : RatExpr v := error Q d j*ofNat d/ofNat Q
lemma slope_correct (x : v → ℕ) (Q d j : NatExpr v) :
    (slope Q d j).eval x=sampleSlope (Q.eval x) (d.eval x) (j.eval x) := by
  simp [slope,sampleSlope,error_correct]

def count (Q d t : NatExpr v) : NatExpr v := .add (.div (.sub (.sub Q (.const 1)) t) d) (.const 1)
lemma count_correct (x : v → ℕ) (Q d t : NatExpr v) :
    (count Q d t).eval x=sampleCount (Q.eval x) (d.eval x) (t.eval x) := rfl

/-- A literal finite arithmetic template for P. Its size is independent of Q,
B,d,j,t; there is no enumeration of the phase-register range. -/
def probability (Q d j t : NatExpr v) : RatExpr v :=
  (phaseRe (offset Q d j t) (slope Q d j) (count Q d t)^2+
   phaseIm (offset Q d j t) (slope Q d j) (count Q d t)^2)/(ofNat Q)^2
lemma probability_correct (x : v → ℕ) (Q d j t : NatExpr v) :
    (probability Q d j t).eval x=fastResidueProbability (Q.eval x) (d.eval x) (j.eval x) (t.eval x) := by
  simp [probability,fastResidueProbability,phaseRe_correct,phaseIm_correct,
    offset_correct,slope_correct,count_correct]
end OrderTrial.Expressions
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PolynomialFilterExpressions.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace NatExpr
variable {v : Type*}
def pow (a : NatExpr v) : ℕ → NatExpr v
  | 0 => .const 1
  | n+1 => .mul (pow a n) a
@[simp] lemma eval_pow (x : v → ℕ) (a : NatExpr v) (n : ℕ) :
    (pow a n).eval x=(a.eval x)^n := by
  induction n with
  | zero => simp [pow,eval]
  | succ n ih => simp [pow,eval,ih,pow_succ]
end NatExpr

namespace RatExpr
variable {v : Type*}
def sumList {α : Type*} (f : α → RatExpr v) : List α → RatExpr v
  | [] => 0
  | a::as => f a+sumList f as
@[simp] lemma eval_sumList {α : Type*} (x : v → ℕ) (f : α → RatExpr v) (as : List α) :
    (sumList f as).eval x=(as.map (fun a => (f a).eval x)).sum := by
  induction as with
  | nil => simp [sumList]
  | cons a as ih => simp [sumList,ih]
end RatExpr

namespace OrderTrial.Expressions
variable {v : Type*}
open RatExpr

def rampPoly (q a : ℤ) : PolyExpr v :=
  if a ≤ q then (.X-.const ((a:ℚ)/4))^2 else 0
def rampLin (q a : ℤ) : PolyExpr v :=
  if a ≤ q then .X-.const ((a:ℚ)/4) else 0
lemma rampPoly_correct (x : v → ℕ) (q a : ℤ) :
    (rampPoly q a).eval x=rampPiece q a := by
  by_cases h : a ≤ q <;> simp [rampPoly,rampPiece,h,PolyExpr.eval]
lemma rampLin_correct (x : v → ℕ) (q a : ℤ) :
    (rampLin q a).eval x=rampLinear q a := by
  by_cases h : a ≤ q <;> simp [rampLin,rampLinear,h,PolyExpr.eval]

def splineRePoly (q : ℤ) : PolyExpr v :=
  -(.X+.const (1/2))+2*(.X+.const (1/2))^2-4*rampPoly q 0+
    4*rampPoly q 2-4*rampPoly q 4
def splineImPoly (q : ℤ) : PolyExpr v :=
  2*(.X+.const (1/2))^2-4*rampPoly q (-1)+4*rampPoly q 1-
    4*rampPoly q 3+4*rampPoly q 5-.const (1/4)
def phaseRePoly (q : ℤ) : PolyExpr v :=
  -1+4*(.X+.const (1/2))-8*rampLin q 0+8*rampLin q 2-8*rampLin q 4
def phaseImPoly (q : ℤ) : PolyExpr v :=
  4*(.X+.const (1/2))-8*rampLin q (-1)+8*rampLin q 1-
    8*rampLin q 3+8*rampLin q 5
lemma splineRePoly_correct (x : v → ℕ) (q : ℤ) :
    (splineRePoly q).eval x=splineRePiece q := by
  simp [splineRePoly,splineRePiece,rampPoly_correct,PolyExpr.eval]
lemma splineImPoly_correct (x : v → ℕ) (q : ℤ) :
    (splineImPoly q).eval x=splineImPiece q := by
  simp [splineImPoly,splineImPiece,rampPoly_correct,PolyExpr.eval]
lemma phaseRePoly_correct (x : v → ℕ) (q : ℤ) :
    (phaseRePoly q).eval x=phaseRePiece q := by
  simp [phaseRePoly,phaseRePiece,rampLin_correct,PolyExpr.eval]
lemma phaseImPoly_correct (x : v → ℕ) (q : ℤ) :
    (phaseImPoly q).eval x=phaseImPiece q := by
  simp [phaseImPoly,phaseImPiece,rampLin_correct,PolyExpr.eval]

def linearPoly (d : NatExpr v) (η : RatExpr v) : PolyExpr v := .C ((ofNat d)⁻¹)*.X+.C η
lemma linearPoly_correct (x : v → ℕ) (d : NatExpr v) (η : RatExpr v) :
    (linearPoly d η).eval x=linearArg (d.eval x) (η.eval x) := by
  simp [linearPoly,linearArg,PolyExpr.eval]

def integralZero (d : NatExpr v) (A : PolyExpr v) : PolyExpr v :=
  .C ((ofNat d)⁻¹)*A.comp (linearPoly d 0)
def integralSlope (d : NatExpr v) (η : RatExpr v) (G₀ G₁ : PolyExpr v) : PolyExpr v :=
  .C ((ofNat d*η)⁻¹)*(G₁.comp (linearPoly d η)-G₀.comp (linearPoly d 0))
def massZero (d : NatExpr v) (q₀ : ℤ) : PolyExpr v :=
  integralZero d (phaseRePoly q₀)^2+integralZero d (phaseImPoly q₀)^2
def massSlope (d : NatExpr v) (η : RatExpr v) (q₀ q₁ : ℤ) : PolyExpr v :=
  integralSlope d η (splineRePoly q₀) (splineRePoly q₁)^2+
  integralSlope d η (splineImPoly q₀) (splineImPoly q₁)^2

def massCoeff (d : NatExpr v) (η : RatExpr v) (q₀ q₁ : ℤ) (k : ℕ) : RatExpr v :=
  ifEq η 0 ((massZero d q₀).coeff k) ((massSlope d η q₀ q₁).coeff k)
lemma massCoeff_correct (x : v → ℕ) (d : NatExpr v) (η : RatExpr v) (q₀ q₁ : ℤ) (k : ℕ) :
    (massCoeff d η q₀ q₁ k).eval x=(massPiece (d.eval x) (η.eval x) q₀ q₁).coeff k := by
  by_cases h : η.eval x=0 <;>
    simp [massCoeff,RatExpr.eval_ifEq,PolyExpr.coeff_correct,h,massPiece,integralPiece,
      massZero,massSlope,integralZero,integralSlope,linearPoly_correct,
      phaseRePoly_correct,phaseImPoly_correct,splineRePoly_correct,splineImPoly_correct,
      PolyExpr.eval]

def rounded (D : NatExpr v) (a : RatExpr v) : RatExpr v :=
  ofInt (ofNat D*a).ceil/ofNat D
lemma rounded_correct (x : v → ℕ) (D : NatExpr v) (a : RatExpr v) :
    (rounded D a).eval x=roundCoeff (D.eval x) (a.eval x) := by
  simp [rounded,roundCoeff]

def roundingDen (Q B : NatExpr v) : NatExpr v := .mul Q (NatExpr.pow B 8)
lemma roundingDen_correct (x : v → ℕ) (Q B : NatExpr v) :
    (roundingDen Q B).eval x=Q.eval x*(B.eval x)^8 := by
  simp [roundingDen,NatExpr.eval]

def low (d : NatExpr v) (η : RatExpr v) (q : ℤ×ℤ) : NatExpr v :=
  NatExpr.max (ofNat d*const q.1/4).ceilNat (ofNat d*(const q.2/4-η)).ceilNat
def high (d : NatExpr v) (η : RatExpr v) (q : ℤ×ℤ) : NatExpr v :=
  NatExpr.min d (NatExpr.min (ofNat d*(const q.1+1)/4).ceilNat
    (ofNat d*((const q.2+1)/4-η)).ceilNat)
lemma low_correct (x : v → ℕ) (d : NatExpr v) (η : RatExpr v) (q : ℤ×ℤ) :
    (low d η q).eval x=pieceLo (d.eval x) (η.eval x) q := by
  simp [low,pieceLo,intervalLo]
lemma high_correct (x : v → ℕ) (d : NatExpr v) (η : RatExpr v) (q : ℤ×ℤ) :
    (high d η q).eval x=pieceHi (d.eval x) (η.eval x) q := by
  simp [high,pieceHi,intervalHi]

def pieceSum (Q B d j : NatExpr v) (q : ℤ×ℤ) : RatExpr v :=
  let η := error Q d j
  let lo := low d η q
  let hi := high d η q
  fiveTerm (fun k => rounded (roundingDen Q B) (massCoeff d η q.1 q.2 k)) lo hi+
    ofNat (.sub hi lo)*(64/ofNat Q)
lemma pieceSum_correct (x : v → ℕ) (Q B d j : NatExpr v) (q : ℤ×ℤ) :
    (pieceSum Q B d j q).eval x=packedPieceSum (Q.eval x) (B.eval x) (d.eval x) (j.eval x) q := by
  simp [pieceSum,packedPieceSum,fiveTerm_correct,rounded_correct,roundingDen_correct,
    massCoeff_correct,error_correct,low_correct,high_correct,NatExpr.eval]

/-- Literal fixed 32-piece table; no noncomputable Finset enumeration is used
by the circuit generator. -/
def quarterList : List (ℤ×ℤ) :=
  ([0,1,2,3] : List ℤ).flatMap (fun q => ([-2,-1,0,1,2,3,4,5] : List ℤ).map (q,·))
lemma quarterList_nodup : quarterList.Nodup := by decide
lemma quarterList_finset : quarterList.toFinset=quarterPairs := by decide

def majorantSumE (Q B d j : NatExpr v) : RatExpr v :=
  sumList (pieceSum Q B d j) quarterList/2
lemma majorantSumE_correct (x : v → ℕ) (Q B d j : NatExpr v) :
    (majorantSumE Q B d j).eval x=packedMajorantSum (Q.eval x) (B.eval x) (d.eval x) (j.eval x) := by
  simp only [majorantSumE,RatExpr.eval_over,RatExpr.eval_num,RatExpr.eval_sumList,
    pieceSum_correct,packedMajorantSum]
  rw [← List.sum_toFinset _ quarterList_nodup,quarterList_finset]
  norm_num

end OrderTrial.Expressions
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/DynamicMajorantExpressions.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial.Expressions
variable {v : Type*}
open RatExpr

def dynamicRamp (q : IntExpr v) (a : ℤ) : PolyExpr v :=
  .C (ifIntLe (.ofInt a) q 1 0)*(.X-.const ((a:ℚ)/4))^2
def dynamicRampLin (q : IntExpr v) (a : ℤ) : PolyExpr v :=
  .C (ifIntLe (.ofInt a) q 1 0)*(.X-.const ((a:ℚ)/4))
lemma dynamicRamp_correct (x : v → ℕ) (q : IntExpr v) (a : ℤ) :
    (dynamicRamp q a).eval x=rampPiece (q.eval x) a := by
  by_cases h : a ≤ q.eval x <;> simp [dynamicRamp,rampPiece,h,PolyExpr.eval]
lemma dynamicRampLin_correct (x : v → ℕ) (q : IntExpr v) (a : ℤ) :
    (dynamicRampLin q a).eval x=rampLinear (q.eval x) a := by
  by_cases h : a ≤ q.eval x <;> simp [dynamicRampLin,rampLinear,h,PolyExpr.eval]

def dynamicSplineRe (q : IntExpr v) : PolyExpr v :=
  -(.X+.const (1/2))+2*(.X+.const (1/2))^2-4*dynamicRamp q 0+
    4*dynamicRamp q 2-4*dynamicRamp q 4
def dynamicSplineIm (q : IntExpr v) : PolyExpr v :=
  2*(.X+.const (1/2))^2-4*dynamicRamp q (-1)+4*dynamicRamp q 1-
    4*dynamicRamp q 3+4*dynamicRamp q 5-.const (1/4)
def dynamicPhaseRe (q : IntExpr v) : PolyExpr v :=
  -1+4*(.X+.const (1/2))-8*dynamicRampLin q 0+8*dynamicRampLin q 2-8*dynamicRampLin q 4
def dynamicPhaseIm (q : IntExpr v) : PolyExpr v :=
  4*(.X+.const (1/2))-8*dynamicRampLin q (-1)+8*dynamicRampLin q 1-
    8*dynamicRampLin q 3+8*dynamicRampLin q 5
lemma dynamicSplineRe_correct (x : v → ℕ) (q : IntExpr v) :
    (dynamicSplineRe q).eval x=splineRePiece (q.eval x) := by
  simp [dynamicSplineRe,splineRePiece,dynamicRamp_correct,PolyExpr.eval]
lemma dynamicSplineIm_correct (x : v → ℕ) (q : IntExpr v) :
    (dynamicSplineIm q).eval x=splineImPiece (q.eval x) := by
  simp [dynamicSplineIm,splineImPiece,dynamicRamp_correct,PolyExpr.eval]
lemma dynamicPhaseRe_correct (x : v → ℕ) (q : IntExpr v) :
    (dynamicPhaseRe q).eval x=phaseRePiece (q.eval x) := by
  simp [dynamicPhaseRe,phaseRePiece,dynamicRampLin_correct,PolyExpr.eval]
lemma dynamicPhaseIm_correct (x : v → ℕ) (q : IntExpr v) :
    (dynamicPhaseIm q).eval x=phaseImPiece (q.eval x) := by
  simp [dynamicPhaseIm,phaseImPiece,dynamicRampLin_correct,PolyExpr.eval]


def dynamicMassZero (d : NatExpr v) (q₀ : IntExpr v) : PolyExpr v :=
  integralZero d (dynamicPhaseRe q₀)^2+integralZero d (dynamicPhaseIm q₀)^2
def dynamicMassSlope (d : NatExpr v) (η : RatExpr v) (q₀ q₁ : IntExpr v) : PolyExpr v :=
  integralSlope d η (dynamicSplineRe q₀) (dynamicSplineRe q₁)^2+
    integralSlope d η (dynamicSplineIm q₀) (dynamicSplineIm q₁)^2

def dynamicMassCoeff (d : NatExpr v) (η : RatExpr v) (q₀ q₁ : IntExpr v) (k : ℕ) : RatExpr v :=
  ifEq η 0 ((dynamicMassZero d q₀).coeff k) ((dynamicMassSlope d η q₀ q₁).coeff k)
lemma dynamicMassCoeff_correct (x : v → ℕ) (d : NatExpr v) (η : RatExpr v)
    (q₀ q₁ : IntExpr v) (k : ℕ) :
    (dynamicMassCoeff d η q₀ q₁ k).eval x=
      (massPiece (d.eval x) (η.eval x) (q₀.eval x) (q₁.eval x)).coeff k := by
  by_cases h : η.eval x=0 <;>
    simp [dynamicMassCoeff,RatExpr.eval_ifEq,PolyExpr.coeff_correct,h,massPiece,integralPiece,
      dynamicMassZero,dynamicMassSlope,integralZero,integralSlope,linearPoly_correct,
      dynamicPhaseRe_correct,dynamicPhaseIm_correct,dynamicSplineRe_correct,dynamicSplineIm_correct,
      PolyExpr.eval]

def quarter (a : RatExpr v) : IntExpr v := (4*a).floor
lemma quarter_correct (x : v → ℕ) (a : RatExpr v) :
    (quarter a).eval x=quarterIndex (a.eval x) := by simp [quarter,quarterIndex]

/-- Actual constant-depth arithmetic for U, including dynamic quarter selection.
No residue loop and no polynomial-valued oracle occurs in this expression. -/
def majorantE (Q B d j u : NatExpr v) : RatExpr v :=
  let η := error Q d j
  let q₀ := quarter (ofNat u/ofNat d)
  let q₁ := quarter (ofNat u/ofNat d+η)
  RatExpr.sum (fun k => rounded (roundingDen Q B) (dynamicMassCoeff d η q₀ q₁ k)*(ofNat u)^k) 5+
    64/ofNat Q
lemma majorantE_correct (x : v → ℕ) (Q B d j u : NatExpr v) :
    (majorantE Q B d j u).eval x=
      majorant (Q.eval x) (B.eval x) (d.eval x) (j.eval x) (u.eval x) := by
  simp [majorantE,majorant,roundedValue,selectedMass,rounded_correct,roundingDen_correct,
    dynamicMassCoeff_correct,error_correct,quarter_correct]

end ExactQuantumFactoring.OrderTrial.Expressions


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetentionExpressions.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial.Expressions
open RatExpr
variable {v : Type*}

/-- Bounded priority search for the least covering power of two.  The bounds
are compile-time constants, not exponentiation gates with variable exponents. -/
def coveringPow (d : NatExpr v) : ℕ → NatExpr v
  | 0 => .const 1
  | k+1 => .iteLe d (.const (2^k)) (coveringPow d k) (.const (2^(k+1)))
lemma coveringPow_correct (x : v → ℕ) (d : NatExpr v) (n : ℕ)
    (hd : d.eval x≤2^n) : (coveringPow d n).eval x=2^(Nat.clog 2 (d.eval x)) := by
  induction n with
  | zero =>
    have hc : Nat.clog 2 (d.eval x)=0 := Nat.eq_zero_of_le_zero (Nat.clog_le_of_le_pow hd)
    simp [coveringPow,NatExpr.eval,hc]
  | succ n ih =>
    change (if d.eval x≤2^n then (coveringPow d n).eval x else 2^(n+1))=_
    by_cases h : d.eval x≤2^n
    · rw [ite_eq_left h]; exact ih h
    · have hc : Nat.clog 2 (d.eval x)=n+1 := by
        have h₁ := Nat.clog_le_of_le_pow hd
        have h₂ := (Nat.lt_clog_iff_pow_lt (by omega : 1<2)).mpr (Nat.lt_of_not_ge h)
        omega
      rw [ite_eq_right h,hc]

def lambdaE (n : ℕ) (d : NatExpr v) : RatExpr v :=
  1/ofNat (.mul (.const 1024) (coveringPow d n))
lemma lambdaE_correct (x : v → ℕ) (n : ℕ) (d : NatExpr v) (hd : d.eval x≤2^n) :
    (lambdaE n d).eval x=prescribedMass (d.eval x) := by
  simp [lambdaE,coveringPow_correct x d n hd,prescribedMass,NatExpr.eval,pow_add]
  ring

def coefficientE (n : ℕ) (Q B d j : NatExpr v) : RatExpr v :=
  ofInt ((ofNat (.const (2^(10*n))) * lambdaE n d / majorantSumE Q B d j).floor) /
    ofNat (.const (2^(10*n)))
lemma coefficientE_correct (x : v → ℕ) (n : ℕ) (Q B d j : NatExpr v) (hd : d.eval x≤2^n) (hpos : 0<d.eval x) :
    (coefficientE n Q B d j).eval x=
      modeCoeff n (prescribedMass (d.eval x)) (majorantSum (Q.eval x) (B.eval x) (d.eval x) (j.eval x)) := by
  simp [coefficientE,lambdaE_correct x n d hd,majorantSumE_correct,packedMajorantSum_correct hpos,modeCoeff,NatExpr.eval,mul_div_assoc]

def remainderE (n : ℕ) (Q B d j : NatExpr v) : RatExpr v :=
  lambdaE n d - coefficientE n Q B d j * majorantSumE Q B d j
lemma remainderE_correct (x : v → ℕ) (n : ℕ) (Q B d j : NatExpr v) (hd : d.eval x≤2^n) (hpos : 0<d.eval x) :
    (remainderE n Q B d j).eval x=
      modeRemainder n (prescribedMass (d.eval x)) (majorantSum (Q.eval x) (B.eval x) (d.eval x) (j.eval x)) := by
  simp [remainderE,lambdaE_correct x n d hd,coefficientE_correct x n Q B d j hd hpos,
    majorantSumE_correct,packedMajorantSum_correct hpos,modeRemainder]

def discrepancyE (n : ℕ) (Q B d j t : NatExpr v) : RatExpr v :=
  2*(ofNat B)^3*(majorantE Q B d j (.mod (.mul j t) d)-probability Q d j t)*coefficientE n Q B d j
lemma discrepancyE_correct (x : v → ℕ) (n : ℕ) (Q B d j t : NatExpr v) (hd : d.eval x≤2^n)
    (hdt : 0<d.eval x) (ht : t.eval x<d.eval x) (hdQ : d.eval x≤Q.eval x) :
    (discrepancyE n Q B d j t).eval x =
      2*(B.eval x:ℚ)^3*(majorant (Q.eval x) (B.eval x) (d.eval x) (j.eval x)
        ((j.eval x*t.eval x)%d.eval x)-residueProbabilityRat (Q.eval x) (d.eval x) (j.eval x) (t.eval x))*
        modeCoeff n (prescribedMass (d.eval x)) (majorantSum (Q.eval x) (B.eval x) (d.eval x) (j.eval x)) := by
  simp [discrepancyE,majorantE_correct,coefficientE_correct x n Q B d j hd hdt,NatExpr.eval,
    probability_correct,fastResidueProbability_eq hdt hdQ ht]

def thirdRetentionE (n : ℕ) (Q B d j : NatExpr v) : RatExpr v :=
  4*(ofNat B)^2*remainderE n Q B d j
lemma thirdRetentionE_correct (x : v → ℕ) (n : ℕ) (Q B d j : NatExpr v) (hd : d.eval x≤2^n) (hpos : 0<d.eval x) :
    (thirdRetentionE n Q B d j).eval x=4*(B.eval x:ℚ)^2*
      modeRemainder n (prescribedMass (d.eval x)) (majorantSum (Q.eval x) (B.eval x) (d.eval x) (j.eval x)) := by
  simp [thirdRetentionE,remainderE_correct x n Q B d j hd hpos]

end ExactQuantumFactoring.OrderTrial.Expressions


end

end OAI


