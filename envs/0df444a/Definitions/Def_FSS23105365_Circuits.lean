-- Prove2me | Definitions.Def_FSS23105365_Circuits
-- name    : FSS23105365_Circuits
-- status  : Definition
-- author  : @YY
-- created : 2026-10-09T15:40:00.770827+00:00
-- url     : https://prove2.me/theorems/1cd9498e-ab03-43f1-85a1-61e680eb80dd
-- title:
--   Fair-bit Boolean circuits and finite output laws
-- statement:
--   A finite topologically ordered AND/OR/NOT circuit with constants, checked backward wire references, and designated outputs. AND/OR fan-in is unbounded. Input bits are independent fair bits. Depth is the maximum output gate depth; size counts inputs, gates, source wires and output wires. The output probability is its number of seed preimages divided by $2^r$. Exactness requires all outputs to encode outcomes and all outcome masses to match. Support preservation quantifies over every seed. Total variation is half the finite sum of absolute mass differences. Encoders are arbitrary at this foundational interface; each target uses its specified injective encoding.
-- source:
--   Jiarui Zhang, Chengwei Liang, Haozhe Jiang, Binhang Yuan, Jingzhao Zhang, Revision Provably Reduces Sequential Computation in Diffusion Language Models, Zenodo preprint, 2026-10-02, https://doi.org/10.5281/zenodo.23105365, Section 2, circuit model and Eq. (2); Appendix E.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

abbrev Bits (r : ℕ) := Fin r → Bool

inductive Gate where
  | constant (b : Bool)
  | neg (wire : ℕ)
  | conj (wires : List ℕ)
  | disj (wires : List ℕ)

def Gate.sources : Gate → List ℕ
  | .constant _ => []
  | .neg j => [j]
  | .conj js => js
  | .disj js => js

def Gate.eval (values : List Bool) : Gate → Bool
  | .constant b => b
  | .neg j => !(values.getD j false)
  | .conj js => js.all (fun j => values.getD j false)
  | .disj js => js.any (fun j => values.getD j false)

def Gate.depth (depths : List ℕ) (g : Gate) : ℕ :=
  1 + (g.sources.map (fun j => depths.getD j 0)).foldl max 0

/-- Gates are in topological order. Inputs have depth zero; each gate adds one.
The source lists permit unbounded fan-in. All sources must refer to earlier wires. -/
structure Circuit (Out : Type) where
  randomBits : ℕ
  gates : List Gate
  output : Out → ℕ
  gate_valid : ∀ i : Fin gates.length, ∀ j ∈ (gates.get i).sources,
    j < randomBits + i.val
  output_valid : ∀ o, output o < randomBits + gates.length

def Circuit.eval {Out : Type} (C : Circuit Out) (seed : Bits C.randomBits) : Out → Bool :=
  let values := C.gates.foldl (fun vs g => vs ++ [g.eval vs]) (List.ofFn seed)
  fun o => values.getD (C.output o) false

noncomputable def Circuit.depth {Out : Type} [Fintype Out] (C : Circuit Out) : ℕ := by
  classical
  exact
    let ds := C.gates.foldl (fun vs g => vs ++ [g.depth vs])
      (List.replicate C.randomBits 0)
    (List.ofFn (fun i : Fin (Fintype.card Out) =>
      ds.getD (C.output ((Fintype.equivFin Out).symm i)) 0)).foldl max 0

/-- Size counts inputs, gates, gate input wires, and output wires. -/
def Circuit.size {Out : Type} [Fintype Out] (C : Circuit Out) : ℕ :=
  C.randomBits + C.gates.length +
    (C.gates.map (fun g => g.sources.length)).sum + Fintype.card Out

noncomputable def mass {Out Ω : Type} [Fintype Ω]
    (C : Circuit Out) (encode : Ω → (Out → Bool)) (x : Ω) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun seed : Bits C.randomBits =>
    C.eval seed = encode x)).card : ℝ) / (2 : ℝ) ^ C.randomBits

def ValidOutputs {Out Ω : Type} (C : Circuit Out) (encode : Ω → (Out → Bool)) : Prop :=
  ∀ seed : Bits C.randomBits, ∃ x : Ω, C.eval seed = encode x

def ExactLaw {Out Ω : Type} [Fintype Ω] (C : Circuit Out)
    (encode : Ω → (Out → Bool)) (p : Ω → ℝ) : Prop :=
  ValidOutputs C encode ∧ ∀ x, mass C encode x = p x

def SupportPreserving {Out Ω : Type} (C : Circuit Out)
    (encode : Ω → (Out → Bool)) (p : Ω → ℝ) : Prop :=
  ∀ seed : Bits C.randomBits, ∃ x : Ω, C.eval seed = encode x ∧ 0 < p x

noncomputable def tv {Ω : Type} [Fintype Ω] (p q : Ω → ℝ) : ℝ :=
  (∑ x, |p x - q x|) / 2

end FSS23105365


