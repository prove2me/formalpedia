-- Prove2me | Definitions.Def_ApproxCountRwPHP_Unprovability_Priorities
-- name    : ApproxCountRwPHP_Unprovability_Priorities
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:58:55.757722+00:00
-- url     : https://prove2.me/theorems/228cd24d-713a-44bc-9134-7b3159769365
-- title:
--   Priority-order randomness, freshness, and traversal
-- statement:
--   A partial injection maps elements of [N] into an arbitrary infinite universe U. Fix an enumeration σ of an N-element subset S of U. A priority oracle gives each x in [N] an ordering of S and each X in U an ordering of [N]. The reference law is the full product of uniform measures on finite permutations.
--
--   Freshness requires that the map be an injection and the law be a probability measure, and that every finite family of unmatched coordinates have independent uniform orders. Traversal first matches each new argument into S, then matches the interpreted function value into [N], and follows the edge given by its preimage. A constant uses the same rule with zero arguments.
--
--   $$T^\omega(\pi)\quad\text{and}\quad\operatorname{out}^\omega(T,\pi)$$
--
--   The traversal returns an optional map and bit, making failure explicit when space is exhausted. The size hypotheses in the two source results exclude failure. Conditioning uses normalized restriction to the positive-probability traversal event.
-- source:
--   Oliver Korten, Jiatu Li, Igor Oliveira, Hanlin Ren, STOC 2027 submission #1023 (October 2026), §6.1, Observation 6.4, Lemma 6.5, printed p. 35–37, PDF p. 37–39; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1023.pdf#page=37–39

import Definitions.Def_ApproxCountRwPHP_Unprovability_Game

open MeasureTheory FirstOrder

namespace ApproxCountRwPHP.Unprovability

abbrev PartialMap (N : ℕ) (U : Type) := Fin N → Option U

def partialInjection {N : ℕ} {U : Type} (π : PartialMap N U) : Prop :=
  ∀ x y X, π x = some X → π y = some X → x = y

def extendsMap {N : ℕ} {U : Type} (π' π : PartialMap N U) : Prop :=
  ∀ x X, π x = some X → π' x = some X

noncomputable def mapSize {N : ℕ} {U : Type} (π : PartialMap N U) : ℕ :=
  (Finset.univ.filter (fun x => (π x).isSome)).card

abbrev PriorityCoordinate (N : ℕ) (U : Type) := Fin N ⊕ U
abbrev PriorityOrder (N : ℕ) := Equiv.Perm (Fin N)
abbrev PriorityOracle (N : ℕ) (U : Type) := PriorityCoordinate N U → PriorityOrder N

instance priorityOrderMeasurable (N : ℕ) : MeasurableSpace (PriorityOrder N) := ⊤
instance priorityOrderDiscrete (N : ℕ) : DiscreteMeasurableSpace (PriorityOrder N) := ⟨fun _ => trivial⟩

noncomputable def uniformOrder (N : ℕ) : Measure (PriorityOrder N) :=
  (PMF.uniformOfFintype (PriorityOrder N)).toMeasure

/-- Full product law, including all coordinates of the infinite universe. -/
noncomputable def priorityLaw (N : ℕ) (U : Type) : Measure (PriorityOracle N U) :=
  Measure.infinitePi (fun _ => uniformOrder N)

def unmatched {N : ℕ} {U : Type} (π : PartialMap N U) : PriorityCoordinate N U → Prop
  | .inl x => π x = none
  | .inr X => ¬ ∃ x, π x = some X

/-- Freshness means uniform independent orders at every finite family of
unmatched coordinates, with no restriction on already matched coordinates. -/
def fresh {N : ℕ} {U : Type} (π : PartialMap N U) (μ : Measure (PriorityOracle N U)) : Prop :=
  partialInjection π ∧ IsProbabilityMeasure μ ∧
  ∀ r (cs : Fin r → PriorityCoordinate N U), Function.Injective cs →
    (∀ i, unmatched π (cs i)) →
    μ.map (fun ω i => ω (cs i)) = Measure.pi (fun _ : Fin r => uniformOrder N)

noncomputable def preimage {N : ℕ} {U : Type} (π : PartialMap N U) (X : U) : Option (Fin N) :=
  open Classical in (List.finRange N).find? (fun x => π x = some X)

/-- Enumeration σ of the chosen N-element set S. The order ωx is read only
when x is unmatched. -/
noncomputable def matchLeft {N : ℕ} {U : Type} (σ : Fin N ↪ U)
    (ω : PriorityOracle N U) (π : PartialMap N U) (x : Fin N) : Option (PartialMap N U) :=
  open Classical in
  match π x with
  | some _ => some π
  | none => do
      let j ← (List.ofFn (ω (.inl x))).find? (fun j => ¬ ∃ y, π y = some (σ j))
      pure (Function.update π x (some (σ j)))

noncomputable def matchRight {N : ℕ} {U : Type} (ω : PriorityOracle N U)
    (π : PartialMap N U) (X : U) : Option (PartialMap N U) :=
  open Classical in
  match preimage π X with
  | some _ => some π
  | none => do
      let y ← (List.ofFn (ω (.inr X))).find? (fun y => π y = none)
      pure (Function.update π y (some X))

/-- One query traversal, in the order prescribed on PDF 38. Failure is explicit
rather than an invented value; the source's size hypotheses preclude failure. -/
noncomputable def traverseQuery {S : Signature} {N : ℕ} {U : Type}
    [S.language.Structure U] (σ : Fin N ↪ U) (ω : PriorityOracle N U)
    (π : PartialMap N U) (q : TableQuery S N) : Option (PartialMap N U × Fin N) := do
  let π' ← (List.ofFn q.2).foldlM (fun state x => matchLeft σ ω state x) π
  let args ← optionVector (fun i => π' (q.2 i))
  let X := FirstOrder.Language.Structure.funMap (L := S.language) (⟨q.1, rfl⟩ : S.language.Functions (S.arity q.1)) args
  let π'' ← matchRight ω π' X
  let answer ← preimage π'' X
  pure (π'', answer)

noncomputable def traverse {S : Signature} {N : ℕ} {U : Type}
    [S.language.Structure U] (σ : Fin N ↪ U) (ω : PriorityOracle N U) :
    DecisionTree S N → PartialMap N U → Option (PartialMap N U × Bool)
  | .leaf b, π => some (π,b)
  | .node q next, π => do
      let (π', answer) ← traverseQuery σ ω π q
      traverse σ ω (next answer) π'

noncomputable def traversalMap {S : Signature} {N : ℕ} {U : Type}
    [S.language.Structure U] (σ : Fin N ↪ U) (ω : PriorityOracle N U)
    (T : DecisionTree S N) (π : PartialMap N U) : Option (PartialMap N U) :=
  (traverse σ ω T π).map Prod.fst

noncomputable def traversalOutput {S : Signature} {N : ℕ} {U : Type}
    [S.language.Structure U] (σ : Fin N ↪ U) (ω : PriorityOracle N U)
    (T : DecisionTree S N) (π : PartialMap N U) : Option Bool :=
  (traverse σ ω T π).map Prod.snd

end ApproxCountRwPHP.Unprovability


