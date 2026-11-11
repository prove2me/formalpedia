-- Prove2me | Definitions.Def_XORFullTilt_Hardness_EffectiveGames
-- name    : XORFullTilt_Hardness_EffectiveGames
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T14:53:47.430193+00:00
-- url     : https://prove2.me/theorems/e9a93644-5927-4636-8975-e976deb29f90
-- title:
--   Effective game inputs, promise RE and polynomial-time verifiers
-- statement:
--   An explicit input is a natural-number code for two alphabet bounds, a list of sampled question pairs and the pairs where the tilted predicate is one. Questions are reduced to their finite alphabets, the distinguished Alice question is zero, and the referee samples a list entry uniformly. A missing or empty list uses the pair $(0,0)$. Every code denotes a valid rational game; every rational law has such an integer-multiplicity description. This effective representation does not restrict the separate semantic game definitions.
--
--   Promise-RE means that there exists an RE predicate containing all YES inputs and no NO inputs. Promise-RE-completeness adds a total computable reduction from every RE language on binary strings, taking members to YES and nonmembers to NO.
--
--   A succinct verifier has two polynomial bounds, for random tape and question length, a polynomial-time sampler and a polynomial-time Boolean table evaluator. The published program model provides finite syntax, size-charged timed evaluations and explicit polynomial runtime bounds connected to the computed functions. The sampler receives the input and a uniformly random bounded bit string and may correlate its outputs. Alice's distinguished question is represented separately; other questions are padded finite bit strings. The predicate uses the tilted rule and exactly one answer bit per player. Program texts, runtime clocks, tape and question bounds, and the input have a finite description. One RE separator is required uniformly on these descriptions.
--
--   This interface distinguishes computable explicit expansion from polynomial-time succinct computation, and keeps strict soundness separate from closed-threshold completeness.
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), p.12, succinct presentation; p.17, Definition 3.4; p.20, Theorems 4.2–4.3

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_FiniteLaws
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime

namespace XORFullTilt.Hardness

/-- Integer-multiplicity explicit rational tables. The four components are the two
    alphabet bounds, a list of sampled pairs, and the pairs where f is one. -/
abbrev RawTable := ℕ × ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)

def rawTable (n : ℕ) : RawTable := (Encodable.decode (α := RawTable) n).getD (0,0,[],[])

def tablePair (t : RawTable) (i : Fin (max 1 t.2.2.1.length)) :
    Fin (t.1+1) × Fin (t.2.1+1) :=
  let z := t.2.2.1.getD i.val (0,0)
  (⟨z.1 % (t.1+1), Nat.mod_lt _ (by omega)⟩,
   ⟨z.2 % (t.2.1+1), Nat.mod_lt _ (by omega)⟩)

/-- Every code denotes a valid game; malformed tables use the zero pair. -/
noncomputable def explicitGame (n : ℕ) :
    TiltedGame (Fin ((rawTable n).1+1)) (Fin ((rawTable n).2.1+1)) :=
  let t := rawTable n
  letI : Nonempty (Fin (max 1 t.2.2.1.length)) := ⟨⟨0, by omega⟩⟩
  tiltedOfPMF ((PMF.uniformOfFintype (Fin (max 1 t.2.2.1.length))).map (tablePair t)) 0
    (fun x y => decide ((x.val,y.val) ∈ t.2.2.2))

noncomputable def explicitValue (n : ℕ) : ℝ := quantumValue (explicitGame n).game

/-- RE separator rather than enumerability of the closed-threshold YES set. -/
def PromiseRE {α : Type} [Primcodable α] (yes no : α → Prop) : Prop :=
  ∃ S : α → Prop, REPred S ∧ (∀ x, yes x → S x) ∧ (∀ x, no x → ¬ S x)

def PromiseREComplete {α : Type} [Primcodable α] (yes no : α → Prop) : Prop :=
  PromiseRE yes no ∧ ∀ L : List Bool → Prop, REPred L →
    ∃ r : List Bool → α, Computable r ∧
      (∀ x, L x → yes (r x)) ∧ (∀ x, ¬ L x → no (r x))

/-- An honest polynomial-time verifier, using the published charged program syntax
    and its timed evaluation relation. The sampler may correlate its two outputs.
    The boolean flag in its first output marks the distinguished question. -/
structure SuccinctVerifier where
  randomBound : Polynomial ℕ
  questionBound : Polynomial ℕ
  sampler : MIPRE.Cost.PolyTimeFun (List Bool × List Bool) ((Bool × List Bool) × List Bool)
  predicate : MIPRE.Cost.PolyTimeFun (List Bool × (Bool × List Bool) × List Bool) Bool

abbrev Question (q : ℕ) := Fin q → Bool

def padQuestion (q : ℕ) (s : List Bool) : Question q := fun i => s.getD i.val false

noncomputable def SuccinctVerifier.game (V : SuccinctVerifier) (z : List Bool) :
    TiltedGame (Option (Question (V.questionBound.eval z.length)))
      (Question (V.questionBound.eval z.length)) := by
  classical
  let r := V.randomBound.eval z.length
  let q := V.questionBound.eval z.length
  let sample : Question r → Option (Question q) × Question q := fun seed =>
    let out := V.sampler (z,List.ofFn seed)
    ((if out.1.1 then none else some (padQuestion q out.1.2)), padQuestion q out.2)
  exact tiltedOfPMF ((PMF.uniformOfFintype (Question r)).map sample) none (fun x y =>
    V.predicate (z, (x.isNone, x.elim [] List.ofFn), List.ofFn y))

noncomputable def succinctValue (V : SuccinctVerifier) (z : List Bool) : ℝ :=
  quantumValue (V.game z).game

/-- A finite description contains the two program texts, all polynomial clocks,
    the tape and question bounds, and the input. Semantic functions and proofs are absent. -/
noncomputable def verifierInput (V : SuccinctVerifier) (z : List Bool) : List Bool :=
  let poly : Polynomial ℕ → MIPRE.Cost.Data := fun p =>
    MIPRE.Cost.Data.ofList (fun n => MIPRE.Cost.encode n)
      ((List.range (p.natDegree+1)).map p.coeff)
  (MIPRE.Cost.Data.ofList id
    [V.sampler.code.toData, V.predicate.code.toData,
      poly V.sampler.timeBound, poly V.predicate.timeBound,
      poly V.randomBound, poly V.questionBound, MIPRE.Cost.encode z]).toBits

/-- One separator works uniformly on finite program descriptions and their inputs. -/
noncomputable def SuccinctPromiseRE (c s : ℝ) : Prop :=
  ∃ S : List Bool → Prop, REPred S ∧ ∀ (V : SuccinctVerifier) (z : List Bool),
    (succinctValue V z ≥ c → S (verifierInput V z)) ∧
    (succinctValue V z < s → ¬ S (verifierInput V z))

end XORFullTilt.Hardness


