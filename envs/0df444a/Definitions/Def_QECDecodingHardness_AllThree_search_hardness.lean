-- Prove2me | Definitions.Def_QECDecodingHardness_AllThree_search_hardness
-- name    : QECDecodingHardness_AllThree_search_hardness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:44.528909+00:00
-- url     : https://prove2.me/theorems/66a2092d-0f47-4450-9b35-f46ad0925018
-- title:
--   Uniform polynomial-time oracle search hardness for the three decoding tasks
-- statement:
--   An encoded search task consists of a query type, its explicit binary encoding, and a relation specifying accepted answers. It is NP-hard in the operational sense used here when every query has an accepted answer and, for every polynomially verifiable language A over an alphabet Γ, there are polynomial-time preprocessing and postprocessing Turing machines P and F such that
--
--   $$\forall x\in\Gamma^*\ \forall a,\quad a\text{ is an accepted answer to }P(x)\ \Longrightarrow\ (F(x,a)=1\iff x\in A).$$
--
--   One oracle call suffices; its answer can be any minimizing output. The running-time bounds are supplied by actual Mathlib TM2 computations with a fixed polynomial before all inputs, rather than by the sizes of mathematical outputs. The NP verifier interface is the published PricingWithTips definition.
--
--   The three concrete query types consist of a lattice size and a full syndrome for the corresponding computed code. Their encoding includes unary size and location/check inventories, both incidence tables, and the syndrome. This is a nonsuccinct representation polynomially equivalent to an explicit geometric instance. Square-family parameter k means L=k+1; the color family includes order zero. A feasible answer explicitly contains a minimum error, and a distinct answer reports infeasibility.
--
--   This interface states search hardness directly while admitting the threshold-decision route in the paper: preprocessing can construct a threshold instance, and postprocessing can compute and compare the returned error weight.
-- source:
--   Shouzhen (Bailey) Gu, Lily Wang, Aleksander Kubica, STOC 2027 submission #745 (October 2026), pp.3,5–6, Section II complexity conventions and proof of Theorem 1

import Definitions.Def_QECDecodingHardness_AllThree_code_capacity_models
import Definitions.Def_QECDecodingHardness_AllThree_cnot_model
import Definitions.Def_PricingWithTips_NPHardness

namespace QECDecodingHardness.AllThree

/-- A search relation on explicitly encoded queries. No solver or correctness
property is a field. The returned word includes an error or infeasibility flag. -/
structure EncodedSearchTask where
  Query : Type
  encode : Query → List Bool
  accepts : Query → List Bool → Prop

/-- Mixed input/answer tape, with tagged alphabets and one delimiter. -/
def oraclePairEncoding {Γ : Type} (p : List Γ × List Bool) : List (Option (Γ ⊕ Bool)) :=
  p.1.map (fun a => some (Sum.inl a)) ++ [none] ++
    p.2.map (fun b => some (Sum.inr b))

/-- Operational NP search hardness. For each NP language, there are actual
polynomial-time TM2 preprocessing and postprocessing computations, uniform
before all input words and all accepted oracle answers. One query suffices.
Totality of the search relation is part of the conclusion, so a relation with
no legal answers cannot become NP-hard by vacuity. No oracle tie-break is fixed. -/
def NPOracleHard (T : EncodedSearchTask) : Prop :=
  (∀ q : T.Query, ∃ a, T.accepts q a) ∧
  ∀ (Γ : Type) (L : Set (List Γ)), PricingWithTips.PolynomiallyVerifiable L →
    ∃ (prepare : List Γ → T.Query) (finish : List Γ × List Bool → Bool),
      Nonempty (Turing.TM2ComputableInPolyTime (id : List Γ → List Γ) T.encode prepare) ∧
      Nonempty (Turing.TM2ComputableInPolyTime oraclePairEncoding
        (fun b : Bool => [b]) finish) ∧
      ∀ (x : List Γ) (a : List Bool), T.accepts (prepare x) a →
        (finish (x, a) = true ↔ x ∈ L)

inductive DecodingFamily where
  | colorCodeZ
  | surfaceCodeXYZ
  | transversalCNOTZ
  deriving DecidableEq

/-- Color parameter k includes the distance-one patch. Square families use
L=k+1, covering every positive lattice size with no truncated time schedule. -/
def familySystem (f : DecodingFamily) (k : ℕ) : CheckSystem :=
  match f with
  | .colorCodeZ => colorCodeZ k
  | .surfaceCodeXYZ => surfaceCodeXYZ (k + 1)
  | .transversalCNOTZ => transversalCNOTZ (k + 1)

abbrev DecodingInstance (f : DecodingFamily) := Σ k : ℕ, Syndrome (familySystem f k)

/-- Explicit, nonsuccinct input representation: unary parameter and location/
check inventories, then both derived incidence tables and the full syndrome.
The matrix is always the fixed lattice's matrix, never an arbitrary input field.
Dense table serialization is polynomially equivalent to the sparse geometry
and syndrome description; it does not assert a sharper construction size. -/
def encodeDecodingInstance {f : DecodingFamily} (I : DecodingInstance f) : List Bool :=
  let S := familySystem f I.1
  List.replicate I.1 true ++ [false] ++
    List.replicate S.locations true ++ [false] ++
    List.replicate S.checks true ++ [false] ++
    (List.finRange S.checks).flatMap (fun c =>
      (List.finRange S.locations).flatMap (fun q =>
        [decide (S.fromX c q = 1), decide (S.fromZ c q = 1)])) ++
    (List.finRange S.checks).map (fun c => decide (I.2 c = 1))

def decodingSearchTask (f : DecodingFamily) : EncodedSearchTask where
  Query := DecodingInstance f
  encode := encodeDecodingInstance
  accepts := fun I a => MinimumAnswer (familySystem f I.1) I.2 a

end QECDecodingHardness.AllThree


