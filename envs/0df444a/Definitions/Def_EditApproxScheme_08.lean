-- Prove2me | Definitions.Def_EditApproxScheme_08
-- name    : EditApproxScheme_08
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T16:37:51.752538+00:00
-- url     : https://prove2.me/theorems/de90cee0-c6e4-44cc-8eba-1e6d80409c94
-- title:
--   Edit-distance approximation scheme, part 8 of 20: parameters and warmup
-- statement:
--   This is **part 8 of 20** of the definitions of a uniform almost-linear approximation scheme for edit distance, which the main statement `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` is about. This part contains rational connection budgets, equality of actions, band rounding spacing and rounded band actions, the root search and square roots used to compute the parameters, wide warmup inputs, the initial support of refinement, global parameter work, remaining depth, and the keys of the computed family table. It also proves 10 supporting lemmas (namespace `OAI.EditApproximation.Lemmas`) that these definitions use.
--
--   Each part imports the previous one, so importing part 20 brings all definitions into scope. A description of the whole scheme is given in part 20.
--
--   **Formalization Note** These 20 parts replace the single 1.4 MB block `Def_EditApproximation`, which was too large for the platform to import. In the source, the supporting lemmas were pasted as local `have` proofs inside the definition bodies: 948 copies of 145 lemmas. Each lemma is now proved once as a top-level theorem and cited by name; one lemma that nothing used was dropped. The file was then split into sequential parts by deleting declarations. All 1,403 declarations from the source keep exactly the same elaborated types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean#L4102-L4749 (line numbers refer to the lemma-lifted file, 12,145 lines)

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean
-- Part 8 of 20 of the edit-distance approximation definitions: embedded proof lemmas lifted
-- to top-level theorems (OAI.EditApproximation.Lemmas.*), then split by skeleton subtraction.

import Definitions.Def_EditApproxScheme_07

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Finset

def rationalConnectionBudget {n : ℕ} (start : ℚ) : List (OAI.EditApproximation.TargetInterval n) → ℚ → ℚ
  | [], finish => |start - finish|
  | state :: rest, finish => |start - state.lo| + rationalConnectionBudget state.hi rest finish

def bandChildEnvelope {ny M : ℕ} (b : ℕ)
    (band : List (Fin M → OAI.EditApproximation.TargetInterval ny))
    (initial : Fin M → OAI.EditApproximation.TargetInterval ny → ℚ) (i : Fin M) : ℚ :=
  OAI.EditApproximation.rationalDyadicCeiling (max ((b : ℚ) / M)
    (OAI.EditApproximation.rationalMaximum 0 (band.map fun action => initial i (action i))))

def bandEnvelopeExponent {ny M : ℕ} (b : ℕ) (band : List (Fin M → OAI.EditApproximation.TargetInterval ny))
    (initial : Fin M → OAI.EditApproximation.TargetInterval ny → ℚ) (i : Fin M) : ℤ :=
  Int.clog 2 (max ((b : ℚ) / M) (OAI.EditApproximation.rationalMaximum 0 (band.map fun action => initial i (action i))))

deriving instance DecidableEq for OAI.EditApproximation.TargetInterval

def zeroConnectionWithWork {n : ℕ} (start : ℕ) : List (OAI.EditApproximation.TargetInterval n) → ℕ → Bool × ℕ
  | [], finish => OAI.EditApproximation.naturalEqualWithWork start finish
  | state :: rest, finish =>
    let current := OAI.EditApproximation.naturalEqualWithWork start state.lo
    let tail := zeroConnectionWithWork state.hi rest finish
    (current.1 && tail.1, current.2 + tail.2 + 1)

theorem _root_.OAI.EditApproximation.Lemmas.binaryGridRoundWithWork_value (spacing : ℕ) (position : ℕ) (hspacing : LT.lt.{0} 0 spacing) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.binaryGridRoundWithWork spacing position).1 = OAI.EditApproximation.gridRound spacing position := by
  simp only [OAI.EditApproximation.binaryGridRoundWithWork, OAI.EditApproximation.Lemmas.bitMulWithWork_value, OAI.EditApproximation.Lemmas.bitWordValue_bits,
    (OAI.EditApproximation.Lemmas.binaryNaturalDivModWithWork_spec position spacing hspacing).1, OAI.EditApproximation.gridRound]

theorem _root_.OAI.EditApproximation.Lemmas.binaryIntervalRoundWithWork_value {n : ℕ} (spacing : ℕ) (hspacing : LT.lt.{0} 0 spacing) (q : OAI.EditApproximation.TargetInterval n) :
    (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.binaryIntervalRoundWithWork spacing q.lo q.hi).1.1,
      OAI.EditApproximation.bitWordValue (OAI.EditApproximation.binaryIntervalRoundWithWork spacing q.lo q.hi).1.2) =
      ((OAI.EditApproximation.roundInterval spacing q).lo, (OAI.EditApproximation.roundInterval spacing q).hi) := by
  simp only [OAI.EditApproximation.binaryIntervalRoundWithWork, OAI.EditApproximation.Lemmas.binaryGridRoundWithWork_value _ _ hspacing,
    OAI.EditApproximation.roundInterval]

def roundStateWithWork {n : ℕ} (spacing : ℕ) (hspacing : 0 < spacing)
    (q : OAI.EditApproximation.TargetInterval n) : OAI.EditApproximation.TargetInterval n × ℕ := by
  exact
    let output := OAI.EditApproximation.binaryIntervalRoundWithWork spacing q.lo q.hi
    let heq := OAI.EditApproximation.Lemmas.binaryIntervalRoundWithWork_value spacing hspacing q
    (⟨OAI.EditApproximation.bitWordValue output.1.1, OAI.EditApproximation.bitWordValue output.1.2,
      by exact (congrArg Prod.fst heq).le.trans ((OAI.EditApproximation.roundInterval spacing q).ordered.trans
        (congrArg Prod.snd heq).symm.le),
      by exact (congrArg Prod.snd heq).le.trans (OAI.EditApproximation.roundInterval spacing q).valid⟩, output.2 + 1)

def actionEqualWithWork {n M : ℕ} (a b : Fin M → OAI.EditApproximation.TargetInterval n) : Bool × ℕ :=
  OAI.EditApproximation.allWithWork (fun i =>
    let left := OAI.EditApproximation.naturalEqualWithWork (a i).lo (b i).lo
    let right := OAI.EditApproximation.naturalEqualWithWork (a i).hi (b i).hi
    (left.1 && right.1, left.2 + right.2 + 1)) (List.finRange M)

def localRefinementRepresentatives {n : ℕ} (N P F : ℕ) (a : ℚ)
    (initial : OAI.EditApproximation.TargetInterval n → ℚ) (q : OAI.EditApproximation.TargetInterval n) : List (ℕ × OAI.EditApproximation.TargetInterval n) :=
  ((OAI.EditApproximation.dyadicScales N).filter fun (b : ℕ) => decide
    (initial q / (16 * F) ≤ b ∧ (b : ℚ) ≤ 8 * a * initial q)).flatMap fun b =>
      ((OAI.EditApproximation.localTargetStates n (OAI.EditApproximation.seedGridSpacing b P) ⌈initial q⌉₊ q).filter fun r => decide
        ((b : ℚ) / (4 * a) ≤ initial r ∧ initial r ≤ 8 * F * b)).map fun r => (b, r)

def sharedBandRationalAction {ny M : ℕ} (center : OAI.EditApproximation.TargetInterval ny)
    (states : Fin M → OAI.EditApproximation.TargetInterval ny) : OAI.EditApproximation.PhysicalRationalAction M ny :=
  ⟨center, 0, fun i => (i, states i)⟩

def localGroupQueryKeys {n : ℕ} (N F exponent : ℕ) (a : ℚ)
    (initial : OAI.EditApproximation.TargetInterval n → ℚ) (q : OAI.EditApproximation.TargetInterval n) : List (ℕ × (ℕ × ℕ)) :=
  (OAI.EditApproximation.dyadicQueryWindow N (initial q) a F).flatMap fun (b : ℕ) =>
    (OAI.EditApproximation.localTargetCells ((2 : ℚ) ^ (-(exponent : ℤ)) * b) ⌈initial q⌉₊ q).map fun cell => (b, cell)

def rationalWidePrefixCost {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (r : OAI.EditApproximation.TargetInterval ny) (states : Fin M → OAI.EditApproximation.TargetInterval ny)
    (child : Fin M → OAI.EditApproximation.TargetInterval ny → ℚ) (j : ℕ) (p : ℚ) : ℚ :=
  OAI.EditApproximation.rationalConnectionBudget r.lo ((List.ofFn states).take j)
    ((OAI.EditApproximation.balancedCut parent.lo (parent.hi - parent.lo) M j : ℚ) + p) +
      ∑ i, if i.val < j then child i (states i) else 0

def bandRoundSpacing {ny M : ℕ} (thetaExponent b : ℕ) (band : List (Fin M → OAI.EditApproximation.TargetInterval ny))
    (initial : Fin M → OAI.EditApproximation.TargetInterval ny → ℚ) (i : Fin M) : ℕ :=
  2 ^ (OAI.EditApproximation.bandEnvelopeExponent b band initial i - thetaExponent).toNat

def actionMemberWithWork {n M : ℕ} (a : Fin M → OAI.EditApproximation.TargetInterval n) :
    List (Fin M → OAI.EditApproximation.TargetInterval n) → Bool × ℕ
  | [] => (false, 1)
  | b :: rest =>
    let test := OAI.EditApproximation.actionEqualWithWork a b
    let tail := actionMemberWithWork a rest
    (test.1 || tail.1, test.2 + tail.2 + 1)

def wideEarlierInputCover {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx) (P history : ℕ)
    (representatives : List (ℕ × OAI.EditApproximation.TargetInterval ny)) : Finset (Fin M × ℕ × OAI.EditApproximation.TargetInterval ny) :=
  representatives.toFinset.biUnion fun br =>
    Finset.univ.biUnion fun i : Fin M =>
      (Finset.range history).biUnion fun t =>
        ((OAI.EditApproximation.wideChildStateList parent br.2 br.1 P i).toFinset).image fun r => (i, t, r)

def queryEarlierRepresentatives {n : ℕ} (N P F exponent : ℕ) (a : ℚ)
    (initial : OAI.EditApproximation.TargetInterval n → ℚ) (q : OAI.EditApproximation.TargetInterval n) : List (ℕ × OAI.EditApproximation.TargetInterval n) :=
  OAI.EditApproximation.localRefinementRepresentatives N P F a initial q ++
  (OAI.EditApproximation.localGroupQueryKeys N F exponent a initial q).flatMap (fun key =>
    (OAI.EditApproximation.cellRepresentativeStates n P F key.1 a initial ((2 : ℚ) ^ (-(exponent : ℤ))) key.2).map
      fun r => (key.1, r)) ++
  (OAI.EditApproximation.dyadicQueryWindow N (initial q) a F).map
    fun b => (b, OAI.EditApproximation.roundInterval (OAI.EditApproximation.seedGridSpacing b P) q)

def rationalWidePrefixMinimum {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (r : OAI.EditApproximation.TargetInterval ny) (actions : List (Fin M → OAI.EditApproximation.TargetInterval ny)) (hnonempty : actions ≠ [])
    (child : Fin M → OAI.EditApproximation.TargetInterval ny → ℚ) (j : ℕ) (p : ℚ) : ℚ :=
  OAI.EditApproximation.rationalMinimum (OAI.EditApproximation.rationalWidePrefixCost parent r (actions.head hnonempty) child j p)
    (actions.map fun action => OAI.EditApproximation.rationalWidePrefixCost parent r action child j p)

def roundedBandAction {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → OAI.EditApproximation.TargetInterval ny))
    (initial : Fin M → OAI.EditApproximation.TargetInterval ny → ℚ) (action : Fin M → OAI.EditApproximation.TargetInterval ny) :
    Fin M → OAI.EditApproximation.TargetInterval ny :=
  fun i => OAI.EditApproximation.roundInterval (OAI.EditApproximation.bandRoundSpacing thetaExponent b band initial i) (action i)

def queryEarlierInputCover {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (N P F exponent history : ℕ) (a : ℚ)
    (initial : OAI.EditApproximation.TargetInterval ny → ℚ) (q : OAI.EditApproximation.TargetInterval ny) :
    Finset (Fin M × ℕ × OAI.EditApproximation.TargetInterval ny) :=
  OAI.EditApproximation.wideEarlierInputCover parent P history (OAI.EditApproximation.queryEarlierRepresentatives N P F exponent a initial q)

def canonicalRoundedBandAction {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → OAI.EditApproximation.TargetInterval ny)) (hnonempty : band ≠ [])
    (initial : Fin M → OAI.EditApproximation.TargetInterval ny → ℚ) : Fin M → OAI.EditApproximation.TargetInterval ny :=
  OAI.EditApproximation.roundedBandAction thetaExponent b band initial (band.head hnonempty)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Filter

def parameterClogWithWork (n : ℕ) : ℕ × ℕ :=
  let result := OAI.EditApproximation.inputBitLengthWithWork (n - 1)
  (result.1, result.2 + 2)

def parameterLogWithWork (n : ℕ) : ℕ × ℕ :=
  let result := OAI.EditApproximation.inputBitLengthWithWork n
  (result.1 - 1, result.2 + 1)

def parameterRootSearch (n : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | k + 1 => if (k + 1) * (k + 1) ≤ n then (k + 1, 3) else
      let result := parameterRootSearch n k
      (result.1, result.2 + 3)

def parameterPowerWithWork (a : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | k + 1 => let result := parameterPowerWithWork a k
      (result.1 * a, result.2 + 2)

def physicalCoarseInputStorage {M J : ℕ} (source target : List ℕ)
    (entry : OAI.EditApproximation.PhysicalEntry M J target.length) : ℕ :=
  let interval := OAI.EditApproximation.physicalSourceInterval source.length entry.1
  OAI.EditApproximation.coarsePreparedInputStorage source target interval.lo interval.hi entry.2.lo entry.2.hi

def computedQueryPassWithWork (N pass : ℕ) : (OAI.EditApproximation.BinaryFraction × OAI.EditApproximation.RefinementParameterWords) × ℕ := by
  exact
    let seed := OAI.EditApproximation.scheduledSeedWordWithWork N pass
    let parameters := OAI.EditApproximation.refinementParameterWordsWithWork N pass (OAI.EditApproximation.inputSmallLog N).bits
      (by rw [OAI.EditApproximation.Lemmas.bitWordValue_bits]; exact Nat.two_pow_pos _)
    ((seed.1, parameters.1), seed.2 + parameters.2 + 2)

def storedIntegerBits (values : List ℤ) : ℕ :=
  1 + (values.map fun z => Nat.size z.natAbs + 2).sum

def parameterSqrtWithWork (n : ℕ) : ℕ × ℕ := OAI.EditApproximation.parameterRootSearch n n

def computedQuerySetupWithWork (N : ℕ) :=
  let parameters := OAI.EditApproximation.vectorMapWithWork (OAI.EditApproximation.computedSeedPassCount N + 1)
    (fun i => OAI.EditApproximation.computedQueryPassWithWork N i.val)
  let base := OAI.EditApproximation.refinementBaseWithWork (OAI.EditApproximation.inputSmallLog N).bits
  ((parameters.1, base.1), parameters.2 + base.2 + 5)

def integerParametersWithWork (N : ℕ) : OAI.EditApproximation.IntegerParameters × ℕ :=
  let first := OAI.EditApproximation.parameterClogWithWork (N + 2)
  let heightExponent := OAI.EditApproximation.parameterClogWithWork first.1
  let height := OAI.EditApproximation.parameterPowerWithWork 2 heightExponent.1
  let smallExponent := OAI.EditApproximation.parameterClogWithWork (max 1 heightExponent.1)
  let small := OAI.EditApproximation.parameterPowerWithWork 2 smallExponent.1
  let logarithm := OAI.EditApproximation.parameterLogWithWork small.1
  let firstRoot := OAI.EditApproximation.parameterSqrtWithWork logarithm.1
  let secondRoot := OAI.EditApproximation.parameterSqrtWithWork firstRoot.1
  let branching := OAI.EditApproximation.parameterPowerWithWork 2 (heightExponent.1 / 20)
  let coarseBranching := OAI.EditApproximation.parameterPowerWithWork height.1 secondRoot.1
  let factor := OAI.EditApproximation.parameterPowerWithWork height.1 (secondRoot.1 + 4)
  let grid := OAI.EditApproximation.parameterPowerWithWork height.1 (secondRoot.1 + 20)
  let rounds := OAI.EditApproximation.parameterPowerWithWork 2 ((3 * heightExponent.1 + 3) / 4)
  let spacingDenominator := OAI.EditApproximation.parameterPowerWithWork small.1 2
  ({ H := height.1, ell := small.1, p := secondRoot.1, B := coarseBranching.1,
     initialFactor := factor.1, M := branching.1, P := grid.1,
     T := rounds.1, S := height.1 / spacingDenominator.1 },
   first.2 + heightExponent.2 + height.2 + smallExponent.2 + small.2 + logarithm.2 +
     firstRoot.2 + secondRoot.2 + branching.2 + coarseBranching.2 + factor.2 + grid.2 +
     rounds.2 + spacingDenominator.2 + 15)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

structure PhysicalTableRequest (M J ny : ℕ) where
  pass : ℕ
  copy : ℕ
  node : OAI.EditApproximation.PhysicalNode M J
  index : ℕ
  state : OAI.EditApproximation.TargetInterval ny

deriving DecidableEq

def rawRefinementCenters {n : ℕ} (N P F : ℕ) (a value : ℚ) (q : OAI.EditApproximation.TargetInterval n) :
    List (OAI.EditApproximation.TargetInterval n) :=
  ((OAI.EditApproximation.dyadicQueryWindow N value a F).flatMap fun b =>
    OAI.EditApproximation.localTargetStates n (OAI.EditApproximation.seedGridSpacing b P) ⌈value⌉₊ q).eraseDups

def wideWarmupInputs {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx) (P : ℕ)
    (representatives : List (ℕ × OAI.EditApproximation.TargetInterval ny)) : List (Fin M × OAI.EditApproximation.TargetInterval ny) :=
  (representatives.flatMap fun br => (List.finRange M).flatMap fun i =>
    (OAI.EditApproximation.wideChildStateList parent br.2 br.1 P i).map fun r => (i, r)).eraseDups

def queryMeanRead {ι : Type u_1} (count : ℕ) (reader : Fin count → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction) :
    OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction :=
  .charge (count + 1) (OAI.EditApproximation.BitQuery.collect reader (List.ofFn fun i : Fin count => i)
    (fun words => OAI.EditApproximation.BitQuery.compute (OAI.EditApproximation.BinaryFraction.queryMeanWithWork count words)))

def physicalNodeCodeWithWork {M J : ℕ} (node : OAI.EditApproximation.PhysicalNode M J) : ℕ × ℕ :=
  let path := OAI.EditApproximation.treeLayerCodeWithWork M node.1.val node.2
  let power := OAI.EditApproximation.parameterPowerWithWork M J
  (path.1 + power.1 * node.1.val, path.2 + power.2 + 3)

def rationalParametersWithWork (ell : ℕ) : OAI.EditApproximation.RationalParameters × ℕ :=
  let fourth := OAI.EditApproximation.parameterPowerWithWork ell 4
  let fifth := OAI.EditApproximation.parameterPowerWithWork ell 5
  let tenth := OAI.EditApproximation.parameterPowerWithWork ell 10
  let twentieth := OAI.EditApproximation.parameterPowerWithWork ell 20
  let fortieth := OAI.EditApproximation.parameterPowerWithWork ell 40
  ({ F := ell, initialSlope := 32 * ell, coneSlope := 128 * ell,
     delta := 1 / (tenth.1 : ℚ), kappa := 1 / (fourth.1 : ℚ), tau := 1 / (fourth.1 : ℚ),
     theta := 1 / (fortieth.1 : ℚ), gamma := 1 / (twentieth.1 : ℚ), eta := fifth.1 },
   fourth.2 + fifth.2 + tenth.2 + twentieth.2 + fortieth.2 + 20)

def onlineMassWithWork (M P H : ℕ) : ℕ × ℕ :=
  let width := 40 * P + 2
  let square := OAI.EditApproximation.parameterPowerWithWork width 2
  let dimension := H + M * square.1 + 2
  let rounds := OAI.EditApproximation.parameterPowerWithWork dimension 80
  (rounds.1 * (rounds.1 + 1) / 2, square.2 + rounds.2 + 9)

def refinementInitialSupport {n : ℕ} (N P F exponent : ℕ) (a value : ℚ)
    (q : OAI.EditApproximation.TargetInterval n) : List (OAI.EditApproximation.TargetInterval n) :=
  q :: (OAI.EditApproximation.rawRefinementCenters N P F a value q ++
    (OAI.EditApproximation.localGroupQueryKeys N F exponent a (fun _ => value) q).flatMap (fun key =>
      OAI.EditApproximation.cellTargetStates n (OAI.EditApproximation.seedGridSpacing key.1 P)
        ((2 : ℚ) ^ (-(exponent : ℤ)) * key.1) key.2) ++
    (OAI.EditApproximation.dyadicQueryWindow N value a F).map (fun b => OAI.EditApproximation.roundInterval (OAI.EditApproximation.seedGridSpacing b P) q))

def refinementBandInputList {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (N P F exponent : ℕ) (a : ℚ) (initial : OAI.EditApproximation.TargetInterval ny → ℚ) (q : OAI.EditApproximation.TargetInterval ny) :
    List (Fin M × OAI.EditApproximation.TargetInterval ny) :=
  OAI.EditApproximation.wideWarmupInputs parent P (OAI.EditApproximation.queryEarlierRepresentatives N P F exponent a initial q)

def previousPassRequest {M J ny : ℕ} (T S copy : ℕ)
    (parent : OAI.EditApproximation.PhysicalTableRequest M J ny) (state : OAI.EditApproximation.TargetInterval ny) : OAI.EditApproximation.PhysicalTableRequest M J ny :=
  ⟨parent.pass - 1, copy, parent.node, T + S, state⟩

def physicalEntryCodeWithWork {M J n : ℕ} (entry : OAI.EditApproximation.PhysicalEntry M J n) : ℕ × ℕ :=
  let node := OAI.EditApproximation.physicalNodeCodeWithWork entry.1
  let width := n + 1
  (entry.2.lo + width * entry.2.hi + width * width * node.1, node.2 + 8)

def queryPhysicalBoundedWithWork {M J n : ℕ} (passes copies T S : ℕ)
    (request : OAI.EditApproximation.PhysicalTableRequest M J n) : Bool × ℕ :=
  let pass := OAI.EditApproximation.binaryNaturalCompareWithWork request.pass passes
  let copy := OAI.EditApproximation.binaryNaturalCompareWithWork request.copy copies
  let cap := OAI.EditApproximation.binaryNaturalAddWithWork T S
  let index := OAI.EditApproximation.wordLEWithWork request.index.bits cap.1
  (decide (pass.1 = .lt) && decide (copy.1 = .lt) && index.1,
    pass.2 + copy.2 + cap.2 + index.2 + 4)

def globalParameterWork (N : ℕ) : ℕ :=
  (OAI.EditApproximation.integerParametersWithWork N).2 + (OAI.EditApproximation.rationalParametersWithWork (OAI.EditApproximation.inputSmallLog N)).2 +
    (OAI.EditApproximation.onlineMassWithWork (OAI.EditApproximation.integerParameters N).M (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputHeight N)).2

def physicalLargeInputWithWork (N : ℕ) (epsilon : OAI.EditApproximation.BinaryFraction) : Bool × ℕ :=
  let inspected := OAI.EditApproximation.inspectAccuracyWithWork (OAI.EditApproximation.inputHeight N) epsilon
  if inspected.1.isSome = true then
    let product := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat (OAI.EditApproximation.inputSmallLog N)) epsilon
    let accuracy := OAI.EditApproximation.BinaryFraction.ltWithWork product.1 (OAI.EditApproximation.BinaryFraction.nat 10)
    let threshold := OAI.EditApproximation.binaryNaturalCompareWithWork (OAI.EditApproximation.inputSmallLog N) (2 ^ 1000)
    let mass := OAI.EditApproximation.onlineMassWithWork (OAI.EditApproximation.integerParameters N).M (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputHeight N)
    let width := OAI.EditApproximation.inputBitLengthWithWork mass.1
    let capacity := OAI.EditApproximation.binaryNaturalCompareWithWork (OAI.EditApproximation.inputHeight N) width.1
    (decide (threshold.1 ≠ .lt ∧ accuracy.1 ≠ true ∧ capacity.1 ≠ .lt),
      inspected.2 + product.2 + accuracy.2 + threshold.2 + mass.2 + width.2 + capacity.2 + 10)
  else (false, inspected.2 + 1)

def physicalTableCodeAllocation {M J n : ℕ} (request : OAI.EditApproximation.PhysicalTableRequest M J n) : ℕ :=
  2 * request.node.1.val + 2 * J + 20

def queryPhysicalBoundedAllocation {M J n : ℕ} (passes copies T S : ℕ)
    (request : OAI.EditApproximation.PhysicalTableRequest M J n) : ℕ :=
  request.pass.bits.length + passes.bits.length + request.copy.bits.length + copies.bits.length +
    OAI.EditApproximation.binaryNaturalAddAllocation T S + OAI.EditApproximation.naturalWordLEAllocation request.index.bits (OAI.EditApproximation.binaryNaturalAddWithWork T S).1

def physicalTableCodeWithWork {M J n : ℕ} (copies T S : ℕ)
    (request : OAI.EditApproximation.PhysicalTableRequest M J n) : ℕ × ℕ :=
  let entry := OAI.EditApproximation.physicalEntryCodeWithWork (request.node, request.state)
  let power := OAI.EditApproximation.parameterPowerWithWork M J
  let capacity := (n + 1) * (n + 1) * (power.1 * (J + 1))
  (request.index + (T + S + 1) * (request.copy + copies * (entry.1 + capacity * request.pass)),
    entry.2 + power.2 + 15)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.PhysicalTableRequest

variable {M J ny : ℕ}

def remainingDepth (request : OAI.EditApproximation.PhysicalTableRequest M J ny) : ℕ :=
  J - request.node.1.val

def rank (T S : ℕ) (request : OAI.EditApproximation.PhysicalTableRequest M J ny) : ℕ :=
  request.pass * (T + S + 1) + request.index

def Bounded (passes copies T S : ℕ) (request : OAI.EditApproximation.PhysicalTableRequest M J ny) : Prop :=
  request.pass < passes ∧ request.copy < copies ∧ request.index ≤ T + S

def warmup (pass copy : ℕ) (node : OAI.EditApproximation.PhysicalNode M J) (j : ℕ) (state : OAI.EditApproximation.TargetInterval ny) :
    OAI.EditApproximation.PhysicalTableRequest M J ny :=
  ⟨pass, copy, node, j, state⟩

def refinement (pass copy : ℕ) (node : OAI.EditApproximation.PhysicalNode M J) (T t : ℕ) (state : OAI.EditApproximation.TargetInterval ny) :
    OAI.EditApproximation.PhysicalTableRequest M J ny :=
  ⟨pass, copy, node, T + t, state⟩

def sameIndexChild (request : OAI.EditApproximation.PhysicalTableRequest M J ny)
    (hbelow : request.node.1.val < J) (i : Fin M) (state : OAI.EditApproximation.TargetInterval ny) :
    OAI.EditApproximation.PhysicalTableRequest M J ny :=
  { request with node := OAI.EditApproximation.physicalChild request.node hbelow i, state := state }

def combinedRank (T S : ℕ) (request : OAI.EditApproximation.PhysicalTableRequest M J ny) : ℕ :=
  request.remainingDepth + request.rank T S

end OAI.EditApproximation.PhysicalTableRequest

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

theorem _root_.OAI.EditApproximation.Lemmas.combinedRank_lt_of_progress {M : ℕ} {J : ℕ} {ny : ℕ} (T : ℕ) (S : ℕ) (first : OAI.EditApproximation.PhysicalTableRequest M J ny) (second : OAI.EditApproximation.PhysicalTableRequest M J ny) (hprogress : LT.lt.{0} second.remainingDepth first.remainingDepth ∧
    LE.le.{0} (OAI.EditApproximation.PhysicalTableRequest.rank T S second)
      (OAI.EditApproximation.PhysicalTableRequest.rank T S first) ∨
  LE.le.{0} second.remainingDepth first.remainingDepth ∧
    LT.lt.{0} (OAI.EditApproximation.PhysicalTableRequest.rank T S second)
      (OAI.EditApproximation.PhysicalTableRequest.rank T S first)) :
    OAI.EditApproximation.PhysicalTableRequest.combinedRank T S second < OAI.EditApproximation.PhysicalTableRequest.combinedRank T S first := by
  unfold OAI.EditApproximation.PhysicalTableRequest.combinedRank
  rcases hprogress with h | h
  · exact Nat.add_lt_add_of_lt_of_le h.1 h.2
  · exact Nat.add_lt_add_of_le_of_lt h.1 h.2

theorem _root_.OAI.EditApproximation.Lemmas.warmup_previous_child_progress {M : ℕ} {J : ℕ} {ny : ℕ} (pass : ℕ) (copy : ℕ) (T : ℕ) (S : ℕ) (j : ℕ) (node : OAI.EditApproximation.PhysicalNode M J) (hbelow : LT.lt.{0} (↑(Sigma.fst.{0, 0} node)) J) (i : Fin M) (state : OAI.EditApproximation.TargetInterval ny) (previousState : OAI.EditApproximation.TargetInterval ny) (hj : LT.lt.{0} 0 j) :
    (OAI.EditApproximation.PhysicalTableRequest.warmup pass copy (OAI.EditApproximation.physicalChild node hbelow i) (j - 1) previousState).remainingDepth <
        (OAI.EditApproximation.PhysicalTableRequest.warmup pass copy node j state).remainingDepth ∧
      OAI.EditApproximation.PhysicalTableRequest.rank T S (OAI.EditApproximation.PhysicalTableRequest.warmup pass copy (OAI.EditApproximation.physicalChild node hbelow i) (j - 1) previousState) <
        OAI.EditApproximation.PhysicalTableRequest.rank T S (OAI.EditApproximation.PhysicalTableRequest.warmup pass copy node j state) := by
  constructor
  · unfold OAI.EditApproximation.PhysicalTableRequest.remainingDepth OAI.EditApproximation.PhysicalTableRequest.warmup OAI.EditApproximation.physicalChild
    dsimp only
    omega
  · dsimp only [OAI.EditApproximation.PhysicalTableRequest.rank, OAI.EditApproximation.PhysicalTableRequest.warmup]
    omega

theorem _root_.OAI.EditApproximation.Lemmas.combinedRank_warmup_child {M : ℕ} {J : ℕ} {ny : ℕ} (pass : ℕ) (copy : ℕ) (T : ℕ) (S : ℕ) (j : ℕ) (node : OAI.EditApproximation.PhysicalNode M J) (hbelow : LT.lt.{0} (↑(Sigma.fst.{0, 0} node)) J) (i : Fin M) (state : OAI.EditApproximation.TargetInterval ny) (previousState : OAI.EditApproximation.TargetInterval ny) (hj : LT.lt.{0} 0 j) :
    OAI.EditApproximation.PhysicalTableRequest.combinedRank T S (OAI.EditApproximation.PhysicalTableRequest.warmup pass copy (OAI.EditApproximation.physicalChild node hbelow i) (j - 1) previousState) <
      OAI.EditApproximation.PhysicalTableRequest.combinedRank T S (OAI.EditApproximation.PhysicalTableRequest.warmup pass copy node j state) :=
  OAI.EditApproximation.Lemmas.combinedRank_lt_of_progress T S _ _ (Or.inr
    ⟨(OAI.EditApproximation.Lemmas.warmup_previous_child_progress pass copy T S j node hbelow i state previousState hj).1.le,
      (OAI.EditApproximation.Lemmas.warmup_previous_child_progress pass copy T S j node hbelow i state previousState hj).2⟩)

def physicalWarmupChildQuery {M J ny : ℕ} (pass copy T S t : ℕ)
    (node : OAI.EditApproximation.PhysicalNode M J) (hbelow : node.1.val < J) (q : OAI.EditApproximation.TargetInterval ny)
    (input : Fin M × OAI.EditApproximation.TargetInterval ny) :
    OAI.EditApproximation.FiniteQuery {child : OAI.EditApproximation.PhysicalTableRequest M J ny //
      child.combinedRank T S < (OAI.EditApproximation.PhysicalTableRequest.warmup pass copy node (t + 1) q).combinedRank T S} := by
  exact
    .read ⟨OAI.EditApproximation.PhysicalTableRequest.warmup pass copy (OAI.EditApproximation.physicalChild node hbelow input.1) t input.2,
      by simpa only [Nat.add_sub_cancel] using
        OAI.EditApproximation.Lemmas.combinedRank_warmup_child pass copy T S (t + 1)
          node hbelow input.1 q input.2 (Nat.zero_lt_succ t)⟩ .done

theorem _root_.OAI.EditApproximation.Lemmas.sameIndexChild_progress {M : ℕ} {J : ℕ} {ny : ℕ} (T : ℕ) (S : ℕ) (request : OAI.EditApproximation.PhysicalTableRequest M J ny) (hbelow : LT.lt.{0} (↑(Sigma.fst.{0, 0} request.node)) J) (i : Fin M) (state : OAI.EditApproximation.TargetInterval ny) :
    (OAI.EditApproximation.PhysicalTableRequest.sameIndexChild request hbelow i state).remainingDepth < request.remainingDepth ∧
      OAI.EditApproximation.PhysicalTableRequest.rank T S (OAI.EditApproximation.PhysicalTableRequest.sameIndexChild request hbelow i state) ≤ OAI.EditApproximation.PhysicalTableRequest.rank T S request := by
  constructor
  · unfold OAI.EditApproximation.PhysicalTableRequest.remainingDepth OAI.EditApproximation.PhysicalTableRequest.sameIndexChild OAI.EditApproximation.physicalChild
    dsimp only
    omega
  · exact le_rfl

theorem _root_.OAI.EditApproximation.Lemmas.combinedRank_sameIndexChild {M : ℕ} {J : ℕ} {ny : ℕ} (T : ℕ) (S : ℕ) (request : OAI.EditApproximation.PhysicalTableRequest M J ny) (hbelow : LT.lt.{0} (↑(Sigma.fst.{0, 0} request.node)) J) (i : Fin M) (state : OAI.EditApproximation.TargetInterval ny) :
    OAI.EditApproximation.PhysicalTableRequest.combinedRank T S (OAI.EditApproximation.PhysicalTableRequest.sameIndexChild request hbelow i state) < OAI.EditApproximation.PhysicalTableRequest.combinedRank T S request :=
  OAI.EditApproximation.Lemmas.combinedRank_lt_of_progress T S request _ (Or.inl (OAI.EditApproximation.Lemmas.sameIndexChild_progress T S request hbelow i state))

def physicalRefinementCurrentQuery {M J ny : ℕ} (pass copy T S t : ℕ)
    (node : OAI.EditApproximation.PhysicalNode M J) (hbelow : node.1.val < J) (q : OAI.EditApproximation.TargetInterval ny)
    (input : Fin M × OAI.EditApproximation.TargetInterval ny) :
    OAI.EditApproximation.FiniteQuery {child : OAI.EditApproximation.PhysicalTableRequest M J ny //
      child.combinedRank T S < (OAI.EditApproximation.PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} := by
  exact
    .read ⟨OAI.EditApproximation.PhysicalTableRequest.refinement pass copy (OAI.EditApproximation.physicalChild node hbelow input.1) T t input.2,
      OAI.EditApproximation.Lemmas.combinedRank_sameIndexChild T S
        (OAI.EditApproximation.PhysicalTableRequest.refinement pass copy node T t q) hbelow input.1 input.2⟩ .done

theorem _root_.OAI.EditApproximation.Lemmas.refinement_history_child_progress {M : ℕ} {J : ℕ} {ny : ℕ} (pass : ℕ) (copy : ℕ) (T : ℕ) (S : ℕ) (t : ℕ) (s : ℕ) (node : OAI.EditApproximation.PhysicalNode M J) (hbelow : LT.lt.{0} (↑(Sigma.fst.{0, 0} node)) J) (i : Fin M) (state : OAI.EditApproximation.TargetInterval ny) (previousState : OAI.EditApproximation.TargetInterval ny) (hs : LT.lt.{0} s t) :
    (OAI.EditApproximation.PhysicalTableRequest.refinement pass copy (OAI.EditApproximation.physicalChild node hbelow i) T s previousState).remainingDepth <
        (OAI.EditApproximation.PhysicalTableRequest.refinement pass copy node T t state).remainingDepth ∧
      OAI.EditApproximation.PhysicalTableRequest.rank T S (OAI.EditApproximation.PhysicalTableRequest.refinement pass copy (OAI.EditApproximation.physicalChild node hbelow i) T s previousState) <
        OAI.EditApproximation.PhysicalTableRequest.rank T S (OAI.EditApproximation.PhysicalTableRequest.refinement pass copy node T t state) := by
  constructor
  · unfold OAI.EditApproximation.PhysicalTableRequest.remainingDepth OAI.EditApproximation.PhysicalTableRequest.refinement OAI.EditApproximation.physicalChild
    dsimp only
    omega
  · dsimp only [OAI.EditApproximation.PhysicalTableRequest.rank, OAI.EditApproximation.PhysicalTableRequest.refinement]
    omega

def physicalRefinementEarlierQuery {M J ny : ℕ} (pass copy T S t : ℕ)
    (node : OAI.EditApproximation.PhysicalNode M J) (hbelow : node.1.val < J) (q : OAI.EditApproximation.TargetInterval ny)
    (input : Fin M × ℕ × OAI.EditApproximation.TargetInterval ny) :
    OAI.EditApproximation.FiniteQuery {child : OAI.EditApproximation.PhysicalTableRequest M J ny //
      child.combinedRank T S < (OAI.EditApproximation.PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} := by
  exact
    if hs : input.2.1 < t then
      .read ⟨OAI.EditApproximation.PhysicalTableRequest.refinement pass copy (OAI.EditApproximation.physicalChild node hbelow input.1) T input.2.1 input.2.2,
        OAI.EditApproximation.Lemmas.combinedRank_lt_of_progress T S _ _ (Or.inr
          ⟨(OAI.EditApproximation.Lemmas.refinement_history_child_progress pass copy T S t input.2.1
            node hbelow input.1 q input.2.2 hs).1.le,
            (OAI.EditApproximation.Lemmas.refinement_history_child_progress pass copy T S t input.2.1
              node hbelow input.1 q input.2.2 hs).2⟩)⟩ .done
    else .done 0

def physicalRefinementWarmupRead {M J ny : ℕ} (pass copy T S t : ℕ) (ht : 0 < t)
    (node : OAI.EditApproximation.PhysicalNode M J) (q : OAI.EditApproximation.TargetInterval ny)
    (otherNode : OAI.EditApproximation.PhysicalNode M J) (hnode : node.1.val ≤ otherNode.1.val)
    (j : ℕ) (hj : j ≤ T) (r : OAI.EditApproximation.TargetInterval ny) :
    OAI.EditApproximation.FiniteQuery {child : OAI.EditApproximation.PhysicalTableRequest M J ny //
      child.combinedRank T S < (OAI.EditApproximation.PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} := by
  exact
    .read ⟨OAI.EditApproximation.PhysicalTableRequest.warmup pass copy otherNode j r, by
      apply OAI.EditApproximation.Lemmas.combinedRank_lt_of_progress T S _ _
      apply Or.inr
      constructor
      · exact Nat.sub_le_sub_left hnode J
      · change pass * (T + S + 1) + j < pass * (T + S + 1) + (T + t)
        omega⟩ .done

theorem _root_.OAI.EditApproximation.Lemmas.rank_lt_previous_pass {M : ℕ} {J : ℕ} {ny : ℕ} (T : ℕ) (S : ℕ) (first : OAI.EditApproximation.PhysicalTableRequest M J ny) (second : OAI.EditApproximation.PhysicalTableRequest M J ny) (hpass : LT.lt.{0} second.pass first.pass) (hindex : LE.le.{0} second.index (HAdd.hAdd.{0, 0, 0} T S)) :
    OAI.EditApproximation.PhysicalTableRequest.rank T S second < OAI.EditApproximation.PhysicalTableRequest.rank T S first := by
  have hblock : second.pass * (T + S + 1) + second.index <
      (second.pass + 1) * (T + S + 1) := by
    nlinarith only [hindex]
  have hnext := Nat.mul_le_mul_right (T + S + 1) (Nat.succ_le_of_lt hpass)
  exact hblock.trans_le (hnext.trans (Nat.le_add_right _ _))

theorem _root_.OAI.EditApproximation.Lemmas.previousPassRequest_progress {M : ℕ} {J : ℕ} {ny : ℕ} (T : ℕ) (S : ℕ) (copy : ℕ) (parent : OAI.EditApproximation.PhysicalTableRequest M J ny) (hpass : LT.lt.{0} 0 parent.pass) (state : OAI.EditApproximation.TargetInterval ny) :
    (OAI.EditApproximation.previousPassRequest T S copy parent state).remainingDepth = parent.remainingDepth ∧
      (OAI.EditApproximation.previousPassRequest T S copy parent state).rank T S < parent.rank T S := by
  refine ⟨rfl, ?_⟩
  exact OAI.EditApproximation.Lemmas.rank_lt_previous_pass T S parent _ (by
    change parent.pass - 1 < parent.pass
    omega) le_rfl

def previousPassRead {M J ny : ℕ} (T S : ℕ)
    (parent : OAI.EditApproximation.PhysicalTableRequest M J ny) (hpass : 0 < parent.pass)
    (state : OAI.EditApproximation.TargetInterval ny) (copy : ℕ) :
    OAI.EditApproximation.FiniteQuery {child : OAI.EditApproximation.PhysicalTableRequest M J ny //
      child.combinedRank T S < parent.combinedRank T S} := by
  exact
    .read ⟨OAI.EditApproximation.previousPassRequest T S copy parent state,
      OAI.EditApproximation.Lemmas.combinedRank_lt_of_progress T S parent _ (Or.inr
        ⟨(OAI.EditApproximation.Lemmas.previousPassRequest_progress T S copy parent hpass state).1.le,
          (OAI.EditApproximation.Lemmas.previousPassRequest_progress T S copy parent hpass state).2⟩)⟩ .done

abbrev ChargedPhysicalRequest (M J ny passes copies T S : ℕ) :=
  Sum (OAI.EditApproximation.PhysicalEntry M J ny)
    {request : OAI.EditApproximation.PhysicalTableRequest M J ny // request.Bounded passes copies T S}

def chargedPreviousPass {M J ny passes copies T S : ℕ}
    (parent : {r : OAI.EditApproximation.PhysicalTableRequest M J ny // r.Bounded passes copies T S})
    (state : OAI.EditApproximation.TargetInterval ny) (copy : Fin copies) :
    {r : OAI.EditApproximation.PhysicalTableRequest M J ny // r.Bounded passes copies T S} :=
  ⟨OAI.EditApproximation.previousPassRequest T S copy.val parent.val state,
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) parent.property.1, copy.isLt, le_rfl⟩

def queryPhysicalTableRead {M J n : ℕ} (copies T S : ℕ)
    (parent : OAI.EditApproximation.PhysicalTableRequest M J n)
    (child : {r : OAI.EditApproximation.PhysicalTableRequest M J n // r.combinedRank T S < parent.combinedRank T S}) :
    OAI.EditApproximation.BitQuery {r : OAI.EditApproximation.PhysicalTableRequest M J n // r.combinedRank T S < parent.combinedRank T S}
      OAI.EditApproximation.BinaryFraction :=
  .charge ((OAI.EditApproximation.physicalTableCodeWithWork copies T S child.val).2 + 1) (.read child .done)

abbrev ComputedFamilyTableKey (source target : List ℕ) (N : ℕ) :=
  OAI.EditApproximation.ChargedPhysicalRequest (OAI.EditApproximation.integerParameters N).M
    (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M source.length) target.length
    (OAI.EditApproximation.computedSeedPassCount N + 1) (OAI.EditApproximation.inputHeight N ^ 2) (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S

def chargedPhysicalCodeWithWork {M J n passes copies T S : ℕ} :
    OAI.EditApproximation.ChargedPhysicalRequest M J n passes copies T S → ℕ × ℕ
  | .inl entry => let result := OAI.EditApproximation.physicalEntryCodeWithWork entry
      (2 * result.1, result.2 + 2)
  | .inr request => let result := OAI.EditApproximation.physicalTableCodeWithWork copies T S request.val
      (2 * result.1 + 1, result.2 + 3)

def queryPhysicalWarmupRead {M J n : ℕ} (copies pass copy T S t : ℕ) (ht : 0 < t)
    (node : OAI.EditApproximation.PhysicalNode M J) (q : OAI.EditApproximation.TargetInterval n)
    (otherNode : OAI.EditApproximation.PhysicalNode M J) (hnode : node.1.val ≤ otherNode.1.val)
    (j : ℕ) (hj : j ≤ T) (r : OAI.EditApproximation.TargetInterval n) :
    OAI.EditApproximation.BitQuery {child : OAI.EditApproximation.PhysicalTableRequest M J n // child.combinedRank T S <
      (OAI.EditApproximation.PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} OAI.EditApproximation.BinaryFraction := by
  exact
    OAI.EditApproximation.queryPhysicalTableRead copies T S (OAI.EditApproximation.PhysicalTableRequest.refinement pass copy node T t q)
      ⟨OAI.EditApproximation.PhysicalTableRequest.warmup pass copy otherNode j r, by
        apply OAI.EditApproximation.Lemmas.combinedRank_lt_of_progress T S _ _
        apply Or.inr
        constructor
        · exact Nat.sub_le_sub_left hnode J
        · change pass * (T + S + 1) + j < pass * (T + S + 1) + (T + t)
          omega⟩

def queryPhysicalCurrentRead {M J n : ℕ} (copies pass copy T S t : ℕ)
    (node : OAI.EditApproximation.PhysicalNode M J) (hbelow : node.1.val < J) (q : OAI.EditApproximation.TargetInterval n)
    (input : Fin M × OAI.EditApproximation.TargetInterval n) :
    OAI.EditApproximation.BitQuery {child : OAI.EditApproximation.PhysicalTableRequest M J n // child.combinedRank T S <
      (OAI.EditApproximation.PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} OAI.EditApproximation.BinaryFraction := by
  exact
    OAI.EditApproximation.queryPhysicalTableRead copies T S (OAI.EditApproximation.PhysicalTableRequest.refinement pass copy node T t q)
      ⟨OAI.EditApproximation.PhysicalTableRequest.refinement pass copy (OAI.EditApproximation.physicalChild node hbelow input.1) T t input.2,
        OAI.EditApproximation.Lemmas.combinedRank_sameIndexChild T S
          (OAI.EditApproximation.PhysicalTableRequest.refinement pass copy node T t q) hbelow input.1 input.2⟩

def queryPhysicalEarlierRead {M J n : ℕ} (copies pass copy T S t : ℕ)
    (node : OAI.EditApproximation.PhysicalNode M J) (hbelow : node.1.val < J) (q : OAI.EditApproximation.TargetInterval n)
    (input : Fin M × ℕ × OAI.EditApproximation.TargetInterval n) :
    OAI.EditApproximation.BitQuery {child : OAI.EditApproximation.PhysicalTableRequest M J n // child.combinedRank T S <
      (OAI.EditApproximation.PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} OAI.EditApproximation.BinaryFraction := by
  exact
    .charge ((OAI.EditApproximation.binaryNaturalCompareWithWork input.2.1 t).2 + 1)
      (if hs : (OAI.EditApproximation.binaryNaturalCompareWithWork input.2.1 t).1 = .lt then
        OAI.EditApproximation.queryPhysicalTableRead copies T S (OAI.EditApproximation.PhysicalTableRequest.refinement pass copy node T t q)
          ⟨OAI.EditApproximation.PhysicalTableRequest.refinement pass copy (OAI.EditApproximation.physicalChild node hbelow input.1) T input.2.1 input.2.2,
            OAI.EditApproximation.Lemmas.combinedRank_lt_of_progress T S _ _ (Or.inr
              ⟨(OAI.EditApproximation.Lemmas.refinement_history_child_progress pass copy T S t input.2.1
                node hbelow input.1 q input.2.2 ((OAI.EditApproximation.Lemmas.binaryNaturalCompareWithWork_lt _ _).mp hs)).1.le,
                (OAI.EditApproximation.Lemmas.refinement_history_child_progress pass copy T S t input.2.1
                  node hbelow input.1 q input.2.2 ((OAI.EditApproximation.Lemmas.binaryNaturalCompareWithWork_lt _ _).mp hs)).2⟩)⟩
      else .done (OAI.EditApproximation.BinaryFraction.nat 0))

def chargedPhysicalRemaining {M J n passes copies T S : ℕ} :
    OAI.EditApproximation.ChargedPhysicalRequest M J n passes copies T S → ℕ
  | .inl _ => 0
  | .inr request => request.val.remainingDepth

def chargedPhysicalCodeAllocation {M J n passes copies T S : ℕ} :
    OAI.EditApproximation.ChargedPhysicalRequest M J n passes copies T S → ℕ
  | .inl entry => 2 * entry.1.1.val + J + 12
  | .inr request => OAI.EditApproximation.physicalTableCodeAllocation request.val + 2

def queryPhysicalMassRead {M J n : ℕ} (copies pass copy T S t : ℕ) (ht : 0 < t)
    (node : OAI.EditApproximation.PhysicalNode M J) (hbelow : node.1.val < J) (q : OAI.EditApproximation.TargetInterval n)
    (input : Fin M × OAI.EditApproximation.TargetInterval n) :
    OAI.EditApproximation.BitQuery {child : OAI.EditApproximation.PhysicalTableRequest M J n // child.combinedRank T S <
      (OAI.EditApproximation.PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} OAI.EditApproximation.BinaryFraction :=
  OAI.EditApproximation.queryMeanRead T (fun j => OAI.EditApproximation.queryPhysicalWarmupRead copies pass copy T S t ht node q
    (OAI.EditApproximation.physicalChild node hbelow input.1) (by change node.1.val ≤ node.1.val + 1; omega)
    j.val j.isLt.le input.2)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Finset MeasureTheory ProbabilityTheory

def integerClosedRange (lo hi : ℤ) : List ℤ :=
  (List.range (hi - lo + 1).toNat).map fun i : ℕ => lo + (i : ℤ)

def groupSampleCount (M Q b : ℕ) (h : ℚ) : ℕ := min M ⌈(Q : ℚ) * M * h / b⌉₊

def groupScaleTrueCost {M : ℕ} (h : ℚ) (envelope value : Fin M → ℚ) : ℚ :=
  ∑ i, if envelope i = h then value i else 0

def selectGroupMember {ι : Type u_1} (members : List ι) (hnonempty : members ≠ [])
    (estimate : ι → ℚ) : ι :=
  (members.argmax fun member => -estimate member).getD (members.head hnonempty)

instance coarseDrawsMeasurableSpace (B D : ℕ) [MeasurableSpace (Fin B)] :
    MeasurableSpace (OAI.EditApproximation.CoarseThresholdDraws B D) := by
  induction D with
  | zero => exact inferInstanceAs (MeasurableSpace PUnit)
  | succ D ih =>
    letI := ih
    exact inferInstanceAs
      (MeasurableSpace ((Fin B → Fin B) × (Fin B → OAI.EditApproximation.CoarseThresholdDraws B D)))

def groupDyadicScales (M b : ℕ) (F : ℚ) : List ℚ :=
  (OAI.EditApproximation.integerClosedRange (Int.clog 2 ((b : ℚ) / M)) (Int.log 2 (64 * F * b))).map
    fun exponent => (2 : ℚ) ^ exponent

def groupScaleEstimate {M : ℕ} (k : ℕ) (h : ℚ) (envelope value : Fin M → ℚ)
    (draw : Fin k → Fin M) : ℚ :=
  if k = M then OAI.EditApproximation.groupScaleTrueCost h envelope value
  else (M : ℚ) / k * ∑ j, if envelope (draw j) = h then value (draw j) else 0

noncomputable def coarseDrawMeasure (B : ℕ) [NeZero B]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)] :
    (D : ℕ) → Measure (OAI.EditApproximation.CoarseThresholdDraws B D)
  | 0 => Measure.dirac PUnit.unit
  | D + 1 =>
    (Measure.pi fun _ : Fin B => (PMF.uniformOfFintype (Fin B)).toMeasure).prod
      (Measure.pi fun _ : Fin B => coarseDrawMeasure B D)

def groupMemberEstimate {M T : ℕ} (scales : Fin T → ℚ) (count : Fin T → ℕ)
    (connection : ℚ) (envelope value : Fin M → ℚ)
    (draw : ∀ scale : Fin T, Fin (count scale) → Fin M) : ℚ :=
  connection + ∑ scale, OAI.EditApproximation.groupScaleEstimate (count scale) (scales scale) envelope value (draw scale)

end OAI.EditApproximation

end


