-- Prove2me | Definitions.Def_EditApproxScheme_01
-- name    : EditApproxScheme_01
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T16:29:57.018064+00:00
-- url     : https://prove2.me/theorems/ec7e22b1-19bf-42a2-9cc4-6b2708d45f30
-- title:
--   Edit-distance approximation scheme, part 1 of 20: binary arithmetic foundations
-- statement:
--   This is **part 1 of 20** of the definitions of a uniform almost-linear approximation scheme for edit distance, which the main statement `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` is about. This part contains the arithmetic foundation: natural numbers as least-significant-bit-first Boolean words with bitwise sum, carry and borrow, signed sign–magnitude integers, binary fractions, division with remainder, and basic list utilities (sorting, erasing, mapping), each paired with an operation count and an allocation function. It also contains the dyadic and coarse exponents used to size the algorithm, and three small rewriting lemmas about `if`-expressions that later parts use.
--
--   Each part imports the previous one, so importing part 20 brings all definitions into scope. A description of the whole scheme is given in part 20.
--
--   **Formalization Note** These 20 parts replace the single 1.4 MB block `Def_EditApproximation`, which was too large for the platform to import. In the source, the supporting lemmas were pasted as local `have` proofs inside the definition bodies: 948 copies of 145 lemmas. Each lemma is now proved once as a top-level theorem and cited by name; one lemma that nothing used was dropped. The file was then split into sequential parts by deleting declarations. All 1,403 declarations from the source keep exactly the same elaborated types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean#L9-L760 (line numbers refer to the lemma-lifted file, 12,145 lines)

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean
-- Part 1 of 20 of the edit-distance approximation definitions: embedded proof lemmas lifted
-- to top-level theorems (OAI.EditApproximation.Lemmas.*), then split by skeleton subtraction.

import Mathlib

theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI.EditDistortion

end OAI.EditDistortion

/-! A uniform almost-linear approximation scheme for edit distance.
The statement retains the concrete binary algorithm and its exact resource accounting. -/

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

def bitWordValue : List Bool → ℕ
  | [] => 0
  | bit :: bits => bit.toNat + 2 * bitWordValue bits

def bitSum (a b carry : Bool) : Bool := xor (xor a b) carry

def bitCarry (a b carry : Bool) : Bool := (a && b) || (a && carry) || (b && carry)

structure UnreducedRational where
  num : ℤ
  den : ℕ
  den_pos : 0 < den

def orderingMatches (o : Ordering) (a b : ℕ) : Prop :=
  (o = .lt ∧ a < b) ∨ (o = .eq ∧ a = b) ∨ (o = .gt ∧ b < a)

def bitOrdering (high : Ordering) (a b : Bool) : Ordering :=
  match high with
  | .lt => .lt
  | .gt => .gt
  | .eq => if a = b then .eq else if a then .gt else .lt

def bitDifference (a b borrow : Bool) : Bool := xor (xor a b) borrow

def bitBorrow (a b borrow : Bool) : Bool := ((!a) && (b || borrow)) || (b && borrow)

structure SignedBinary where
  negative : Bool
  bits : List Bool

def signedMagnitude (negative : Bool) (magnitude : ℕ) : ℤ :=
  if negative then -(magnitude : ℤ) else magnitude

def trimBitWordWithWork : List Bool → List Bool × ℕ
  | [] => ([], 1)
  | bit :: bits =>
    let tail := trimBitWordWithWork bits
    (if tail.1 = [] ∧ bit = false then [] else bit :: tail.1, tail.2 + 3)

def balancedCut (lo width M i : ℕ) : ℕ := lo + i * width / M

def gridRound (spacing position : ℕ) : ℕ := spacing * (position / spacing)

def rationalMinimum (fallback : ℚ) : List ℚ → ℚ
  | [] => fallback
  | value :: rest => min value (rationalMinimum fallback rest)

structure RationalBellmanAction (Parent : Type u_1) (Child : Type u_2) (M : ℕ) where
  center : Parent
  connection : ℚ
  childState : Fin M → Child

def rationalRefinementUpdate (δ cone : ℚ) : Option ℚ → ℚ
  | none => cone
  | some online => min cone (max (cone / (1 + δ)) online)

def heightExponent (N : ℕ) : ℕ := Nat.clog 2 (Nat.clog 2 (N + 2))

def coarseExponent (ell : ℕ) : ℕ := Nat.sqrt (Nat.sqrt (Nat.log 2 ell))

structure IntegerParameters where
  H : ℕ
  ell : ℕ
  p : ℕ
  B : ℕ
  initialFactor : ℕ
  M : ℕ
  P : ℕ
  T : ℕ
  S : ℕ

structure RationalParameters where
  F : ℚ
  initialSlope : ℚ
  coneSlope : ℚ
  delta : ℚ
  kappa : ℚ
  tau : ℚ
  theta : ℚ
  gamma : ℚ
  eta : ℚ

def gridPointsBetween (g lo hi : ℕ) : List ℕ :=
  (List.range' (lo ⌈/⌉ g) ((hi / g + 1) - lo ⌈/⌉ g)).map fun i => g * i

def scaledSeedValue (U : ℕ) (a gap : ℚ) : ℚ :=
  max (⌈(U : ℚ) / a⌉₊ : ℚ) |gap|

def dyadicScales (N : ℕ) : List ℕ :=
  (List.range (Nat.log 2 N + 1)).map fun k => 2 ^ k

def seedGridSpacing (b P : ℕ) : ℕ := max 1 (b / P)

def finiteAssignments {α : Type u_1} : (M : ℕ) → (Fin M → List α) → List (Fin M → α)
  | 0, _ => [Fin.elim0]
  | M + 1, choices =>
    (choices 0).flatMap fun head =>
      (finiteAssignments M (fun i => choices i.succ)).map fun tail => Fin.cons head tail

def powerTwoWord (n : ℕ) : List Bool := List.replicate n false ++ [true]

def filterWithWork {α : Type u_1} (test : α → Bool × ℕ) : List α → List α × ℕ
  | [] => ([], 0)
  | a :: rest =>
    let current := test a
    let tail := filterWithWork test rest
    (if current.1 then a :: tail.1 else tail.1, current.2 + tail.2 + 3)

def allWithWork {α : Type u_1} (test : α → Bool × ℕ) : List α → Bool × ℕ
  | [] => (true, 0)
  | a :: rest =>
    let current := test a
    let tail := allWithWork test rest
    (current.1 && tail.1, current.2 + tail.2 + 3)

def arithmeticMapWithWork {α : Type u_1} {β : Type u_2} (f : α → β × ℕ) : List α → List β × ℕ
  | [] => ([], 0)
  | a :: rest =>
    let current := f a
    let tail := arithmeticMapWithWork f rest
    (current.1 :: tail.1, current.2 + tail.2 + 3)

def arithmeticFlatMapWithWork {α : Type u_1} {β : Type u_2} (f : α → List β × ℕ) : List α → List β × ℕ
  | [] => ([], 0)
  | a :: rest =>
    let current := f a
    let tail := arithmeticFlatMapWithWork f rest
    (current.1 ++ tail.1, current.2 + tail.2 + current.1.length + 3)

def upperMedian (values : List ℕ) : ℕ :=
  (values.mergeSort (· ≤ ·)).getD (values.length / 2) 0

def filterMapWithWork {α : Type u_1} {β : Type u_2} (f : α → Option β × ℕ) : List α → List β × ℕ
  | [] => ([], 0)
  | a :: rest =>
    let first := f a
    let tail := filterMapWithWork f rest
    (match first.1 with | none => tail.1 | some b => b :: tail.1, first.2 + tail.2 + 3)

def cellGridPoints (side : ℚ) (g cell : ℕ) : List ℕ :=
  (List.range' ⌈(cell : ℚ) * side / g⌉₊
    (⌈((cell : ℚ) + 1) * side / g⌉₊ - ⌈(cell : ℚ) * side / g⌉₊)).map fun i => g * i

def groupRoundSpacing (exponent : ℕ) (h : ℚ) : ℕ :=
  ⌈max 1 ((2 : ℚ) ^ (-(exponent : ℤ)) * h)⌉₊

def refinementFactor (A : ℚ) (F : ℕ) : ℚ := max 1 (A / F)

def localCellCoordinates (side : ℚ) (p radius : ℕ) : List ℕ :=
  let first := ⌊((p - radius : ℕ) : ℚ) / side⌋₊
  let last := ⌊((p + radius : ℕ) : ℚ) / side⌋₊
  List.range' first (last + 1 - first)

def dyadicSeedPassCount (f initial : ℕ) : ℕ := (initial - f) ⌈/⌉ (f - 2)

def dyadicSeedExponent (f initial pass : ℕ) : ℕ := initial - pass * (f - 2)

def memberByWithWork {α : Type u_1} (equal : α → α → Bool × ℕ) (a : α) : List α → Bool × ℕ
  | [] => (false, 1)
  | b :: rest =>
    let test := equal a b
    let tail := memberByWithWork equal a rest
    (test.1 || tail.1, test.2 + tail.2 + 1)

inductive BinaryMemo (α : Type u_1) where
  | empty
  | node (value : Option α) (left right : BinaryMemo α)

def binaryMemoKey : ℕ → ℕ → List Bool
  | 0, _ => []
  | d + 1, n => decide (n % 2 = 1) :: binaryMemoKey d (n / 2)

inductive FiniteQuery (ι : Type u_1) where
  | done (value : ℚ)
  | read (key : ι) (next : ℚ → FiniteQuery ι)

def finiteAnswerTable {κ : Type u_1} [DecidableEq κ] : List κ → List ℚ → κ → ℚ
  | key :: keys, value :: values, query =>
      if query = key then value else finiteAnswerTable keys values query
  | _, _, _ => 0

def queryFinRange (n m : ℕ) (h : n = m) : List (Fin m) :=
  (List.finRange n).map fun i => ⟨i.val, by simpa only [← h] using i.isLt⟩

def queryInsertWithWork {α : Type u_1} (le : α → α → Bool × ℕ) (a : α) : List α → List α × ℕ
  | [] => ([a], 1)
  | b :: rest =>
    let test := le a b
    if test.1 then (a :: b :: rest, test.2 + 2)
    else
      let tail := queryInsertWithWork le a rest
      (b :: tail.1, test.2 + tail.2 + 2)

def integerSymbolCode : ℤ → ℕ
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

inductive PositionCounts where
  | empty
  | node (count : ℕ) (left right : PositionCounts)

def integerMagnitude : List ℤ → ℕ
  | [] => 0
  | z :: zs => max z.natAbs (integerMagnitude zs)

def integerInputPositionBits (target : List ℤ) : ℕ := Nat.size target.length

def dpLength {α : Type u_1} : List α → ℕ × ℕ
  | [] => (0, 1)
  | _ :: rest => let result := dpLength rest; (result.1 + 1, result.2 + 1)

def dpDrop {α : Type u_1} : ℕ → List α → List α × ℕ
  | 0, word => (word, 1)
  | _ + 1, [] => ([], 1)
  | n + 1, _ :: rest => let result := dpDrop n rest; (result.1, result.2 + 1)

def dpTake {α : Type u_1} : ℕ → List α → List α × ℕ
  | 0, _ => ([], 1)
  | _ + 1, [] => ([], 1)
  | n + 1, first :: rest => let result := dpTake n rest; (first :: result.1, result.2 + 1)

def dpGetD : List ℕ → ℕ → ℕ × ℕ
  | [], _ => (0, 1)
  | first :: _, 0 => (first, 1)
  | _ :: rest, n + 1 => let result := dpGetD rest n; (result.1, result.2 + 1)

def dpMember {α : Type u_1} [DecidableEq α] (a : α) : List α → Bool × ℕ
  | [] => (false, 1)
  | first :: rest => if a = first then (true, 1) else
      let result := dpMember a rest; (result.1, result.2 + 1)

def dpMinimum (fallback : ℕ) : List ℕ → ℕ × ℕ
  | [] => (fallback, 1)
  | first :: rest => let result := dpMinimum fallback rest; (min first result.1, result.2 + 1)

def integerMagnitudeWithWork : List ℤ → ℕ × ℕ
  | [] => (0, 0)
  | z :: rest =>
    let tail := integerMagnitudeWithWork rest
    (max z.natAbs tail.1, tail.2 + 2)

def inputBitLengthWithWork (n : ℕ) : ℕ × ℕ :=
  if h : n = 0 then (0, 1) else
    let tail := inputBitLengthWithWork (n / 2)
    (tail.1 + 1, tail.2 + 2)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

def naturalPairWithWork (a b : ℕ) : ℕ × ℕ :=
  if a < b then (b * b + a, 4) else (a * a + a + b, 5)

def inspectBitPrefix : ℕ → List Bool → Bool × ℕ
  | 0, [] => (true, 1)
  | 0, _ :: _ => (false, 1)
  | _ + 1, [] => (true, 1)
  | n + 1, _ :: rest =>
    let result := inspectBitPrefix n rest
    (result.1, result.2 + 1)

def memoRequestCells (bits addressCells : ℕ) : ℕ := addressCells + 8 * (bits + 1) + 64

def arithmeticMapAllocation {α : Type u_1} (allocation : α → ℕ) : List α → ℕ
  | [] => 0
  | a :: rest => allocation a + arithmeticMapAllocation allocation rest + 1

def arithmeticFlatMapAllocation {α : Type u_1} {β : Type u_2} (f : α → List β × ℕ)
    (allocation : α → ℕ) : List α → ℕ
  | [] => 0
  | x :: xs => allocation x + arithmeticFlatMapAllocation f allocation xs + (f x).1.length

def filterAllocation {α : Type u_1} (test : α → Bool × ℕ) (allocation : α → ℕ) : List α → ℕ
  | [] => 0
  | x :: xs => allocation x + filterAllocation test allocation xs + if (test x).1 then 1 else 0

def filterMapAllocation {α : Type u_1} {β : Type u_2} (f : α → Option β × ℕ)
    (allocation : α → ℕ) : List α → ℕ
  | [] => 0
  | x :: xs => allocation x + filterMapAllocation f allocation xs + if (f x).1.isSome then 1 else 0

def naturalEqualAllocation (a b : ℕ) : ℕ := a.bits.length + b.bits.length + 1

def memberByAllocation {α : Type u_1} (allocation : α → α → ℕ) (a : α) : List α → ℕ
  | [] => 0
  | b :: rest => allocation a b + memberByAllocation allocation a rest + 1

def naturalWordLEAllocation (a b : List Bool) : ℕ := a.length + b.length + 1

def vectorMapAllocation (d : ℕ) (allocation : Fin d → ℕ) : ℕ :=
  (∑ i, allocation i) + 3 * d

def allAllocation {α : Type u_1} (allocation : α → ℕ) : List α → ℕ
  | [] => 0
  | x :: xs => allocation x + allAllocation allocation xs + 1

def queryInsertAllocation {α : Type u_1} (le : α → α → Bool × ℕ)
    (allocation : α → α → ℕ) (a : α) : List α → ℕ
  | [] => 1
  | b :: rest => allocation a b + if (le a b).1 then 2 else queryInsertAllocation le allocation a rest + 1

def wordLEAllocation (_a _b : List Bool) : ℕ := 0

def indexedLeafAllocation (symbolBits positionBits : ℕ) (symbol : Option ℕ) (lo hi : ℕ) : ℕ :=
  match symbol with
  | none => 1
  | some _ => if lo = hi then 1 else symbolBits + 2 * positionBits + 4

def storedNaturalBits (values : List ℕ) : ℕ :=
  1 + (values.map fun a => Nat.size a + 1).sum

def coarseHistoryKeyCost {α : Type u_1} {β : Type u_2} {ι : Type u_3} (cost : ι → ℕ) : Sum α (Sum ι β) → ℕ
  | .inr (.inl entry) => cost entry
  | _ => 0

def bitAddNilLeftWithWork (right : List Bool) (carry : Bool) : List Bool × ℕ :=
  match right with
  | [] => (if carry then [true] else [], 1)
  | b :: bs =>
    let rest := bitAddNilLeftWithWork bs (OAI.EditApproximation.bitCarry false b carry)
    (OAI.EditApproximation.bitSum false b carry :: rest.1, rest.2 + 9)
termination_by structural right

def bitCompareNilLeftWithWork (right : List Bool) : Ordering × ℕ :=
  match right with
  | [] => (.eq, 1)
  | b :: bs =>
    let high := bitCompareNilLeftWithWork bs
    (OAI.EditApproximation.bitOrdering high.1 false b, high.2 + 4)
termination_by structural right

def bitSubtractNilLeftWithWork (right : List Bool) (borrow : Bool) : List Bool × Bool × ℕ :=
  match right with
  | [] => ([], borrow, 1)
  | b :: bs =>
    let rest := bitSubtractNilLeftWithWork bs (OAI.EditApproximation.bitBorrow false b borrow)
    (OAI.EditApproximation.bitDifference false b borrow :: rest.1, rest.2.1, rest.2.2 + 9)
termination_by structural right

structure BinaryFraction where
  numerator : OAI.EditApproximation.SignedBinary
  denominator : List Bool
  denominator_pos : 0 < OAI.EditApproximation.bitWordValue denominator

def rationalActionValue {Parent : Type u_1} {Child : Type u_2} {M : ℕ}
    (distance : Parent → Parent → ℚ) (L : ℚ) (child : Child → ℚ)
    (query : Parent) (action : OAI.EditApproximation.RationalBellmanAction Parent Child M) : ℚ :=
  L * distance query action.center + action.connection + ∑ i, child (action.childState i)

def inputHeight (N : ℕ) : ℕ := 2 ^ OAI.EditApproximation.heightExponent N

def smallLogExponent (N : ℕ) : ℕ := Nat.clog 2 (max 1 (OAI.EditApproximation.heightExponent N))

def rationalParameters (ell : ℕ) : OAI.EditApproximation.RationalParameters :=
  { F := ell, initialSlope := 32 * ell, coneSlope := 128 * ell,
    delta := 1 / (ell : ℚ) ^ 10, kappa := 1 / (ell : ℚ) ^ 4,
    tau := 1 / (ell : ℚ) ^ 4, theta := 1 / (ell : ℚ) ^ 40,
    gamma := 1 / (ell : ℚ) ^ 20, eta := (ell : ℚ) ^ 5 }

def materializedAssignmentsWithWork {α : Type u_1} :
    (M : ℕ) → (Fin M → List α) → List (Vector α M) × ℕ
  | 0, _ => ([Vector.ofFn Fin.elim0], 1)
  | M + 1, choices =>
    let previous := materializedAssignmentsWithWork M (fun i => choices i.succ)
    let expanded := OAI.EditApproximation.arithmeticFlatMapWithWork (fun head =>
      OAI.EditApproximation.arithmeticMapWithWork (fun tail : Vector α M =>
        (Vector.ofFn (Fin.cons head tail.get), 3 * (M + 1))) previous.1) (choices 0)
    (expanded.1, previous.2 + expanded.2 + 1)

def dyadicScalesWithWork (N : ℕ) : List ℕ × ℕ :=
  let count := max 1 N.bits.length
  let values := OAI.EditApproximation.arithmeticMapWithWork (fun e =>
    let word := OAI.EditApproximation.powerTwoWord e
    (OAI.EditApproximation.bitWordValue word, e + 3)) (List.range count)
  (values.1, values.2 + N.bits.length + count + 2)

def dedupByWithWork {α : Type u_1} (equal : α → α → Bool × ℕ) : List α → List α × ℕ
  | [] => ([], 1)
  | a :: rest =>
    let tail := dedupByWithWork equal rest
    let member := OAI.EditApproximation.memberByWithWork equal a rest
    (if member.1 then tail.1 else a :: tail.1, tail.2 + member.2 + 2)

def queryEraseLoopWithWork {α : Type u_1} (equal : α → α → Bool × ℕ) :
    List α → List α → List α × ℕ
  | [], seen => (seen.reverse, seen.length + 1)
  | a :: rest, seen =>
    let test := OAI.EditApproximation.memberByWithWork equal a seen
    let tail := queryEraseLoopWithWork equal rest (if test.1 then seen else a :: seen)
    (tail.1, test.2 + tail.2 + 2)

structure RecursiveMemoResult (κ : Type u_1) where
  value : ℚ
  memory : OAI.EditApproximation.BinaryMemo ℚ
  freshKeys : List κ
  dictionaryVisits : ℕ
  requests : ℕ

def querySortWithWork {α : Type u_1} (le : α → α → Bool × ℕ) : List α → List α × ℕ
  | [] => ([], 1)
  | a :: rest =>
    let tail := querySortWithWork le rest
    let inserted := OAI.EditApproximation.queryInsertWithWork le a tail.1
    (inserted.1, tail.2 + inserted.2 + 1)

def encodeIntegerSymbolsWithWork : List ℤ → List ℕ × ℕ
  | [] => ([], 0)
  | z :: zs =>
    let rest := encodeIntegerSymbolsWithWork zs
    (OAI.EditApproximation.integerSymbolCode z :: rest.1, rest.2 + 3)

def integerInputSymbolBits (source target : List ℤ) : ℕ :=
  Nat.size (2 * OAI.EditApproximation.integerMagnitude (source ++ target))

def dpSingleton {α : Type u_1} [DecidableEq α] (a : α) (word : List α) : ℕ × ℕ :=
  if word = [] then (1, 1) else
    let count := OAI.EditApproximation.dpLength word
    let found := OAI.EditApproximation.dpMember a word
    (count.1 - if found.1 then 1 else 0, count.2 + found.2 + 2)

def dpCandidateAllocation {α : Type u_1} (target : List α) (j k : ℕ) : ℕ :=
  (OAI.EditApproximation.dpTake k (OAI.EditApproximation.dpDrop j target).1).1.length

def integerInputInspectionWithWork (source target : List ℤ) : (ℕ × ℕ) × ℕ :=
  let left := OAI.EditApproximation.integerMagnitudeWithWork source
  let right := OAI.EditApproximation.integerMagnitudeWithWork target
  let lengths := (OAI.EditApproximation.dpLength source, OAI.EditApproximation.dpLength target)
  let symbols := OAI.EditApproximation.inputBitLengthWithWork (2 * max left.1 right.1)
  let positions := OAI.EditApproximation.inputBitLengthWithWork lengths.2.1
  ((symbols.1, positions.1),
    left.2 + right.2 + lengths.1.2 + lengths.2.2 + symbols.2 + positions.2 + 4)

def bitAddNilLeftAllocation (right : List Bool) (carry : Bool) : ℕ :=
  match right with
  | [] => if carry then 1 else 0
  | b :: bs => bitAddNilLeftAllocation bs (OAI.EditApproximation.bitCarry false b carry) + 1
termination_by structural right

def bitSubtractNilLeftAllocation (right : List Bool) (borrow : Bool) : ℕ :=
  match right with
  | [] => 0
  | b :: bs => bitSubtractNilLeftAllocation bs (OAI.EditApproximation.bitBorrow false b borrow) + 1
termination_by structural right

def trimBitWordAllocation : List Bool → ℕ
  | [] => 0
  | bit :: bits => trimBitWordAllocation bits +
      if (OAI.EditApproximation.trimBitWordWithWork bits).1 = [] ∧ bit = false then 0 else 1

def dedupByAllocation {α : Type u_1} (equal : α → α → Bool × ℕ)
    (allocation : α → α → ℕ) : List α → ℕ
  | [] => 0
  | a :: rest => dedupByAllocation equal allocation rest + OAI.EditApproximation.memberByAllocation allocation a rest +
      if (OAI.EditApproximation.memberByWithWork equal a rest).1 then 0 else 1

def dyadicScalesAllocation (N : ℕ) : ℕ :=
  OAI.EditApproximation.arithmeticMapAllocation (fun e => e + 1) (List.range (max 1 N.bits.length)) + N.bits.length + max 1 N.bits.length

def queryRangeValidAllocation (B range : ℕ) : ℕ :=
  (0 : ℕ).bits.length + range.bits.length + OAI.EditApproximation.naturalWordLEAllocation range.bits B.bits

def queryEraseLoopAllocation {α : Type u_1} (equal : α → α → Bool × ℕ)
    (allocation : α → α → ℕ) : List α → List α → ℕ
  | [], seen => seen.length
  | a :: rest, seen =>
    OAI.EditApproximation.memberByAllocation allocation a seen +
      queryEraseLoopAllocation equal allocation rest (if (OAI.EditApproximation.memberByWithWork equal a seen).1 then seen else a :: seen) +
      if (OAI.EditApproximation.memberByWithWork equal a seen).1 then 0 else 1

def queryEncodedLEAllocation {α : Type u_1} (code : α → ℕ × ℕ) (allocation : α → ℕ) (a b : α) : ℕ :=
  allocation a + allocation b + OAI.EditApproximation.naturalWordLEAllocation (code a).1.bits (code b).1.bits +
    Nat.size (code a).1 + Nat.size (code b).1

def bitAddWithWork (left right : List Bool) (carry : Bool) : List Bool × ℕ :=
  match left with
  | [] => OAI.EditApproximation.bitAddNilLeftWithWork right carry
  | a :: as =>
    match right with
    | [] =>
      let rest := bitAddWithWork as [] (OAI.EditApproximation.bitCarry a false carry)
      (OAI.EditApproximation.bitSum a false carry :: rest.1, rest.2 + 9)
    | b :: bs =>
      let rest := bitAddWithWork as bs (OAI.EditApproximation.bitCarry a b carry)
      (OAI.EditApproximation.bitSum a b carry :: rest.1, rest.2 + 9)
termination_by structural left

def bitCompareWithWork (left right : List Bool) : Ordering × ℕ :=
  match left with
  | [] => OAI.EditApproximation.bitCompareNilLeftWithWork right
  | a :: as =>
    match right with
    | [] =>
      let high := bitCompareWithWork as []
      (OAI.EditApproximation.bitOrdering high.1 a false, high.2 + 4)
    | b :: bs =>
      let high := bitCompareWithWork as bs
      (OAI.EditApproximation.bitOrdering high.1 a b, high.2 + 4)
termination_by structural left

def bitSubtractWithWork (left right : List Bool) (borrow : Bool) : List Bool × Bool × ℕ :=
  match left with
  | [] => OAI.EditApproximation.bitSubtractNilLeftWithWork right borrow
  | a :: as =>
    match right with
    | [] =>
      let rest := bitSubtractWithWork as [] (OAI.EditApproximation.bitBorrow a false borrow)
      (OAI.EditApproximation.bitDifference a false borrow :: rest.1, rest.2.1, rest.2.2 + 9)
    | b :: bs =>
      let rest := bitSubtractWithWork as bs (OAI.EditApproximation.bitBorrow a b borrow)
      (OAI.EditApproximation.bitDifference a b borrow :: rest.1, rest.2.1, rest.2.2 + 9)
termination_by structural left

def rationalBellman {Parent : Type u_1} {Child : Type u_2} {M : ℕ}
    (fallback : Parent → ℚ) (distance : Parent → Parent → ℚ) (L : ℚ)
    (actions : List (OAI.EditApproximation.RationalBellmanAction Parent Child M)) (child : Child → ℚ) (query : Parent) : ℚ :=
  OAI.EditApproximation.rationalMinimum (fallback query) (actions.map (OAI.EditApproximation.rationalActionValue distance L child query))

def inputSmallLog (N : ℕ) : ℕ := 2 ^ OAI.EditApproximation.smallLogExponent N

structure BinaryBellmanAction (Parent : Type u_1) (Child : Type u_2) (M : ℕ) where
  center : Parent
  connection : OAI.EditApproximation.BinaryFraction
  childState : Fin M → Child

def queryEraseWithWork {α : Type u_1} (equal : α → α → Bool × ℕ) (xs : List α) :
    List α × ℕ := OAI.EditApproximation.queryEraseLoopWithWork equal xs []

inductive BitQuery (ι : Type u_1) (β : Type u_2) where
  | done (value : β)
  | read (key : ι) (next : OAI.EditApproximation.BinaryFraction → BitQuery ι β)
  | charge (work : ℕ) (next : BitQuery ι β)

def dpCandidate {α : Type u_1} [DecidableEq α] (a : α) (target : List α)
    (previous : List ℕ) (j k : ℕ) : ℕ × ℕ :=
  let suffix := OAI.EditApproximation.dpDrop j target
  let piece := OAI.EditApproximation.dpTake k suffix.1
  let one := OAI.EditApproximation.dpSingleton a piece.1
  let old := OAI.EditApproximation.dpGetD previous (j + k)
  (one.1 + old.1, suffix.2 + piece.2 + one.2 + old.2 + 3)

def dpCellAllocation {α : Type u_1} (target : List α) (j : ℕ) : ℕ :=
  OAI.EditApproximation.dpCandidateAllocation target j 0 +
    ((List.range (target.length - j + 1)).map (OAI.EditApproximation.dpCandidateAllocation target j)).sum +
      4 * (target.length - j + 1)

def initialThresholdQ (N : ℕ) : ℚ := (OAI.EditApproximation.inputHeight N : ℚ) ^ 4

def initialLambda (N : ℕ) : ℚ := 1 / (64 * OAI.EditApproximation.inputHeight N)

structure BitRecursiveMemoResult (κ : Type u_1) where
  value : OAI.EditApproximation.BinaryFraction
  memory : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.BinaryFraction
  freshKeys : List κ
  dictionaryVisits : ℕ
  requests : ℕ
  localWork : ℕ

structure RefinementParameterWords where
  tau : OAI.EditApproximation.BinaryFraction
  factor : OAI.EditApproximation.BinaryFraction
  eta : OAI.EditApproximation.BinaryFraction
  kappa : OAI.EditApproximation.BinaryFraction
  delta : OAI.EditApproximation.BinaryFraction

def inspectAccuracyWithWork (budget : ℕ) (epsilon : OAI.EditApproximation.BinaryFraction) : Option OAI.EditApproximation.BinaryFraction × ℕ :=
  let numerator := OAI.EditApproximation.inspectBitPrefix budget epsilon.numerator.bits
  let denominator := OAI.EditApproximation.inspectBitPrefix budget epsilon.denominator
  (if numerator.1 && denominator.1 then some epsilon else none,
    numerator.2 + denominator.2 + 2)

local instance queryRoundsNeZero (N : ℕ) : NeZero (OAI.EditApproximation.inputHeight N ^ 2) :=
  ⟨pow_ne_zero _ (Nat.ne_of_gt (Nat.two_pow_pos _))⟩

def bitAddAllocation (left right : List Bool) (carry : Bool) : ℕ :=
  match left with
  | [] => OAI.EditApproximation.bitAddNilLeftAllocation right carry
  | a :: as =>
    match right with
    | [] => bitAddAllocation as [] (OAI.EditApproximation.bitCarry a false carry) + 1
    | b :: bs => bitAddAllocation as bs (OAI.EditApproximation.bitCarry a b carry) + 1
termination_by structural left

def bitSubtractAllocation (left right : List Bool) (borrow : Bool) : ℕ :=
  match left with
  | [] => OAI.EditApproximation.bitSubtractNilLeftAllocation right borrow
  | a :: as =>
    match right with
    | [] => bitSubtractAllocation as [] (OAI.EditApproximation.bitBorrow a false borrow) + 1
    | b :: bs => bitSubtractAllocation as bs (OAI.EditApproximation.bitBorrow a b borrow) + 1
termination_by structural left

def materializedAssignmentsAllocation {α : Type u_1} :
    (M : ℕ) → (Fin M → List α) → ℕ
  | 0, _ => 1
  | M + 1, choices =>
    let previous := (OAI.EditApproximation.materializedAssignmentsWithWork M (fun i => choices i.succ)).1
    let build := fun head => OAI.EditApproximation.arithmeticMapWithWork (fun tail : Vector α M =>
      (Vector.ofFn (Fin.cons head tail.get), 3 * (M + 1))) previous
    materializedAssignmentsAllocation M (fun i => choices i.succ) +
      OAI.EditApproximation.arithmeticFlatMapAllocation build
        (fun _ => OAI.EditApproximation.arithmeticMapAllocation (fun _ : Vector α M => M + 1) previous) (choices 0)

def queryEraseAllocation {α : Type u_1} (equal : α → α → Bool × ℕ)
    (allocation : α → α → ℕ) (xs : List α) : ℕ := OAI.EditApproximation.queryEraseLoopAllocation equal allocation xs []

def querySortAllocation {α : Type u_1} (le : α → α → Bool × ℕ)
    (allocation : α → α → ℕ) : List α → ℕ
  | [] => 0
  | a :: rest => querySortAllocation le allocation rest +
    OAI.EditApproximation.queryInsertAllocation le allocation a (OAI.EditApproximation.querySortWithWork le rest).1

def binaryNaturalAddWithWork (a b : ℕ) : List Bool × ℕ :=
  OAI.EditApproximation.bitAddWithWork a.bits b.bits false

def bitMulWithWork : List Bool → List Bool → List Bool × ℕ
  | [], _ => ([], 1)
  | bit :: bits, right =>
    let rest := bitMulWithWork bits right
    if bit then
      let total := OAI.EditApproximation.bitAddWithWork (false :: rest.1) right false
      (total.1, rest.2 + total.2 + 2)
    else (false :: rest.1, rest.2 + 2)

def binaryNaturalCompareWithWork (a b : ℕ) : Ordering × ℕ := OAI.EditApproximation.bitCompareWithWork a.bits b.bits

def binaryNaturalSubtractWithWork (a b : ℕ) : List Bool × ℕ :=
  let result := OAI.EditApproximation.bitSubtractWithWork a.bits b.bits false
  (result.1, result.2.2)

def integerParameters (N : ℕ) : OAI.EditApproximation.IntegerParameters :=
  let H := OAI.EditApproximation.inputHeight N
  let ell := OAI.EditApproximation.inputSmallLog N
  let p := OAI.EditApproximation.coarseExponent ell
  { H, ell, p, B := H ^ p, initialFactor := H ^ (p + 4),
    M := 2 ^ (OAI.EditApproximation.heightExponent N / 20), P := H ^ (p + 20),
    T := 2 ^ ((3 * OAI.EditApproximation.heightExponent N + 3) / 4), S := H / ell ^ 2 }

def bitDivModWithWork (divisor : List Bool) : List Bool → List Bool × List Bool × ℕ
  | [] => ([], [], 1)
  | bit :: bits =>
    let previous := bitDivModWithWork divisor bits
    let candidate := bit :: previous.2.1
    let comparison := OAI.EditApproximation.bitCompareWithWork candidate divisor
    if comparison.1 = .lt then
      (false :: previous.1, candidate, previous.2.2 + comparison.2 + 4)
    else
      let reduced := OAI.EditApproximation.bitSubtractWithWork candidate divisor false
      (true :: previous.1, reduced.1, previous.2.2 + comparison.2 + reduced.2.2 + 5)

def wordLEWithWork (a b : List Bool) : Bool × ℕ :=
  let compared := OAI.EditApproximation.bitCompareWithWork b a
  (!(decide (compared.1 = .lt)), compared.2 + 1)

def computedSeedInitialExponent (N : ℕ) : ℕ :=
  (OAI.EditApproximation.coarseExponent (OAI.EditApproximation.inputSmallLog N) + 4) * OAI.EditApproximation.heightExponent N

def queryOrderedInputsWithWork {α : Type u_1} (equal le : α → α → Bool × ℕ)
    (xs : List α) : List α × ℕ :=
  let unique := OAI.EditApproximation.queryEraseWithWork equal xs
  let sorted := OAI.EditApproximation.querySortWithWork le unique.1
  (sorted.1, unique.2 + sorted.2 + 1)

def queryActionInputsWithWork {Parent : Type u_1} {Child : Type u_2} {M : ℕ}
    (actions : List (OAI.EditApproximation.BinaryBellmanAction Parent Child M)) : List Child × ℕ :=
  let inputs := OAI.EditApproximation.arithmeticFlatMapWithWork (fun action =>
    OAI.EditApproximation.arithmeticMapWithWork (fun i : Fin M => (action.childState i, 1)) (List.finRange M)) actions
  (inputs.1, inputs.2 + M + 1)

def largeAccuracyInput (N : ℕ) (epsilon : ℚ) : Prop :=
  2 ^ 1000 ≤ OAI.EditApproximation.inputSmallLog N ∧ 10 ≤ (OAI.EditApproximation.inputSmallLog N : ℚ) * epsilon

def dpCell {α : Type u_1} [DecidableEq α] (a : α) (target : List α)
    (previous : List ℕ) (j : ℕ) : ℕ × ℕ :=
  let fallback := OAI.EditApproximation.dpCandidate a target previous j 0
  let candidates := (List.range (target.length - j + 1)).map (OAI.EditApproximation.dpCandidate a target previous j)
  let minimum := OAI.EditApproximation.dpMinimum fallback.1 (candidates.map Prod.fst)
  (minimum.1, fallback.2 + (candidates.map Prod.snd).sum + minimum.2 +
    (OAI.EditApproximation.dpLength target).2 + 3 * candidates.length + 4)

def suffixDPAllocation {α : Type u_1} : List α → List α → ℕ
  | [], target => target.length + 1
  | _ :: rest, target => suffixDPAllocation rest target +
      (List.ofFn fun j : Fin (target.length + 1) => OAI.EditApproximation.dpCellAllocation target j.val).sum +
        3 * (target.length + 1)

def binaryNaturalAddAllocation (a b : ℕ) : ℕ := OAI.EditApproximation.bitAddAllocation a.bits b.bits false

def queryOrderedInputsAllocation {α : Type u_1} (equal le : α → α → Bool × ℕ)
    (equalAllocation leAllocation : α → α → ℕ) (xs : List α) : ℕ :=
  OAI.EditApproximation.queryEraseAllocation equal equalAllocation xs +
    OAI.EditApproximation.querySortAllocation le leAllocation (OAI.EditApproximation.queryEraseWithWork equal xs).1

def queryActionInputsAllocation {Parent : Type u_1} {Child : Type u_2} {M : ℕ}
    (actions : List (OAI.EditApproximation.BinaryBellmanAction Parent Child M)) : ℕ :=
  OAI.EditApproximation.arithmeticFlatMapAllocation (fun action =>
    OAI.EditApproximation.arithmeticMapWithWork (fun i : Fin M => (action.childState i, 1)) (List.finRange M))
    (fun _ => OAI.EditApproximation.arithmeticMapAllocation (fun _ : Fin M => 1) (List.finRange M) + M) actions

def binaryNaturalMulWithWork (a b : ℕ) : List Bool × ℕ := OAI.EditApproximation.bitMulWithWork a.bits b.bits

def binaryNaturalDivModWithWork (n d : ℕ) : List Bool × List Bool × ℕ :=
  OAI.EditApproximation.bitDivModWithWork d.bits n.bits

def bitCeilDivWithWork (divisor bits : List Bool) : List Bool × ℕ :=
  let divided := OAI.EditApproximation.bitDivModWithWork divisor bits
  let zeroCheck := OAI.EditApproximation.bitCompareWithWork divided.2.1 []
  if zeroCheck.1 = .eq then (divided.1, divided.2.2 + zeroCheck.2 + 3)
  else
    let rounded := OAI.EditApproximation.bitAddWithWork divided.1 [true] false
    (rounded.1, divided.2.2 + zeroCheck.2 + rounded.2 + 3)

def wordMinWithWork (a b : List Bool) : List Bool × ℕ :=
  let compared := OAI.EditApproximation.wordLEWithWork a b
  (if compared.1 then a else b, compared.2 + 1)

def wordInsertWithWork (a : List Bool) : List (List Bool) → List (List Bool) × ℕ
  | [] => ([a], 1)
  | b :: rest =>
    let compared := OAI.EditApproximation.wordLEWithWork a b
    if compared.1 then (a :: b :: rest, compared.2 + 2) else
      let tail := wordInsertWithWork a rest
      (b :: tail.1, compared.2 + tail.2 + 2)

def saturatingSubtractWithWork (a b : ℕ) : List Bool × ℕ :=
  let test := OAI.EditApproximation.binaryNaturalCompareWithWork a b
  if test.1 = .lt then ([], test.2 + 1) else
    let result := OAI.EditApproximation.binaryNaturalSubtractWithWork a b
    (result.1, test.2 + result.2 + 2)

def computedSeedPassCount (N : ℕ) : ℕ :=
  OAI.EditApproximation.dyadicSeedPassCount (OAI.EditApproximation.smallLogExponent N) (OAI.EditApproximation.computedSeedInitialExponent N)

def bitPowerWithWork (base : List Bool) : ℕ → List Bool × ℕ
  | 0 => ([true], 1)
  | n + 1 =>
    let previous := bitPowerWithWork base n
    let product := OAI.EditApproximation.bitMulWithWork previous.1 base
    let answer := OAI.EditApproximation.trimBitWordWithWork product.1
    (answer.1, previous.2 + product.2 + answer.2 + 2)

end OAI.EditApproximation

end


