-- Prove2me | Definitions.Def_ExponomialAssortment_FPTAS_DP
-- name    : ExponomialAssortment_FPTAS_DP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T21:13:53.983179+00:00
-- url     : https://prove2.me/theorems/3c149f00-5036-4e12-b5f0-87c70a66133c
-- title:
--   Feasible dynamic-program paths and state pruning
-- statement:
--   States record current index, selected count, utility sum relative to the preceding product and average price. Transitions enforce capacity, mandatory outside inclusion and forced first product; finite paths encode pruning. Reachability includes the initial state. All first-product guesses are evaluated, and selection maximizes true revenue among their outputs.
-- source:
--   Aouad, Feldman and Segev (2023), DOI 10.1287/mnsc.2022.4492, published repository manuscript, §§3.1–5.3 and §8, printed 11–19, 30, PDF 12–20, 31

import Definitions.Def_ExponomialAssortment_FPTAS_Rounding

noncomputable section

namespace ExponomialAssortment.FPTAS

structure State where
  i : ℕ
  count : ℕ
  utilitySum : ℝ
  avg : ℝ

def stateGap {n : ℕ} (u : Fin n → ℝ) (i : Fin n) : ℝ :=
  if h : 0 < i.val then u ⟨i.val - 1, by omega⟩ - u i else 0

def stateCoefficient {n : ℕ} (u : Fin n → ℝ) (s : State) : ℝ :=
  if h : s.i < n then
    Real.exp (-s.utilitySum - s.count * stateGap u ⟨s.i, h⟩) / (s.count + 1)
  else 0

def initial {n : ℕ} (I : Instance n) (η : ℝ) (f : Fin n) : State :=
  if h : I.outside < f then
    ⟨f.val, 1, roundedUtility I η I.outside -
      roundedUtility I η ⟨f.val - 1, by omega⟩, 0⟩
  else ⟨f.val, 0, 0, 0⟩

def initialSelection {n : ℕ} (I : Instance n) (f : Fin n) : Finset (Fin n) :=
  if I.outside < f then {I.outside} else ∅

def bestSingle {n : ℕ} (I : Instance n) (η : ℝ) (l : Fin n) : Prop :=
  l ≠ I.outside ∧ ∀ j, j ≠ I.outside →
    coefficient (roundedUtility I η) {j, I.outside} j * I.price j ≤
    coefficient (roundedUtility I η) {l, I.outside} l * I.price l

def kIndex {n : ℕ} (I : Instance n) (η : ℝ) (l : Fin n) : ℕ :=
  if I.outside < l then
    (⌊I.utility I.outside / delta n η⌋ - ⌊I.utility l / delta n η⌋).toNat else 0

def Delta {n : ℕ} (I : Instance n) (η : ℝ) : ℝ :=
  Real.log ((4 * n / η) * (pmax I / pmin I))

def Profitable {n : ℕ} (I : Instance n) (η : ℝ) (l : Fin n) (s : State) : Prop :=
  Real.exp (-(kIndex I η l : ℝ) * delta n η - Delta I η) ≤
    stateCoefficient (roundedUtility I η) s

/-- A transition of (3), (4), or (8). Infeasible branches have no successor. -/
def Step {n : ℕ} (I : Instance n) (C : ℕ) (η : ℝ)
    (roundedPrice joint : Bool) (force : Option (Fin n))
    (s t : State) (pick : Bool) (r : ℝ) : Prop :=
  ∃ hi : s.i < n, let i : Fin n := ⟨s.i, hi⟩
    t.i = s.i + 1 ∧
    t.utilitySum = s.utilitySum + s.count *
      stateGap (if joint then roundedUtility I η else I.utility) i ∧
    if pick then
      s.count < C ∧ t.count = s.count + 1 ∧
      r = stateCoefficient (if joint then roundedUtility I η else I.utility) s *
        (I.price i - s.avg) ∧
      (if s.i + 1 = n then t.avg = s.avg else
        if roundedPrice then Round I η ((s.count * s.avg + I.price i) / (s.count + 1)) t.avg
        else t.avg = (s.count * s.avg + I.price i) / (s.count + 1))
    else i ≠ I.outside ∧ force ≠ some i ∧ t.count = s.count ∧ t.avg = s.avg ∧ r = 0

/-- Finite execution paths, with a zero suffix only at termination; feasibility is separate. -/
inductive Path {n : ℕ} (I : Instance n) (C : ℕ) (η : ℝ)
    (roundedPrice joint prune : Bool) (l : Fin n) (force : Option (Fin n)) :
    State → Finset (Fin n) → ℝ → Prop
  | stop (s) (h : s.i = n ∨ (prune = true ∧ ¬ Profitable I η l s)) :
      Path I C η roundedPrice joint prune l force s ∅ 0
  | move (s t : State) (pick : Bool) (r v : ℝ) (S : Finset (Fin n))
      (hi : s.i < n) (hp : prune = true → Profitable I η l s)
      (hs : Step I C η roundedPrice joint force s t pick r)
      (ht : Path I C η roundedPrice joint prune l force t S v) :
      Path I C η roundedPrice joint prune l force s
        (if pick then insert ⟨s.i, hi⟩ S else S) (r + v)

def PrunedRun {n : ℕ} (I : Instance n) (C : ℕ) (η : ℝ) (l f : Fin n)
    (S : Finset (Fin n)) (v : ℝ) : Prop :=
  Feasible I C S ∧ f ∈ S ∧ ∃ T,
    Path I C η true true true l (some f) (initial I η f) T v ∧
    S = initialSelection I f ∪ T

def PrunedOptimal {n : ℕ} (I : Instance n) (C : ℕ) (η : ℝ) (l f : Fin n)
    (S : Finset (Fin n)) (v : ℝ) : Prop :=
  PrunedRun I C η l f S v ∧ ∀ T w, PrunedRun I C η l f T w → w ≤ v

def Reachable {n : ℕ} (I : Instance n) (C : ℕ) (η : ℝ) (l f : Fin n)
    (s : State) : Prop :=
  Relation.ReflTransGen (fun a b => Profitable I η l a ∧
    ∃ pick r, Step I C η true true (some f) a b pick r) (initial I η f) s

def firstProduct {n : ℕ} (I : Instance n) (S : Finset (Fin n)) (f : Fin n) : Prop :=
  f ∈ S ∧ f ≠ I.outside ∧ ∀ j ∈ S, j ≠ I.outside → f ≤ j

/-- Every guess is evaluated; a returned candidate maximizes true expected revenue among them. -/
def Selected {n : ℕ} (I : Instance n) (C : ℕ) (η : ℝ) (S : Finset (Fin n)) : Prop :=
  ∃ l, bestSingle I η l ∧
    ∃ candidates : Fin n → Finset (Fin n), ∃ values : Fin n → ℝ,
      (∀ f, f ≠ I.outside → PrunedOptimal I C η l f (candidates f) (values f)) ∧
      (∃ f, f ≠ I.outside ∧ S = candidates f) ∧
      ∀ f, f ≠ I.outside → revenue I (candidates f) ≤ revenue I S

end ExponomialAssortment.FPTAS


