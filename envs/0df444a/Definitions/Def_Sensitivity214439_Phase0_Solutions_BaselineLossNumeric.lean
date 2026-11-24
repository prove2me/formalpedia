-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossNumeric
-- name    : Sensitivity214439_Phase0_Solutions_BaselineLossNumeric
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:48:20.332859+00:00
-- url     : https://prove2.me/theorems/96bdd917-0236-4d4e-bac4-f662660fa986
-- title:
--   Finite states and dual certificates for exact-source loss
-- statement:
--   A baseline recipe records whether the gate is unary, its total guard-socket and check counts, its soft and hard cutoffs, allowances, and lower and upper target ranks. A state records two child source ranks $a,b<12$ and weak and strong soft counts $f_i,f_j<8$. Admissibility requires $i\le j$, $5\le a\le b$, equal ranks in the unary case, compatible ordered counts, and scalar acceptance at both ranks.
--
--   The needed rank of one target is determined by its unchanged mate. The own fee is the sum of the corresponding exact-source $M$-entries. Replacing a guard of height $h$ by $h'$ defines a rejection predicate; its first rejecting height in $\{0,\ldots,12\}$ determines the guard's $A$-fee. Two extra-count branches record rejection at the next source rank through soft or hard failures.
--
--   A dual certificate consists of a positive denominator and integer coefficients for socket count, check count, weak count, strong count, and an extra count. Its extra coefficient is nonpositive. Validity requires a dominating inequality for every permitted guard-height/size column and a total inequality bounded by the chosen output $M$-entry. A certificate table is certified when these tests hold for every admissible state and rejection branch. Explicit state keys and decidable predicates make this a finite exact check.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineLossNumeric.lean lines 8–159; SHA256 0c63cc64f41372ca81ec16e16ee0d34cf05c1d58d3325d9a866df8a4d3a51b1a; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range

namespace SensitivityBaselineLossNumeric
end SensitivityBaselineLossNumeric



/-! Small computable certificates for every exact-source baseline loss bound.
The five dual coefficients price physical sockets, checks, two exact soft
counts, and the count witnessing rejection at the next rank. -/
namespace SensitivityBaselineLossNumeric

structure Recipe where
  unary : Bool
  degree : ℕ
  checks : ℕ
  soft : Fin 12 → ℕ
  hard : Fin 12 → ℕ
  allowance : Fin 12 → ℕ
  lo : Fin 12 → ℕ → Fin 12
  hi : Fin 12 → ℕ → Fin 12

def occupied (cutoff height : ℕ) : ℕ := if cutoff < height then 1 else 0

def accepts (r : Recipe) (j : Fin 12) (softCount hardCount a b : ℕ) : Prop :=
  softCount ≤ r.allowance j ∧ hardCount = 0 ∧
    (r.lo j softCount).val ≤ min a b ∧ (r.hi j softCount).val ≤ max a b

instance (r : Recipe) (j : Fin 12) (softCount hardCount a b : ℕ) :
    Decidable (accepts r j softCount hardCount a b) := by
  unfold accepts
  infer_instance

structure State where
  a : Fin 12
  b : Fin 12
  fi : Fin 8
  fj : Fin 8

def Admissible (r : Recipe) (i j : Fin 12) (s : State) : Prop :=
  i ≤ j ∧ 5 ≤ s.a.val ∧ s.a ≤ s.b ∧ (r.unary = true → s.a = s.b) ∧
    s.fi.val ≤ s.fj.val ∧ (r.soft i = r.soft j → s.fi = s.fj) ∧
    accepts r i s.fi.val 0 s.a.val s.b.val ∧ accepts r j s.fj.val 0 s.a.val s.b.val

instance (r : Recipe) (i j : Fin 12) (s : State) : Decidable (Admissible r i j s) := by
  unfold Admissible
  infer_instance

def need (r : Recipe) (i : Fin 12) (f mate : ℕ) : ℕ :=
  if mate < (r.lo i f).val then 12 else
    if mate < (r.hi i f).val then (r.hi i f).val else (r.lo i f).val

def ownFee (r : Recipe) (input : Array ℕ) (i : Fin 12) (s : State) : ℕ :=
  SensitivityLocalNumeric.entry input 2 (need r i s.fi.val s.b.val) s.a.val +
    if r.unary then 0 else SensitivityLocalNumeric.entry input 2 (need r i s.fi.val s.a.val) s.b.val

def bad (r : Recipe) (i : Fin 12) (s : State) (old fresh : ℕ) : Prop :=
  ¬ accepts r i (s.fi.val - occupied (r.soft i) old + occupied (r.soft i) fresh)
    (occupied (r.hard i) fresh) s.a.val s.b.val

instance (r : Recipe) (i : Fin 12) (s : State) (old fresh : ℕ) :
    Decidable (bad r i s old fresh) := by
  unfold bad
  infer_instance

def firstBad (r : Recipe) (i : Fin 12) (s : State) (old : ℕ) : ℕ :=
  ((List.range 13).find? fun fresh => decide (bad r i s old fresh)).getD 13





def guardFee (r : Recipe) (input : Array ℕ) (i : Fin 12) (s : State) (old : ℕ) : ℕ :=
  let top := firstBad r i s old - 1
  if top < 12 then SensitivityLocalNumeric.entry input 0 old top else 0

def nextRank (j : Fin 12) : Fin 12 := Fin.ofNat 12 (j.val + 1)

def acceptanceCount (r : Recipe) (j : Fin 12) (s : State) : ℕ :=
  ((List.range (r.allowance j + 1)).filter fun f =>
    decide (accepts r j f 0 s.a.val s.b.val)).length

def extraCut (r : Recipe) (j : Fin 12) (branch : Fin 2) : ℕ :=
  if j.val = 11 then 12 else if branch.val = 0 then r.soft (nextRank j) else r.hard (nextRank j)

def extraRequired (r : Recipe) (j : Fin 12) (s : State) (branch : Fin 2) : ℕ :=
  if j.val = 11 then 0 else if branch.val = 0 then acceptanceCount r (nextRank j) s else 1

def AllowedColumn (r : Recipe) (i j : Fin 12) (s : State) (height : Fin 13) (size : Fin 3) : Prop :=
  1 ≤ size.val ∧ size.val ≤ (if r.unary then 1 else 2) ∧ height.val ≤ r.hard j ∧
    occupied (r.soft i) height.val ≤ s.fi.val ∧ occupied (r.soft j) height.val ≤ s.fj.val

instance (r : Recipe) (i j : Fin 12) (s : State) (height : Fin 13) (size : Fin 3) :
    Decidable (AllowedColumn r i j s height size) := by
  unfold AllowedColumn
  infer_instance

structure Dual where
  denominator : ℕ
  sockets : ℤ
  checks : ℤ
  weak : ℤ
  strong : ℤ
  extra : ℤ
deriving Repr

def Valid (r : Recipe) (input output : Array ℕ) (i j : Fin 12) (s : State)
    (branch : Fin 2) (cert : Dual) : Prop :=
  0 < cert.denominator ∧ cert.extra ≤ 0 ∧
    (∀ (height : Fin 13) (size : Fin 3), AllowedColumn r i j s height size →
      height.val < firstBad r i s height.val ∧
      (cert.denominator : ℤ) * size.val * guardFee r input i s height.val ≤
        cert.sockets * size.val + cert.checks +
          cert.weak * occupied (r.soft i) height.val + cert.strong * occupied (r.soft j) height.val +
          cert.extra * occupied (extraCut r j branch) height.val) ∧
    (cert.denominator : ℤ) * ownFee r input i s + cert.sockets * r.degree + cert.checks * r.checks +
      cert.weak * s.fi.val + cert.strong * s.fj.val + cert.extra * extraRequired r j s branch ≤
        (cert.denominator : ℤ) * SensitivityLocalNumeric.entry output 2 i.val j.val

instance (r : Recipe) (input output : Array ℕ) (i j : Fin 12) (s : State)
    (branch : Fin 2) (cert : Dual) : Decidable (Valid r input output i j s branch cert) := by
  unfold Valid
  infer_instance

def stateKey (s : State) (branch : Fin 2) : ℕ :=
  (((s.a.val * 12 + s.b.val) * 8 + s.fi.val) * 8 + s.fj.val) * 2 + branch.val

def Certified (r : Recipe) (input output : Array ℕ) (i j : Fin 12)
    (table : ℕ → Dual) : Prop :=
  i ≤ j → ∀ a : Fin 12, 5 ≤ a.val → ∀ b : Fin 12, a ≤ b →
    (r.unary = true → a = b) → ∀ fi : Fin 8, accepts r i fi.val 0 a.val b.val →
      ∀ fj : Fin 8, fi.val ≤ fj.val → (r.soft i = r.soft j → fi = fj) →
        accepts r j fj.val 0 a.val b.val → ∀ branch : Fin 2,
          (j.val = 11 → branch.val = 0) →
            Valid r input output i j ⟨a,b,fi,fj⟩ branch (table (stateKey ⟨a,b,fi,fj⟩ branch))

instance (r : Recipe) (input output : Array ℕ) (i j : Fin 12) (table : ℕ → Dual) :
    Decidable (Certified r input output i j table) := by
  unfold Certified
  infer_instance





end SensitivityBaselineLossNumeric


