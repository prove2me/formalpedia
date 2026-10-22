-- Prove2me | Definitions.Def_HardyCapsetCertificateModel20261020
-- name    : HardyCapsetCertificateModel20261020
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-20T15:29:52.947926+00:00
-- url     : https://prove2.me/theorems/e3c19cc2-c226-4d5f-aff5-2b4b4b97ee55
-- title:
--   HardyCapsetCertificateModel20261020
-- statement:
--   Finite certificate data and independently checkable conditions for full-space completion of the exact ternary cap baseline. Point identifiers decode in big-endian base three. Each ambient identifier has either a candidate index, a fixed-point witness, or a pair of distinct fixed blockers. Constraint rows contain candidate indices, natural coefficients and weights, witnessed forbidden pairs and triples, and a finite local-pattern capacity. Sparse coverage witnesses list distinct contributing rows for each variable; positivity, the geometric checks, all capacities and the strict integer cost bound are expressed as decidable propositions. Packed strings store pairs of natural identifiers only; the decoder supplies no mathematical assertion.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetModel20261020
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Chain
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order

set_option autoImplicit false
namespace HardyCapset20261020.Cert

def CompletionBound (n : Point) (t : ZMod 3) : Prop :=
  ∀ A : Finset Point, IsCap A → core n t ⊆ A → A.card ≤ 512

def digit (q i : ℕ) : ℕ := (q / 3 ^ (7 - i)) % 3

def natDot (n q : ℕ) : ℕ := ∑ i : Fin 8, digit n i.val * digit q i.val

def dotCode (n q : ℕ) : ℕ := natDot n q % 3

def LineCode (a b c : ℕ) : Prop :=
  ∀ i : Fin 8, (digit a i.val + digit b i.val + digit c i.val) % 3 = 0

instance (a b c : ℕ) : Decidable (LineCode a b c) := inferInstanceAs
  (Decidable (∀ i : Fin 8, (digit a i.val + digit b i.val + digit c i.val) % 3 = 0))

def baseArray : Array ℕ := baselineIds.toArray

def entry (a : Array ℕ) (i : ℕ) : ℕ := a[i]?.getD 0

def baseAt (i : ℕ) : ℕ := entry baseArray i

/-- Compact storage only: two characters, offset by 256, encode each witness. -/
def unpackPairs : List Char → List (ℕ × ℕ)
  | a :: b :: rest => (a.toNat - 256, b.toNat - 256) :: unpackPairs rest
  | _ => []

def packedBlockers (s : String) : Array (ℕ × ℕ) := (unpackPairs s.toList).toArray

structure Edge where
  left : ℕ
  right : ℕ
  anchor : ℕ
  deriving Repr, DecidableEq, Inhabited

structure Triple where
  first : ℕ
  second : ℕ
  third : ℕ
  deriving Repr, DecidableEq, Inhabited

structure Row where
  vars : Array ℕ
  coeff : Array ℕ
  bound : ℕ
  weight : ℕ
  edges : Array Edge := #[]
  triples : Array Triple := #[]
  deriving Repr, Inhabited

structure Certificate where
  normal : ℕ
  level : ℕ
  pool : Array ℕ
  blockers : Array (ℕ × ℕ)
  denominator : ℕ
  rows : Array Row
  coverRows : Array (Array ℕ)
  deriving Repr, Inhabited

def vertex (c : Certificate) (j : ℕ) : Point := decode (entry c.pool j)

def fixedSet (c : Certificate) : Finset Point := core (decode c.normal) c.level

def FixedAnchor (c : Certificate) (a : ℕ) : Prop :=
  a < baseArray.size ∧ dotCode c.normal (baseAt a) ≠ c.level

instance (c : Certificate) (a : ℕ) : Decidable (FixedAnchor c a) := inferInstanceAs
  (Decidable (a < baseArray.size ∧ dotCode c.normal (baseAt a) ≠ c.level))

def BlockOK (c : Certificate) (q : ℕ) (ab : ℕ × ℕ) : Prop :=
  if ab.1 < baseArray.size then
    if ab.1 = ab.2 then FixedAnchor c ab.1 ∧ q = baseAt ab.1
    else FixedAnchor c ab.1 ∧ FixedAnchor c ab.2 ∧
      baseAt ab.1 ≠ baseAt ab.2 ∧ LineCode (baseAt ab.1) (baseAt ab.2) q
  else ab.1 - baseArray.size < c.pool.size ∧ entry c.pool (ab.1 - baseArray.size) = q

instance (c : Certificate) (q : ℕ) (ab : ℕ × ℕ) : Decidable (BlockOK c q ab) := by
  unfold BlockOK
  infer_instance

def rowPoint (c : Certificate) (r : Row) (k : ℕ) : ℕ :=
  entry c.pool (entry r.vars k)

def EdgeOK (c : Certificate) (r : Row) (e : Edge) : Prop :=
  e.left < r.vars.size ∧ e.right < r.vars.size ∧ FixedAnchor c e.anchor ∧
  rowPoint c r e.left ≠ rowPoint c r e.right ∧
  LineCode (rowPoint c r e.left) (rowPoint c r e.right) (baseAt e.anchor)

instance (c : Certificate) (r : Row) (e : Edge) : Decidable (EdgeOK c r e) := by
  unfold EdgeOK
  infer_instance

def TripleOK (c : Certificate) (r : Row) (e : Triple) : Prop :=
  e.first < r.vars.size ∧ e.second < r.vars.size ∧ e.third < r.vars.size ∧
  rowPoint c r e.first ≠ rowPoint c r e.second ∧
  rowPoint c r e.first ≠ rowPoint c r e.third ∧
  rowPoint c r e.second ≠ rowPoint c r e.third ∧
  LineCode (rowPoint c r e.first) (rowPoint c r e.second) (rowPoint c r e.third)

instance (c : Certificate) (r : Row) (e : Triple) : Decidable (TripleOK c r e) := by
  unfold TripleOK
  infer_instance

def bit {n : ℕ} (s : Fin n → Bool) (i : ℕ) : Bool :=
  if h : i < n then s ⟨i, h⟩ else false

def LegalPattern (r : Row) (s : Fin r.vars.size → Bool) : Prop :=
  (∀ e ∈ r.edges.toList, ¬ (bit s e.left = true ∧ bit s e.right = true)) ∧
  (∀ e ∈ r.triples.toList,
    ¬ (bit s e.first = true ∧ bit s e.second = true ∧ bit s e.third = true))

instance (r : Row) (s : Fin r.vars.size → Bool) : Decidable (LegalPattern r s) := by
  unfold LegalPattern
  infer_instance

def PatternBound (r : Row) : Prop :=
  ∀ s : Fin r.vars.size → Bool, LegalPattern r s →
    (∑ k : Fin r.vars.size, if s k then entry r.coeff k.val else 0) ≤ r.bound

instance (r : Row) : Decidable (PatternBound r) := by
  unfold PatternBound
  infer_instance

def RowOK (c : Certificate) (r : Row) : Prop :=
  r.coeff.size = r.vars.size ∧
  (∀ j ∈ r.vars.toList, j < c.pool.size) ∧
  (∀ e ∈ r.edges.toList, EdgeOK c r e) ∧
  (∀ e ∈ r.triples.toList, TripleOK c r e) ∧ PatternBound r

instance (c : Certificate) (r : Row) : Decidable (RowOK c r) := by
  unfold RowOK
  infer_instance

def coefficient (r : Row) (j : ℕ) : ℕ :=
  ∑ k : Fin r.vars.size, if entry r.vars k.val = j then entry r.coeff k.val else 0

def cover (c : Certificate) (j : ℕ) : ℕ :=
  ∑ r : Fin c.rows.size, c.rows[r].weight * coefficient c.rows[r] j

def cost (c : Certificate) : ℕ :=
  ∑ r : Fin c.rows.size, c.rows[r].weight * c.rows[r].bound

def deletedCount (c : Certificate) : ℕ :=
  (baselineIds.filter (fun q => dotCode c.normal q = c.level)).length

def LocalCoverOK (c : Certificate) (j : ℕ) : Prop :=
  let l := c.coverRows[j]!.toList
  l.Nodup ∧ (∀ r ∈ l, r < c.rows.size) ∧
    c.denominator ≤ (l.map (fun r => c.rows[r]!.weight * coefficient c.rows[r]! j)).sum

instance (c : Certificate) (j : ℕ) : Decidable (LocalCoverOK c j) := by
  unfold LocalCoverOK
  infer_instance

def Check (c : Certificate) : Prop :=
  c.normal < 6561 ∧ c.level < 3 ∧ 0 < c.denominator ∧
  (∀ q ∈ c.pool.toList, q < 6561) ∧
  c.blockers.size = 6561 ∧
  (∀ q : Fin 6561, BlockOK c q.val c.blockers[q.val]!) ∧
  (∀ r ∈ c.rows.toList, RowOK c r) ∧
  c.coverRows.size = c.pool.size ∧
  (∀ j : Fin c.pool.size, LocalCoverOK c j.val) ∧
  cost c < c.denominator * (deletedCount c + 1)

instance (c : Certificate) : Decidable (Check c) := by
  unfold Check
  infer_instance

end HardyCapset20261020.Cert


