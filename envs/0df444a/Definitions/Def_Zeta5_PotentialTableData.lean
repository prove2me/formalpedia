-- Prove2me | Definitions.Def_Zeta5_PotentialTableData
-- name    : Zeta5_PotentialTableData
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-13T15:06:18.332416+00:00
-- url     : https://prove2.me/theorems/8a38a6bb-ac75-40c0-92d4-9821055b00ef
-- title:
--   Rational certificates for the complete potential table
-- statement:
--   These finite certificate types encode bounds for the sixteen arcsine components of the comparison potential, their fixed weighted sum, and the external field. They include rational square-root enclosures, logarithm estimates, nested reciprocal and half-angle arctangent estimates, and the signs needed to multiply lower bounds.
--
--   For each interval, rational bounds $u$ and $v$ must satisfy
--
--   $$2u-v\le -\frac{1329}{200}.$$
--
--   A table is a finite binary tree of interval certificates. Its validity predicate checks every row and verifies overlap at every join, allowing separately checked chunks to certify an entire interval. The analytic interpretation is a separate theorem.
--
--   **Formalization Note** The full dependency chain of this module uses only Std and rational arithmetic.
-- source:
--   Derived rational-certificate encoding of mo271/Zeta5 at commit 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, Apery/Table2/All.lean, potential_ineq_le_two (lines 4116–4120), and the U*.lean/I*.lean certificate files; https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Table2/All.lean#L4116-L4120. The certificate datatype and its generic soundness adapter are new formalization infrastructure.

import Definitions.Def_Zeta5_PotentialCertificateData

/-!
The complete arithmetic certificate format. Everything in this module is over
`Rat`, finite data, and decidable propositions; it has no analytic imports.
The soundness theorems live in the separate PotentialTable*Sound modules.
-/

namespace Apery.PotentialCertificate

structure LogCertificate where
  bound : Rat
  scale : Nat
  order : Nat

def LogCertificate.UpperValid (c : LogCertificate) (x : Rat) : Prop :=
  (Certificate.mk .logUpper x c.bound c.scale c.order).Valid

def LogCertificate.LowerValid (c : LogCertificate) (x : Rat) : Prop :=
  (Certificate.mk .logLower x c.bound c.scale c.order).Valid

instance (c : LogCertificate) (x : Rat) : Decidable (c.UpperValid x) :=
  inferInstanceAs (Decidable (Certificate.mk .logUpper x c.bound c.scale c.order).Valid)

instance (c : LogCertificate) (x : Rat) : Decidable (c.LowerValid x) :=
  inferInstanceAs (Decidable (Certificate.mk .logLower x c.bound c.scale c.order).Valid)

inductive Position where
  | left | inside | right

structure OmegaCertificate where
  position : Position
  radius : Rat
  log : LogCertificate

def OmegaCertificate.Valid (c : OmegaCertificate) (p a b : Rat) : Prop :=
  match c.position with
  | .left => a < b ∧ p ≤ a ∧ 0 ≤ c.radius ∧
      (p - a) * (p - b) ≤ c.radius ^ 2 ∧
      c.log.UpperValid (((a + b) / 2 - p + c.radius) / 2)
  | .inside => a ≤ p ∧ p ≤ b ∧ c.log.UpperValid ((b - a) / 4)
  | .right => a < b ∧ b ≤ p ∧ 0 ≤ c.radius ∧
      (p - a) * (p - b) ≤ c.radius ^ 2 ∧
      c.log.UpperValid ((p - (a + b) / 2 + c.radius) / 2)

instance (c : OmegaCertificate) (p a b : Rat) : Decidable (c.Valid p a b) := by
  unfold OmegaCertificate.Valid
  cases c.position <;> infer_instance

/-- Direct alternating series, reciprocal, and half-angle bounds can be nested. -/
inductive AtanCertificate where
  | direct (bound : Rat) (order : Nat)
  | reciprocal (bound : Rat) (inner : AtanCertificate)
  | half (bound radius : Rat) (inner : AtanCertificate)

def AtanCertificate.bound : AtanCertificate → Rat
  | .direct b _ | .reciprocal b _ | .half b _ _ => b

/-- `upper = true` certifies an upper bound; `false` certifies a lower bound. -/
def AtanCertificate.Valid (c : AtanCertificate) (upper : Bool) (x : Rat) : Prop :=
  match c with
  | .direct b m =>
      (Certificate.mk (if upper then .arctanUpper else .arctanLower) x b 0 m).Valid
  | .reciprocal b inner => 0 < x ∧ inner.Valid (!upper) (1 / x) ∧
      (if upper then 3.14159265358979323847 / 2 - inner.bound ≤ b
       else b ≤ 3.14159265358979323846 / 2 - inner.bound)
  | .half b w inner => 0 ≤ x ∧ 0 ≤ w ∧
      (if upper then w ^ 2 ≤ 1 + x ^ 2 else 1 + x ^ 2 ≤ w ^ 2) ∧
      inner.Valid upper (x / (1 + w)) ∧
      (if upper then 2 * inner.bound ≤ b else b ≤ 2 * inner.bound)

instance atanDecidable (c : AtanCertificate) (upper : Bool) (x : Rat) :
    Decidable (c.Valid upper x) :=
  match c with
  | .direct b m => by unfold AtanCertificate.Valid; infer_instance
  | .reciprocal b inner => by
      unfold AtanCertificate.Valid
      have := atanDecidable inner (!upper) (1 / x)
      infer_instance
  | .half b w inner => by
      unfold AtanCertificate.Valid
      have := atanDecidable inner upper (x / (1 + w))
      infer_instance

-- The fixed sixteen components of the published measure are listed below.
-- Their correspondence to aρ, bρ, cρ is proved once in PotentialTableUSound.
structure UCertificate where
  point : Rat
  w1 : OmegaCertificate
  w2 : OmegaCertificate
  w3 : OmegaCertificate
  w4 : OmegaCertificate
  w5 : OmegaCertificate
  w6 : OmegaCertificate
  w7 : OmegaCertificate
  w8 : OmegaCertificate
  w9 : OmegaCertificate
  w10 : OmegaCertificate
  w11 : OmegaCertificate
  w12 : OmegaCertificate
  w13 : OmegaCertificate
  w14 : OmegaCertificate
  w15 : OmegaCertificate
  w16 : OmegaCertificate

def UCertificate.upper (c : UCertificate) : Rat :=
  (525779809 / 50000000000) * c.w1.log.bound +
  (29471737793 / 1000000000000) * c.w2.log.bound +
  (42934365099 / 1000000000000) * c.w3.log.bound +
  (29102115983 / 500000000000) * c.w4.log.bound +
  (6903762131 / 100000000000) * c.w5.log.bound +
  (78873099189 / 1000000000000) * c.w6.log.bound +
  (84856120711 / 1000000000000) * c.w7.log.bound +
  (88396082127 / 1000000000000) * c.w8.log.bound +
  (706427057 / 8000000000) * c.w9.log.bound +
  (17094464251 / 200000000000) * c.w10.log.bound +
  (39449592119 / 500000000000) * c.w11.log.bound +
  (35176735959 / 500000000000) * c.w12.log.bound +
  (11767795323 / 200000000000) * c.w13.log.bound +
  (22210660553 / 500000000000) * c.w14.log.bound +
  (30462865791 / 1000000000000) * c.w15.log.bound +
  (5959622577 / 1000000000000) * c.w16.log.bound

def UCertificate.Valid (c : UCertificate) : Prop :=
  c.w1.Valid c.point (1953374043 / 500000000000) (8992695531 / 1000000000000) ∧
  c.w2.Valid c.point (289031033 / 125000000000) (3068199571 / 200000000000) ∧
  c.w3.Valid c.point (280457333 / 200000000000) (6432545181 / 250000000000) ∧
  c.w4.Valid c.point (220431339 / 250000000000) (20954789123 / 500000000000) ∧
  c.w5.Valid c.point (289098953 / 500000000000) (65851089563 / 1000000000000) ∧
  c.w6.Valid c.point (396324613 / 1000000000000) (24870259471 / 250000000000) ∧
  c.w7.Valid c.point (283911191 / 1000000000000) (72162863729 / 500000000000) ∧
  c.w8.Valid c.point (53051547 / 250000000000) (201105762729 / 1000000000000) ∧
  c.w9.Valid c.point (82548843 / 500000000000) (269345996903 / 1000000000000) ∧
  c.w10.Valid c.point (33336783 / 250000000000) (86772388539 / 250000000000) ∧
  c.w11.Valid c.point (55761057 / 500000000000) (86161340883 / 200000000000) ∧
  c.w12.Valid c.point (19269871 / 200000000000) (515561896511 / 1000000000000) ∧
  c.w13.Valid c.point (85815639 / 1000000000000) (297724389273 / 500000000000) ∧
  c.w14.Valid c.point (78667711 / 1000000000000) (664241383483 / 1000000000000) ∧
  c.w15.Valid c.point (14825913 / 200000000000) (89520072139 / 125000000000) ∧
  c.w16.Valid c.point (7174131 / 100000000000) (746637295669 / 1000000000000)

instance (c : UCertificate) : Decidable c.Valid := by
  unfold UCertificate.Valid
  infer_instance


/-- A lower bound on V throughout [left, right], including a degenerate point. -/
structure VCertificate where
  left : Rat
  right : Rat
  sqrtLower : Rat
  sqrtUpper : Rat
  logLower : LogCertificate
  logUpper : LogCertificate
  atanLower : AtanCertificate
  atanUpper : AtanCertificate
  positive : Bool

def VCertificate.parenthesis (c : VCertificate) : Rat :=
  3.14159265358979323846 + c.atanLower.bound - 6 * c.atanUpper.bound

def VCertificate.lower (c : VCertificate) : Rat :=
  c.logLower.bound - 6 * (3 / 40) * c.logUpper.bound - 2 + 12 * (3 / 40) +
    2 * (if c.positive then c.sqrtLower else c.sqrtUpper) * c.parenthesis

def VCertificate.Valid (c : VCertificate) : Prop :=
  0 < c.left ∧ c.left ≤ c.right ∧
  0 < c.sqrtLower ∧ c.sqrtLower ^ 2 ≤ c.left ∧
  0 ≤ c.sqrtUpper ∧ c.right ≤ c.sqrtUpper ^ 2 ∧
  c.logLower.LowerValid (1 + c.left) ∧
  c.logUpper.UpperValid (c.right + (3 / 40) ^ 2) ∧
  c.atanLower.Valid false (1 / c.sqrtUpper) ∧
  c.atanUpper.Valid true ((3 / 40) / c.sqrtLower) ∧
  (if c.positive then 0 ≤ c.parenthesis else c.parenthesis ≤ 0)

instance (c : VCertificate) : Decidable c.Valid := by
  unfold VCertificate.Valid
  infer_instance

inductive VPosition where
  | left | box | right

structure IntervalCertificate where
  left : Rat
  right : Rat
  u : UCertificate
  v : VCertificate
  uPosition : Position
  vPosition : VPosition

def IntervalCertificate.UValid (c : IntervalCertificate) : Prop :=
  match c.uPosition with
  | .left => c.u.point ≤ c.left ∧ c.right ≤ 1953374043 / 500000000000
  | .inside => 1953374043 / 500000000000 ≤ c.left ∧
      c.right ≤ 8992695531 / 1000000000000 ∧
      1953374043 / 500000000000 ≤ c.u.point ∧ c.u.point ≤ 8992695531 / 1000000000000
  | .right => 8992695531 / 1000000000000 ≤ c.left ∧ c.right ≤ c.u.point

def IntervalCertificate.VValid (c : IntervalCertificate) : Prop :=
  match c.vPosition with
  | .left => c.v.left = c.v.right ∧ c.right ≤ c.v.left ∧ c.v.left ≤ 59205077 / 10 ^ 10
  | .box => c.v.left ≤ c.left ∧ c.right ≤ c.v.right
  | .right => c.v.left = c.v.right ∧ 59205079 / 10 ^ 10 ≤ c.v.left ∧ c.v.left ≤ c.left

instance (c : IntervalCertificate) : Decidable c.UValid := by
  unfold IntervalCertificate.UValid
  cases c.uPosition <;> infer_instance

instance (c : IntervalCertificate) : Decidable c.VValid := by
  unfold IntervalCertificate.VValid
  cases c.vPosition <;> infer_instance

def IntervalCertificate.Valid (c : IntervalCertificate) : Prop :=
  0 ≤ c.left ∧ c.left ≤ c.right ∧ c.u.Valid ∧ c.v.Valid ∧ c.UValid ∧ c.VValid ∧
    2 * c.u.upper - c.v.lower ≤ -1329 / 200

instance (c : IntervalCertificate) : Decidable c.Valid := by
  unfold IntervalCertificate.Valid
  infer_instance

/-- Balanced trees support both standalone chunks and composition of checked chunks. -/
inductive TableCertificate where
  | leaf (interval : IntervalCertificate)
  | join (left right : TableCertificate)

def TableCertificate.left : TableCertificate → Rat
  | .leaf c => c.left
  | .join a _ => a.left

def TableCertificate.right : TableCertificate → Rat
  | .leaf c => c.right
  | .join _ b => b.right

def TableCertificate.Valid : TableCertificate → Prop
  | .leaf c => c.Valid
  | .join a b => a.Valid ∧ b.Valid ∧ b.left ≤ a.right

instance tableDecidable (c : TableCertificate) : Decidable c.Valid :=
  match c with
  | .leaf c => inferInstanceAs (Decidable c.Valid)
  | .join a b => by
      change Decidable (a.Valid ∧ b.Valid ∧ b.left ≤ a.right)
      have := tableDecidable a
      have := tableDecidable b
      infer_instance

end Apery.PotentialCertificate


