-- Prove2me | Definitions.Def_Octonion_octonions
-- name    : Octonion_octonions
-- status  : Definition
-- author  : @jawneeboy
-- created : 2026-09-23T13:24:59.894984+00:00
-- url     : https://prove2.me/theorems/60ae8f5c-d282-4786-b8d2-ab23429c9ae2
-- title:
--   Octonions as quaternion pairs
-- statement:
--   Use the Cayley–Dickson model $\mathbb O_R=\mathbb H_R\times\mathbb H_R$, with $(a,b)(c,d)=(ac-\bar d b,da+b\bar c)$ and $\overline{(a,b)}=(\bar a,-b)$. Over a commutative ring $R$, coordinatewise addition and this product give a unital nonassociative ring with additive involutive conjugation.
-- source:
--   Standard reference: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345. Relevant topics appear in Chapter 6 (composition algebras), Chapter 9 (octavian integers), and Section 10.1 (the 240 octavian units), as confirmed by the publisher's table of contents. Supporting exposition: John Baez, Integral Octonions (Part 6), September 17, 2013, https://math.ucr.edu/home/baez/octonions/integers/integers_6.html. These references concern the classical mathematics. This contribution supplies Lean definitions and machine-checked proofs in the stated coordinate convention; it does not claim new mathematical results or reproduce a particular proof from the book. The topic references do not assert that the exact Lean statement occurs there. Verification of the book references is limited to its table of contents, not a statement-by-statement comparison with the book; no page-specific or numbered theorem attribution is claimed. Local formalization: Basic/Def_Octonion_octonions.lean; SHA-256 f1b02dd740cdb2a27d6e517cadde9fd0f57c7cae57973b5a86617f93fc52cae9.

import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

open Quaternion

/-- The octonions over `R`: pairs of quaternions `(a, b)` with the Cayley-Dickson
product `(a, b) * (c, d) = (a c − d̄ b, d a + b c̄)`, conjugation `(a, b)‾ = (ā, −b)`
and coordinatewise addition. Over a commutative ring, this file constructs a
`NonAssocRing` with additive, involutive conjugation. Over `ℚ`, multiplication is
noncommutative and nonassociative; `Octonion.exists_not_assoc` proves the latter.
Octonions are alternative and power-associative, but those identities are not
formalized in this package. -/
@[ext]
structure octonions (R : Type*) [Zero R] [One R] [Neg R] where
  /-- First quaternion component. -/
  fst : ℍ[R]
  /-- Second quaternion component. -/
  snd : ℍ[R]

scoped[Octonion] notation "𝕆[" R "]" => octonions R

/-- The underlying type equivalence with a pair of quaternions. Addition is
coordinatewise; multiplication is the Cayley-Dickson product. -/
def toProd (R : Type*) [Zero R] [One R] [Neg R] : octonions R ≃ ℍ[R] × ℍ[R] where
  toFun x := (x.fst, x.snd)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace Octonion
variable {R : Type*} [CommRing R]

instance : Zero (octonions R) := ⟨⟨0, 0⟩⟩
instance : Add (octonions R) := ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
instance : Neg (octonions R) := ⟨fun x => ⟨-x.fst, -x.snd⟩⟩
instance : Sub (octonions R) := ⟨fun x y => ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
instance : One (octonions R) := ⟨⟨1, 0⟩⟩
instance : NatCast (octonions R) where natCast n := ⟨n, 0⟩
instance : IntCast (octonions R) where intCast z := ⟨z, 0⟩

/-- Cayley-Dickson product: (a, b) * (c, d) = (a c − d̄ b, d a + b c̄). -/
def cdMul (x y : octonions R) : octonions R :=
  ⟨x.fst * y.fst - star y.snd * x.snd, y.snd * x.fst + x.snd * star y.fst⟩

instance : Mul (octonions R) := ⟨cdMul⟩

/-- Octonion conjugation: (a, b)‾ = (ā, −b). -/
def conj (x : octonions R) : octonions R := ⟨star x.fst, -x.snd⟩

instance : Star (octonions R) := ⟨conj⟩

@[simp] theorem fst_add (x y : octonions R) : (x + y).fst = x.fst + y.fst := rfl
@[simp] theorem snd_add (x y : octonions R) : (x + y).snd = x.snd + y.snd := rfl
@[simp] theorem fst_neg (x : octonions R) : (-x).fst = -x.fst := rfl
@[simp] theorem snd_neg (x : octonions R) : (-x).snd = -x.snd := rfl
@[simp] theorem fst_zero : (0 : octonions R).fst = 0 := rfl
@[simp] theorem snd_zero : (0 : octonions R).snd = 0 := rfl
@[simp] theorem fst_one : (1 : octonions R).fst = 1 := rfl
@[simp] theorem snd_one : (1 : octonions R).snd = 0 := rfl
@[simp] theorem fst_cdMul (x y : octonions R) :
    (cdMul x y).fst = x.fst * y.fst - star y.snd * x.snd := rfl
@[simp] theorem snd_cdMul (x y : octonions R) :
    (cdMul x y).snd = y.snd * x.fst + x.snd * star y.fst := rfl
@[simp] theorem fst_conj (x : octonions R) : (conj x).fst = star x.fst := rfl
@[simp] theorem snd_conj (x : octonions R) : (conj x).snd = -x.snd := rfl
@[simp] theorem fst_mul (x y : octonions R) :
    (x * y).fst = x.fst * y.fst - star y.snd * x.snd := rfl
@[simp] theorem snd_mul (x y : octonions R) :
    (x * y).snd = y.snd * x.fst + x.snd * star y.fst := rfl

instance : SMul ℕ (octonions R) := ⟨fun n x => ⟨n • x.fst, n • x.snd⟩⟩
instance : SMul ℤ (octonions R) := ⟨fun z x => ⟨z • x.fst, z • x.snd⟩⟩

instance : AddCommGroup (octonions R) := by
  apply (toProd R).injective.addCommGroup <;> intros <;> rfl

/-- Conjugation is involutive. -/
theorem conj_conj (x : octonions R) : conj (conj x) = x := by
  obtain ⟨a, b⟩ := x
  show conj (conj ⟨a, b⟩) = ⟨a, b⟩
  ext <;> simp [conj]

instance : InvolutiveStar (octonions R) where
  star_involutive := fun x => by show conj (conj x) = x; exact conj_conj x

/-- Conjugation is additive. -/
theorem conj_add (x y : octonions R) : conj (x + y) = conj x + conj y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  show conj (⟨a, b⟩ + ⟨c, d⟩) = conj ⟨a, b⟩ + conj ⟨c, d⟩
  ext <;> simp [conj] <;> abel

instance : StarAddMonoid (octonions R) where
  star_add := conj_add

theorem cdMul_zero_left (x : octonions R) : cdMul 0 x = 0 := by
  obtain ⟨a, b⟩ := x
  show cdMul 0 ⟨a, b⟩ = 0
  ext <;> simp [cdMul]

theorem cdMul_zero_right (x : octonions R) : cdMul x 0 = 0 := by
  obtain ⟨a, b⟩ := x
  show cdMul ⟨a, b⟩ 0 = 0
  ext <;> simp [cdMul]

theorem cdMul_one_left (x : octonions R) : cdMul 1 x = x := by
  obtain ⟨a, b⟩ := x
  show cdMul 1 ⟨a, b⟩ = ⟨a, b⟩
  ext <;> simp [cdMul]

theorem cdMul_one_right (x : octonions R) : cdMul x 1 = x := by
  obtain ⟨a, b⟩ := x
  show cdMul ⟨a, b⟩ 1 = ⟨a, b⟩
  ext <;> simp [cdMul]

theorem cdMul_add_left (x y z : octonions R) : cdMul x (y + z) = cdMul x y + cdMul x z := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  obtain ⟨e, f⟩ := z
  show cdMul ⟨a, b⟩ (⟨c, d⟩ + ⟨e, f⟩) = cdMul ⟨a, b⟩ ⟨c, d⟩ + cdMul ⟨a, b⟩ ⟨e, f⟩
  ext <;> simp [cdMul] <;> ring

theorem cdMul_add_right (x y z : octonions R) : cdMul (x + y) z = cdMul x z + cdMul y z := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  obtain ⟨e, f⟩ := z
  show cdMul (⟨a, b⟩ + ⟨c, d⟩) ⟨e, f⟩ = cdMul ⟨a, b⟩ ⟨e, f⟩ + cdMul ⟨c, d⟩ ⟨e, f⟩
  ext <;> simp [cdMul] <;> ring

theorem natCast_zero' : ((0 : ℕ) : octonions R) = 0 := by
  show (⟨((0 : ℕ) : ℍ[R]), (0 : ℍ[R])⟩ : octonions R) = 0
  ext <;> simp
theorem natCast_succ' (n : ℕ) :
    ((n + 1 : ℕ) : octonions R) = (n : octonions R) + 1 := by
  show (⟨((n + 1 : ℕ) : ℍ[R]), (0 : ℍ[R])⟩ : octonions R) = ⟨(n : ℍ[R]), (0 : ℍ[R])⟩ + ⟨1, 0⟩
  ext <;> simp [Nat.cast_add]
theorem intCast_ofNat' (n : ℕ) :
    ((n : ℤ) : octonions R) = ((n : ℕ) : octonions R) := by
  show (⟨((n : ℤ) : ℍ[R]), (0 : ℍ[R])⟩ : octonions R) = ⟨((n : ℕ) : ℍ[R]), (0 : ℍ[R])⟩
  ext <;> simp
theorem intCast_negSucc' (n : ℕ) :
    ((Int.negSucc n : ℤ) : octonions R) = -((n + 1 : ℕ) : octonions R) := by
  show (⟨(Int.negSucc n : ℍ[R]), (0 : ℍ[R])⟩ : octonions R) = -⟨((n + 1 : ℕ) : ℍ[R]), (0 : ℍ[R])⟩
  ext <;> simp [Int.cast_negSucc, Nat.cast_add]

instance : AddCommGroupWithOne (octonions R) where
  natCast n := ⟨n, 0⟩
  intCast z := ⟨z, 0⟩
  natCast_zero := natCast_zero'
  natCast_succ := natCast_succ'
  intCast_ofNat := intCast_ofNat'
  intCast_negSucc := intCast_negSucc'

/-- The Cayley-Dickson product is distributive with a two-sided unit, giving a
`NonAssocRing`. Nonassociativity over `ℚ` is proved in `Octonion.exists_not_assoc`. -/
instance instNonAssocRing : NonAssocRing (octonions R) where
  left_distrib := fun x y z => cdMul_add_left (R := R) x y z
  right_distrib := fun x y z => cdMul_add_right (R := R) x y z
  zero_mul := fun x => cdMul_zero_left (R := R) x
  mul_zero := fun x => cdMul_zero_right (R := R) x
  one_mul := fun x => cdMul_one_left (R := R) x
  mul_one := fun x => cdMul_one_right (R := R) x

end Octonion


