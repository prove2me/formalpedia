-- Prove2me | Definitions.Def_LocalConjugacy_Examples
-- name    : LocalConjugacy_Examples
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T03:41:17.076993+00:00
-- url     : https://prove2.me/theorems/47bf8e84-53db-4c38-88bf-e1744638c6af
-- title:
--   Concrete groups and cohomology for the counterexamples
-- statement:
--   The standard groups $S_3$, $Q_8$, and $C_3$; the imprimitive wreath product $C_3\wr S_3$ through its three-coordinate permutation action; the Heisenberg group of order $27$ through upper-unitriangular coordinates; and nonabelian $H^1$ for explicit finite-group actions. The general linear group in the target is Mathlib's $GL(2,\mathbf F_3)$.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, arXiv:2609.37678v1, https://arxiv.org/pdf/2609.37678v1, §§1–4, pp. 1–8. Adapted in part from the author’s local Apache-2.0 Lean development.

import Definitions.Def_LocalConjugacy_Cohomology

/-!
# Concrete groups and finite cohomology for the two counterexamples

Mathlib supplies the quaternion group, permutation groups, general linear group,
cyclic groups (`Multiplicative (ZMod n)`), Sylow subgroups, and semidirect products.
The imprimitive wreath product here uses the natural action of S₃ on three points;
the regular wreath product would have six base coordinates and the wrong order.
The Heisenberg model records the three upper-unitriangular matrix coordinates.
Finite cocycles need no extra continuity predicate: all finite groups in the
examples carry their discrete topology, in which every map is continuous.
-/

namespace LocalConjugacy

/-- The symmetric group on three letters, using Mathlib's permutation group. -/
abbrev S3 := Equiv.Perm (Fin 3)

/-- The quaternion group of order eight, using Mathlib's standard presentation. -/
abbrev Q8 := QuaternionGroup 2

/-- The cyclic group of order three, written multiplicatively. -/
abbrev C3 := Multiplicative (ZMod 3)

/-- The base of the imprimitive wreath product: one C₃ for each of three letters. -/
abbrev WreathBase := Fin 3 → C3

/-- Permuting coordinates is a homomorphism S₃ → Aut(C₃³).
The inverse permutation in `arrowCongr` gives a left group action. -/
def wreathAction : S3 →* MulAut WreathBase where
  toFun s := MulEquiv.arrowCongr s (MulEquiv.refl C3)
  map_one' := by
    -- Equality of coordinate permutations reduces to equality at each coordinate.
    ext b i
    rfl
  map_mul' s t := by
    -- The inverse of a product reverses the two precompositions.
    ext b i
    rfl

/-- The natural, imprimitive wreath product C₃ ≀ S₃, of order 3³ · 6 = 162. -/
abbrev WreathC3S3 := WreathBase ⋊[wreathAction] S3

/-- Coordinates of the matrix [[1,a,c],[0,1,b],[0,0,1]] over F₃.
This fixes the Heisenberg group itself, rather than only its order and exponent. -/
@[ext] structure Heisenberg3 where
  a : ZMod 3
  b : ZMod 3
  c : ZMod 3

/-- Matrix multiplication in the three coordinates; the cross term is a · b'. -/
instance heisenbergMul : Mul Heisenberg3 :=
  ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c + x.a * y.b⟩⟩

/-- The identity matrix has all three upper-diagonal coordinates zero. -/
instance heisenbergOne : One Heisenberg3 := ⟨⟨0, 0, 0⟩⟩

/-- Matrix inversion introduces the cross-term correction in the top-right entry. -/
instance heisenbergInv : Inv Heisenberg3 :=
  ⟨fun x => ⟨-x.a, -x.b, -x.c + x.a * x.b⟩⟩

/-- The matrix coordinate operations satisfy the group axioms over F₃. -/
instance : Group Heisenberg3 where
  mul := heisenbergMul.mul
  one := heisenbergOne.one
  inv := heisenbergInv.inv
  mul_assoc x y z := by
    -- The group law is associative by the distributive law in F₃.
    apply Heisenberg3.ext
    · change (x.a + y.a) + z.a = x.a + (y.a + z.a)
      ring
    · change (x.b + y.b) + z.b = x.b + (y.b + z.b)
      ring
    · change (x.c + y.c + x.a * y.b) + z.c + (x.a + y.a) * z.b =
        x.c + (y.c + z.c + y.a * z.b) + x.a * (y.b + z.b)
      ring
  one_mul x := by
    -- The zero triple is the identity matrix.
    apply Heisenberg3.ext
    · change 0 + x.a = x.a
      ring
    · change 0 + x.b = x.b
      ring
    · change 0 + x.c + 0 * x.b = x.c
      ring
  mul_one x := by
    apply Heisenberg3.ext
    · change x.a + 0 = x.a
      ring
    · change x.b + 0 = x.b
      ring
    · change x.c + 0 + x.a * 0 = x.c
      ring
  inv_mul_cancel x := by
    -- The correction a · b in the inverse cancels the cross term.
    apply Heisenberg3.ext
    · change -x.a + x.a = 0
      ring
    · change -x.b + x.b = 0
      ring
    · change (-x.c + x.a * x.b) + x.c + (-x.a) * x.b = 0
      ring

/-- Nonabelian cocycles for an explicitly supplied finite-group action. -/
def FiniteCocycle {J N : Type*} [Group J] [Group N] (a : J →* MulAut N) :=
  {f : J → N // ∀ x y, f (x * y) = f x * a x (f y)}

/-- Two cocycles differ by one global coboundary coefficient.
The structural equivalence proof is included so the quotient is an actual type. -/
def finiteCohomologySetoid {J N : Type*} [Group J] [Group N]
    (a : J →* MulAut N) : Setoid (FiniteCocycle a) where
  r f g := ∃ n : N, ∀ x, g.val x = n⁻¹ * f.val x * a x n
  iseqv := by
    constructor
    · -- The identity coefficient leaves a cocycle unchanged.
      intro f
      exact ⟨1, by simp⟩
    · -- Inverting a witness reverses the cohomology relation.
      rintro f g ⟨n, hn⟩
      refine ⟨n⁻¹, fun x => ?_⟩
      rw [hn x]
      simp [mul_assoc]
    · -- Multiplication composes the two global witnesses.
      rintro f g h ⟨n, hn⟩ ⟨m, hm⟩
      refine ⟨n * m, fun x => ?_⟩
      rw [hm x, hn x]
      simp [mul_assoc]

/-- Nonabelian H¹ for finite discrete groups, as an actual quotient of cocycles. -/
def FiniteH1 {J N : Type*} [Group J] [Group N] (a : J →* MulAut N) :=
  Quotient (finiteCohomologySetoid a)

/-- Finite local conjugacy, expressed directly with Mathlib's Sylow subgroups.
The subgroup embeddings place both Sylow subgroups in the same ambient group.
Primes not dividing a subgroup order are included; their Sylow subgroups are trivial. -/
def FiniteLocallyConjugate {G : Type*} [Group G] (H K : Subgroup G) : Prop :=
  ∀ (p : ℕ) (hp : p.Prime),
    letI : Fact p.Prime := ⟨hp⟩
    ∃ (P : Sylow p H) (Q : Sylow p K),
      Conjugate (P.toSubgroup.map H.subtype) (Q.toSubgroup.map K.subtype)

/-- The normal copy of Q₈ in its semidirect product with S₃. -/
def quaternionKernel (a : S3 →* MulAut Q8) : Subgroup (Q8 ⋊[a] S3) :=
  (SemidirectProduct.inl : Q8 →* Q8 ⋊[a] S3).range

/-- The canonical S₃ complement in the same semidirect product. -/
def quaternionComplement (a : S3 →* MulAut Q8) : Subgroup (Q8 ⋊[a] S3) :=
  (SemidirectProduct.inr : S3 →* Q8 ⋊[a] S3).range

end LocalConjugacy


