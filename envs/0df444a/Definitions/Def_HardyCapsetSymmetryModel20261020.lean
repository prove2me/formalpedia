-- Prove2me | Definitions.Def_HardyCapsetSymmetryModel20261020
-- name    : HardyCapsetSymmetryModel20261020
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-20T15:56:11.303204+00:00
-- url     : https://prove2.me/theorems/c7c7812a-79d1-40fb-8b18-0876573d4a96
-- title:
--   HardyCapsetSymmetryModel20261020
-- statement:
--   Signed coordinate permutations of the eight-dimensional ternary space as additive equivalences, the dot-product preservation predicate, the predicate that the exact baseline is preserved, composition words in finitely many generators, and finite records for hyperplane coverage. A signed equivalence requires every coordinate sign to have square one and uses an explicitly inverse coordinate permutation.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificateModel20261020
set_option autoImplicit false

namespace HardyCapset20261020.Cert

def dot (n x : Point) : ZMod 3 := ∑ i : Fin 8, n i * x i

def Orthogonal (g : Point ≃+ Point) : Prop :=
  ∀ n x : Point, dot (g n) (g x) = dot n x

def PreservesBaseline (g : Point ≃+ Point) : Prop := baseline.image g = baseline

def signedEquiv (π : Equiv.Perm (Fin 8)) (s : Fin 8 → ZMod 3)
    (hs : ∀ i, s i * s i = 1) : Point ≃+ Point where
  toFun x i := s i * x (π i)
  invFun y i := s (π.symm i) * y (π.symm i)
  left_inv x := by
    funext i
    change s (π.symm i) * (s (π.symm i) * x (π (π.symm i))) = x i
    rw [π.apply_symm_apply, ← mul_assoc, hs, one_mul]
  right_inv y := by
    funext i
    change s i * (s (π.symm (π i)) * y (π.symm (π i))) = y i
    rw [π.symm_apply_apply, ← mul_assoc, hs, one_mul]
  map_add' x y := by
    funext i
    exact mul_add (s i) (x (π i)) (y (π i))

def genGet (generators : Array (Point ≃+ Point)) (i : ℕ) : Point ≃+ Point :=
  generators[i]?.getD (AddEquiv.refl Point)

def wordMap (generators : Array (Point ≃+ Point)) : List ℕ → (Point ≃+ Point)
  | [] => AddEquiv.refl Point
  | i :: rest => (wordMap generators rest).trans (genGet generators i)

structure CoverageRecord where
  representative : ℕ
  groupIndex : ℕ
  factor : ℕ
  deriving Repr, Inhabited

end HardyCapset20261020.Cert


