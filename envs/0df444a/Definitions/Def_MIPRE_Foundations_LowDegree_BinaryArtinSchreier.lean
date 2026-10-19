-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier
-- name    : MIPRE_Foundations_LowDegree_BinaryArtinSchreier
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:55:02.256332+00:00
-- url     : https://prove2.me/theorems/a762d799-7e2d-4d75-8cfd-5c6e76e9aca5
-- title:
--   Definitions of BinaryArtinSchreier: The characteristic-two Artin–Schreier tower step The polynomial `X² + X + a` has no root exactly when its quadratic…
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryArtinSchreier` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The characteristic-two Artin–Schreier tower step. The polynomial `X² + X + a` has no root exactly when its quadratic quotient is an extension field. In that extension, multiplication of `a` by the canonical root supplies the next no-root parameter. These are algebraic correctness lemmas for the explicit binary tower constructor; they do not choose a root by searching through the field.
--
--   **Definitions** (2): `MIPRE.LowDegree.BinaryArtinSchreier.quadratic` (The monic quadratic used by the characteristic-two tower.); `MIPRE.LowDegree.BinaryArtinSchreier.quadraticBasis` (The specified basis of every monic quadratic quotient, indexed by `Fin 2`.).
--
--   **Embedded lemmas** (8): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `comp_quadratic_irreducible`, `quadraticBasis_apply`, `quadratic_eval`, `quadratic_irreducible_iff`, `quadratic_monic`, `quadratic_natDegree`, `root_not_mem_range`, `root_relation`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryArtinSchreier` (`MIPRE/Foundations/LowDegree/BinaryArtinSchreier.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryArtinSchreier.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryArtinSchreier.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdjoinRoot
import Theorems.Thm_MIPRE_LowDegree_BinaryFiniteField_minpoly_natDegree_of_not_mem_range

/-!
# The characteristic-two Artin–Schreier tower step

The polynomial `X² + X + a` has no root exactly when its quadratic quotient is
an extension field. In that extension, multiplication of `a` by the canonical
root supplies the next no-root parameter. These are algebraic correctness
lemmas for the explicit binary tower constructor; they do not choose a root
by searching through the field.
-/

noncomputable section

namespace MIPRE.LowDegree.BinaryArtinSchreier

open Polynomial Module

variable {K : Type*} [Field K]

/-- The monic quadratic used by the characteristic-two tower. -/
def quadratic (a : K) : K[X] := X ^ 2 + X + C a

@[simp] theorem quadratic_natDegree (a : K) : (quadratic a).natDegree = 2 := by
  simpa [quadratic] using (natDegree_quadratic (a := (1 : K)) (b := 1) (c := a) one_ne_zero)

theorem quadratic_monic (a : K) : (quadratic a).Monic := by
  simpa [quadratic, Monic] using
    (leadingCoeff_quadratic (a := (1 : K)) (b := 1) (c := a) one_ne_zero)

@[simp] theorem quadratic_eval (a x : K) : (quadratic a).eval x = x ^ 2 + x + a := by
  simp [quadratic]

/-- Degree two reduces irreducibility to the explicit no-root property. -/
theorem quadratic_irreducible_iff (a : K) :
    Irreducible (quadratic a) ↔ ∀ x : K, x ^ 2 + x + a ≠ 0 := by
  constructor
  · intro h x
    simpa only [IsRoot, quadratic_eval] using
      (h.not_isRoot_of_natDegree_ne_one (by simp) (x := x))
  · intro h
    apply irreducible_of_degree_le_three_of_not_isRoot (by simp)
    simpa only [IsRoot, quadratic_eval] using h

/-- The specified basis of every monic quadratic quotient, indexed by `Fin 2`. -/
def quadraticBasis (a : K) : Basis (Fin 2) K (AdjoinRoot (quadratic a)) :=
  (AdjoinRoot.powerBasis' (quadratic_monic a)).basis.reindex
    (finCongr (quadratic_natDegree a))

@[simp] theorem quadraticBasis_apply (a : K) (i : Fin 2) :
    quadraticBasis a i = AdjoinRoot.root (quadratic a) ^ (i : ℕ) := by
  rw [quadraticBasis, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

/-- The root of the quadratic satisfies its defining Artin–Schreier equation. -/
theorem root_relation (a : K) :
    AdjoinRoot.root (quadratic a) ^ 2 + AdjoinRoot.root (quadratic a) +
      algebraMap K (AdjoinRoot (quadratic a)) a = 0 := by
  have h := AdjoinRoot.eval₂_root (quadratic a)
  change (X ^ 2 + X + C a : K[X]).eval₂ _ _ = 0 at h
  rw [eval₂_add, eval₂_add, eval₂_pow, eval₂_X, eval₂_C] at h
  exact h

variable [CharP K 2]

omit [CharP K 2] in
/-- The quadratic root cannot already lie in the original field. -/
theorem root_not_mem_range (a : K) (ha : Irreducible (quadratic a)) :
    AdjoinRoot.root (quadratic a) ∉ (algebraMap K (AdjoinRoot (quadratic a))).range := by
  let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
  rintro ⟨x, hx⟩
  have hr := root_relation a
  rw [← hx, ← map_pow, ← map_add, ← map_add] at hr
  have hz : x ^ 2 + x + a = 0 := (algebraMap K _).injective (hr.trans (map_zero _).symm)
  exact (quadratic_irreducible_iff a).1 ha x hz

/-- A binary annihilating polynomial of the old dimension gives the next
irreducible polynomial by substitution of `X² + X`. The hypothesis on `g`
is supplied by the explicit Frobenius orbit product, after coefficient descent. -/
theorem comp_quadratic_irreducible [Finite K] [Algebra (ZMod 2) K]
    [FiniteDimensional (ZMod 2) K] (t : ℕ)
    (hK : Module.finrank (ZMod 2) K = 2 ^ t)
    (a : K) (ha : Irreducible (quadratic a))
    (g : (ZMod 2)[X]) (hg : g.Monic) (hd : g.natDegree = 2 ^ t)
    (hz : aeval a g = 0) :
    Irreducible (g.comp (quadratic (0 : ZMod 2))) := by
  let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
  let : CharP (AdjoinRoot (quadratic a)) 2 := charP_of_injective_algebraMap'
    K (A := AdjoinRoot (quadratic a)) 2
  let : Module.Finite K (AdjoinRoot (quadratic a)) := (quadratic_monic a).finite_adjoinRoot
  let : Module.Finite (ZMod 2) (AdjoinRoot (quadratic a)) :=
    Module.Finite.trans K (AdjoinRoot (quadratic a))
  let : Fintype K := Fintype.ofFinite K
  have hcard : Nat.card K = 2 ^ (2 ^ t) := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hK]
  have hdim : Module.finrank K (AdjoinRoot (quadratic a)) = 2 := by
    rw [(AdjoinRoot.powerBasis' (quadratic_monic a)).finrank]
    exact quadratic_natDegree a
  have htotal : Module.finrank (ZMod 2) (AdjoinRoot (quadratic a)) = 2 ^ (t + 1) := by
    rw [← Module.finrank_mul_finrank (ZMod 2) K (AdjoinRoot (quadratic a)), hK, hdim,
      pow_succ]
  have hdeg := BinaryFiniteField.minpoly_natDegree_of_not_mem_range t hcard htotal
    (AdjoinRoot.root (quadratic a)) (root_not_mem_range a ha)
  have hi : IsIntegral (ZMod 2) (AdjoinRoot.root (quadratic a)) :=
    IsIntegral.of_finite (ZMod 2) _
  have hp : aeval (AdjoinRoot.root (quadratic a)) (g.comp (quadratic (0 : ZMod 2))) = 0 := by
    rw [aeval_comp]
    have hroot : aeval (AdjoinRoot.root (quadratic a)) (quadratic (0 : ZMod 2)) =
        algebraMap K (AdjoinRoot (quadratic a)) a := by
      change aeval (AdjoinRoot.root (quadratic a)) (X ^ 2 + X + C (0 : ZMod 2)) = _
      rw [map_add, map_add, map_pow, aeval_X, aeval_C, map_zero, add_zero]
      exact CharTwo.add_eq_zero.mp (root_relation a)
    rw [hroot]
    change aeval ((IsScalarTower.toAlgHom (ZMod 2) K (AdjoinRoot (quadratic a))) a) g = 0
    rw [aeval_algHom_apply, hz, map_zero]
  have heq : g.comp (quadratic (0 : ZMod 2)) =
      minpoly (ZMod 2) (AdjoinRoot.root (quadratic a)) := by
    apply eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hi)
      (hg.comp (quadratic_monic (0 : ZMod 2)) (by simp)) ((minpoly.dvd_iff).2 hp)
    rw [natDegree_comp, hd, quadratic_natDegree, hdeg, pow_succ]
  rw [heq]
  exact minpoly.irreducible hi

end MIPRE.LowDegree.BinaryArtinSchreier

end


