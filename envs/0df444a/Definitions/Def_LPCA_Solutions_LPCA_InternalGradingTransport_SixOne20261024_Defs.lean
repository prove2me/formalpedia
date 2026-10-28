-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_InternalGradingTransport_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_InternalGradingTransport_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:07:31.071827+00:00
-- url     : https://prove2.me/theorems/e03806ee-0d2a-4664-a2ce-37367192e001
-- title:
--   Internal Grading Transport — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for internal grading transport used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   An additive equivalence preserving each specified submodule transfers
--   the internal direct-sum property. No replacement scalar action is needed.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_InternalGradingTransport.lean, selected declarations in lines 9–46; source SHA-256 de4070130e44d2540254891d89f25a909fb22dbf1a75bd6c0cae0db4a2ccaeec; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.DirectSum.Module

set_option autoImplicit false

namespace LPCA

universe u

/-- An additive equivalence preserving each specified submodule transfers
the internal direct-sum property. No replacement scalar action is needed. -/
theorem internalGradingTransport
    {R I M N : Type u} [Ring R] [DecidableEq I]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (A : I → Submodule R M) (B : I → Submodule R N)
    (E : M ≃+ N) (hmem : ∀ i x, x ∈ A i ↔ E x ∈ B i)
    (hA : DirectSum.IsInternal A) : DirectSum.IsInternal B := by
  let e : ∀ i, A i ≃+ B i := fun i =>
    { toFun := fun x => ⟨E x, (hmem i x).mp x.property⟩
      invFun := fun y => ⟨E.symm y, (hmem i (E.symm y)).mpr
        (by simpa only [E.apply_symm_apply] using y.property)⟩
      left_inv := fun x => Subtype.ext (E.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (E.apply_symm_apply y)
      map_add' := fun x y => Subtype.ext (E.map_add x y) }
  let G := DirectSum.congrAddEquiv e
  have hG : ∀ z, DirectSum.coeAddMonoidHom B (G z) = E (DirectSum.coeAddMonoidHom A z) := by
    intro z
    induction z using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | add z w hz hw => simp only [map_add, hz, hw]
    | of i x =>
      change DirectSum.coeAddMonoidHom B
        (DirectSum.map (fun i => (e i).toAddMonoidHom) (DirectSum.of (fun i => A i) i x)) = _
      rw [DirectSum.map_of, DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
      rfl
  change Function.Bijective (DirectSum.coeAddMonoidHom B)
  constructor
  · intro x y h
    apply G.symm.injective
    apply hA.injective
    apply E.injective
    rw [← hG, ← hG, G.apply_symm_apply, G.apply_symm_apply]
    exact h
  · intro y
    obtain ⟨x, hx⟩ := hA.surjective (E.symm y)
    refine ⟨G x, ?_⟩
    rw [hG, hx, E.apply_symm_apply]

end LPCA


