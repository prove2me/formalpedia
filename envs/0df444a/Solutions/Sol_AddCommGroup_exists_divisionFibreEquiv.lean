-- Prove2me | solution 1 for AddCommGroup.exists_divisionFibreEquiv
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:39.944173+00:00
-- url     : https://prove2.me/submissions/557f3a11-b7f6-42d2-9ff2-74deedfc2216

import Mathlib

set_option autoImplicit false

private theorem division_carry_decomposition (a b : ZMod 71) :
    (a + b).val + 71 * ((a.val + b.val) / 71) = a.val + b.val := by
  rw [ZMod.val_add]
  exact Nat.mod_add_div _ _

/-- The division fibres are the standard torsion extension as a set. The displayed
coordinate and carry equations identify addition without assuming a group structure
on the dependent union. -/
theorem _root_.solution
    (G : Type*) [AddCommGroup G] (Q : G) :
    let T := (nsmulAddMonoidHom (α := G) 71).ker
    let F := Σ a : ZMod 71, {X : G // (71 : ℕ) • X = a.val • ((71 : ℕ) • Q)}
    ∃ e : (T × ZMod 71) ≃ F,
      (∀ (v : T) (a : ZMod 71), (e (v, a)).1 = a ∧
        ((e (v, a)).2 : G) = (v : G) + a.val • Q) ∧
      (∀ x : F, ((e.symm x).1 : G) = (x.2 : G) - x.1.val • Q ∧
        (e.symm x).2 = x.1) ∧
      ∀ (v w : T) (a b : ZMod 71),
        ((e (v + w, a + b)).2 : G) =
          ((e (v, a)).2 : G) + ((e (w, b)).2 : G) -
            ((a.val + b.val) / 71) • ((71 : ℕ) • Q) := by
  let T := (nsmulAddMonoidHom (α := G) 71).ker
  let F := Σ a : ZMod 71, {X : G // (71 : ℕ) • X = a.val • ((71 : ℕ) • Q)}
  have hcomm (a : ℕ) : (71 : ℕ) • (a • Q) = a • ((71 : ℕ) • Q) := by
    rw [← mul_nsmul, ← mul_nsmul, Nat.mul_comm]
  let e : (T × ZMod 71) ≃ F :=
    { toFun := fun x => ⟨x.2, ⟨(x.1 : G) + x.2.val • Q, by
        rw [nsmul_add, show (71 : ℕ) • (x.1 : G) = 0 from x.1.property,
          zero_add, hcomm]⟩⟩
      invFun := fun x => (⟨(x.2 : G) - x.1.val • Q, by
        change (71 : ℕ) • ((x.2 : G) - x.1.val • Q) = 0
        rw [nsmul_sub, x.2.property, hcomm, sub_self]⟩, x.1)
      left_inv := by
        intro x
        apply Prod.ext
        · apply Subtype.ext
          change (x.1 : G) + x.2.val • Q - x.2.val • Q = (x.1 : G)
          simp
        · rfl
      right_inv := by
        rintro ⟨a, X, hX⟩
        apply congrArg (Sigma.mk a)
        apply Subtype.ext
        change X - a.val • Q + a.val • Q = X
        exact sub_add_cancel _ _ }
  refine ⟨e, ?_, ?_, ?_⟩
  · intro v a
    exact ⟨rfl, rfl⟩
  · intro x
    exact ⟨rfl, rfl⟩
  · intro v w a b
    change ((v : G) + (w : G)) + (a + b).val • Q =
      ((v : G) + a.val • Q) + ((w : G) + b.val • Q) -
        ((a.val + b.val) / 71) • ((71 : ℕ) • Q)
    have hn := congrArg (fun n : ℕ => n • Q) (division_carry_decomposition a b)
    simp only [add_nsmul, mul_nsmul] at hn
    have heq : (a + b).val • Q = a.val • Q + b.val • Q -
        ((a.val + b.val) / 71) • ((71 : ℕ) • Q) := (eq_sub_iff_add_eq).mpr hn
    rw [heq]
    abel
