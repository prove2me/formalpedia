-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_BlockTriangularLevi
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_BlockTriangularLevi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:51.754993+00:00
-- url     : https://prove2.me/theorems/c11cbd86-a0ff-445e-a57d-038cbd551199
-- title:
--   Block Triangular Levi
-- statement:
--   Definitions and structural lemmas for Block Triangular Levi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/BlockTriangularLevi.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace UpperTheory.Reformulated.B.P6.BlockTriangularLevi
open scoped Sigma DFunLike EquivLike Equiv Matrix CommSemiring CommRing Membership Set Preorder PartialOrder SemilatticeInf Lattice DistribLattice MulZeroClass Units Semiring HMul MulOne MulOneClass Monoid DivInvMonoid Group OfNat One Inv InvOneClass DivInvOneMonoid DivisionMonoid Subgroup Submonoid Subsemigroup Subtype SetLike MulZeroOneClass MonoidHom OneHom Pi PUnit Fin Finset HAdd AddMonoidWithOne AddGroupWithOne Ring DivisionRing Field CommGroup Circle DivisionSemiring Semifield Complex SeminormedRing SeminormedCommRing NormedCommRing NormedField AddChar Zero HSub
noncomputable def GlobalTheory.SmGL.blk :
    {α n : Type} → {m : α → Type} → (a : α) × m a ≃ n → n → α :=
  fun {α n : Type} {m : α → Type} (e : (a : α) × m a ≃ n) (i : n) ↦ Sigma.fst (β := fun (a : α) ↦ m a) (DFunLike.coe (β := fun (x_h1 : n) ↦ (a : α) × m a) e.symm i)
theorem blockIndex_sigma_equiv {α n : Type} {m : α → Type} (e : (a : α) × m a ≃ n) (a : α) (i : m a) :
    GlobalTheory.SmGL.blk (m := m) e (e ⟨a, i⟩) = a := by
  show (e.symm (e ⟨a, i⟩)).1 = a
  rw [Equiv.symm_apply_apply]
theorem blockTriangular_mul_submatrix {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [Fintype n] (e : (a : α) × m a ≃ n) (a : α) (X Y : Matrix n n R)
    (hX : X.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e))
    (hY : Y.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)) :
    (X * Y).submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩)
      = X.submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩)
        * Y.submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← e.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single a]
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro l _
    rcases lt_or_gt_of_ne hb with h | h
    · have h' : GlobalTheory.SmGL.blk (m := m) e (e ⟨b, l⟩) < GlobalTheory.SmGL.blk (m := m) e (e ⟨a, i⟩) := by
        rw [blockIndex_sigma_equiv, blockIndex_sigma_equiv]; exact h
      rw [hX h', zero_mul]
    · have h' : GlobalTheory.SmGL.blk (m := m) e (e ⟨a, j⟩) < GlobalTheory.SmGL.blk (m := m) e (e ⟨b, l⟩) := by
        rw [blockIndex_sigma_equiv, blockIndex_sigma_equiv]; exact h
      rw [hY h', mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h
theorem GlobalTheory.SmGL.parab_obl_1 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : LinearOrder α] [inst_h3 : Fintype n] [inst_h4 : DecidableEq n] (e : (a : α) × m a ≃ n) {x y : GL n R}, Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} x → Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} y → Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} (x * y) := by
  intro R _ α n m _ _ _ e x y hx hy
  show ((x * y : GL n R) : Matrix n n R).BlockTriangular _
  rw [Units.val_mul]
  exact Matrix.BlockTriangular.mul hx hy
theorem GlobalTheory.SmGL.parab_obl_2 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : LinearOrder α] [inst_h3 : Fintype n] [inst_h4 : DecidableEq n] (e : (a : α) × m a ≃ n), Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} (OfNat.ofNat (nat_lit 1)) := by
  intro R _ α n m _ _ _ e
  show ((1 : GL n R) : Matrix n n R).BlockTriangular _
  rw [Units.val_one]
  exact Matrix.blockTriangular_one
theorem GlobalTheory.SmGL.parab_obl_3 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : LinearOrder α] [inst_h3 : Fintype n] [inst_h4 : DecidableEq n] (e : (a : α) × m a ≃ n) {x : GL n R}, Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} x → Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} x⁻¹ := by
  intro R _ α n m _ _ _ e x hx
  show ((x⁻¹ : GL n R) : Matrix n n R).BlockTriangular _
  rw [Matrix.coe_units_inv]
  haveI : Invertible (x : Matrix n n R) := x.invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular hx
noncomputable def GlobalTheory.SmGL.parab :
    (R : Type) → [inst_h0 : CommRing R] → {α n : Type} → {m : α → Type} → [inst_h2 : LinearOrder α] → [inst_h3 : Fintype n] → [inst_h4 : DecidableEq n] → (a : α) × m a ≃ n → Subgroup (GL n R) :=
  fun (R : Type) {inst_h0 : CommRing R} {α n : Type} {m : α → Type} {inst_h2 : LinearOrder α} {inst_h3 : Fintype n} {inst_h4 : DecidableEq n} (e : (a : α) × m a ≃ n) ↦ { carrier := {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)}, mul_mem' := @GlobalTheory.SmGL.parab_obl_1 R inst_h0 α n m inst_h2 inst_h3 inst_h4 e, one_mem' := GlobalTheory.SmGL.parab_obl_2 R (m := m) e, inv_mem' := @GlobalTheory.SmGL.parab_obl_3 R inst_h0 α n m inst_h2 inst_h3 inst_h4 e }
@[reducible] noncomputable def GlobalTheory.SmGL.Levi :
    (R : Type) → [inst_h0 : CommRing R] → {α : Type} → (m : α → Type) → [inst_h2 : (a : α) → Fintype (m a)] → [inst_h3 : (a : α) → DecidableEq (m a)] → Type :=
  fun (R : Type) {inst_f0 : CommRing R} {α : Type} (m : α → Type) {inst_f1 : (a : α) → Fintype (m a)} {inst_f2 : (a : α) → DecidableEq (m a)} ↦ (a : α) → GL (m a) R
theorem GlobalTheory.SmGL.diagBlock_obl_1 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : LinearOrder α] [inst_h3 : (a : α) → Fintype (m a)] [inst_h4 : (a : α) → DecidableEq (m a)] [inst_h5 : Fintype n] [inst_h6 : DecidableEq n] (e : (a : α) × m a ≃ n) (a : α), Eq (α := Matrix (m a) (m a) R) (Matrix.submatrix (m := n) (n := n) (Units.val (Subtype.val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x) (OfNat.ofNat (nat_lit 1)))) (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h7 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h8 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) (OfNat.ofNat (nat_lit 1)) := by
  intro R _ α n m _ _ _ _ _ e a
  show ((1 : GL n R) : Matrix n n R).submatrix _ _ = 1
  rw [Units.val_one]
  exact Matrix.submatrix_one _ (e.injective.comp sigma_mk_injective)
theorem GlobalTheory.SmGL.diagBlock_obl_2 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : Fintype α] [inst_h3 : LinearOrder α] [inst_h4 : (a : α) → Fintype (m a)] [inst_h5 : (a : α) → DecidableEq (m a)] [inst_h6 : Fintype n] [inst_h7 : DecidableEq n] (e : (a : α) × m a ≃ n) (a : α) (x y : ↥(GlobalTheory.SmGL.parab R (m := m) e)), ((x * y).val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x).val.submatrix (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h8 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h9 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) = HMul.hMul (α := Matrix (m a) (m a) R) (x.val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x).val.submatrix (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h10 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h11 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) (y.val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x).val.submatrix (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h12 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h13 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) := by
  intro R _ α n m _ _ _ _ _ _ e a x y
  have hx : ((x : GL n R) : Matrix n n R).BlockTriangular (GlobalTheory.SmGL.blk (m := m) e) := x.2
  have hy : ((y : GL n R) : Matrix n n R).BlockTriangular (GlobalTheory.SmGL.blk (m := m) e) := y.2
  have key := blockTriangular_mul_submatrix e a _ _ hx hy
  exact key
noncomputable def GlobalTheory.SmGL.diagBlock :
    (R : Type) → [inst_h0 : CommRing R] → {α n : Type} → {m : α → Type} → [inst_h2 : Fintype α] → [inst_h3 : LinearOrder α] → [inst_h4 : (a : α) → Fintype (m a)] → [inst_h5 : (a : α) → DecidableEq (m a)] → [inst_h6 : Fintype n] → [inst_h7 : DecidableEq n] → (e : (a : α) × m a ≃ n) → (a : α) → ↥(GlobalTheory.SmGL.parab R (m := m) e) →* Matrix (m a) (m a) R :=
  fun (R : Type) {inst_f3 : CommRing R} {α n : Type} {m : α → Type} {inst_f4 : Fintype α} {inst_f5 : LinearOrder α} {inst_f6 : (a : α) → Fintype (m a)} {inst_f7 : (a : α) → DecidableEq (m a)} {inst_f8 : Fintype n} {inst_f9 : DecidableEq n} (e : (a : α) × m a ≃ n) (a : α) ↦ { toFun := fun (p : ↥(GlobalTheory.SmGL.parab R (m := m) e)) ↦ p.val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x).val.submatrix (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h8 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h9 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i), map_one' := GlobalTheory.SmGL.diagBlock_obl_1 R (m := m) e a, map_mul' := GlobalTheory.SmGL.diagBlock_obl_2 R (m := m) e a }
noncomputable def GlobalTheory.SmGL.leviProj :
    (R : Type) → [inst_h0 : CommRing R] → {α n : Type} → {m : α → Type} → [inst_h2 : Fintype α] → [inst_h3 : LinearOrder α] → [inst_h4 : (a : α) → Fintype (m a)] → [inst_h5 : (a : α) → DecidableEq (m a)] → [inst_h6 : Fintype n] → [inst_h7 : DecidableEq n] → (e : (a : α) × m a ≃ n) → ↥(GlobalTheory.SmGL.parab R (m := m) e) →* GlobalTheory.SmGL.Levi R m :=
  fun (R : Type) {inst_f10 : CommRing R} {α n : Type} {m : α → Type} {inst_f11 : Fintype α} {inst_f12 : LinearOrder α} {inst_f13 : (a : α) → Fintype (m a)} {inst_f14 : (a : α) → DecidableEq (m a)} {inst_f15 : Fintype n} {inst_f16 : DecidableEq n} (e : (a : α) × m a ≃ n) ↦ MonoidHom.pi (f := fun (a : α) ↦ GL (m a) R) fun (a : α) ↦ MonoidHom.toHomUnits (GlobalTheory.SmGL.diagBlock R (m := m) e a)
noncomputable def GlobalTheory.SmGL.unipRad :
    (R : Type) → [inst_h0 : CommRing R] → {α n : Type} → {m : α → Type} → [inst_h2 : Fintype α] → [inst_h3 : LinearOrder α] → [inst_h4 : (a : α) → Fintype (m a)] → [inst_h5 : (a : α) → DecidableEq (m a)] → [inst_h6 : Fintype n] → [inst_h7 : DecidableEq n] → (a : α) × m a ≃ n → Subgroup (GL n R) :=
  fun (R : Type) {inst_f17 : CommRing R} {α n : Type} {m : α → Type} {inst_f18 : Fintype α} {inst_f19 : LinearOrder α} {inst_f20 : (a : α) → Fintype (m a)} {inst_f21 : (a : α) → DecidableEq (m a)} {inst_f22 : Fintype n} {inst_f23 : DecidableEq n} (e : (a : α) × m a ≃ n) ↦ Subgroup.map (G := ↥(GlobalTheory.SmGL.parab R (m := m) e)) (Subgroup.subtype (GlobalTheory.SmGL.parab R (m := m) e)) (MonoidHom.ker (GlobalTheory.SmGL.leviProj R (m := m) e))
noncomputable def GlobalTheory.SmGL.points :
    (n : Type) → (_ : n) × Unit ≃ n :=
  fun (n : Type) ↦ Equiv.sigmaUnique n fun (x_h0 : n) ↦ Unit
noncomputable def GlobalTheory.SmGL.unipB :
    (R : Type) → [inst_h0 : CommRing R] → (n : Type) → [inst_h1 : Fintype n] → [inst_h2 : DecidableEq n] → [inst_h3 : LinearOrder n] → Subgroup (GL n R) :=
  fun (R : Type) {inst_f24 : CommRing R} (n : Type) {inst_f25 : Fintype n} {inst_f26 : DecidableEq n} {inst_f27 : LinearOrder n} ↦ GlobalTheory.SmGL.unipRad R (m := fun (a : n) ↦ Unit) (GlobalTheory.SmGL.points n)
noncomputable def GlobalTheory.Whittaker.superDiag :
    {R : Type} → [inst_h0 : CommRing R] → {n : ℕ} → GL (Fin n) R → R :=
  fun {R : Type} {inst_f28 : CommRing R} {n : ℕ} (g : GL (Fin n) R) ↦ ∑ i : Fin n, ∑ j : Fin n with j.val = i.val + OfNat.ofNat (nat_lit 1), g.val i j
noncomputable def DiscreteGroups.sglob.LConv.IsWhitTest :
    {k : Type} → [inst_h0 : Field k] → [inst_h1 : TopologicalSpace k] → {m : ℕ} → AddChar k Circle → (GL (Fin m) k → ℂ) → Prop :=
  fun {k : Type} {inst_f29 : Field k} {inst_f30 : TopologicalSpace k} {m : ℕ} (ψ : AddChar k Circle) (f : GL (Fin m) k → ℂ) ↦ (∀ (u : GL (Fin m) k), Membership.mem (γ := Subgroup (GL (Fin m) k)) (GlobalTheory.SmGL.unipB k (Fin m)) u → ∀ (g : GL (Fin m) k), f (u * g) = Subtype.val (p := fun (x : ℂ) ↦ Membership.mem (γ := Submonoid ℂ) (Submonoid.unitSphere ℂ) x) (DFunLike.coe (β := fun (x_h4 : k) ↦ Circle) ψ (GlobalTheory.Whittaker.superDiag u)) * f g) ∧ IsLocallyConstant f ∧ ∃ (C : Set (GL (Fin m) k)), IsCompact C ∧ ∀ (g : GL (Fin m) k), f g ≠ OfNat.ofNat (nat_lit 0) → ∃ (u : GL (Fin m) k), Membership.mem (γ := Subgroup (GL (Fin m) k)) (GlobalTheory.SmGL.unipB k (Fin m)) u ∧ ∃ c ∈ C, g = u * c
end UpperTheory.Reformulated.B.P6.BlockTriangularLevi


