-- Prove2me | Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Positive
-- name    : LeanPool_OrderClosures_BanLat_Operators_Positive
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:12:53.727949+00:00
-- url     : https://prove2.me/theorems/1251c7d9-801c-433f-8966-42b88fa70a89
-- title:
--   Positive
-- statement:
--   Definitions and structural lemmas for Positive, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Positive.lean

module
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Theorems.Thm_IsVLArchimedean_eq_zero_of_nonneg_of_forall_nsmul_le
public import Theorems.Thm_P2M_abs_smul__56c684b926d9
public import Theorems.Thm_abs_eq_zero_iff_zero
public import Theorems.Thm_nonneg_smul_sup
public import Theorems.Thm_posPart_smul_nonneg

set_option autoImplicit true
@[expose] public section
@[expose] public section
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]
def Positive (f : X →ₗ[ℝ] Y) : Prop :=
  ∀ x : X, 0 ≤ x → 0 ≤ f x
namespace Positive
instance : LE (X →ₗ[ℝ] Y) where
  le T S := Positive (S - T)
theorem le_iff {T S : X →ₗ[ℝ] Y} : T ≤ S ↔ ∀ x, 0 ≤ x → T x ≤ S x := by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · have hxs := h x hx; rwa [LinearMap.sub_apply, sub_nonneg] at hxs
  · rw [LinearMap.sub_apply, sub_nonneg]; exact h x hx
@[simp] theorem zero_le_iff {T : X →ₗ[ℝ] Y} : 0 ≤ T ↔ Positive T := by
  change Positive (T - 0) ↔ _; rw [sub_zero]
instance : PartialOrder (X →ₗ[ℝ] Y) where
  le_refl T := by
    change Positive (T - T); rw [sub_self]; intro _ _; exact le_refl 0
  le_trans T S R hTS hSR := by
    intro x hx
    have heq : (R - T) x = (R - S) x + (S - T) x := by
      simp [LinearMap.sub_apply]
    rw [heq]
    exact add_nonneg (hSR x hx) (hTS x hx)
  le_antisymm T S hTS hST := by
    ext x
    have hp : T x⁺ = S x⁺ :=
      le_antisymm ((le_iff.mp hTS) _ (posPart_nonneg x))
        ((le_iff.mp hST) _ (posPart_nonneg x))
    have hn : T x⁻ = S x⁻ :=
      le_antisymm ((le_iff.mp hTS) _ (negPart_nonneg x))
        ((le_iff.mp hST) _ (negPart_nonneg x))
    rw [show x = x⁺ - x⁻ from (posPart_sub_negPart x).symm,
      map_sub, map_sub, hp, hn]
section ExtensionLemma
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]
  [IsVLArchimedean Y] {τ : X → Y}
omit [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [VectorLattice X] [VectorLattice Y] [IsVLArchimedean Y] in
lemma tau_zero
    (hτ_add : ∀ x y, 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y) :
    τ 0 = 0 := by
  have h := hτ_add 0 0 le_rfl le_rfl
  rw [add_zero] at h
  exact (add_left_cancel (show τ 0 + 0 = τ 0 + τ 0 from by
    rw [add_zero]; exact h)).symm
omit [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice X]
  [VectorLattice Y] [IsVLArchimedean Y] in
lemma tau_nsmul
    (hτ_add : ∀ x y, 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y)
    (n : ℕ) {x : X} (hx : 0 ≤ x) :
    τ (n • x) = n • τ x := by
  induction n with
  | zero => simp [tau_zero hτ_add]
  | succ n ih =>
    rw [succ_nsmul, hτ_add _ _ (nsmul_nonneg hx n) hx, ih, succ_nsmul]
omit [VectorLattice X] [VectorLattice Y] [IsVLArchimedean Y] in
lemma tau_mono
    (hτ_nn : ∀ x, 0 ≤ x → 0 ≤ τ x)
    (hτ_add : ∀ x y, 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y)
    {a b : X} (ha : 0 ≤ a) (hab : a ≤ b) :
    τ a ≤ τ b := by
  have hd : 0 ≤ b - a := sub_nonneg.mpr hab
  have : τ b = τ a + τ (b - a) := by
    rw [← hτ_add a (b - a) ha hd]; congr 1; abel
  rw [this]
  exact le_add_of_nonneg_right (hτ_nn _ hd)
lemma tau_real_smul
    (hτ_nn : ∀ x, 0 ≤ x → 0 ≤ τ x)
    (hτ_add : ∀ x y, 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y)
    {r : ℝ} (hr : 0 ≤ r) {x : X} (hx : 0 ≤ x) :
    τ (r • x) = r • τ x := by
  set d := τ (r • x) - r • τ x with hd_def
  suffices hd : d = 0 from sub_eq_zero.mp hd
  rw [← abs_eq_zero_iff_zero]
  apply IsVLArchimedean.eq_zero_of_nonneg_of_forall_nsmul_le
    (y := τ x) (abs_nonneg d)
  intro m
  set k := Nat.floor ((m : ℝ) * r)
  have hmr : 0 ≤ (m : ℝ) * r := mul_nonneg (Nat.cast_nonneg m) hr
  have hk_le : (k : ℝ) ≤ (m : ℝ) * r := Nat.floor_le hmr
  have hmr_lt : (m : ℝ) * r < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmrx : m • (r • x) = ((m : ℝ) * r) • x := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  -- m • τ(r•x) and m • (r • τ x) both lie in [k • τ x, (k+1) • τ x]
  have hlo : k • τ x ≤ m • τ (r • x) := by
    rw [← tau_nsmul hτ_add m (smul_nonneg hr hx),
        ← tau_nsmul hτ_add k hx]
    exact tau_mono hτ_nn hτ_add (nsmul_nonneg hx k)
      <| by
      rw [hmrx, ← Nat.cast_smul_eq_nsmul ℝ k x]
      exact smul_le_smul_of_nonneg_right hk_le hx
  have hhi : m • τ (r • x) ≤ (k + 1) • τ x := by
    rw [← tau_nsmul hτ_add m (smul_nonneg hr hx),
        ← tau_nsmul hτ_add (k + 1) hx]
    exact tau_mono hτ_nn hτ_add
      (nsmul_nonneg (smul_nonneg hr hx) m)
      <| by
      rw [hmrx, ← Nat.cast_smul_eq_nsmul ℝ (k + 1) x]
      exact smul_le_smul_of_nonneg_right (by push_cast; exact hmr_lt.le) hx
  have hlo' : k • τ x ≤ m • (r • τ x) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    exact smul_le_smul_of_nonneg_right hk_le (hτ_nn _ hx)
  have hhi' : m • (r • τ x) ≤ (k + 1) • τ x := by
    rw [← Nat.cast_smul_eq_nsmul ℝ m (r • τ x),
      ← Nat.cast_smul_eq_nsmul ℝ (k + 1) (τ x), smul_smul]
    exact smul_le_smul_of_nonneg_right (by push_cast; exact hmr_lt.le)
      (hτ_nn _ hx)
  -- Both values lie in an interval of width τ x, so |m•d| ≤ τ x
  have h1 : m • τ (r • x) - m • (r • τ x) ≤ τ x :=
    calc m • τ (r • x) - m • (r • τ x)
        ≤ (k + 1) • τ x - k • τ x := sub_le_sub hhi hlo'
      _ = τ x := by rw [add_nsmul, one_nsmul, add_sub_cancel_left]
  have h2 : m • (r • τ x) - m • τ (r • x) ≤ τ x :=
    calc m • (r • τ x) - m • τ (r • x)
        ≤ (k + 1) • τ x - k • τ x := sub_le_sub hhi' hlo
      _ = τ x := by rw [add_nsmul, one_nsmul, add_sub_cancel_left]
  -- Convert to m • |d| ≤ τ x
  have habs : |m • τ (r • x) - m • (r • τ x)| ≤ τ x :=
    sup_le h1 (show -(m • τ (r • x) - m • (r • τ x)) ≤ τ x by rwa [neg_sub])
  have hmd : m • τ (r • x) - m • (r • τ x) = m • d := by
    rw [← smul_sub]
  rw [hmd] at habs
  rw [← Nat.cast_smul_eq_nsmul ℝ m d] at habs
  rw [abs_smul' d (↑m : ℝ), abs_of_nonneg (Nat.cast_nonneg m)] at habs
  rwa [Nat.cast_smul_eq_nsmul ℝ m |d|] at habs
lemma posPart_smul_nonneg {r : ℝ} (hr : 0 ≤ r) (x : X) :
    (r • x)⁺ = r • x⁺ := by
  change (r • x) ⊔ 0 = r • (x ⊔ 0)
  rw [← smul_zero r, ← nonneg_smul_sup x 0 r hr, smul_zero]
lemma negPart_smul_nonneg {r : ℝ} (hr : 0 ≤ r) (x : X) :
    (r • x)⁻ = r • x⁻ := by
  change (-(r • x)) ⊔ 0 = r • ((-x) ⊔ 0)
  rw [← smul_neg, ← smul_zero r, ← nonneg_smul_sup (-x) 0 r hr, smul_zero]
omit [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]
  [IsVLArchimedean Y] in
lemma extFun_add
    (hτ_add : ∀ x y, 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y)
    (x y : X) :
    τ (x + y)⁺ - τ (x + y)⁻ = (τ x⁺ - τ x⁻) + (τ y⁺ - τ y⁻) := by
  have hid : (x + y)⁺ + x⁻ + y⁻ = (x + y)⁻ + x⁺ + y⁺ := by
    have l1 : (x + y)⁺ = x + y + (x + y)⁻ :=
      eq_add_of_sub_eq (posPart_sub_negPart _)
    have l2 : x⁺ = x + x⁻ := eq_add_of_sub_eq (posPart_sub_negPart x)
    have l3 : y⁺ = y + y⁻ := eq_add_of_sub_eq (posPart_sub_negPart y)
    rw [l1, l2, l3]; abel
  have hlhs : τ ((x + y)⁺ + x⁻ + y⁻) =
      τ (x + y)⁺ + τ x⁻ + τ y⁻ := by
    rw [hτ_add _ _ (add_nonneg (posPart_nonneg _) (negPart_nonneg _))
        (negPart_nonneg _),
      hτ_add _ _ (posPart_nonneg _) (negPart_nonneg _)]
  have hrhs : τ ((x + y)⁻ + x⁺ + y⁺) =
      τ (x + y)⁻ + τ x⁺ + τ y⁺ := by
    rw [hτ_add _ _ (add_nonneg (negPart_nonneg _) (posPart_nonneg _))
        (posPart_nonneg _),
      hτ_add _ _ (negPart_nonneg _) (posPart_nonneg _)]
  have key := hlhs.symm.trans ((congrArg τ hid).trans hrhs)
  calc τ (x + y)⁺ - τ (x + y)⁻
      = τ (x + y)⁺ + τ x⁻ + τ y⁻ - τ x⁻ - τ y⁻ - τ (x + y)⁻ := by
        abel
    _ = τ (x + y)⁻ + τ x⁺ + τ y⁺ - τ x⁻ - τ y⁻ - τ (x + y)⁻ := by
        rw [key]
    _ = τ x⁺ - τ x⁻ + (τ y⁺ - τ y⁻) := by abel
lemma extFun_smul
    (hτ_nn : ∀ x, 0 ≤ x → 0 ≤ τ x)
    (hτ_add : ∀ x y, 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y)
    (r : ℝ) (x : X) :
    τ (r • x)⁺ - τ (r • x)⁻ = r • (τ x⁺ - τ x⁻) := by
  by_cases hr : 0 ≤ r
  · rw [posPart_smul_nonneg hr, negPart_smul_nonneg hr,
      tau_real_smul hτ_nn hτ_add hr (posPart_nonneg _),
      tau_real_smul hτ_nn hτ_add hr (negPart_nonneg _), smul_sub]
  · push Not at hr
    have hnr : 0 ≤ -r := le_of_lt (neg_pos.mpr hr)
    have hrx : r • x = -((-r) • x) := by rw [neg_smul, neg_neg]
    have hp : (r • x)⁺ = (-r) • x⁻ := by
      rw [hrx, posPart_neg, negPart_smul_nonneg hnr]
    have hn : (r • x)⁻ = (-r) • x⁺ := by
      rw [hrx, negPart_neg, posPart_smul_nonneg hnr]
    rw [hp, hn,
      tau_real_smul hτ_nn hτ_add hnr (negPart_nonneg _),
      tau_real_smul hτ_nn hτ_add hnr (posPart_nonneg _)]
    rw [← smul_sub (-r) (τ x⁻) (τ x⁺),
      show τ x⁻ - τ x⁺ = -(τ x⁺ - τ x⁻) from (neg_sub _ _).symm,
      smul_neg, neg_smul, neg_neg]
variable
  (hτ_nn : ∀ x, 0 ≤ x → 0 ≤ τ x)
  (hτ_add : ∀ x y, 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y)
noncomputable def extension : X →ₗ[ℝ] Y :=
  { toFun := fun x => τ x⁺ - τ x⁻
    map_add' := extFun_add hτ_add
    map_smul' := fun r x => by
      simp only [RingHom.id_apply]
      exact extFun_smul hτ_nn hτ_add r x }
end ExtensionLemma
variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [BanachLattice X] [NormedVectorLattice Y]
end Positive


