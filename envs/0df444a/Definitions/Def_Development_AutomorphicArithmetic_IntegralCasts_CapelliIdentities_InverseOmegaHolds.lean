-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InverseOmegaHolds
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InverseOmegaHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:14.766848+00:00
-- url     : https://prove2.me/theorems/66da9955-9c5b-459b-8066-a28728ec5c0d
-- title:
--   Inverse Omega Holds
-- statement:
--   Definitions and structural lemmas for Inverse Omega Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InverseOmegaHolds.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Gwa1.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)
noncomputable def UpperTheory.Reformulated.B.Gwa1.IsWq :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → WeierstrassCurve ℂ_[p] → PowerSeries ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) ↦
      have c : ℂ_[p] →+* PowerSeries ℂ_[p] := Algebra.algebraMap ℂ_[p] (PowerSeries ℂ_[p]);
      have X : PowerSeries ℂ_[p] := PowerSeries.X;
      wq =
        (1 : PowerSeries ℂ_[p]) + (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₁ * X * wq +
                (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₂ * X ^ (2 : ℕ) * wq +
              (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₃ * X ^ (3 : ℕ) * wq ^ (2 : ℕ) +
            (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₄ * X ^ (4 : ℕ) * wq ^ (2 : ℕ) +
          (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₆ * X ^ (6 : ℕ) * wq ^ (3 : ℕ)
noncomputable def UpperTheory.Reformulated.B.Gwa1.dX.{u_1} :
    {A : Type u_1} → [CommRing A] → PowerSeries A → PowerSeries A :=
    fun {A : Type u_1} [CommRing A] (f : PowerSeries A) ↦
      PowerSeries.mk fun (n : ℕ) ↦ ((↑n : A) + (1 : A)) * (PowerSeries.coeff (n + (1 : ℕ)) : PowerSeries A → A) f
noncomputable def UpperTheory.Reformulated.B.Gwa1.omegaW :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → WeierstrassCurve ℂ_[p] → PowerSeries ℂ_[p] → PowerSeries ℂ_[p] :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) ↦
      have c : ℂ_[p] →+* PowerSeries ℂ_[p] := Algebra.algebraMap ℂ_[p] (PowerSeries ℂ_[p]);
      have X : PowerSeries ℂ_[p] := PowerSeries.X;
      ((-2 : PowerSeries ℂ_[p]) * wq - X * UpperTheory.Reformulated.B.Gwa1.dX wq) *
        (wq *
            ((c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₁ * X + (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₃ * X ^ (3 : ℕ) * wq -
              (2 : PowerSeries ℂ_[p])))⁻¹
noncomputable def UpperTheory.Reformulated.B.Gwa1.flog :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → WeierstrassCurve ℂ_[p] → PowerSeries ℂ_[p] → PowerSeries ℂ_[p] :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) ↦
      PowerSeries.mk fun (n : ℕ) ↦
        if n = (0 : ℕ) then (0 : ℂ_[p])
        else (PowerSeries.coeff (n - (1 : ℕ)) : PowerSeries ℂ_[p] → ℂ_[p]) (UpperTheory.Reformulated.B.Gwa1.omegaW W wq) / (↑n : ℂ_[p])
noncomputable def UpperTheory.Reformulated.B.Gwa1.InvOmega :
    Prop :=
    ∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]),
      UpperTheory.Reformulated.B.Gwa1.IsIntP W.a₁ →
        UpperTheory.Reformulated.B.Gwa1.IsIntP W.a₂ →
          UpperTheory.Reformulated.B.Gwa1.IsIntP W.a₃ →
            UpperTheory.Reformulated.B.Gwa1.IsIntP W.a₄ →
              UpperTheory.Reformulated.B.Gwa1.IsIntP W.a₆ →
                UpperTheory.Reformulated.B.Gwa1.IsWq W wq →
                  ∃ (v : PowerSeries ℂ_[p]),
                    (∀ (n : ℕ), UpperTheory.Reformulated.B.Gwa1.IsIntP ((PowerSeries.coeff n : PowerSeries ℂ_[p] → ℂ_[p]) v)) ∧
                      v * UpperTheory.Reformulated.B.Gwa1.dX (UpperTheory.Reformulated.B.Gwa1.flog W wq) = (1 : PowerSeries ℂ_[p])
namespace UpperTheory.Reformulated.B.Gwa1
open PowerSeries
def lowIn {R : Type*} [CommRing R] (O : Subring R) (n : ℕ) : Subring R⟦X⟧ where
  carrier := {f | ∀ k < n, coeff k f ∈ O}
  mul_mem' := by
    intro f g hf hg k hk
    rw [coeff_mul]
    refine O.sum_mem fun x hx => ?_
    have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    exact O.mul_mem (hf _ (by omega)) (hg _ (by omega))
  one_mem' := by
    intro k _
    rw [coeff_one]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  add_mem' := by
    intro f g hf hg k hk
    rw [map_add]
    exact O.add_mem (hf k hk) (hg k hk)
  zero_mem' := by
    intro k _
    rw [map_zero]
    exact O.zero_mem
  neg_mem' := by
    intro f hf k hk
    rw [map_neg]
    exact O.neg_mem (hf k hk)
noncomputable def ball (p : ℕ) [Fact (Nat.Prime p)] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro x y hx hy
    change ‖x * y‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy
  one_mem' := by
    change ‖(1 : ℂ_[p])‖ ≤ 1
    rw [norm_one]
  add_mem' := by
    intro x y hx hy
    exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  zero_mem' := by
    change ‖(0 : ℂ_[p])‖ ≤ 1
    rw [norm_zero]
    exact zero_le_one
  neg_mem' := by
    intro x hx
    change ‖-x‖ ≤ 1
    rw [norm_neg]
    exact hx
end UpperTheory.Reformulated.B.Gwa1


