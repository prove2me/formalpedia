-- Prove2me | solution 1 for AlgebraicCurve.Pic0.finite_torsion_of_forall_primePow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/3e754433-be9c-5fb8-8016-b6a21c30d309

import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Finite.Prod
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_finite_torsion_of_forall_primePow

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    (h : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), Finite (Pic0.torsion K F (p ^ k))) (n : ℕ) (hn : 0 < n) :
    Finite (Pic0.torsion K F n) := by
  suffices H : ∀ m : ℕ, 0 < m → Finite (Submodule.torsionBy ℤ (Pic0 K F) (m : ℤ)) by
    exact H n hn
  intro m
  induction m using Nat.recOnPosPrimePosCoprime
  ·
    rename_i p k hp hk
    intro _
    haveI : Fact p.Prime := ⟨hp⟩
    exact h p k
  ·
    intro h0
    exact absurd h0 (lt_irrefl 0)
  ·
    intro _
    haveI : Subsingleton (Submodule.torsionBy ℤ (Pic0 K F) ((1 : ℕ) : ℤ)) := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      have hx := x.2
      have hy := y.2
      rw [Submodule.mem_torsionBy_iff] at hx hy
      simp only [Nat.cast_one, one_smul] at hx hy
      rw [hx, hy]
    infer_instance
  ·
    rename_i a b ha hb hab iha ihb
    intro _
    haveI := iha (by omega)
    haveI := ihb (by omega)
    obtain ⟨u, v, huv⟩ : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hab
    have key : ∀ x : Pic0 K F, x = u • ((a : ℤ) • x) + v • ((b : ℤ) • x) := fun x => by
      have hx := congrArg (fun r : ℤ => r • x) huv
      simp only [add_zsmul, mul_smul, one_smul] at hx
      exact hx.symm
    let f : Submodule.torsionBy ℤ (Pic0 K F) ((a * b : ℕ) : ℤ) →
        Submodule.torsionBy ℤ (Pic0 K F) (a : ℤ) × Submodule.torsionBy ℤ (Pic0 K F) (b : ℤ) :=
      fun x =>
        (⟨(b : ℤ) • (x : Pic0 K F), by
            have hx := x.2
            rw [Submodule.mem_torsionBy_iff] at hx ⊢
            rw [smul_smul]
            push_cast at hx
            exact hx⟩,
         ⟨(a : ℤ) • (x : Pic0 K F), by
            have hx := x.2
            rw [Submodule.mem_torsionBy_iff] at hx ⊢
            rw [smul_smul, mul_comm]
            push_cast at hx
            exact hx⟩)
    refine Finite.of_injective f ?_
    intro x y hxy
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    apply Subtype.ext
    calc (x : Pic0 K F) = u • ((a : ℤ) • (x : Pic0 K F)) + v • ((b : ℤ) • (x : Pic0 K F)) := key _
      _ = u • ((a : ℤ) • (y : Pic0 K F)) + v • ((b : ℤ) • (y : Pic0 K F)) := by rw [h2, h1]
      _ = (y : Pic0 K F) := (key _).symm

end S_AlgebraicCurve_Pic0_finite_torsion_of_forall_primePow
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_finite_torsion_of_forall_primePow (solution)
