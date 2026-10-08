-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicEndgame_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicEndgame_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:19:33.959527+00:00
-- url     : https://prove2.me/theorems/c232957d-7855-4b82-9d43-cc53a07a542f
-- title:
--   FLT.Assumptions.MazurProof.N13TwoAdicEndgame source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13TwoAdicEndgame

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TwoAdicEndgame
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SymmetricSquareTwo_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N18RouteC_Separated_p0

set_option autoImplicit false




/-!
# The N13 two-adic endgame without Mordell--Weil finite generation

A trivial fake two-descent says that multiplication by two on `J(ℚ)` is
surjective.  For the actual finite image quotient of reduction, doubling is
then bijective.  Compatible halves of a kernel element stay in the kernel, so
a separated two-adic filtration already forces reduction to be injective.

The older exponent-nineteen route is retained below as a stronger optional
conclusion.  All arithmetic inputs remain explicit hypotheses: fake-descent
soundness, the reduction map, and the formal filtration.
-/

namespace MazurProof.N13TwoAdicEndgame

noncomputable section

open N18RouteC.Separated

/-- Minimal two-adic formal-kernel package.  Doubling raises a separated
filtration, while multiplication by an odd integer preserves the valuation
of the formal parameter. -/
structure FormalKernelData (K : Type*) [AddCommGroup K] where
  filtration : StrictNSmulFiltration K 2
  val : K → ℕ∞
  val_eq_top : ∀ z : K, val z = ⊤ ↔ z = 0
  val_odd_smul :
    ∀ m : ℤ, ¬(2 ∣ m) → ∀ z : K, val (m • z) = val z

namespace FormalKernelData

variable {K : Type*} [AddCommGroup K]

theorem val_zero (D : FormalKernelData K) : D.val 0 = ⊤ :=
  (D.val_eq_top 0).mpr rfl

/-- Odd multiplication has no nonzero kernel in the two-adic formal
kernel. -/
theorem no_odd_torsion
    (D : FormalKernelData K)
    (m : ℤ) (hm : ¬(2 ∣ m))
    (z : K) (hz : m • z = 0) :
    z = 0 := by
  by_contra hne
  have hval :=
    N13TwoAdicEndgame.FormalKernelData.val_odd_smul D m hm z
  rw [hz, D.val_zero] at hval
  exact hne ((D.val_eq_top z).mp hval.symm)

/-- In particular, multiplication by nineteen is injective. -/
theorem nineteen_injective (D : FormalKernelData K) :
    Function.Injective (fun z : K => 19 • z) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply FormalKernelData.no_odd_torsion D 19 (by norm_num)
  have hnat : 19 • (x - y) = 0 := by
    rw [nsmul_sub]
    exact sub_eq_zero.mpr hxy
  calc
    (19 : ℤ) • (x - y) = (19 : ℕ) • (x - y) :=
      natCast_zsmul (x - y) 19
    _ = 0 := hnat

end FormalKernelData

/-- The exact group-theoretic output of a trivial fake two-descent. -/
def TwoSurjective (G : Type*) [AddCommGroup G] : Prop :=
  ∀ P : G, ∃ Q : G, P = 2 • Q

/-- Surjectivity of multiplication by two is weak descent with zero error. -/
theorem weakDescentWitness_of_twoSurjective
    {G : Type*} [AddCommGroup G]
    (htwo : TwoSurjective G) :
    WeakDescentWitness G 2 1 := by
  intro P
  obtain ⟨Q, hQ⟩ := htwo P
  exact ⟨0, Q, by simp, by simpa using hQ⟩

/-- Surjectivity of doubling iterates to every power of two. -/
theorem twoPow_surjective
    {G : Type*} [AddCommGroup G]
    (htwo : TwoSurjective G) :
    ∀ k : ℕ, Function.Surjective (fun P : G => (2 ^ k) • P) := by
  intro k
  induction k with
  | zero =>
      intro P
      exact ⟨P, by simp⟩
  | succ k ih =>
      intro P
      obtain ⟨R, hR⟩ := ih P
      obtain ⟨Q, hQ⟩ := htwo R
      refine ⟨Q, ?_⟩
      calc
        (2 ^ (k + 1)) • Q = 2 • ((2 ^ k) • Q) := by
          rw [pow_succ, mul_nsmul]
        _ = (2 ^ k) • (2 • Q) :=
          N18RouteC.Separated.nsmul_nsmul_comm 2 (2 ^ k) Q
        _ = (2 ^ k) • R := by rw [← hQ]
        _ = P := hR

/-- If doubling is injective, so is multiplication by every power of two. -/
theorem twoPow_injective_of_two_injective
    {G : Type*} [AddCommGroup G]
    (htwo : Function.Injective (fun P : G => 2 • P)) :
    ∀ k : ℕ, Function.Injective (fun P : G => (2 ^ k) • P) := by
  intro k
  induction k with
  | zero =>
      intro P Q hPQ
      simpa using hPQ
  | succ k ih =>
      intro P Q hPQ
      apply ih
      apply htwo
      simpa [pow_succ, mul_nsmul] using hPQ

/-- A finite quotient target makes the old exponent-nineteen detour
unnecessary.  If reduction is surjective, two-divisibility of the source
makes doubling bijective on the finite target.  Compatible halves of every
kernel element therefore remain in the kernel, so separatedness alone makes
reduction injective. -/
theorem reduction_injective_of_finite_target
    {G J₂ : Type*}
    [AddCommGroup G] [AddCommGroup J₂] [Finite J₂]
    (red : G →+ J₂)
    (red_surjective : Function.Surjective red)
    (twoSurjective : TwoSurjective G)
    (separated : NSeparated red.ker 2) :
    Function.Injective red := by
  have twoSurjectiveTarget :
      Function.Surjective (fun z : J₂ => 2 • z) := by
    intro z
    obtain ⟨P, rfl⟩ := red_surjective z
    obtain ⟨Q, hQ⟩ := twoSurjective P
    refine ⟨red Q, ?_⟩
    simpa only [map_nsmul] using congrArg red hQ.symm
  have twoInjectiveTarget :
      Function.Injective (fun z : J₂ => 2 • z) :=
    Finite.injective_iff_surjective.mpr twoSurjectiveTarget
  have twoPowInjectiveTarget :=
    twoPow_injective_of_two_injective twoInjectiveTarget
  intro P Q hPQ
  let z : red.ker :=
    ⟨P - Q, by
      change red (P - Q) = 0
      rw [map_sub, hPQ, sub_self]⟩
  have zInfinitelyDivisible : InfinitelyNSmulDivisible 2 z := by
    intro k
    obtain ⟨R, hR⟩ := twoPow_surjective twoSurjective k (P - Q)
    change (2 ^ k) • R = P - Q at hR
    have hredR : red R = 0 := by
      apply twoPowInjectiveTarget k
      calc
        (2 ^ k) • red R = red ((2 ^ k) • R) := by
          rw [map_nsmul]
        _ = red (P - Q) := by rw [hR]
        _ = 0 := z.2
        _ = (2 ^ k) • (0 : J₂) := by simp
    let r : red.ker := ⟨R, hredR⟩
    refine ⟨r, ?_⟩
    apply Subtype.ext
    exact hR
  have hz : z = 0 :=
    separated z zInfinitelyDivisible
  exact sub_eq_zero.mp (congrArg Subtype.val hz)

/-- The structural N13 exponent argument. -/
theorem exponent_nineteen
    {G J₂ : Type*}
    [AddCommGroup G] [AddCommGroup J₂] [Finite J₂]
    (abelFibres : N13SymmetricSquareTwo.AbelFiberData J₂)
    (red : G →+ J₂)
    (twoSurjective : TwoSurjective G)
    (separated : NSeparated red.ker 2) :
    ∀ P : G, 19 • P = 0 := by
  have weak : WeakDescentWitness G 2 1 :=
    weakDescentWitness_of_twoSurjective twoSurjective
  have killRed : ∀ Q : J₂, 19 • Q = 0 :=
    N13SymmetricSquareTwo.jacobian_exponent_nineteen abelFibres
  have h := annihilated_of_weakDescent_and_separated
    (AddMonoidHom.id G) Function.injective_id red
    2 1 19 weak killRed separated
  intro P
  simpa [show Nat.lcm 1 19 = 19 by decide] using h P

/-- Once the rational group has exponent nineteen, injectivity of `[19]` on
the formal kernel makes reduction injective. -/
theorem reduction_injective_of_exponent_nineteen
    {G J₂ : Type*}
    [AddCommGroup G] [AddCommGroup J₂]
    (red : G →+ J₂)
    (hexponent : ∀ P : G, 19 • P = 0)
    (formalKernel_nineteen_injective :
      Function.Injective (fun z : red.ker => 19 • z)) :
    Function.Injective red := by
  intro P Q hPQ
  let z : red.ker :=
    ⟨P - Q, by
      change red (P - Q) = 0
      rw [map_sub, hPQ, sub_self]⟩
  have hz19 : 19 • z = 0 := by
    apply Subtype.ext
    change 19 • (P - Q) = 0
    exact hexponent (P - Q)
  have hz0 : z = 0 := by
    apply formalKernel_nineteen_injective
    simpa using hz19
  have hpq0 : P - Q = 0 := by
    simpa [z] using congrArg Subtype.val hz0
  exact sub_eq_zero.mp hpq0

/-- All fixed-instance inputs for the two-adic endgame. -/
structure Data (G J₂ : Type*)
    [AddCommGroup G] [AddCommGroup J₂] [Finite J₂] where
  abelFibres : N13SymmetricSquareTwo.AbelFiberData J₂
  red : G →+ J₂
  twoSurjective : TwoSurjective G
  formalKernel : FormalKernelData red.ker

theorem Data.exponent_nineteen
    {G J₂ : Type*}
    [AddCommGroup G] [AddCommGroup J₂] [Finite J₂]
    (D : Data G J₂) :
    ∀ P : G, 19 • P = 0 :=
  N13TwoAdicEndgame.exponent_nineteen
    D.abelFibres D.red D.twoSurjective D.formalKernel.filtration.separated

theorem Data.reduction_injective
    {G J₂ : Type*}
    [AddCommGroup G] [AddCommGroup J₂] [Finite J₂]
    (D : Data G J₂) :
    Function.Injective D.red :=
  reduction_injective_of_exponent_nineteen D.red
    D.exponent_nineteen
      (FormalKernelData.nineteen_injective D.formalKernel)

end

end MazurProof.N13TwoAdicEndgame


