-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_MemAugIdeal
-- name    : ReciprocityTheory_DualLattices_MemAugIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:03.965137+00:00
-- url     : https://prove2.me/theorems/d81a51be-2eac-4bfa-92cb-a70b8d2a3321
-- title:
--   Mem Aug Ideal
-- statement:
--   Definitions and structural lemmas for Mem Aug Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemAugIdeal.lean

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up.PullbackHopfOrder
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
theorem smulTop_le (q : ℕ) {a b : ℕ} (G : Matrix (Fin a) (Fin b) R) :
    (Ideal.span {(q : R)} • (⊤ : Submodule R (Fin b → R))) ≤
      (Ideal.span {(q : R)} • (⊤ : Submodule R (Fin a → R))).comap G.mulVecLin := by
  refine Submodule.smul_le.2 fun r hr n _ => ?_
  rw [Submodule.mem_comap, map_smul]
  exact Submodule.smul_mem_smul hr Submodule.mem_top
def mq (q : ℕ) {a b : ℕ} (G : Matrix (Fin a) (Fin b) R) :
    LieDualModP q R b →ₗ[R] LieDualModP q R a :=
  Submodule.mapQ _ _ G.mulVecLin (smulTop_le q G)
def qPi (q d : ℕ) : LieDualModP q R d ≃ₗ[R] ((i : Fin d) → R ⧸ Ideal.span {(q : R)}) := by
  let πd : (Fin d → R) →ₗ[R] ((i : Fin d) → R ⧸ Ideal.span {(q : R)}) :=
    LinearMap.pi fun i => (Ideal.span {(q : R)}).mkQ ∘ₗ LinearMap.proj i
  have hπ : ∀ x i, πd x i = Submodule.Quotient.mk (x i) := fun _ _ => rfl
  have hsurj : Function.Surjective πd := by
    intro y
    choose x hx using fun i => Submodule.Quotient.mk_surjective _ (y i)
    exact ⟨x, funext fun i => by rw [hπ, hx]⟩
  have hker : Ideal.span {(q : R)} • (⊤ : Submodule R (Fin d → R)) = LinearMap.ker πd := by
    ext x
    rw [LinearMap.mem_ker]
    constructor
    · intro hx
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro r hr n _
        funext i
        rw [hπ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero, Pi.smul_apply, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
      · intro x y hx hy
        rw [map_add, hx, hy, add_zero]
    · intro hx
      have : ∀ i, ∃ s, s * (q : R) = x i := fun i => by
        have := congrFun hx i
        rw [hπ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this
        exact Ideal.mem_span_singleton'.1 this
      choose s hs using this
      have hx' : x = (q : R) • s := funext fun i => by
        rw [Pi.smul_apply, smul_eq_mul, mul_comm, hs]
      rw [hx']
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  exact (Submodule.quotEquivOfEq _ _ hker).trans (πd.quotKerEquivOfSurjective hsurj)
variable {X N : Type} [AddCommGroup X] [AddCommGroup N]
end ReciprocityTheory.PGsh.Up.PullbackHopfOrder


