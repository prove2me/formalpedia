-- Prove2me | Definitions.Def_N25_GlobalKummerRamification
-- name    : N25_GlobalKummerRamification
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:25:55.270195+00:00
-- url     : https://prove2.me/theorems/3aabd812-91f4-4d87-8315-084cf2347f8c
-- title:
--   Ramification set and cocycle extension representations
-- statement:
--   Fixes the finite ramification set $S={5,71}$ and, for characters $χ_1,χ_2$ and a one-cocycle $c$ with twist $χ_1χ_2^{-1}$, defines the upper-triangular action $(x,y)↦(χ_1(σ)x+c(σ)χ_2(σ)y,χ_2(σ)y)$. These data package the extension representations whose ramification and finite-flatness enter the descent.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GlobalKummer
import Definitions.Def_GroupCohomology_ContinuousUnramified
set_option autoImplicit false
noncomputable section
namespace N25.GlobalKummer

/-- The two finite primes allowed by the level-25 descent. -/
def ramificationSet : Finset Nat.Primes := {⟨5, by decide⟩, ⟨71, by decide⟩}

/-- The upper triangular representation associated with a one-cocycle. -/
def cocycleExtensionRep {k G : Type} [CommRing k] [Group G]
    (A : Rep k G) (c : groupCohomology.cocycles₁ A) : Rep k G :=
  Rep.of
    { toFun := fun σ =>
        { toFun := fun x : A × k => (A.ρ σ x.1 + x.2 • c σ, x.2)
          map_add' := by
            intro x y
            apply Prod.ext
            · change A.ρ σ (x.1 + y.1) + (x.2 + y.2) • c σ =
                (A.ρ σ x.1 + x.2 • c σ) + (A.ρ σ y.1 + y.2 • c σ)
              rw [map_add, add_smul]
              abel
            · rfl
          map_smul' := by
            intro a x
            apply Prod.ext
            · change A.ρ σ (a • x.1) + (a * x.2) • c σ =
                a • (A.ρ σ x.1 + x.2 • c σ)
              rw [map_smul, smul_add, mul_smul]
            · rfl }
      map_one' := by
        apply LinearMap.ext
        intro x
        apply Prod.ext
        · change A.ρ 1 x.1 + x.2 • c 1 = x.1
          simp
        · rfl
      map_mul' := by
        intro σ τ
        apply LinearMap.ext
        intro x
        apply Prod.ext
        · change A.ρ (σ * τ) x.1 + x.2 • c (σ * τ) =
            A.ρ σ (A.ρ τ x.1 + x.2 • c τ) + x.2 • c σ
          have hc : c (σ * τ) = A.ρ σ (c τ) + c σ :=
            (groupCohomology.mem_cocycles₁_iff _).mp c.property σ τ
          rw [hc]
          simp [map_mul, Module.End.mul_apply, smul_add, add_assoc]
        · rfl }

end N25.GlobalKummer


