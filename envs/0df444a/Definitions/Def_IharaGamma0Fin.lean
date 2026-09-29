-- Prove2me | Definitions.Def_IharaGamma0Fin
-- name    : IharaGamma0Fin
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/b1cff061-ef6b-5ee0-8648-8430a9371a8e
-- title:
--   The congruence subgroup Γ0​(N) inside SL2​(Z/M)
-- statement:
--   For natural numbers $N$ and $M$, [`Ihara.Gamma0Fin N M`](../def/IharaGamma0Fin.html#L14) is the subgroup of $\mathrm{SL}_2(\mathbb{Z}/M)$ consisting of those $g$ whose lower-left entry $g_{1,0}$ is divisible by the image of $N$ in $\mathbb{Z}/M$; the membership criterion is recorded as [`Ihara.mem_Gamma0Fin`](../def/IharaGamma0Fin.html#L34), namely $g \in \Gamma_0\mathrm{Fin}(N,M)$ if and only if $(N : \mathbb{Z}/M) \mid g_{1,0}$. That this set is a subgroup is established from the explicit entrywise formulas for the product and for the inverse of a $2\times 2$ matrix of determinant one: the lower-left entry of $ab$ is $a_{1,0}b_{0,0} + a_{1,1}b_{1,0}$, and the lower-left entry of $a^{-1}$ is $-a_{1,0}$. No hypothesis relating $N$ and $M$ enters; for $N$ a unit modulo $M$ the subgroup is everything, and for $N = 0$ or $N = M$ it is the upper-triangular subgroup.
--
--   Under a divisibility hypothesis $N \mid M$, the remaining declarations define the diamond-type character of this subgroup. First, [`Ihara.castHom_apply_one_zero`](../def/IharaGamma0Fin.html#L38) states that for $g$ in the subgroup the reduction of $g_{1,0}$ along $\mathbb{Z}/M \to \mathbb{Z}/N$ is zero. Consequently [`Ihara.gamma0FinMap N M hNM`](../def/IharaGamma0Fin.html#L43) is the monoid homomorphism $\Gamma_0\mathrm{Fin}(N,M) \to \mathbb{Z}/N$ sending $g$ to the reduction of its lower-right entry $g_{1,1}$ modulo $N$; multiplicativity follows from $(ab)_{1,1} = a_{1,0}b_{0,1} + a_{1,1}b_{1,1}$ together with the vanishing of the reduction of $a_{1,0}$. Since the source is a group, this homomorphism lands in the units, and [`Ihara.gamma0FinUnitsChar N M hNM`](../def/IharaGamma0Fin.html#L59) is the resulting homomorphism $\Gamma_0\mathrm{Fin}(N,M) \to (\mathbb{Z}/N)^{\times}$, whose underlying value in $\mathbb{Z}/N$ is again the reduction of $g_{1,1}$ ([`Ihara.gamma0FinUnitsChar_coe`](../def/IharaGamma0Fin.html#L63)). The lemma [`Ihara.gamma0FinMap_apply`](../def/IharaGamma0Fin.html#L56) records the value of the homomorphism on an element.
--
--   **Relation to Mathlib.** Mathlib's congruence subgroups $\Gamma_0(N)$ are subgroups of $\mathrm{SL}_2(\mathbb{Z})$; the subgroup defined here is the analogue inside the finite group $\mathrm{SL}_2(\mathbb{Z}/M)$, built directly on Mathlib's `Matrix.SpecialLinearGroup` and `ZMod.castHom`.
--
--   **Where it is used.** These finite-level congruence subgroups of $\mathrm{SL}_2(\mathbb{Z}/M)$, and the character given by the reduction of the lower-right entry, provide the group-theoretic input for the project's treatment of Ihara-type arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_IharaGamma0Fin.lean

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace Ihara

open Matrix

open scoped MatrixGroups

section CongruenceQuotient

variable (N M : ℕ)

def Gamma0Fin : Subgroup SL(2, ZMod M) where
  carrier := {g | (N : ZMod M) ∣ g 1 0}
  one_mem' := by
    simp only [Set.mem_setOf_eq, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
    exact dvd_zero _
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Matrix.SpecialLinearGroup.coe_mul] at ha hb ⊢
    rw [(Matrix.two_mul_expl a.1 b.1).2.2.1]
    exact dvd_add (ha.mul_right _) (hb.mul_left _)
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl a]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    exact dvd_neg.mpr ha

variable {N M}

theorem mem_Gamma0Fin {g : SL(2, ZMod M)} : g ∈ Gamma0Fin N M ↔ (N : ZMod M) ∣ g 1 0 := Iff.rfl

variable (N M)

theorem castHom_apply_one_zero (hNM : N ∣ M) (g : Gamma0Fin N M) :
    ZMod.castHom hNM (ZMod N) ((g : SL(2, ZMod M)) 1 0) = 0 := by
  obtain ⟨r, hr⟩ := g.2
  rw [hr, map_mul, map_natCast, ZMod.natCast_self, zero_mul]

def gamma0FinMap (hNM : N ∣ M) : Gamma0Fin N M →* ZMod N where
  toFun g := ZMod.castHom hNM (ZMod N) ((g : SL(2, ZMod M)) 1 1)
  map_one' := by
    have h : ((1 : Gamma0Fin N M) : SL(2, ZMod M)) 1 1 = 1 := rfl
    rw [h, map_one]
  map_mul' a b := by
    have h : ((a * b : Gamma0Fin N M) : SL(2, ZMod M)) 1 1 =
        (a : SL(2, ZMod M)) 1 0 * (b : SL(2, ZMod M)) 0 1 +
          (a : SL(2, ZMod M)) 1 1 * (b : SL(2, ZMod M)) 1 1 :=
      (Matrix.two_mul_expl (a : SL(2, ZMod M)).1 (b : SL(2, ZMod M)).1).2.2.2
    rw [h, map_add, map_mul, map_mul, castHom_apply_one_zero N M hNM a, zero_mul, zero_add]

@[simp]
theorem gamma0FinMap_apply (hNM : N ∣ M) (g : Gamma0Fin N M) :
    gamma0FinMap N M hNM g = ZMod.castHom hNM (ZMod N) ((g : SL(2, ZMod M)) 1 1) := rfl

def gamma0FinUnitsChar (hNM : N ∣ M) : Gamma0Fin N M →* (ZMod N)ˣ :=
  (gamma0FinMap N M hNM).toHomUnits

@[simp]
theorem gamma0FinUnitsChar_coe (hNM : N ∣ M) (g : Gamma0Fin N M) :
    (gamma0FinUnitsChar N M hNM g : ZMod N) = ZMod.castHom hNM (ZMod N) ((g : SL(2, ZMod M)) 1 1) :=
  rfl

end CongruenceQuotient

end Ihara


