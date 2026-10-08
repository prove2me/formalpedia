-- Prove2me | Definitions.Def_MazurHuang_EisensteinDescent35
-- name    : MazurHuang_EisensteinDescent35
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:04:50.076079+00:00
-- url     : https://prove2.me/theorems/f3ba2861-1037-4929-80e3-d25cae24128c
-- title:
--   Eisenstein integers and the descent element of the 3-isogenous curve of conductor 35
-- statement:
--   Notation for the descent over the Eisenstein integers used for the curve $E' : t^2 = s^3 - 3(12s+1500)^2$ (namespace `MazurHuang.EisensteinDescent35`).
--
--   * `N35K3` is the cyclotomic field $K = \mathbb{Q}(\zeta_3)$ (`CyclotomicField 3 ℚ`) and `N35O3` its ring of integers $\mathcal{O}_K = \mathbb{Z}[\omega]$.
--   * `n35Zeta` is the primitive cube root of unity $\zeta \in K$ fixed by Mathlib and `n35Omega` is the same element $\omega$ regarded in $\mathcal{O}_K$; it satisfies $\omega^2+\omega+1=0$.
--   * `n35ConjK` and `n35ConjO` are the non-trivial automorphism $\zeta \mapsto \zeta^{-1}$ of $K$ and its restriction to $\mathcal{O}_K$.
--   * `n35SqrtNegThree` is $\sqrt{-3} := 2\omega+1 \in \mathcal{O}_K$, so that $\sqrt{-3}^{\,2} = -3$.
--   * `n35ZetaUnit` is $\omega$ as an element of the unit group $\mathcal{O}_K^\times$.
--   * For integers $m,n,d$, `n35DualA m n d` is the element
--     $$A(m,n,d) = n - \sqrt{-3}\; d\,(12m + 1500 d^2) \in \mathcal{O}_K .$$
--     If $(s,t) = (m/d^2, n/d^3)$ is a rational point of $E'$, then $A\,\overline{A} = n^2 + 3d^2(12m+1500d^2)^2 = m^3$.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT, commit 51bbb4f191ad0d3753b87123635c100a638ae580, branch verify-sorry-restore; Apache-2.0; FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean (declarations N35K3 to n35ConjO_sqrtNegThree, n35ZetaUnit, n35DualA).

/-
The ring of integers of Q(zeta_3) with its conjugation, omega, sqrt(-3), the unit omega and the
descent element n - sqrt(-3) d (12 m + 1500 d^2): definitions and their immediate API.

Author: Xiang Huang
License: Apache-2.0
Source: Xiang Huang's FLT fork, https://github.com/xiangyazi24/FLT,
  commit 51bbb4f191ad0d3753b87123635c100a638ae580,
  FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean (declarations N35K3 ... n35ConjO_sqrtNegThree, n35ZetaUnit, n35DualA);
  the namespace is MazurHuang.EisensteinDescent35 instead of MazurProof.RationalPointsX135;
  nothing else is changed,
  ported to Lean v4.33.1 / Mathlib 0df444a360ea.
-/
import Mathlib

namespace MazurHuang.EisensteinDescent35

noncomputable section

open scoped NumberField

-- FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean, lines 566-654
abbrev N35K3 := CyclotomicField 3 ℚ
abbrev N35O3 := 𝓞 N35K3

local instance n35K3_isCyclotomic :
    IsCyclotomicExtension {3} ℚ N35K3 := by
  change IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ)
  exact CyclotomicField.isCyclotomicExtension 3 ℚ

local instance n35O3_isPrincipalIdealRing :
    IsPrincipalIdealRing N35O3 :=
  IsCyclotomicExtension.Rat.three_pid N35K3

noncomputable def n35Zeta : N35K3 :=
  IsCyclotomicExtension.zeta 3 ℚ N35K3

theorem n35Zeta_isPrimitive : IsPrimitiveRoot n35Zeta 3 :=
  IsCyclotomicExtension.zeta_spec 3 ℚ N35K3

theorem n35Zeta_relation : n35Zeta ^ 2 + n35Zeta + 1 = 0 := by
  simpa [add_assoc, add_comm, add_left_comm] using
    n35Zeta_isPrimitive.isRoot_cyclotomic (by norm_num)

noncomputable def n35ConjK : N35K3 ≃ₐ[ℚ] N35K3 :=
  IsCyclotomicExtension.fromZetaAut
    (n35Zeta_isPrimitive.pow_of_coprime 2 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 3))

@[simp] theorem n35ConjK_zeta :
    n35ConjK n35Zeta = n35Zeta ^ 2 := by
  exact IsCyclotomicExtension.fromZetaAut_spec
    (n35Zeta_isPrimitive.pow_of_coprime 2 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 3))

theorem n35ConjK_involutive : Function.Involutive n35ConjK := by
  have heq : n35ConjK.trans n35ConjK = AlgEquiv.refl := by
    apply AlgEquiv.coe_algHom_injective
    apply (n35Zeta_isPrimitive.powerBasis ℚ).algHom_ext
    rw [AlgEquiv.coe_algHom, AlgEquiv.coe_algHom,
      AlgEquiv.trans_apply,
      IsPrimitiveRoot.powerBasis_gen, n35ConjK_zeta, map_pow,
      n35ConjK_zeta]
    calc
      (n35Zeta ^ 2) ^ 2 = n35Zeta * n35Zeta ^ 3 := by ring
      _ = n35Zeta := by rw [n35Zeta_isPrimitive.pow_eq_one]; ring
  intro x
  have hx := DFunLike.congr_fun heq x
  exact hx

noncomputable def n35ConjO : N35O3 ≃+* N35O3 :=
  NumberField.RingOfIntegers.mapRingEquiv n35ConjK.toRingEquiv

@[simp] theorem n35ConjO_coe (x : N35O3) :
    ((n35ConjO x : N35O3) : N35K3) = n35ConjK (x : N35K3) := by
  exact NumberField.RingOfIntegers.mapRingEquiv_apply _ _

theorem n35ConjO_involutive : Function.Involutive n35ConjO := by
  intro x
  ext
  simp only [n35ConjO_coe]
  exact n35ConjK_involutive x

noncomputable def n35Omega : N35O3 := n35Zeta_isPrimitive.toInteger

@[simp] theorem n35Omega_coe : (n35Omega : N35K3) = n35Zeta := rfl

theorem n35Omega_relation : n35Omega ^ 2 + n35Omega + 1 = 0 := by
  ext
  exact n35Zeta_relation

theorem n35Omega_cube : n35Omega ^ 3 = 1 := by
  unfold n35Omega
  exact n35Zeta_isPrimitive.toInteger_cube_eq_one

@[simp] theorem n35ConjO_omega : n35ConjO n35Omega = n35Omega ^ 2 := by
  ext
  rw [n35ConjO_coe]
  exact n35ConjK_zeta

noncomputable def n35SqrtNegThree : N35O3 := 1 + 2 * n35Omega

theorem n35SqrtNegThree_sq : n35SqrtNegThree ^ 2 = -3 := by
  unfold n35SqrtNegThree
  linear_combination 4 * n35Omega_relation

@[simp] theorem n35ConjO_sqrtNegThree :
    n35ConjO n35SqrtNegThree = -n35SqrtNegThree := by
  unfold n35SqrtNegThree
  rw [map_add, map_mul, map_one, map_ofNat, n35ConjO_omega]
  linear_combination 2 * n35Omega_relation

-- FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean, lines 871-872
noncomputable def n35ZetaUnit : N35O3ˣ :=
  ((n35Zeta_isPrimitive.toInteger_isPrimitiveRoot).isUnit (by norm_num)).unit

-- FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean, lines 928-930
noncomputable def n35DualA (m n d : ℤ) : N35O3 :=
  (n : N35O3) - n35SqrtNegThree *
    (d * (12 * m + 1500 * d ^ 2) : ℤ)

end

end MazurHuang.EisensteinDescent35


