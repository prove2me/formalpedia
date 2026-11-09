-- Prove2me | Definitions.Def_DerandSq_leftReg
-- name    : DerandSq_leftReg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:57:26.049125+00:00
-- url     : https://prove2.me/theorems/b94513b8-b455-4be8-b729-9aa1c10ea68c
-- title:
--   Left-regular representation $\lambda(g)$
-- statement:
--   For a group $\Gamma$ and $g \in \Gamma$, the **left-regular representation** is the unitary operator $\lambda(g)$ on $\ell^2(\Gamma)$ given by
--   $$
--   (\lambda(g)\xi)(h) = \xi(g^{-1}h), \qquad\text{equivalently}\qquad \lambda(g)\,\delta_h = \delta_{gh}.
--   $$
--   The reduced C*-algebra $C^*_{\mathrm{red}}(\Gamma)$ is the norm closure of the span of the $\lambda(g)$ in the bounded operators on $\ell^2(\Gamma)$, with the operator norm.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), Example 2.4, p.8

import Mathlib
import Definitions.Def_DerandSq_L2

namespace DerandSq

/-- The left-regular representation `λ(g)` on `ℓ²(Γ)`: `(λ(g) f)(h) = f(g⁻¹h)`, so that
`λ(g) δ_h = δ_{gh}` (Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), Example 2.4, p.8), for an arbitrary group `Γ`. -/
noncomputable def leftReg {Γ : Type*} [Group Γ] (g : Γ) : L2 Γ →L[ℂ] L2 Γ :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun h => f (g⁻¹ * h), by
        have hf := (lp.memℓp f)
        rw [memℓp_gen_iff (by norm_num)] at hf
        show Memℓp (fun h : Γ => f (g⁻¹ * h)) 2
        rw [memℓp_gen_iff (by norm_num)]
        exact (Equiv.mulLeft g⁻¹).summable_iff.mpr hf⟩
      map_add' := fun f f' => by ext h; rfl
      map_smul' := fun c f => by ext h; rfl }
    1
    (by
      intro f
      rw [one_mul]
      apply le_of_eq
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
      congr 1
      exact (Equiv.mulLeft g⁻¹).tsum_eq (fun h => ‖f h‖ ^ (2 : ENNReal).toReal))

end DerandSq


