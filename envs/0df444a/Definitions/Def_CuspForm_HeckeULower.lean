-- Prove2me | Definitions.Def_CuspForm_HeckeULower
-- name    : CuspForm_HeckeULower
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/52218a20-1668-578c-8cb4-38323b9ef244
-- title:
--   The Up​ operator as a map to level Γ0​(N/p)
-- statement:
--   Fix a weight $k \in \mathbb{Z}$, a level $N$ with $N \neq 0$, and a natural number $p$ with $p^2 \mid N$. The module packages the operator
--   $$U_p f \;=\; \sum_{j=0}^{p-1} f \big|_k \begin{pmatrix} 1 & j \\ 0 & p\end{pmatrix}$$
--   as a $\mathbb{C}$-linear map [`CuspForm.heckeULowerLin k hp2N`](../def/CuspForm_HeckeULower.html#L15) from $S_k(\Gamma_0(N))$ to $S_k(\Gamma_0(N/p))$, i.e. with target the *lower* level $N/p$ rather than $N$. Here $U_p$ on plain functions on the upper half-plane is [`ModularForm.heckeU`](../def/ModularForm_HeckeOperator.html#L93), the finite sum over $j \in \{0,\dots,p-1\}$ of the weight-$k$ slash by the matrix $\begin{pmatrix} 1 & j \\ 0 & p\end{pmatrix}$ viewed in $\mathrm{GL}_2(\mathbb{R})^+$ (for $p = 0$ the sum is empty, so $U_0 = 0$); pointwise this is $(U_p f)(\tau) = p^{-1}\sum_{j<p} f((\tau+j)/p)$.
--
--   The definition is a structure literal: the underlying function of $U_p f$ is [`ModularForm.heckeU k p ⇑f`](../def/ModularForm_HeckeOperator.html#L93), and the three fields of a cusp form are filled by previously established theorems — weight-$k$ invariance under $\Gamma_0(N/p)$ by `heckeU_slash_eq_self_of_mem_Gamma0_div` (using $p^2 \mid N$ and the $\Gamma_0(N)$-invariance of $f$), holomorphy by `mdifferentiable_heckeU`, and vanishing at every cusp by [`CuspFormClass.isZeroAt_heckeU`](../thm.html#CuspFormClass.isZeroAt_heckeU), the cusp condition at level $N/p$ being transported through the characterisation of cusps via $\mathrm{SL}_2(\mathbb{Z})$. Linearity is inherited from the additivity and $\mathbb{C}$-homogeneity of `heckeU`. A side computation supplies the instance $N/p \neq 0$ from $p^2 \mid N$ and $N \neq 0$. Two further declarations record that the construction is definitionally transparent: `coe_heckeULowerLin_apply` states that the coercion of `heckeULowerLin k hp2N f` to a function is literally `heckeU k p ⇑f`, and `heckeULowerLin_apply_apply` is the pointwise form of the same identity; both hold by `rfl`.
--
--   **Relation to Mathlib.** Mathlib supplies `CuspForm`, `CongruenceSubgroup.Gamma0` and the slash action, but not these Hecke operators; [`ModularForm.heckeU`](../def/ModularForm_HeckeOperator.html#L93) and the linear maps built from it ([`ModularForm.heckeULin`](../def/ModularForm_HeckeOperatorForms.html#L34), [`CuspForm.heckeULin`](../def/ModularForm_HeckeOperatorForms.html#L83), and the present level-lowering variant) are the project's own.
--
--   **Where it is used.** Composing `heckeULowerLin` with the inclusion $S_k(\Gamma_0(N/p)) \hookrightarrow S_k(\Gamma_0(N))$ returns the usual endomorphism $U_p$ of level $N$. The level-lowering form is what is needed to show that a newform of level $N$ has $q$-th Fourier coefficient zero whenever $q^2 \mid N$, since a nonzero $U_q f$ would realise the eigensystem of $f$ at the proper divisor level $N/q$; this is part of the oldform/newform bookkeeping underlying level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CuspForm_HeckeULower.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0_div

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace CuspForm

open ModularForm

variable {N : ℕ} {p : ℕ}

def heckeULowerLin (k : ℤ) [NeZero N] (hp2N : p ^ 2 ∣ N) :
    CuspForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 (N / p)) k :=
  haveI : NeZero (N / p) := ⟨fun h => by
    have hp : p ≠ 0 := by
      rintro rfl
      exact NeZero.ne N (zero_dvd_iff.mp ((dvd_pow_self 0 two_ne_zero).trans hp2N))
    have hpN : p ∣ N := (dvd_pow_self p two_ne_zero).trans hp2N
    exact Nat.div_ne_zero_iff.mpr ⟨hp, Nat.le_of_dvd (NeZero.pos N) hpN⟩ h⟩
  { toFun := fun f =>
    { toFun := heckeU k p ⇑f
      slash_action_eq' := fun γ hγ => heckeU_slash_eq_self_of_mem_Gamma0_div k hp2N
        (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
      holo' := mdifferentiable_heckeU (CuspFormClass.holo f) k p
      zero_at_cusps' := fun {c} hc => CuspFormClass.isZeroAt_heckeU f p
        ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
          ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)) }
    map_add' := fun f g => DFunLike.coe_injective <|
      show heckeU k p ⇑(f + g) = heckeU k p ⇑f + heckeU k p ⇑g by rw [CuspForm.coe_add, heckeU_add]
    map_smul' := fun c f => DFunLike.coe_injective <|
      show heckeU k p ⇑(c • f) = c • heckeU k p ⇑f by rw [CuspForm.IsGLPos.coe_smul, heckeU_smul] }

@[simp] theorem coe_heckeULowerLin_apply (k : ℤ) [NeZero N] (hp2N : p ^ 2 ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    ⇑(heckeULowerLin k hp2N f) = heckeU k p ⇑f := rfl

theorem heckeULowerLin_apply_apply (k : ℤ) [NeZero N] (hp2N : p ^ 2 ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane) :
    heckeULowerLin k hp2N f τ = heckeU k p ⇑f τ := rfl

end CuspForm

end


