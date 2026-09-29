-- Prove2me | Definitions.Def_CuspForm_AtkinLehnerOperator
-- name    : CuspForm_AtkinLehnerOperator
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/55619713-d853-57b8-a188-3ab2b2db31e6
-- title:
--   Atkin–Lehner operator on modular and cusp forms of Γ0​(M)
-- statement:
--   Fix a level $M\ge 1$, a weight $k\in\mathbb{Z}$ and an Atkin–Lehner datum $W$ at $(M,q)$, that is, a natural number $R$ with $M=qR$ together with integers $a,b$ satisfying $qa-Rb=1$. Such a datum determines the integral matrix $\mathrm{mat}\,W=\begin{pmatrix} qa & b\\ qR & q\end{pmatrix}$, of determinant $q$ and with lower-left entry $M$, and its image `W.alGL` in $\mathrm{GL}_2(\mathbb{R})$, whose determinant $q$ is positive. Writing `alSlash W k f` for the weight-$k$ slash action $f\mid_k \mathrm{alGL}\,W$ on functions $\mathbb{H}\to\mathbb{C}$, the module packages this operation as two $\mathbb{C}$-linear endomorphisms: [`ModularForm.atkinLehnerLin W k`](../def/CuspForm_AtkinLehnerOperator.html#L16) on $M_k(\Gamma_0(M))$ and [`CuspForm.atkinLehnerLin W k`](../def/CuspForm_AtkinLehnerOperator.html#L41) on $S_k(\Gamma_0(M))$. In each case the value at $f$ is the bundled form whose underlying function is $f\mid_k \mathrm{alGL}\,W$; its weight-$k$ invariance under $\Gamma_0(M)$, its holomorphy, and boundedness at the cusps (respectively vanishing at the cusps, in the cuspidal case) are supplied by the corresponding statements about `alSlash` proved elsewhere in the development. Additivity and $\mathbb{C}$-homogeneity come from the identities $\mathrm{alSlash}(f+g)=\mathrm{alSlash}\,f+\mathrm{alSlash}\,g$ and $\mathrm{alSlash}(c\cdot f)=c\cdot\mathrm{alSlash}\,f$, the latter using that the slash by a matrix of positive determinant involves no complex conjugation.
--
--   The module also records the defining identities: the underlying function of `atkinLehnerLin W k f` is `alSlash W k ⇑f`, in both the modular and the cuspidal setting, and, for cusp forms, the pointwise form of the same identity at a point $\tau$ of the upper half-plane.
--
--   **Relation to Mathlib.** Mathlib supplies the weight-$k$ slash action, the spaces `ModularForm` and `CuspForm`, and `CongruenceSubgroup.Gamma0`, but no Atkin–Lehner operator; the datum, the associated slash operation and these two linear endomorphisms are the project's own.
--
--   **Where it is used.** These operators are the input to the Atkin–Lehner theory used in level lowering: the relations $w_q^2 = q^{k-2}$, the commutation of $w_q$ with the Hecke operators $T_\ell$ for $\ell \nmid M$, the trace identities relating $w_q$ and $U_q$, and the consequence that the $q$-th coefficient of a newform of the relevant type satisfies $a_q^2 = 1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CuspForm_AtkinLehnerOperator.lean

import Mathlib
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Theorems.Thm_ModularForm_alSlash_slash_eq_self_of_mem_Gamma0
import Theorems.Thm_ModularForm_mdifferentiable_alSlash
import Theorems.Thm_ModularForm_isBoundedAt_alSlash
import Theorems.Thm_ModularForm_isZeroAt_alSlash

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularForm

variable {M q : ℕ}

def atkinLehnerLin [NeZero M] (W : AtkinLehnerDatum M q) (k : ℤ) :
    ModularForm (CongruenceSubgroup.Gamma0 M) k →ₗ[ℂ] ModularForm (CongruenceSubgroup.Gamma0 M) k where
  toFun f :=
    { toFun := alSlash W k ⇑f
      slash_action_eq' := fun γ hγ => alSlash_slash_eq_self_of_mem_Gamma0 W k
        (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
      holo' := mdifferentiable_alSlash W k (ModularFormClass.holo f)
      bdd_at_cusps' := fun hc => isBoundedAt_alSlash W k
        (fun c' hc' => ModularFormClass.bdd_at_cusps f hc') hc }
  map_add' f g := DFunLike.coe_injective <|
    show alSlash W k ⇑(f + g) = alSlash W k ⇑f + alSlash W k ⇑g by rw [ModularForm.coe_add, alSlash_add]
  map_smul' c f := DFunLike.coe_injective <|
    show alSlash W k ⇑(c • f) = c • alSlash W k ⇑f by rw [ModularForm.IsGLPos.coe_smul, alSlash_smul]

@[simp] theorem coe_atkinLehnerLin_apply [NeZero M] (W : AtkinLehnerDatum M q) (k : ℤ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 M) k) : ⇑(atkinLehnerLin W k f) = alSlash W k ⇑f := rfl

end ModularForm

namespace CuspForm

open ModularForm

variable {M q : ℕ}

def atkinLehnerLin [NeZero M] (W : AtkinLehnerDatum M q) (k : ℤ) :
    CuspForm (CongruenceSubgroup.Gamma0 M) k →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 M) k where
  toFun f :=
    { toFun := alSlash W k ⇑f
      slash_action_eq' := fun γ hγ => alSlash_slash_eq_self_of_mem_Gamma0 W k
        (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
      holo' := mdifferentiable_alSlash W k (CuspFormClass.holo f)
      zero_at_cusps' := fun hc => isZeroAt_alSlash W k
        (fun c' hc' => CuspFormClass.zero_at_cusps f hc') hc }
  map_add' f g := DFunLike.coe_injective <|
    show alSlash W k ⇑(f + g) = alSlash W k ⇑f + alSlash W k ⇑g by rw [CuspForm.coe_add, alSlash_add]
  map_smul' c f := DFunLike.coe_injective <|
    show alSlash W k ⇑(c • f) = c • alSlash W k ⇑f by rw [CuspForm.IsGLPos.coe_smul, alSlash_smul]

@[simp] theorem coe_atkinLehnerLin_apply [NeZero M] (W : AtkinLehnerDatum M q) (k : ℤ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) : ⇑(atkinLehnerLin W k f) = alSlash W k ⇑f := rfl

theorem atkinLehnerLin_apply_apply [NeZero M] (W : AtkinLehnerDatum M q) (k : ℤ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) (τ : UpperHalfPlane) :
    atkinLehnerLin W k f τ = alSlash W k ⇑f τ := rfl

end CuspForm

end


