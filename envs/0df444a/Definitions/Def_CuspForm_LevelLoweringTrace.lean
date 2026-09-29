-- Prove2me | Definitions.Def_CuspForm_LevelLoweringTrace
-- name    : CuspForm_LevelLoweringTrace
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/824ea296-2ba9-5f6a-b7e9-3d0dcc173740
-- title:
--   Level-lowering trace on weight-two cusp forms
-- statement:
--   Fix $M \ge 1$, a natural number $q$, a prime $q$, and an Atkin–Lehner datum $W : \mathrm{AtkinLehnerDatum}\ M\ q$, i.e. data consisting of a natural number $R = W.R$ with $M = qR$ together with integers $a, b$ satisfying $qa - Rb = 1$ (so in particular $q$ and $R$ are coprime). Attached to such a datum is the integral matrix $W.\mathrm{mat} = \begin{pmatrix} qa & b \\ qR & q\end{pmatrix}$ of determinant $q$, whose image $W.\mathrm{alGL}$ in $\mathrm{GL}_2(\mathbb{R})$ has positive determinant, and the operator $\mathrm{alSlash}\ W\ k\ f = f \mid_k W.\mathrm{alGL}$ on functions on the upper half-plane, formed with Mathlib's weight-$k$ slash action (normalised by $|\det|^{k-1}\,(c\tau+d)^{-k}$). The second ingredient is $\mathrm{heckeU}\ k\ p\ f = \sum_{j<p} f \mid_k \begin{pmatrix}1 & j\\ 0 & p\end{pmatrix}$, which in weight $k$ evaluates to $p^{-1}\sum_{j<p} f((\tau+j)/p)$.
--
--   The module defines [`CuspForm.traceLin W hq`](../def/CuspForm_LevelLoweringTrace.html#L18), a $\mathbb{C}$-linear map from weight-$2$ cusp forms on $\Gamma_0(M)$ to weight-$2$ cusp forms on $\Gamma_0(R)$, whose underlying function on the upper half-plane is
--   $$f \;\longmapsto\; f + U_q\bigl(f \mid_2 W.\mathrm{alGL}\bigr),$$
--   that is, $f + \mathrm{heckeU}\ 2\ q\ (\mathrm{alSlash}\ W\ 2\ f)$. The weight is fixed to be $2$. That this function is weight-$2$ invariant under $\Gamma_0(R)$, holomorphic, and vanishes at the cusps is supplied by the three cited theorems [`ModularForm.add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0`](../thm.html#ModularForm.add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0), [`ModularForm.mdifferentiable_add_heckeU_alSlash`](../thm.html#ModularForm.mdifferentiable_add_heckeU_alSlash) and [`ModularForm.isZeroAt_add_heckeU_alSlash`](../thm.html#ModularForm.isZeroAt_add_heckeU_alSlash); additivity and $\mathbb{C}$-homogeneity follow from the corresponding properties of $\mathrm{alSlash}$ and $\mathrm{heckeU}$. Two accompanying lemmas, [`CuspForm.coe_traceLin_apply`](../def/CuspForm_LevelLoweringTrace.html#L35) and [`CuspForm.traceLin_apply_apply`](../def/CuspForm_LevelLoweringTrace.html#L39), record the above formula for the underlying function and for its value at a point $\tau$.
--
--   **Relation to Mathlib.** Mathlib provides the ambient objects — `CuspForm`, the congruence subgroups `CongruenceSubgroup.Gamma0` and the weight-$k$ slash action — but no Atkin–Lehner matrices, $U_q$ operator or trace map between levels; the datum `AtkinLehnerDatum`, `alSlash`, `heckeU` and this trace are the project's own, defined on top of Mathlib's slash action.
--
--   **Where it is used.** In weight $2$ the displayed formula is the sum over the cosets of $\Gamma_0(M)$ in $\Gamma_0(R)$, so `traceLin` realises the classical trace $\mathrm{Tr}^{M}_{R} : S_2(\Gamma_0(qR)) \to S_2(\Gamma_0(R))$. It is the tool used in the level-lowering part of the argument, where the vanishing of the trace on forms that are new at $q$ forces the relation $a_q^2 = 1$ for the $U_q$-eigenvalue.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CuspForm_LevelLoweringTrace.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Theorems.Thm_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0
import Theorems.Thm_ModularForm_mdifferentiable_add_heckeU_alSlash
import Theorems.Thm_ModularForm_isZeroAt_add_heckeU_alSlash

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace CuspForm

open ModularForm

variable {M q : ℕ}

def traceLin [NeZero M] (W : AtkinLehnerDatum M q) (hq : q.Prime) :
    CuspForm (CongruenceSubgroup.Gamma0 M) 2 →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 W.R) 2 where
  toFun f :=
    { toFun := ⇑f + heckeU 2 q (alSlash W 2 ⇑f)
      slash_action_eq' := fun γ hγ => add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0 W hq
        (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
      holo' := mdifferentiable_add_heckeU_alSlash W 2 (CuspFormClass.holo f)
      zero_at_cusps' := fun hc => isZeroAt_add_heckeU_alSlash W 2
        (fun c' hc' => CuspFormClass.zero_at_cusps f hc') hc }
  map_add' f g := DFunLike.coe_injective <|
    show ⇑(f + g) + heckeU 2 q (alSlash W 2 ⇑(f + g))
        = (⇑f + heckeU 2 q (alSlash W 2 ⇑f)) + (⇑g + heckeU 2 q (alSlash W 2 ⇑g)) by
      rw [CuspForm.coe_add, alSlash_add, heckeU_add]; abel
  map_smul' c f := DFunLike.coe_injective <|
    show ⇑(c • f) + heckeU 2 q (alSlash W 2 ⇑(c • f)) = c • (⇑f + heckeU 2 q (alSlash W 2 ⇑f)) by
      rw [CuspForm.IsGLPos.coe_smul, alSlash_smul, heckeU_smul, smul_add]

@[simp] theorem coe_traceLin_apply [NeZero M] (W : AtkinLehnerDatum M q) (hq : q.Prime)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    ⇑(traceLin W hq f) = ⇑f + heckeU 2 q (alSlash W 2 ⇑f) := rfl

theorem traceLin_apply_apply [NeZero M] (W : AtkinLehnerDatum M q) (hq : q.Prime)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (τ : UpperHalfPlane) :
    traceLin W hq f τ = f τ + heckeU 2 q (alSlash W 2 ⇑f) τ := rfl

end CuspForm

end


