-- Prove2me | Definitions.Def_WeierstrassCurve_VeluVariableChange
-- name    : WeierstrassCurve_VeluVariableChange
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/59e04a82-4b76-575c-88fb-6dbddd255ba7
-- title:
--   Vélu quantities under admissible change of variables
-- statement:
--   Over a field $K$, fix a Weierstrass curve $W$ and an admissible change of variables $C=(u,r,s,t)$ with $u\in K^\times$, acting on curves by Mathlib's $C\bullet W$. The module first packages the inverse coordinate substitution as an injection $\mathrm{vcInvEmbedding}\,C : K\times K\hookrightarrow K\times K$, sending $(x,y)$ to $(\mathrm{vcXInv}\,C\,x,\ \mathrm{vcYInv}\,C\,x\,y)=(u^{-2}(x-r),\ u^{-3}(y-t-s(x-r)))$; injectivity comes from the fact that $\mathrm{vcX}$, $\mathrm{vcY}$ invert these maps. Thus a finite set of affine points on $W$ is carried to a finite set of affine points on $C\bullet W$.
--
--   The remaining lemmas are the transformation laws for the Vélu quantities attached to a point, where $g_y=-(2y+a_1x+a_3)$, $g_x=3x^2+2a_2x+a_4-a_1y$, $t=2g_x-a_1g_y$, $u_{\mathrm{V}}=g_y^2$ and $w=u_{\mathrm{V}}+x\,t$. Evaluating the quantities of $C\bullet W$ at $(\mathrm{vcXInv}\,C\,x,\mathrm{vcYInv}\,C\,x\,y)$ gives: $g_y$ scales by $u^{-3}$; $g_x$ transforms to $u^{-4}(g_x+s\,g_y)$, the shear $s$ contributing a multiple of $g_y$; $t$ scales by $u^{-4}$ and $u_{\mathrm{V}}$ by $u^{-6}$ with no correction; and $w$ transforms to $u^{-6}(w-r\,t)$, the translation $r$ contributing a multiple of $t$. All five are polynomial identities in the coordinates and in $u^{\pm1},r,s,t$; no curve equation is assumed of $(x,y)$.
--
--   Summing over a finite set $S\subseteq K\times K$ and its image under $\mathrm{vcInvEmbedding}\,C$, the last two lemmas give $\mathrm{veluTSum}$ scaling by $u^{-4}$ and $\mathrm{veluWSum}$ transforming to $u^{-6}(\mathrm{veluWSum}\,S-r\,\mathrm{veluTSum}\,S)$.
--
--   **Relation to Mathlib.** Mathlib supplies `WeierstrassCurve`, the group of admissible changes of variables `VariableChange` with its action $C\bullet W$, and division polynomials; the Vélu quantities `veluGx`, `veluGy`, `veluT`, `veluU`, `veluW` and their sums, as well as the coordinate substitutions `vcX`, `vcY`, `vcXInv`, `vcYInv`, are the project's own, introduced in the imported definition modules.
--
--   **Where it is used.** These weight laws are what makes the Vélu quotient construction compatible with change of model: a computation carried out on a convenient normal form of a curve can be transported back to an arbitrary Weierstrass model, which is how the isogeny-theoretic input to the Frey-curve arguments is set up.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_VeluVariableChange.lean

import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve

variable {K : Type*} [Field K]

section Embedding

variable (C : VariableChange K)

def vcInvEmbedding : K × K ↪ K × K where
  toFun P := (Affine.vcXInv C P.1, Affine.vcYInv C P.1 P.2)
  inj' := by
    intro P P' h
    have h1 : Affine.vcXInv C P.1 = Affine.vcXInv C P'.1 := congrArg Prod.fst h
    have h2 : Affine.vcYInv C P.1 P.2 = Affine.vcYInv C P'.1 P'.2 := congrArg Prod.snd h
    have hx : P.1 = P'.1 := by
      have := congrArg (Affine.vcX C) h1
      simpa only [Affine.vcX_vcXInv] using this
    have hy : P.2 = P'.2 := by
      have := congrArg (Affine.vcY C (Affine.vcXInv C P.1)) h2
      rw [Affine.vcY_vcYInv, hx] at this
      simpa only [Affine.vcY_vcYInv] using this
    exact Prod.ext hx hy

@[simp] lemma vcInvEmbedding_apply (P : K × K) :
    vcInvEmbedding C P = (Affine.vcXInv C P.1, Affine.vcYInv C P.1 P.2) := rfl

end Embedding

section PerPoint

variable (C : VariableChange K) (W : WeierstrassCurve K)

lemma variableChange_veluGy (x y : K) :
    (C • W).veluGy (Affine.vcXInv C x) (Affine.vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 3 * W.veluGy x y := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluGy, Affine.vcXInv, Affine.vcYInv, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

lemma variableChange_veluGx (x y : K) :
    (C • W).veluGx (Affine.vcXInv C x) (Affine.vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 4 * (W.veluGx x y + C.s * W.veluGy x y) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluGx, veluGy, Affine.vcXInv, Affine.vcYInv, variableChange_a₁,
    variableChange_a₂, variableChange_a₄, Units.val_inv_eq_inv_val]
  field_simp
  ring

lemma variableChange_veluT (x y : K) :
    (C • W).veluT (Affine.vcXInv C x) (Affine.vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 4 * W.veluT x y := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluT, veluGx, veluGy, Affine.vcXInv, Affine.vcYInv, variableChange_a₁,
    variableChange_a₂, variableChange_a₃, variableChange_a₄, Units.val_inv_eq_inv_val]
  field_simp
  ring

lemma variableChange_veluU (x y : K) :
    (C • W).veluU (Affine.vcXInv C x) (Affine.vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 6 * W.veluU x y := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluU, veluGy, Affine.vcXInv, Affine.vcYInv, variableChange_a₁,
    variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

lemma variableChange_veluW (x y : K) :
    (C • W).veluW (Affine.vcXInv C x) (Affine.vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 6 * (W.veluW x y - C.r * W.veluT x y) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluW, veluU, veluT, veluGx, veluGy, Affine.vcXInv, Affine.vcYInv,
    variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

end PerPoint

section Sums

variable (C : VariableChange K) (W : WeierstrassCurve K) (S : Finset (K × K))

lemma variableChange_veluTSum :
    (C • W).veluTSum (S.map (vcInvEmbedding C))
      = ((C.u⁻¹ : Kˣ) : K) ^ 4 * W.veluTSum S := by
  rw [veluTSum, veluTSum, Finset.sum_map, Finset.mul_sum]
  exact Finset.sum_congr rfl fun P _ => by
    simpa only [vcInvEmbedding_apply] using variableChange_veluT C W P.1 P.2

lemma variableChange_veluWSum :
    (C • W).veluWSum (S.map (vcInvEmbedding C))
      = ((C.u⁻¹ : Kˣ) : K) ^ 6 * (W.veluWSum S - C.r * W.veluTSum S) := by
  rw [veluWSum, Finset.sum_map]
  rw [show W.veluWSum S - C.r * W.veluTSum S
      = ∑ P ∈ S, (W.veluW P.1 P.2 - C.r * W.veluT P.1 P.2) by
    rw [veluWSum, veluTSum, Finset.mul_sum, ← Finset.sum_sub_distrib]]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun P _ => by
    simpa only [vcInvEmbedding_apply] using variableChange_veluW C W P.1 P.2

end Sums

end WeierstrassCurve


