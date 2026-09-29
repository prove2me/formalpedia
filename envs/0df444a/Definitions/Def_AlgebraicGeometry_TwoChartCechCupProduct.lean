-- Prove2me | Definitions.Def_AlgebraicGeometry_TwoChartCechCupProduct
-- name    : AlgebraicGeometry_TwoChartCechCupProduct
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/3937b959-004b-5a6c-99d8-b35a16ca3dbc
-- title:
--   Čech cup product and trace pairing for two-chart covers
-- statement:
--   The setting is an abstract two-chart cover $\mathcal U=(A_0,A_1,A_{01};\rho_0,\rho_1)$ of $R$-algebras together with sections data $S=(M_0,M_1,M_{01};r_0,r_1)$, where $M_i$ is an $A_i$-module with compatible $R$-action and $r_i$ is $R$-linear and semilinear along $\rho_i$. Here $\check H^0 = \ker(S.\mathrm{cechDiff})=\{(x_0,x_1) : r_0x_0=r_1x_1\}$ with $S.\mathrm{cechDiff}(s_0,s_1)=r_1s_1-r_0s_0$, and $\check H^1 = M_{01}/\operatorname{im}(S.\mathrm{cechDiff})$; for the structure sheaf (the line bundle attached to the unit $1\in A_{01}^\times$, so $M_0=A_0$, $M_1=A_1$, $M_{01}=A_{01}$, $r_0=\rho_0$, $r_1=\rho_1$) this gives $A_{01}/\{\rho_1a_1-\rho_0a_0\}$.
--
--   The first theorem records the well-definedness computation: if $x=(x_0,x_1)$ satisfies $r_0x_0=r_1x_1$ and $f$ lies in the image of the structure-sheaf differential, then $f\cdot r_0x_0$ lies in the image of $S.\mathrm{cechDiff}$. This licenses `cupProductFun`, the $R$-linear map $\check H^1(\mathcal U,\mathcal O)\to\check H^1(\mathcal U,S)$ sending the class of $f\in A_{01}$ to the class of $f\cdot r_0x_0$ (the $A_{01}$-action on $M_{01}$), and then `cupProduct`, the $R$-bilinear map $\check H^0(\mathcal U,S)\to\check H^1(\mathcal U,\mathcal O)\to\check H^1(\mathcal U,S)$ assembled from it; two computing lemmas give its value on a class $[f]$ as $[f\cdot r_0x_0]$ and equivalently as $[f\cdot r_1x_1]$. Next, for an $R$-linear functional $t\colon M_{01}\to R$ whose kernel contains the image of $S.\mathrm{cechDiff}$, `traceForm` is the induced functional $\check H^1(\mathcal U,S)\to R$, $[m]\mapsto t(m)$. Finally `tracePairing` is the cup product followed by this functional, the $R$-bilinear pairing $\check H^0(\mathcal U,S)\times\check H^1(\mathcal U,\mathcal O)\to R$ with value $t(f\cdot r_0x_0)$ on $(x,[f])$.
--
--   **Relation to Mathlib.** The two-chart cover, its sections data and the two cohomology modules are the project's own elementary model of Čech cohomology for a cover by two opens, unrelated to Mathlib's category-theoretic Čech machinery; the constructions here are quotient-module lifts and bilinear-map composition from Mathlib's linear algebra API.
--
--   **Where it is used.** The pairing is the algebraic shape of Serre duality on a smooth proper curve covered by two affine opens: taking $S$ to be the sections of $\Omega^1$ and $t$ a sum-of-residues functional on the overlap, `tracePairing` is the pairing $H^0(\Omega^1)\times H^1(\mathcal O)\to R$, with perfectness a separate statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TwoChartCechCupProduct.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u v w

namespace TwoChartCech

namespace Sections

variable {R : Type u} [CommRing R] {𝒰 : Cover.{u, v} R} (S : Sections.{u, v, w} 𝒰)

theorem smul_r0_mem_range_cechDiff (x : S.H0) {f : 𝒰.A01}
    (hf : f ∈ LinearMap.range 𝒰.structureSheaf.cechDiff) :
    f • S.r0 x.val.1 ∈ LinearMap.range S.cechDiff := by
  obtain ⟨s, rfl⟩ := hf
  have hx : S.r0 x.val.1 = S.r1 x.val.2 := (S.mem_H0_iff _).mp x.2
  refine ⟨(s.1 • x.val.1, s.2 • x.val.2), ?_⟩
  rw [Sections.cechDiff_apply, Sections.cechDiff_apply, S.r0_smul, S.r1_smul, hx,
    Cover.lineBundle_r1_apply, Cover.lineBundle_r0_apply, Units.val_one, one_mul, sub_smul]

def cupProductFun (x : S.H0) : 𝒰.structureSheaf.H1 →ₗ[R] S.H1 :=
  (LinearMap.range 𝒰.structureSheaf.cechDiff).liftQ
    ((LinearMap.range S.cechDiff).mkQ ∘ₗ
      (LinearMap.toSpanSingleton 𝒰.A01 S.M01 (S.r0 x.val.1)).restrictScalars R)
    (fun f hf => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact S.smul_r0_mem_range_cechDiff x hf)

theorem cupProductFun_mk (x : S.H0) (f : 𝒰.A01) :
    S.cupProductFun x (Submodule.Quotient.mk f) = Submodule.Quotient.mk (f • S.r0 x.val.1) := rfl

def cupProduct : S.H0 →ₗ[R] 𝒰.structureSheaf.H1 →ₗ[R] S.H1 where
  toFun := S.cupProductFun
  map_add' x y := by
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | H f =>
      rw [LinearMap.add_apply, cupProductFun_mk, cupProductFun_mk, cupProductFun_mk, Submodule.coe_add,
        Prod.fst_add, map_add, smul_add, Submodule.Quotient.mk_add]
  map_smul' r x := by
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | H f =>
      rw [LinearMap.smul_apply, RingHom.id_apply, cupProductFun_mk, cupProductFun_mk, Submodule.coe_smul,
        Prod.smul_fst, LinearMap.map_smul, smul_comm (f : 𝒰.A01) r, Submodule.Quotient.mk_smul]

@[simp] theorem cupProduct_apply_mk (x : S.H0) (f : 𝒰.A01) :
    S.cupProduct x (Submodule.Quotient.mk f) = Submodule.Quotient.mk (f • S.r0 x.val.1) := rfl

theorem cupProduct_apply_mk' (x : S.H0) (f : 𝒰.A01) :
    S.cupProduct x (Submodule.Quotient.mk f) = Submodule.Quotient.mk (f • S.r1 x.val.2) := by
  rw [cupProduct_apply_mk, (S.mem_H0_iff _).mp x.2]

def traceForm (t : S.M01 →ₗ[R] R) (ht : LinearMap.range S.cechDiff ≤ LinearMap.ker t) : S.H1 →ₗ[R] R :=
  (LinearMap.range S.cechDiff).liftQ t ht

@[simp] theorem traceForm_mk (t : S.M01 →ₗ[R] R) (ht : LinearMap.range S.cechDiff ≤ LinearMap.ker t)
    (m : S.M01) : S.traceForm t ht (Submodule.Quotient.mk m) = t m := rfl

def tracePairing (t : S.M01 →ₗ[R] R) (ht : LinearMap.range S.cechDiff ≤ LinearMap.ker t) :
    S.H0 →ₗ[R] 𝒰.structureSheaf.H1 →ₗ[R] R :=
  S.cupProduct.compr₂ (S.traceForm t ht)

@[simp] theorem tracePairing_apply_mk (t : S.M01 →ₗ[R] R) (ht : LinearMap.range S.cechDiff ≤ LinearMap.ker t)
    (x : S.H0) (f : 𝒰.A01) :
    S.tracePairing t ht x (Submodule.Quotient.mk f) = t (f • S.r0 x.val.1) := rfl

end Sections

end TwoChartCech

end


