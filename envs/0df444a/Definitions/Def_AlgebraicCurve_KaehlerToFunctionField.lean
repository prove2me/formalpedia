-- Prove2me | Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
-- name    : AlgebraicCurve_KaehlerToFunctionField
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/998a1e8c-f5f2-5978-b618-e9ecf1fc278c
-- title:
--   Generic germs of Kähler differentials on an integral scheme
-- statement:
--   Throughout, $k$ is a field, $X$ an integral scheme with a morphism $c \colon X \to \operatorname{Spec} k$, and $U \subseteq X$ a nonempty open subset. Two $k$-algebra structures are in play: on $\Gamma(X,U)$ the one induced by $c$, whose structure map sends $r \in k$ to the image of $r$ under $\Gamma(\operatorname{Spec} k) \cong k$ followed by $c^{\#} \colon \Gamma(\operatorname{Spec} k, \top) \to \Gamma(X,U)$, and on the function field $X.\mathrm{functionField}$ (the stalk at the generic point) the one given by [`AlgebraicCurve.baseToFunctionField c`](../def/AlgebraicCurve_CurveModel.html#L18), i.e. the same map into global sections followed by the germ at the generic point. The first group of results records the compatibility of these two structures: `germToFunctionField_algebraMap` and its ring-homomorphism form state that the germ map $\Gamma(X,U) \to X.\mathrm{functionField}$ at the generic point carries the structure map of $\Gamma(X,U)$ to that of the function field, and `germToFunctionField_map` states that for $V \le U$ (with $X$ irreducible) the germ of a restricted section equals the germ of the section.
--
--   On this basis [`AlgebraicCurve.kaehlerToFunctionField c U`](../def/AlgebraicCurve_KaehlerToFunctionField.html#L46) is defined: it is the $k$-linear map
--   $$\Omega^1_{\Gamma(X,U)/k} \longrightarrow \Omega^1_{X.\mathrm{functionField}/k}$$
--   obtained from [`KaehlerDifferential.mapOfRingHom`](../def/AlgebraicGeometry_TwoAffineOpenCoverKaehler.html#L16) applied to the identity of $k$ and the germ homomorphism, with the compatibility above as the required commuting square. Its basic calculus is then recorded: it sends $d s$ to $d\tilde s$, where $\tilde s$ denotes the germ of $s$, and $a \cdot \eta$ to $\tilde a \cdot$ (image of $\eta$), hence $a\,ds \mapsto \tilde a\, d\tilde s$; and it is compatible with restriction, in that for $V \le U$ the map for $V$ composed with the functorial map of Kähler differentials along the restriction $\Gamma(X,U) \to \Gamma(X,V)$ agrees with the map for $U$.
--
--   The last three statements specialise this to a two-chart affine cover $\mathcal V$ of $X$ with charts $U_0$, $U_1$, both chart intersections nonempty: the restriction maps $r_0$, $r_1$ of the Čech system `𝒱.kaehlerSections c` of Kähler differentials are compatible with the generic-germ maps, and consequently, for a pair $(\omega_0,\omega_1)$ lying in $H^0$ of that system (the kernel of the Čech differential, i.e. a pair whose restrictions to $U_0 \cap U_1$ agree), the generic germs of $\omega_0$ and $\omega_1$ coincide. Thus a Čech $0$-cocycle of differentials has a well-defined image in $\Omega^1_{X.\mathrm{functionField}/k}$.
--
--   **Relation to Mathlib.** `Scheme.germToFunctionField` and `KaehlerDifferential` are Mathlib's; the map used here, [`KaehlerDifferential.mapOfRingHom`](../def/AlgebraicGeometry_TwoAffineOpenCoverKaehler.html#L16), is the project's semilinear variant of Mathlib's `KaehlerDifferential.map`, taking a pair of ring homomorphisms with a commuting square instead of algebra and scalar-tower instances.
--
--   **Where it is used.** These maps let a pair of differentials given on the two charts of a two-chart affine cover of a curve over $k$ be compared inside $\Omega^1$ of the function field, so that the Čech description of global differentials can be matched with differentials written in terms of a single generic expression.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_KaehlerToFunctionField.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicCurve

variable {k : Type u} [Field k] {X : Scheme.{u}} (c : X ⟶ Spec (.of k)) [IsIntegral X]

theorem germToFunctionField_algebraMap (U : X.Opens) [Nonempty U] (r : k) :
    (X.germToFunctionField U).hom ((Scheme.TwoAffineOpenCover.algebraOfHom c U).algebraMap r)
      = baseToFunctionField c r := by
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  change (c.appLE ⊤ U le_top ≫ X.germToFunctionField U).hom _
    = (c.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom _
  congr 2
  rw [Scheme.Hom.appLE, Category.assoc]
  erw [TopCat.Presheaf.germ_res]
  try rfl

theorem germToFunctionField_comp_algebraMap (U : X.Opens) [Nonempty U] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := (baseToFunctionField c).toAlgebra
    (X.germToFunctionField U).hom.comp (algebraMap k Γ(X, U))
      = (algebraMap k X.functionField).comp (RingHom.id k) :=
  RingHom.ext fun r => germToFunctionField_algebraMap c U r

omit [IsIntegral X] in

theorem germToFunctionField_map [IrreducibleSpace X] {U V : X.Opens} [Nonempty U] [Nonempty V]
    (h : V ≤ U) (s : Γ(X, U)) :
    (X.germToFunctionField V).hom ((X.presheaf.map (homOfLE h).op).hom s)
      = (X.germToFunctionField U).hom s := by
  rw [← CategoryTheory.ConcreteCategory.comp_apply]
  erw [TopCat.Presheaf.germ_res]
  try rfl

def kaehlerToFunctionField (U : X.Opens) [Nonempty U] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := (baseToFunctionField c).toAlgebra
    Ω[Γ(X, U)⁄k] →ₗ[k] Ω[X.functionField⁄k] :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI := (baseToFunctionField c).toAlgebra
  KaehlerDifferential.mapOfRingHom (RingHom.id k) (X.germToFunctionField U).hom
    (germToFunctionField_comp_algebraMap c U)

variable (U : X.Opens) [Nonempty U]

theorem kaehlerToFunctionField_D (s : Γ(X, U)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := (baseToFunctionField c).toAlgebra
    kaehlerToFunctionField c U (KaehlerDifferential.D k Γ(X, U) s)
      = KaehlerDifferential.D k X.functionField ((X.germToFunctionField U).hom s) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI := (baseToFunctionField c).toAlgebra
  KaehlerDifferential.mapOfRingHom_D _ _ _ s

theorem kaehlerToFunctionField_smul (a : Γ(X, U))
    (η : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U; Ω[Γ(X, U)⁄k]) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := (baseToFunctionField c).toAlgebra
    kaehlerToFunctionField c U (a • η) = (X.germToFunctionField U).hom a • kaehlerToFunctionField c U η :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI := (baseToFunctionField c).toAlgebra
  KaehlerDifferential.mapOfRingHom_smul _ _ _ a η

theorem kaehlerToFunctionField_smul_D (a s : Γ(X, U)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := (baseToFunctionField c).toAlgebra
    kaehlerToFunctionField c U (a • KaehlerDifferential.D k Γ(X, U) s)
      = (X.germToFunctionField U).hom a • KaehlerDifferential.D k X.functionField ((X.germToFunctionField U).hom s) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI := (baseToFunctionField c).toAlgebra
  KaehlerDifferential.mapOfRingHom_smul_D _ _ _ a s

theorem kaehlerToFunctionField_map {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U)
    (η : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U; Ω[Γ(X, U)⁄k]) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
    kaehlerToFunctionField c V
        (KaehlerDifferential.mapOfRingHom (RingHom.id k) (Scheme.TwoAffineOpenCover.restrictAlgHom c h).toRingHom
          (RingHom.ext fun r => (Scheme.TwoAffineOpenCover.restrictAlgHom c h).commutes r) η)
      = kaehlerToFunctionField c U η := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
  letI := (baseToFunctionField c).toAlgebra
  have hcomp : (X.germToFunctionField V).hom.comp (Scheme.TwoAffineOpenCover.restrictAlgHom c h).toRingHom
      = (X.germToFunctionField U).hom :=
    RingHom.ext fun s => germToFunctionField_map (X := X) h s
  unfold kaehlerToFunctionField
  rw [KaehlerDifferential.mapOfRingHom_comp_apply _ _ _ _ _ _
    (h₃ := by rw [hcomp]; exact germToFunctionField_comp_algebraMap c U)]
  exact KaehlerDifferential.mapOfRingHom_congr hcomp _ _ η

end AlgebraicCurve

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

open AlgebraicCurve

variable {k : Type u} [Field k] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of k))
  [IsIntegral X] [Nonempty 𝒱.U0] [Nonempty 𝒱.U1] [Nonempty (𝒱.U0 ⊓ 𝒱.U1 : X.Opens)]

omit [Nonempty 𝒱.U1] in

theorem kaehlerToFunctionField_r0 (ω : Ω[(𝒱.cover c).A0⁄k]) :
    kaehlerToFunctionField c (𝒱.U0 ⊓ 𝒱.U1) ((𝒱.kaehlerSections c).r0 ω) = kaehlerToFunctionField c 𝒱.U0 ω :=
  kaehlerToFunctionField_map c inf_le_left ω

omit [Nonempty 𝒱.U0] in

theorem kaehlerToFunctionField_r1 (ω : Ω[(𝒱.cover c).A1⁄k]) :
    kaehlerToFunctionField c (𝒱.U0 ⊓ 𝒱.U1) ((𝒱.kaehlerSections c).r1 ω) = kaehlerToFunctionField c 𝒱.U1 ω :=
  kaehlerToFunctionField_map c inf_le_right ω

theorem kaehlerToFunctionField_fst_eq_snd_of_mem_H0 (ω : (𝒱.kaehlerSections c).H0) :
    kaehlerToFunctionField c 𝒱.U0 ω.val.1 = kaehlerToFunctionField c 𝒱.U1 ω.val.2 := by
  rw [← kaehlerToFunctionField_r0, ← kaehlerToFunctionField_r1]
  have h := (TwoChartCech.Sections.mem_H0_iff _ _).mp ω.2
  exact congrArg _ h

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end


