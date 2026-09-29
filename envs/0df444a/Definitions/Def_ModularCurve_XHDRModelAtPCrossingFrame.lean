-- Prove2me | Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
-- name    : ModularCurve_XHDRModelAtPCrossingFrame
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/38d3e32d-4871-5780-bd2c-05b998d8807e
-- title:
--   Crossing frame for the level-ΓH​(M) model after base change
-- statement:
--   Working over the base ring `R p` and with a subgroup $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ together with the hypothesis `hj` that $j$ lies in the $q$-expansion function field of full level, the first group of declarations sets up base change of the two-chart integral model `X p Γ hj` of level $\Gamma$. For a ring map $\rho_O\colon$ `R p` $\to O$, `XO Γ hj ρO` is the fibre product of the structure morphism `toBase p Γ hj` with $\operatorname{Spec}(\rho_O)$, and `XO.toBase` is its second projection to $\operatorname{Spec} O$. Given in addition $t\colon O \to \kappa$ and $t'\colon$ `R p` $\to \kappa$ with $t\circ\rho_O = t'$, `bcMap` is the comparison morphism from the fibre `fibre t'` to `XO Γ hj ρO` induced by the identity on the model and $\operatorname{Spec}(t)$ on the base; `bcMap_fst` and `bcMap_snd` record that it commutes with the first projection and that its composite with the second projection is the second projection followed by $\operatorname{Spec}(t)$. For a point $x$ of `XO Γ hj ρO` and $o \in O$, `baseGerm` is the germ at $x$ of the global section pulled back from $o$ along `XO.toBase`, an element of the stalk at $x$.
--
--   The second group fixes a model $\mathfrak{X} :$ `XHDRModelAtP p M H hpM hj`, a valuation subring $A \subseteq \overline{\mathbb{Q}}$ lying over $p$ with algebraically closed residue field of characteristic $p$, a structure map $\rho$ to $A$ compatible with $\overline{\mathbb{Q}}$, and $\rho_O, t$ with $t\circ\rho_O$ equal to the reduction of $\rho$. For $n$ in the fibre product of the two component immersions `𝔛.comp A hA ρ hρ 0` and `… 1`, `crossingPt` is the image of $n$ in `XO (ΓM M H) hj ρO` under the first projection followed by the zeroth component immersion and then `bcMap`; `ξinf` and `ξzero` are the images of the generic point of the curve `(𝔛.Mfib A hA ρ hρ).C` under `efib` followed by the zeroth, respectively first, component immersion and then `bcMap`. Finally, `efib_genericPoint_specializes` asserts that the image under `efib` of that generic point specialises to every point $c$ of the level-`ΓN p M H hpM` fibre over the reduction of $\rho$, `efib` being an isomorphism.
--
--   **Relation to Mathlib.** Mathlib supplies the scheme-theoretic fibre products, germs of sections, generic points and the specialisation order used here; the base-change scheme `XO`, the comparison morphism `bcMap` and the distinguished points of the crossing frame are project-specific vocabulary built from them.
--
--   **Where it is used.** These abbreviations are the shared vocabulary for the local analysis of the level-$\Gamma_H(M)$ Deligne–Rapoport model at a crossing point of its special fibre in characteristic $p$, the $\Gamma_H(M)$ counterpart of the level-$p$ crossing frame imported from `ModularCurve_DRModelPackageCrossingFrame`. They feed the study of the component structure and of the character group attached to the special fibre, which underlies the level-lowering step of the Frey–Serre–Ribet argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_XHDRModelAtPCrossingFrame.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve
open scoped MatrixGroups

noncomputable section

namespace ModularCurve

namespace XHDRLevel

variable {p : ℕ} (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

abbrev XO {O : Type} [CommRing O] (ρO : R p →+* O) : Scheme.{0} :=
  pullback (toBase p Γ hj) (Spec.map (CommRingCat.ofHom ρO))

abbrev XO.toBase {O : Type} [CommRing O] (ρO : R p →+* O) : XO Γ hj ρO ⟶ Spec (CommRingCat.of O) :=
  pullback.snd _ _

def bcMap {O : Type} [CommRing O] (ρO : R p →+* O) {κ : Type} [CommRing κ] (toκ : O →+* κ)
    {toκ' : R p →+* κ} (h : toκ.comp ρO = toκ') :
    fibre (Γ := Γ) (hj := hj) toκ' ⟶ XO Γ hj ρO :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom toκ)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h])

@[reassoc (attr := simp)]
theorem bcMap_fst {O : Type} [CommRing O] (ρO : R p →+* O) {κ : Type} [CommRing κ] (toκ : O →+* κ)
    {toκ' : R p →+* κ} (h : toκ.comp ρO = toκ') :
    bcMap Γ hj ρO toκ h ≫ pullback.fst _ _ = pullback.fst _ _ := by
  rw [bcMap, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
theorem bcMap_snd {O : Type} [CommRing O] (ρO : R p →+* O) {κ : Type} [CommRing κ] (toκ : O →+* κ)
    {toκ' : R p →+* κ} (h : toκ.comp ρO = toκ') :
    bcMap Γ hj ρO toκ h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ) := by
  rw [bcMap, pullback.map, pullback.lift_snd]

variable {Γ hj}

abbrev baseGerm {O : Type} [CommRing O] (ρO : R p →+* O) (x : ↥(XO Γ hj ρO)) (o : O) : (XO Γ hj ρO).presheaf.stalk x :=
  (XO Γ hj ρO).presheaf.germ ⊤ x trivial
    ((XO.toBase Γ hj ρO).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o))

end XHDRLevel

open XHDRLevel

namespace XHDRModelAtP

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
  (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
  {O : Type} [CommRing O] (ρO : R p →+* O)
  (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)

abbrev crossingPt (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) : ↥(XO (ΓM M H) hj ρO) :=
  (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n

abbrev ξinf : ↥(XO (ΓM M H) hj ρO) :=
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral
  (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint (𝔛.Mfib A hA ρ hρ).C)

abbrev ξzero : ↥(XO (ΓM M H) hj ρO) :=
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral
  (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint (𝔛.Mfib A hA ρ hρ).C)

omit [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] in

theorem efib_genericPoint_specializes [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (c : ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) :
    letI := (𝔛.Mfib A hA ρ hρ).isIntegral
    (𝔛.efib A hA ρ hρ).base (genericPoint (𝔛.Mfib A hA ρ hρ).C) ⤳ c := by
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral
  have hc : (𝔛.efib A hA ρ hρ).base ((inv (𝔛.efib A hA ρ hρ)).base c) = c := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  rw [← hc]
  exact (genericPoint_specializes _).map (Scheme.Hom.continuous _)

end XHDRModelAtP

end ModularCurve

end


