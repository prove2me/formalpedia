-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesTildePullback
-- name    : AlgebraicGeometry_ModulesTildePullback
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/12c57e0f-671a-5f46-bb07-9806d111e3e4
-- title:
--   Pullback along `Spec` of a tilde module, via base change
-- statement:
--   Let $\varphi\colon R\to S$ be a morphism of commutative rings (objects of `CommRingCat`), and write $f=\mathrm{Spec}\,\varphi\colon \mathrm{Spec}\,S\to\mathrm{Spec}\,R$. Two comparison isomorphisms are constructed. First, `Scheme.Modules.pushforwardSpecCompΓIso` is a natural isomorphism
--   $$\text{(pushforward along }f)\ \text{followed by}\ \Gamma_{\mathrm{Spec}\,R}\;\cong\;\Gamma_{\mathrm{Spec}\,S}\ \text{followed by restriction of scalars along }\varphi,$$
--   between functors from $\mathcal O_{\mathrm{Spec}\,S}$-modules to $R$-modules, where $\Gamma$ denotes `moduleSpecΓFunctor`, the global-sections functor on modules over an affine scheme composed with the identification of $\Gamma(\mathrm{Spec}\,R,\mathcal O)$ with $R$ through `StructureSheaf.globalSectionsIso`. On each $\mathcal O_{\mathrm{Spec}\,S}$-module $N$ the component is the identity map of underlying additive groups; the content is that the $R$-action obtained from the global sections of $f_*N$ agrees with the $R$-action on $\Gamma(\mathrm{Spec}\,S,N)$ obtained by restricting the $S$-action along $\varphi$, which rests on the naturality of the isomorphism $\Gamma\circ\mathrm{Spec}\cong\mathrm{id}$ in $\varphi$.
--
--   Second, `tilde.functorCompPullbackSpecIso` is a natural isomorphism of functors from $R$-modules to $\mathcal O_{\mathrm{Spec}\,S}$-modules,
--   $$M\mapsto f^{*}\widetilde M\quad\cong\quad M\mapsto \widetilde{S\otimes_R M},$$
--   where $\widetilde{\;\cdot\;}$ is Mathlib's `tilde` and $S\otimes_R-$ is `ModuleCat.extendScalars`. It is the canonical isomorphism supplied by uniqueness of left adjoints: the left-hand functor is left adjoint to the composite of pushforward along $f$ with global sections over $R$ (composing the tilde–$\Gamma$ adjunction over $R$ with $f^*\dashv f_*$), and the right-hand functor is left adjoint to the same functor (composing extension–restriction of scalars with the tilde–$\Gamma$ adjunction over $S$, transported along the first isomorphism above). Its component at a module $M$ is named `tilde.pullbackSpecIso`, giving $f^{*}\widetilde M\cong\widetilde{S\otimes_R M}$, with a lemma identifying the functorial isomorphism's component with it and a lemma recording naturality of its forward direction in $M$.
--
--   **Relation to Mathlib.** Mathlib supplies the ingredients — `tilde` with `tilde.adjunction`, `Scheme.Modules.pullback`/`pushforward` with `Scheme.Modules.pullbackPushforwardAdjunction`, and `ModuleCat.extendRestrictScalarsAdj` — but not this comparison between pullback on an affine scheme and extension of scalars; both isomorphisms here are the project's own.
--
--   **Where it is used.** These isomorphisms are the affine base-change dictionary used in the geometric parts of the argument: they let statements about sections of quasi-coherent sheaves over affine opens after a base change $R\to S$ be rewritten as statements about $S\otimes_R-$ of the corresponding modules, for instance in recognising the sheaf attached to a finite projective module as locally free.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesTildePullback.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace AlgebraicGeometry

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

set_option backward.isDefEq.respectTransparency false in

def Scheme.Modules.pushforwardSpecCompΓIso :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents
    (fun N => LinearEquiv.toModuleIso
      (X₁ := (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).obj N)
      (X₂ := (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom).obj N)
      { __ := AddEquiv.refl _
        map_smul' := fun r m => by
          change (ModuleCat.restrictScalars (StructureSheaf.globalSectionsIso R).hom.hom).obj _ at m
          erw [ModuleCat.restrictScalars.smul_def, ModuleCat.restrictScalars.smul_def]
          erw [ModuleCat.restrictScalars.smul_def, ModuleCat.restrictScalars.smul_def]
          simp only [AddEquiv.toFun_eq_coe, AddEquiv.refl_apply, RingHom.id_apply]
          have h1 : (Limits.initialOpOfTerminal Limits.isTerminalTop).to (op ⊤) =
              𝟙 (op (⊤ : (Spec (.of R)).Opens)) :=
            (Limits.initialOpOfTerminal Limits.isTerminalTop).hom_ext _ _
          have h2 : (Limits.initialOpOfTerminal Limits.isTerminalTop).to (op ⊤) =
              𝟙 (op (⊤ : (Spec (.of S)).Opens)) :=
            (Limits.initialOpOfTerminal Limits.isTerminalTop).hom_ext _ _
          simp only [h1, h2, CategoryTheory.Functor.map_id, RingCat.hom_id, RingHom.id_apply]
          congr 1
          have key := congrArg (fun ψ : R ⟶ Γ(Spec S, ⊤) => ψ.hom r) (Scheme.ΓSpecIso_inv_naturality φ)
          simp only [Scheme.ΓSpecIso_inv, StructureSheaf.globalSectionsIso_hom] at key
          exact key.symm })
    (fun f => by ext; rfl)

def tilde.functorCompPullbackSpecIso :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S :=
  Adjunction.leftAdjointUniq
    ((tilde.adjunction (R := R)).comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)))
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))).ofNatIsoRight
      (Scheme.Modules.pushforwardSpecCompΓIso φ).symm)

def tilde.pullbackSpecIso (M : ModuleCat.{u} R) :
    (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ≅
      tilde ((ModuleCat.extendScalars φ.hom).obj M) :=
  (tilde.functorCompPullbackSpecIso φ).app M

@[simp] theorem tilde.functorCompPullbackSpecIso_app (M : ModuleCat.{u} R) :
    (tilde.functorCompPullbackSpecIso φ).app M = tilde.pullbackSpecIso φ M := rfl

theorem tilde.pullbackSpecIso_hom_naturality {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    (Scheme.Modules.pullback (Spec.map φ)).map ((tilde.functor R).map f) ≫
        (tilde.pullbackSpecIso φ M').hom =
      (tilde.pullbackSpecIso φ M).hom ≫ (tilde.functor S).map ((ModuleCat.extendScalars φ.hom).map f) :=
  (tilde.functorCompPullbackSpecIso φ).hom.naturality f

end AlgebraicGeometry

end


