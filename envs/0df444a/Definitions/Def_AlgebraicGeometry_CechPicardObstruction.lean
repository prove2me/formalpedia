-- Prove2me | Definitions.Def_AlgebraicGeometry_CechPicardObstruction
-- name    : AlgebraicGeometry_CechPicardObstruction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/f6a9fa82-ddd4-5922-acb5-d0bba62cab23
-- title:
--   Čech trivialisations and Picard obstruction cocycles
-- statement:
--   For a scheme $Y$ and an open $W \subseteq Y$, `unitAutSection` assigns to a self-isomorphism $e$ of the unit module $\mathcal{O}_W$ on the open subscheme $W$ the section $e(1) \in \Gamma(Y,W)$, obtained by evaluating the component of $e$ at the top open of $W$ on $1$ and transporting along the canonical identification $\Gamma(W,\top) \cong \Gamma(Y,W)$. Given a finite ordered affine open cover $\mathcal{V}$ of $Y$ (index type a finite linearly ordered set, charts $V_a$ affine with $\bigvee_a V_a = \top$) and a module $\mathcal{M}$ on $Y$, a `CechTrivialisation` is a family of isomorphisms $\mathcal{M}|_{V_a} \cong \mathcal{O}_{V_a}$, restriction being pullback along the open immersion. From such a $\tau$ one gets: `restrict`, the induced isomorphism $\mathcal{M}|_W \cong \mathcal{O}_W$ for any $W \le V_a$; `transition`, for a strictly increasing pair $s = (a<b)$ the section $\tau.\mathrm{transition}\,s \in \Gamma(Y, V_a \cap V_b)$ obtained by applying `unitAutSection` to $\tau|_b \circ \tau|_a^{-1}$, i.e. the multiplicative Čech $1$-cochain of $\mathcal{M}$ in the chosen frames; and `comap`, a trivialisation of $h^*\mathcal{M}$ on the preimage cover $\mathcal{V}.\mathrm{comap}\,h$ for an affine morphism $h$.
--
--   In the `SmallExtension` section the standing data are a ring $B_1$, a field $k$, a module $V$ over both with a $B_1$-linear map $\iota_J : V \to B_1$, morphisms $f : X \to \operatorname{Spec} B_1$, $f_k : X_k \to \operatorname{Spec} k$ and $i : X_k \to X$. `IsFibreReading U W hW δ w`, for $W \le i^{-1}U$, asserts the existence of finitely many $v_j \in V$ and $s_j \in \Gamma(X,U)$ with $\sum_j \iota_J(v_j)\, s_j = \delta$ (the $\iota_J(v_j)$ acting through $B_1 \to \Gamma(X,U)$ determined by $f$) such that for every $\xi$ in the $k$-dual of $V$ one has $w(\xi) = \sum_j \xi(v_j) \cdot (s_j|_W)$, the restriction being of $i^\sharp s_j \in \Gamma(X_k, i^{-1}U)$; thus $w$ reads off, over $X_k$, a chosen presentation of $\delta$ as an element of $J\cdot\Gamma(X,U)$.
--
--   With $g : X_0 \to X$ and $i$ affine and $\mathcal{U}$ an ordered affine cover of $X$, `IsPicObstructionCocycle 𝓛₀ c`, for $c$ a $k$-linear map from the dual of $V$ to the $2$-cochains of $\mathcal{O}$ on $\mathcal{U}.\mathrm{comap}\,i$, asserts the existence of a trivialisation $\tau$ of $\mathcal{L}_0$ on $\mathcal{U}.\mathrm{comap}\,g$ and of sections $u_s, u'_s \in \Gamma(X, \mathcal{U}.\mathrm{inter}\,s)$ for each pair $s$ with $u_s u'_s = 1$, whose restrictions $g^\sharp u_s$ agree with $\tau.\mathrm{transition}\,s$, and such that for every triple $r$ the defect $u_{\partial_2 r}\, u_{\partial_0 r}\, u'_{\partial_1 r} - 1$ on $\mathcal{U}.\mathrm{inter}\,r$ is fibre-read by the $r$-component of $c$. Dually, `IsPicDeformationCocycle M φ₀ w` asserts the existence of a trivialisation $\tau$ of $M$ on $\mathcal{U}$ and of sections $e_a, e'_a \in \Gamma(X, \mathcal{U}.U_a)$ with $e_a e'_a = 1$, such that $g^\sharp e_a$ is the unit comparing the chart-wise trivialisation of $g^*M$ coming from $\tau$ with the given global trivialisation $\varphi_0 : g^*M \cong \mathcal{O}_{X_0}$, and such that for each pair $s$ the defect $\tau.\mathrm{transition}\,s \cdot e'_{s_0} \cdot e_{s_1} - 1$ is fibre-read by the $s$-component of the $1$-cochain $w$. Both are predicates on a choice of cover, trivialisation and multiplicative lifts, not on cohomology classes; the unit conditions are carried as equations $uu' = 1$ rather than through units groups.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used here (`SheafOfModules.unit`, `Scheme.Modules.pullback` with its composition and congruence isomorphisms, affine morphisms, preimages of opens); the ordered affine cover with its alternating Čech cochains, the notion of a chosen Čech trivialisation of a module with its transition sections, and the three `SmallExtension` predicates are the project's own — Mathlib has no obstruction theory for lifting invertible modules along a small extension.
--
--   **Where it is used.** These definitions fix the Čech vocabulary in which lifting an invertible module along a small thickening $X_0 \subseteq X$ with ideal presented by $\iota_J : V \to B_1$ is expressed: the obstruction is recorded as a $V$-valued $2$-cochain on the fibre $X_k$ built from multiplicative lifts of transition functions, and deformations of a trivialised lift as the corresponding $1$-cochains. They feed the relative Picard functor and Néron model infrastructure of the project.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_CechPicardObstruction.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Scheme.Modules

variable {Y : Scheme.{u}}

def unitAutSection (W : Y.Opens)
    (e : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf) :
    Γ(Y, W) :=
  W.topIso.hom ((e.hom.val.app (op ⊤)).hom (1 : (W : Scheme.{u}).presheaf.obj (op ⊤)))

abbrev CechTrivialisation (𝒱 : Y.OrderedAffineCover) (𝓜 : Y.Modules) : Type u :=
  ∀ a : 𝒱.ι, (Scheme.Modules.pullback (𝒱.U a).ι).obj 𝓜 ≅ SheafOfModules.unit ((𝒱.U a : Scheme.{u})).ringCatSheaf

namespace CechTrivialisation

variable {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules}

def restrict (τ : CechTrivialisation 𝒱 𝓜) {a : 𝒱.ι} {W : Y.Opens} (h : W ≤ 𝒱.U a) :
    (Scheme.Modules.pullback W.ι).obj 𝓜 ≅ SheafOfModules.unit ((W : Scheme.{u})).ringCatSheaf :=
  ((Scheme.Modules.pullbackCongr (Y.homOfLE_ι h)).app 𝓜).symm ≪≫
    ((Scheme.Modules.pullbackComp (Y.homOfLE h) (𝒱.U a).ι).app 𝓜).symm ≪≫
    (Scheme.Modules.pullback (Y.homOfLE h)).mapIso (τ a) ≪≫
    Scheme.Modules.pullbackUnitIso (Y.homOfLE h)

def transition (τ : CechTrivialisation 𝒱 𝓜) (s : 𝒱.Idx 1) : Γ(Y, 𝒱.inter s) :=
  unitAutSection (𝒱.inter s) ((τ.restrict (𝒱.inter_le s 0)).symm ≪≫ τ.restrict (𝒱.inter_le s 1))

def comap (τ : CechTrivialisation 𝒱 𝓜) {Y' : Scheme.{u}} (h : Y' ⟶ Y) [IsAffineHom h] :
    CechTrivialisation (𝒱.comap h) ((Scheme.Modules.pullback h).obj 𝓜) := fun a =>
  ((Scheme.Modules.pullbackComp (h ⁻¹ᵁ 𝒱.U a).ι h).app 𝓜) ≪≫
    ((Scheme.Modules.pullbackCongr (morphismRestrict_ι h (𝒱.U a)).symm).app 𝓜) ≪≫
    ((Scheme.Modules.pullbackComp (h ∣_ 𝒱.U a) (𝒱.U a).ι).app 𝓜).symm ≪≫
    (Scheme.Modules.pullback (h ∣_ 𝒱.U a)).mapIso (τ a) ≪≫
    Scheme.Modules.pullbackUnitIso (h ∣_ 𝒱.U a)

end CechTrivialisation

end Scheme.Modules

namespace SmallExtension

open Scheme.TwoAffineOpenCover

variable {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
variable (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ιJ : V →ₗ[B₁] B₁)
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
variable {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X)

def IsFibreReading (U : X.Opens) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) (δ : Γ(X, U))
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W) : Prop :=
  letI := algebraOfHom f U
  ∃ (n : ℕ) (v : Fin n → V) (s : Fin n → Γ(X, U)),
    (∑ j, algebraMap B₁ (X.presheaf.obj (op U)) (ιJ (v j)) * s j) = δ ∧
      ∀ ξ : Module.Dual k V,
        w ξ = ∑ j, ξ (v j) • (OModulePresheaf.unit fk).res hW
          (show (OModulePresheaf.unit fk).obj (i ⁻¹ᵁ U) from (i.app U).hom (s j))

variable {X₀ : Scheme.{u}} (g : X₀ ⟶ X) [IsAffineHom g] [IsAffineHom i]
variable (𝒰 : X.OrderedAffineCover)

def IsPicObstructionCocycle (𝓛₀ : X₀.Modules)
    (c : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 2) : Prop :=
  ∃ (τ : Scheme.Modules.CechTrivialisation (𝒰.comap g) 𝓛₀)
    (u u' : ∀ s : 𝒰.Idx 1, Γ(X, 𝒰.inter s)),
    (∀ s : 𝒰.Idx 1,
      (X₀.presheaf.map (homOfLE (𝒰.comap_inter_le g s)).op).hom ((g.app (𝒰.inter s)).hom (u s)) = τ.transition s) ∧
    (∀ s : 𝒰.Idx 1, u s * u' s = 1) ∧
    ∀ r : 𝒰.Idx 2,
      IsFibreReading V ιJ f fk i (𝒰.inter r) ((𝒰.comap i).inter r) (𝒰.comap_inter_le i r)
        ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 2)).op).hom (u (𝒰.face r 2)) *
            (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (u (𝒰.face r 0)) *
            (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (u' (𝒰.face r 1)) - 1)
        ((LinearMap.proj r).comp c)

def IsPicDeformationCocycle (M : X.Modules)
    (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1) : Prop :=
  ∃ (τ : Scheme.Modules.CechTrivialisation 𝒰 M) (e e' : ∀ a : 𝒰.ι, Γ(X, 𝒰.U a)),
    (∀ a : 𝒰.ι, e a * e' a = 1) ∧
    (∀ a : 𝒰.ι,
      (g.app (𝒰.U a)).hom (e a) =
        Scheme.Modules.unitAutSection ((𝒰.comap g).U a)
          ((τ.comap g a).symm ≪≫
            ((Scheme.Modules.pullback ((𝒰.comap g).U a).ι).mapIso φ₀ ≪≫
              Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι))) ∧
    ∀ s : 𝒰.Idx 1,
      IsFibreReading V ιJ f fk i (𝒰.inter s) ((𝒰.comap i).inter s) (𝒰.comap_inter_le i s)
        (τ.transition s *
            (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (e' (s.1 0)) *
            (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (e (s.1 1)) - 1)
        ((LinearMap.proj s).comp w)

end SmallExtension

end AlgebraicGeometry

end


