-- Prove2me | Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
-- name    : ModularCurve_DRResolvedModelPackageLevel
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/ca3641f2-a0d5-51f0-8da4-e9120f80c796
-- title:
--   Resolved Deligne–Rapoport model package at level Γ0​(N0​q)
-- statement:
--   Throughout, $N_0\ge 1$ and $q$ is a prime with $q\nmid N_0$, $R=R_q$ is the subring of $\mathbb{Q}$ of fractions whose denominator is coprime to $q$, and $\mathfrak{X}$ is a `DRModelPackageLevel` for $(N_0,q)$, i.e. a package of data and properties attached to the Igusa scheme $X$ of level $N_0q$ over $\operatorname{Spec}R$ (its smooth locus, Atkin–Lehner involution, degeneracy components $c_0,c_1$ of the special fibre, and so on). Two helpers set up the base change: for a ring map $\rho\colon R\to O$, `DRLevel.XO ρ` is the fibre product $X\times_{\operatorname{Spec}R}\operatorname{Spec}O$, and `DRLevel.bcMap ρ toκ`, for $toκ\colon O\to\kappa$, is the induced map from $X\times_{\operatorname{Spec}R}\operatorname{Spec}\kappa$ to $X\times_{\operatorname{Spec}R}\operatorname{Spec}O$. The combinatorial helper `chainPos width n d` sends $d=0$ to the first strict transform, $0<d<\mathrm{width}(n)$ to the $(d-1)$-st exceptional curve over the node $n$, and $d\ge\mathrm{width}(n)$ to the second strict transform; here the index type of components is $\mathrm{Fin}\,2\sqcup\coprod_n \mathrm{Fin}(\mathrm{width}(n)-1)$.
--
--   The structure `DRResolvedModelPackageLevel`, for $O$, $\rho\colon R\to O$, an algebraically closed field $\kappa$ of characteristic $q$ and $toκ\colon O\to\kappa$, carries a scheme $Y$ with morphisms $\mathrm{toBase}\colon Y\to\operatorname{Spec}O$ and $\mathrm{toDR}\colon Y\to X\times_R\operatorname{Spec}O$ compatible over $\operatorname{Spec}O$, with $Y$ integral and locally Noetherian, $\mathrm{toBase}$ proper and flat and $\mathrm{toDR}$ proper. Over the locus where $q$ vanishes (the complement of the preimage of the basic open $D(q)\subseteq\operatorname{Spec}O$) all stalks of $Y$ are required to be regular local of Krull dimension at most $2$; $\mathrm{toDR}$ is required to restrict to an isomorphism over the preimage of $\mathfrak{X}$'s smooth locus and over the preimage of $D(q)$.
--
--   The special fibre is described by data rather than constructed: a finite type `node` with an equivalence to the points of the scheme-theoretic intersection $c_0\times_{X_\kappa}c_1$ of the two components of the fibre over $\kappa$, widths $\mathrm{width}(n)\ge 1$ (data, not computed from a formula), and a family `comp` of ideal sheaf data indexed by $\mathrm{Fin}\,2\sqcup\coprod_n\mathrm{Fin}(\mathrm{width}(n)-1)$, each invertible in the sense of `Scheme.IdealSheafData.IsInvertible` (locally generated on affine basic opens by a non-zerodivisor), with integral closed subscheme and support inside the $q=0$ locus, and whose product has ideal $(q)$ on every affine open. Chosen points $\eta_v$ are required to be generic points of the respective components: on some affine open the germ of the ideal of $\mathrm{comp}\,v$ generates the maximal ideal of the stalk at $\eta_v$ while the germs of all other component ideals are the unit ideal; conversely every point of the $q=0$ locus whose stalk has Krull dimension at most $1$ is one of the $\eta_v$. For $i\in\mathrm{Fin}\,2$ the base change to $\kappa$ of the $i$-th strict transform is required to be isomorphic over $\operatorname{Spec}\kappa$ to the level-$N_0$ Igusa fibre, compatibly with $\mathfrak{X}$'s component $c_i$ followed by `bcMap` and with $\mathrm{toDR}$; each exceptional component is required to be supported over the single image point of the corresponding node, and its base change to $\kappa$ to be isomorphic over $\kappa$ to the curve of a `CurveModel` with function field $\kappa(t)$. Incidence is recorded by points $\mathrm{edgePt}\,n\,d$ for $d\in\mathrm{Fin}(\mathrm{width}(n))$: the assignment is injective, $\mathrm{edgePt}\,n\,d$ lies in the supports of the components $\mathrm{chainPos}\,n\,d$ and $\mathrm{chainPos}\,n\,(d+1)$ and maps to the image of the node $n$, every point lying on two distinct components is such an edge point with the corresponding pair of chain positions, and at each edge point the germs of the two ideals together generate the maximal ideal (transversality). Finally there is an open $\mathrm{smoothOffEdges}$ which is smooth of relative dimension $1$ over $\operatorname{Spec}O$ and contains every point that is not an edge point.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used ($\mathrm{Spec}$, pullbacks, `IdealSheafData`, `IsProper`, `Flat`, `IsIntegral`, `IsLocallyNoetherian`, `IsRegularLocalRing`, `ringKrullDim`, `SmoothOfRelativeDimension`); the invertibility condition on ideal sheaf data, the component index type `X0MqComponents`, the curve-model notion and the model package itself are the project's own.
--
--   **Where it is used.** The structure axiomatises the minimal regular model of $X_0(N_0q)$ over a base $O$ in which $q$ is not invertible, obtained from the Deligne–Rapoport model by resolving the crossings of the two copies of $X_0(N_0)_\kappa$ into chains of rational curves. Its component data (widths, chain incidences, the identification of the two strict transforms with the level-$N_0$ fibre) is what feeds the computation of the component group of the Néron model of $J_0(N_0q)$ at $q$ used in level lowering at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_DRResolvedModelPackageLevel.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_AlgebraicCurve_RelCartier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ModularCurve.IgusaScheme

namespace ModularCurve

attribute [local instance] DRModelPackageLevel.neZero_mul

def DRResolvedModelPackageLevel.chainPos {node : Type} (width : node → ℕ) (n : node) (d : ℕ) : X0MqComponents width :=
  if h0 : d = 0 then Sum.inl 0
  else if h : d < width n then Sum.inr ⟨n, ⟨d - 1, by omega⟩⟩
  else Sum.inl 1

namespace DRLevel

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime]

abbrev XO {O : Type} [CommRing O] (ρ : R q →+* O) : Scheme.{0} :=
  pullback (toBase N₀ q) (Spec.map (CommRingCat.ofHom ρ))

def bcMap {O : Type} [CommRing O] (ρ : R q →+* O) {κ : Type} [CommRing κ] (toκ : O →+* κ) :
    fibre (N₀ := N₀) (toκ.comp ρ) ⟶ XO (N₀ := N₀) ρ :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom toκ)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp])

end DRLevel

open DRLevel

structure DRResolvedModelPackageLevel (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] (ρ : R q →+* O)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ) where

  Y : Scheme.{0}
  toBase : Y ⟶ Spec (CommRingCat.of O)
  toDR : Y ⟶ XO (N₀ := N₀) ρ
  toDR_over : toDR ≫ pullback.snd _ _ = toBase
  [toDR_proper : IsProper toDR]
  [isProper : IsProper toBase]
  [flat : Flat toBase]
  [isIntegral : IsIntegral Y]
  [isLocallyNoetherian : IsLocallyNoetherian Y]

  regular : ∀ y : Y, y ∉ toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) →
    IsRegularLocalRing (Y.presheaf.stalk y)
  stalk_dim_le_two : ∀ y : Y, y ∉ toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) →
    ringKrullDim (Y.presheaf.stalk y) ≤ 2

  toDR_iso_smoothLocus : IsIso (toDR ∣_ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρ)) ⁻¹ᵁ 𝔛.smoothLocus))
  toDR_iso_generic : IsIso (toDR ∣_ (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρ)) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)))

  node : Type
  [node_fintype : Fintype node]
  [node_deq : DecidableEq node]
  width : node → ℕ
  one_le_width : ∀ n, 1 ≤ width n

  nodeEquiv : node ≃ ↥(pullback (𝔛.comp κ (toκ.comp ρ) 0) (𝔛.comp κ (toκ.comp ρ) 1))
  comp : X0MqComponents width → Y.IdealSheafData
  comp_isInvertible : ∀ v, (comp v).IsInvertible
  comp_integral : ∀ v, IsIntegral (comp v).subscheme
  comp_support : ∀ v (y : Y), y ∈ (comp v).support →
    y ∉ toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)
  comp_prod : ∀ U : Y.affineOpens, (∏ v, comp v).ideal U = Ideal.span {((q : ℕ) : Γ(Y, U))}
  η : X0MqComponents width → Y
  η_not_mem : ∀ v, η v ∉ toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)
  η_stalk : ∀ v, ∃ (U : Y.affineOpens) (hU : η v ∈ (U : Y.Opens)),
    Ideal.map (Y.presheaf.germ (U : Y.Opens) (η v) hU).hom ((comp v).ideal U) =
        IsLocalRing.maximalIdeal (Y.presheaf.stalk (η v)) ∧
      ∀ w, w ≠ v → Ideal.map (Y.presheaf.germ (U : Y.Opens) (η v) hU).hom ((comp w).ideal U) = ⊤
  codim : ∀ y : Y, y ∉ toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) →
    ringKrullDim (Y.presheaf.stalk y) ≤ 1 → ∃ v, y = η v

  strict_iso : ∀ i : Fin 2,
    ∃ e : pullback ((comp (Sum.inl i)).subschemeι ≫ toBase) (Spec.map (CommRingCat.ofHom toκ)) ⟶ fibre0 (N₀ := N₀) (toκ.comp ρ),
      IsIso e ∧ e ≫ pullback.snd _ _ = pullback.snd _ _ ∧
        e ≫ 𝔛.comp κ (toκ.comp ρ) i ≫ bcMap ρ toκ = pullback.fst _ _ ≫ (comp (Sum.inl i)).subschemeι ≫ toDR

  exc_image : ∀ (n : node) (i : Fin (width n - 1)), ∀ y ∈ (comp (Sum.inr ⟨n, i⟩)).support,
    toDR.base y = (pullback.fst (𝔛.comp κ (toκ.comp ρ) 0) (𝔛.comp κ (toκ.comp ρ) 1) ≫ 𝔛.comp κ (toκ.comp ρ) 0 ≫
      bcMap ρ toκ).base (nodeEquiv n)

  edgePt : (n : node) → Fin (width n) → Y
  edgePt_injective : Function.Injective (fun e : Σ n, Fin (width n) => edgePt e.1 e.2)
  edgePt_mem : ∀ (n : node) (d : Fin (width n)),
    edgePt n d ∈ ((comp (DRResolvedModelPackageLevel.chainPos width n d)).support : Set Y) ∩
      ((comp (DRResolvedModelPackageLevel.chainPos width n (d + 1))).support : Set Y)
  edgePt_over : ∀ (n : node) (d : Fin (width n)),
    toDR.base (edgePt n d) = (pullback.fst (𝔛.comp κ (toκ.comp ρ) 0) (𝔛.comp κ (toκ.comp ρ) 1) ≫ 𝔛.comp κ (toκ.comp ρ) 0 ≫
      bcMap ρ toκ).base (nodeEquiv n)
  edgePt_exhaust : ∀ v w, v ≠ w → ∀ y ∈ ((comp v).support : Set Y) ∩ ((comp w).support : Set Y),
    ∃ (n : node) (d : Fin (width n)), y = edgePt n d ∧
      ((v = DRResolvedModelPackageLevel.chainPos width n d ∧ w = DRResolvedModelPackageLevel.chainPos width n (d + 1)) ∨
       (w = DRResolvedModelPackageLevel.chainPos width n d ∧ v = DRResolvedModelPackageLevel.chainPos width n (d + 1)))
  edgePt_transversal : ∀ (n : node) (d : Fin (width n)), ∃ (U : Y.affineOpens) (hU : edgePt n d ∈ (U : Y.Opens)),
    Ideal.map (Y.presheaf.germ (U : Y.Opens) (edgePt n d) hU).hom
        ((comp (DRResolvedModelPackageLevel.chainPos width n d)).ideal U ⊔
          (comp (DRResolvedModelPackageLevel.chainPos width n (d + 1))).ideal U) =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk (edgePt n d))

  exc_rational : ∀ (n : node) (i : Fin (width n - 1)),
    ∃ (M : AlgebraicCurve.CurveModel κ (RatFunc κ))
      (e : M.C ⟶ pullback ((comp (Sum.inr ⟨n, i⟩)).subschemeι ≫ toBase) (Spec.map (CommRingCat.ofHom toκ))),
      IsIso e ∧ e ≫ pullback.snd _ _ = M.toBase

  smoothOffEdges : Y.Opens
  [smoothOffEdges_smooth : SmoothOfRelativeDimension 1 (smoothOffEdges.ι ≫ toBase)]
  mem_smoothOffEdges : ∀ y : Y, (∀ (n : node) (d : Fin (width n)), y ≠ edgePt n d) → y ∈ smoothOffEdges

attribute [instance] DRResolvedModelPackageLevel.toDR_proper DRResolvedModelPackageLevel.isProper DRResolvedModelPackageLevel.flat
  DRResolvedModelPackageLevel.isIntegral DRResolvedModelPackageLevel.isLocallyNoetherian DRResolvedModelPackageLevel.node_fintype
  DRResolvedModelPackageLevel.node_deq DRResolvedModelPackageLevel.smoothOffEdges_smooth

end ModularCurve

end


