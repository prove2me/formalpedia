-- Prove2me | Definitions.Def_ModularCurve_DRResolvedModelPackageV4
-- name    : ModularCurve_DRResolvedModelPackageV4
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/cdd65d0b-db49-5749-ab9f-d6f9bb93cd50
-- title:
--   Resolved Deligne–Rapoport model packages for X0​(p)
-- statement:
--   Fix a prime $p$. The module defines two helpers and one structure. `DRResolvedModelPackage.chainPos` sends a width function $w\colon\mathrm{node}\to\mathbb N$, a node $n$ and $d\in\mathbb N$ to an element of `X0MqComponents w` $=\mathrm{Fin}\,2\sqcup\Sigma_x\,\mathrm{Fin}(w(x)-1)$: the value is $\mathrm{inl}\,0$ for $d=0$, $\mathrm{inr}(n,d-1)$ for $0<d<w(n)$, and $\mathrm{inl}\,1$ otherwise, so it walks the chain $\mathrm{inl}\,0,(n,0),\dots,(n,w(n)-2),\mathrm{inl}\,1$. `DRModel.baseChangeMap` associates to a ring homomorphism $\mathrm{to}\kappa\colon O\to\kappa$ the morphism $\mathfrak X_{\kappa}\to\mathfrak X_{O}$ between base changes of `DRModel.toBase p` induced by the identity on the model and $\operatorname{Spec}\mathrm{to}\kappa$, using uniqueness of ring maps out of $\mathbb Z$.
--
--   Given a `DRModelPackage` $\mathfrak X$ for $p$, a commutative ring $O$, an algebraically closed field $\kappa$ of characteristic $p$ and $\mathrm{to}\kappa\colon O\to\kappa$, the structure `DRResolvedModelPackage` bundles: an integral, locally Noetherian scheme $Y$, proper and flat over $\operatorname{Spec}O$, with a proper morphism $\mathrm{toDR}$ to $\mathfrak X\times_{\mathbb Z}\operatorname{Spec}O$ over $\operatorname{Spec}O$; regularity and $\operatorname{Kdim}\le 2$ of all stalks at points outside the preimage of $D(p)\subseteq\operatorname{Spec}O$; $\mathrm{toDR}$ an isomorphism over $\mathfrak X$'s smooth locus and over $D(p)$. The special fibre is presented combinatorially: a finite type $\mathrm{node}$ in bijection with the points of $\mathfrak X_\kappa$'s component intersection $\mathrm{compInf}\times\mathrm{compZero}$, widths $w(n)\ge 1$, and a family $\mathrm{comp}_v$ of ideal sheaf data indexed by `X0MqComponents w`, each invertible in the sense of `IsInvertible` and with integral subscheme, supported over $p$, with $\prod_v\mathrm{comp}_v$ the ideal $(p)$ on every affine open. Further fields give generic points $\eta_v$ where $\mathrm{comp}_v$ germs to the maximal ideal and the others to the unit ideal, exhaust all points over $p$ of stalk dimension $\le 1$; identify the $\kappa$-fibres of $\mathrm{comp}_{\mathrm{inl}\,0},\mathrm{comp}_{\mathrm{inl}\,1}$ with $\mathfrak X$'s two rational components compatibly with $\mathrm{toDR}$; force each exceptional $\mathrm{comp}_{(n,i)}$ to lie over the crossing point $\mathrm{nodeEquiv}\,n$ and to have $\kappa$-fibre a curve model with function field $\kappa(t)$; provide injectively indexed points $\mathrm{edgePt}(n,d)$ lying on $\mathrm{comp}_{\mathrm{chainPos}(n,d)}$ and $\mathrm{comp}_{\mathrm{chainPos}(n,d+1)}$, over $\mathrm{nodeEquiv}\,n$, exhausting all pairwise intersections of components and transversal there (the germ of the sum of the two ideals is the maximal ideal); and an open $\mathrm{smoothOffEdges}$, smooth of relative dimension $1$ over $\operatorname{Spec}O$, containing every non-edge point.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used here (`Scheme.IdealSheafData`, properness, flatness, `SmoothOfRelativeDimension`, `IsRegularLocalRing`, `ringKrullDim`); the resolved Deligne–Rapoport model package, the invertibility predicate on ideal sheaf data and the component indexing `X0MqComponents` are the project's own.
--
--   **Where it is used.** The structure axiomatises a regular model of $X_0(p)$ over a base $O$ obtained from the Deligne–Rapoport model by resolving the supersingular crossing points into chains of rational curves, with its special fibre described by the data entering the `x0MqResolvedTable` intersection matrix. It is the geometric input for computations of the component group of the Jacobian at $p$ and for the Picard-functor comparisons used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_DRResolvedModelPackageV4.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace ModularCurve

def DRResolvedModelPackage.chainPos {node : Type} (width : node → ℕ) (n : node) (d : ℕ) : X0MqComponents width :=
  if h0 : d = 0 then Sum.inl 0
  else if h : d < width n then Sum.inr ⟨n, ⟨d - 1, by omega⟩⟩
  else Sum.inl 1

variable (p : ℕ) [Fact p.Prime]

variable {p} in

def DRModel.baseChangeMap {O κ : Type} [CommRing O] [CommRing κ] (toκ : O →+* κ) :
    pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) ⟶
      pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom toκ)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by
      rw [Category.comp_id, ← Spec.map_comp]
      congr 1
      ext1
      exact RingHom.ext_int _ _)

structure DRResolvedModelPackage (𝔛 : DRModelPackage p) (O : Type) [CommRing O]
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ) where

  Y : Scheme.{0}

  toBase : Y ⟶ Spec (CommRingCat.of O)

  toDR : Y ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))
  toDR_over : toDR ≫ pullback.snd _ _ = toBase
  [toDR_proper : IsProper toDR]
  [isProper : IsProper toBase]
  [flat : Flat toBase]
  [isIntegral : IsIntegral Y]
  [isLocallyNoetherian : IsLocallyNoetherian Y]

  regular : ∀ y : Y, y ∉ toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) →
    IsRegularLocalRing (Y.presheaf.stalk y)

  stalk_dim_le_two : ∀ y : Y, y ∉ toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) →
    ringKrullDim (Y.presheaf.stalk y) ≤ 2

  toDR_iso_smoothLocus : IsIso (toDR ∣_ (pullback.fst (DRModel.toBase p) _ ⁻¹ᵁ 𝔛.smoothLocus))

  toDR_iso_generic : IsIso (toDR ∣_ (pullback.snd (DRModel.toBase p) _ ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)))

  node : Type
  [node_fintype : Fintype node]
  [node_deq : DecidableEq node]

  width : node → ℕ
  one_le_width : ∀ n, 1 ≤ width n

  nodeEquiv : node ≃ ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ))

  comp : X0MqComponents width → Y.IdealSheafData

  comp_isInvertible : ∀ v, (comp v).IsInvertible

  comp_integral : ∀ v, IsIntegral (comp v).subscheme

  comp_support : ∀ v (y : Y), y ∈ (comp v).support →
    y ∉ toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)

  comp_prod : ∀ U : Y.affineOpens, (∏ v, comp v).ideal U = Ideal.span {((p : ℕ) : Γ(Y, U))}

  η : X0MqComponents width → Y
  η_not_mem : ∀ v, η v ∉ toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)

  η_stalk : ∀ v, ∃ (U : Y.affineOpens) (hU : η v ∈ (U : Y.Opens)),
    Ideal.map (Y.presheaf.germ (U : Y.Opens) (η v) hU).hom ((comp v).ideal U) =
        IsLocalRing.maximalIdeal (Y.presheaf.stalk (η v)) ∧
      ∀ w, w ≠ v → Ideal.map (Y.presheaf.germ (U : Y.Opens) (η v) hU).hom ((comp w).ideal U) = ⊤

  codim : ∀ y : Y, y ∉ toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) →
    ringKrullDim (Y.presheaf.stalk y) ≤ 1 → ∃ v, y = η v

  strict_iso_inf : ∃ e : pullback ((comp (Sum.inl 0)).subschemeι ≫ toBase) (Spec.map (CommRingCat.ofHom toκ)) ⟶ (𝔛.ratModel κ).C,
    IsIso e ∧ e ≫ (𝔛.ratModel κ).toBase = pullback.snd _ _ ∧
      e ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ = pullback.fst _ _ ≫ (comp (Sum.inl 0)).subschemeι ≫ toDR
  strict_iso_zero : ∃ e : pullback ((comp (Sum.inl 1)).subschemeι ≫ toBase) (Spec.map (CommRingCat.ofHom toκ)) ⟶ (𝔛.ratModel κ).C,
    IsIso e ∧ e ≫ (𝔛.ratModel κ).toBase = pullback.snd _ _ ∧
      e ≫ 𝔛.compZero κ ≫ DRModel.baseChangeMap toκ = pullback.fst _ _ ≫ (comp (Sum.inl 1)).subschemeι ≫ toDR

  exc_image : ∀ (n : node) (i : Fin (width n - 1)), ∀ y ∈ (comp (Sum.inr ⟨n, i⟩)).support,
    toDR.base y = (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (nodeEquiv n)

  edgePt : (n : node) → Fin (width n) → Y
  edgePt_injective : Function.Injective (fun e : Σ n, Fin (width n) => edgePt e.1 e.2)

  edgePt_mem : ∀ (n : node) (d : Fin (width n)),
    edgePt n d ∈ ((comp (DRResolvedModelPackage.chainPos width n d)).support : Set Y) ∩ ((comp (DRResolvedModelPackage.chainPos width n (d + 1))).support : Set Y)

  edgePt_over : ∀ (n : node) (d : Fin (width n)),
    toDR.base (edgePt n d) = (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (nodeEquiv n)

  edgePt_exhaust : ∀ v w, v ≠ w → ∀ y ∈ ((comp v).support : Set Y) ∩ ((comp w).support : Set Y),
    ∃ (n : node) (d : Fin (width n)), y = edgePt n d ∧
      ((v = DRResolvedModelPackage.chainPos width n d ∧ w = DRResolvedModelPackage.chainPos width n (d + 1)) ∨
       (w = DRResolvedModelPackage.chainPos width n d ∧ v = DRResolvedModelPackage.chainPos width n (d + 1)))

  edgePt_transversal : ∀ (n : node) (d : Fin (width n)), ∃ (U : Y.affineOpens) (hU : edgePt n d ∈ (U : Y.Opens)),
    Ideal.map (Y.presheaf.germ (U : Y.Opens) (edgePt n d) hU).hom
        ((comp (DRResolvedModelPackage.chainPos width n d)).ideal U ⊔ (comp (DRResolvedModelPackage.chainPos width n (d + 1))).ideal U) =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk (edgePt n d))

  exc_rational : ∀ (n : node) (i : Fin (width n - 1)),
    ∃ (M : AlgebraicCurve.CurveModel κ (RatFunc κ))
      (e : M.C ⟶ pullback ((comp (Sum.inr ⟨n, i⟩)).subschemeι ≫ toBase) (Spec.map (CommRingCat.ofHom toκ))),
      IsIso e ∧ e ≫ pullback.snd _ _ = M.toBase

  smoothOffEdges : Y.Opens
  [smoothOffEdges_smooth : SmoothOfRelativeDimension 1 (smoothOffEdges.ι ≫ toBase)]

  mem_smoothOffEdges : ∀ y : Y, (∀ (n : node) (d : Fin (width n)), y ≠ edgePt n d) → y ∈ smoothOffEdges

attribute [instance] DRResolvedModelPackage.toDR_proper DRResolvedModelPackage.isProper DRResolvedModelPackage.flat
  DRResolvedModelPackage.isIntegral DRResolvedModelPackage.isLocallyNoetherian DRResolvedModelPackage.node_fintype
  DRResolvedModelPackage.node_deq DRResolvedModelPackage.smoothOffEdges_smooth

end ModularCurve

end


