-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:59.68609+00:00
-- url     : https://prove2.me/theorems/4befd0c5-9404-4b11-8d5a-5f5fb77a27e3
-- title:
--   Principalization Certificate
-- statement:
--   Definitions and structural lemmas for Principalization Certificate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/PrincipalizationCertificate.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
mutual

inductive PrincipalizationCertificate {k : Type u} [Field k] :
    ∀ (W : Scheme.{u}), (W ⟶ Spec (CommRingCat.of k)) → W.IdealSheafData → ℕ →
      Set ↥W → W.IdealSheafData → Prop
  | memory {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
      {Mem : Set ↥W} {Z : W.IdealSheafData}
      (h : (Z.support : Set ↥W) ⊆ Mem) :
      PrincipalizationCertificate W p I m Mem Z
  | large {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
      {Mem : Set ↥W} {Z : W.IdealSheafData}
      (hm : 2 ≤ m) :
      PrincipalizationCertificate W p I m Mem Z
  | toOrder {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
      {Mem : Set ↥W} {Z : W.IdealSheafData}
      (M N : W.IdealSheafData) (μ : ℕ)
      (hI : I = M * N)
      (hM : (M.support : Set ↥W) ⊆ Mem)
      (hmu : m ≤ μ)
      (hZ : (Z.support : Set ↥W) ⊆ orderAtLeastLocus N μ)
      (hcert : OrderCertificate W p N μ Mem Z) :
      PrincipalizationCertificate W p I m Mem Z
  | localize {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
      {Mem : Set ↥W} {Z : W.IdealSheafData}
      (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
      (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
      (hcert : ∀ (z : ↥W) (hz : z ∈ Z.support),
        PrincipalizationCertificate (U z hz).toScheme ((U z hz).ι ≫ p) (I.comap (U z hz).ι) m
          ((U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)) :
      PrincipalizationCertificate W p I m Mem Z

inductive OrderCertificate {k : Type u} [Field k] :
    ∀ (W : Scheme.{u}), (W ⟶ Spec (CommRingCat.of k)) → W.IdealSheafData → ℕ →
      Set ↥W → W.IdealSheafData → Prop
  | memory {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
      {Mem : Set ↥W} {Z : W.IdealSheafData}
      (h : (Z.support : Set ↥W) ⊆ Mem) :
      OrderCertificate W p N μ Mem Z
  | large {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
      {Mem : Set ↥W} {Z : W.IdealSheafData}
      (hmu : 2 ≤ μ) :
      OrderCertificate W p N μ Mem Z
  | localize {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
      {Mem : Set ↥W} {Z : W.IdealSheafData}
      (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
      (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
      (hcert : ∀ (z : ↥W) (hz : z ∈ Z.support),
        OrderCertificate (U z hz).toScheme ((U z hz).ι ≫ p) (N.comap (U z hz).ι) μ
          ((U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)) :
      OrderCertificate W p N μ Mem Z
  | descend {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
      {Mem : Set ↥W} {Z : W.IdealSheafData}
      (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
      (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
      (H : ∀ (z : ↥W) (hz : z ∈ Z.support), (U z hz).toScheme.IdealSheafData)
      (hH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        IsSmoothDivisor ((U z hz).ι ≫ p) (H z hz))
      (hNsubH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        (((N.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)) ⊆
          ((H z hz).support : Set ↥(U z hz).toScheme))
      (hZH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        (((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)) ⊆
          ((H z hz).support : Set ↥(U z hz).toScheme))
      (J : ∀ (z : ↥W) (hz : z ∈ Z.support), Option ((H z hz).subscheme.IdealSheafData))
      (hJnone : ∀ (z : ↥W) (hz : z ∈ Z.support), J z hz = none →
        IsOpen ((H z hz).subschemeι.base ⁻¹'
          (((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme))))
      (hJcomp : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = some Jz → NonzeroOnComponents Jz)
      (hJloc : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = some Jz →
        ∀ x : ↥(H z hz).subscheme,
          ((H z hz).subschemeι ≫ (U z hz).ι).base x ∉ Mem →
          ∃ V : (H z hz).subscheme.Opens, x ∈ V ∧
            Jz.comap V.ι =
              (((N.comap (U z hz).ι).comap (H z hz).subschemeι)).comap V.ι)
      (hJcert : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = some Jz →
        PrincipalizationCertificate (H z hz).subscheme ((H z hz).subschemeι ≫ (U z hz).ι ≫ p) Jz μ
          (((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem)
          ((Z.comap (U z hz).ι).comap (H z hz).subschemeι)) :
      OrderCertificate W p N μ Mem Z

end
end FunctorialResolution.EmbeddedResolution


