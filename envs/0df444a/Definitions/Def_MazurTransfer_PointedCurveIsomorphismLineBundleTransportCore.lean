-- Prove2me | Definitions.Def_MazurTransfer_PointedCurveIsomorphismLineBundleTransportCore
-- name    : MazurTransfer_PointedCurveIsomorphismLineBundleTransportCore
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T07:39:53.435989+00:00
-- url     : https://prove2.me/theorems/839edf35-ed33-4ea8-b546-67476c464710
-- title:
--   Inverse rigidified line-bundle transports along a pointed curve isomorphism
-- statement:
--   Let $e:C^{\prime}\simeq C$ be an isomorphism of schemes over a commutative ring $R$, carrying the specified section on $C^{\prime}$ to the specified section on $C$. Pullback along $e$ and $e^{-1}$ gives the two specified transports of rigidified line bundles. Their underlying module composites come with isomorphisms $$e^*(e^{-1})^*M\simeq M,\qquad(e^{-1})^*e^*N\simeq N.$$ The construction includes the inverse section and structural-map identities and compatibility with change of test scheme. It supports transport of the original Picard representing equivalence without changing its representing scheme.
-- source:
--   MazurTheorem CurveIsoRigidifiedLineBundleTransport.lean, Apache-2.0, Vas and contributors. Original official Anthropic FLT module-pullback APIs at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2. All nine reachable original declaration bodies are retained unchanged; one unreachable backward base-change helper is omitted using authoritative frontend ranges. All nine original closed types and all five data values are kernel-compared. The import alone changes to the public pointed-curve pullback Definition. Named downstream consumer: CurveIsoPicardRepresentationTransport for actual literal rational/mod-3/mod-5 fibres.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: pointed curve isomorphisms give inverse transports of
rigidified line bundles, with actual module isomorphisms for both composites.
Named downstream consumer: CurveIsoPicardRepresentationTransport.
-/
import Definitions.Def_MazurTransfer_PointedCurveRigidifiedLineBundlePullback

noncomputable section
universe u
namespace MazurTransfer.CurveIsoRigidifiedLineBundleTransport
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
open CurveHomRigidifiedLineBundlePullback
variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
variable {c : C ⟶ Spec (.of R)} {c' : C' ⟶ Spec (.of R)}
variable {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
variable {ε' : SchemeHomOver (𝟙 (Spec (.of R))) c'}
variable (e : C' ≅ C) (he : e.hom ≫ c = c') (hε : ε'.val ≫ e.hom = ε.val)

include he in
theorem inv_over : e.inv ≫ c' = c := by
  rw [← he,e.inv_hom_id_assoc]

include hε in
theorem inv_section : ε.val ≫ e.inv = ε'.val := by
  rw [← hε,Category.assoc,e.hom_inv_id,Category.comp_id]

theorem curvePullback_inv_hom {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) :
    curvePullback e.inv (inv_over e he) t ≫ curvePullback e.hom he t = 𝟙 (pullback c t) := by
  apply pullback.hom_ext
  · rw [Category.assoc,curvePullback_fst,← Category.assoc,curvePullback_fst,
      Category.assoc,e.inv_hom_id,Category.comp_id,Category.id_comp]
  · rw [Category.assoc,curvePullback_snd,curvePullback_snd,Category.id_comp]

theorem curvePullback_hom_inv {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) :
    curvePullback e.hom he t ≫ curvePullback e.inv (inv_over e he) t = 𝟙 (pullback c' t) := by
  apply pullback.hom_ext
  · rw [Category.assoc,curvePullback_fst,← Category.assoc,curvePullback_fst,
      Category.assoc,e.hom_inv_id,Category.comp_id,Category.id_comp]
  · rw [Category.assoc,curvePullback_snd,curvePullback_snd,Category.id_comp]

def forward {T : Scheme.{u}} {t : T ⟶ Spec (.of R)} (M : RigidifiedLineBundle c ε t) :
    RigidifiedLineBundle c' ε' t := pullbackRigidified e.hom he hε M

def backward {T : Scheme.{u}} {t : T ⟶ Spec (.of R)} (M : RigidifiedLineBundle c' ε' t) :
    RigidifiedLineBundle c ε t := pullbackRigidified e.inv (inv_over e he) (inv_section e hε) M

def backward_forward_iso {T : Scheme.{u}} {t : T ⟶ Spec (.of R)} (M : RigidifiedLineBundle c ε t) :
    (backward e he hε (forward e he hε M)).L ≅ M.L :=
  (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (curvePullback_inv_hom e he t)).app M.L ≪≫
    (Scheme.Modules.pullbackId _).app M.L

def forward_backward_iso {T : Scheme.{u}} {t : T ⟶ Spec (.of R)} (M : RigidifiedLineBundle c' ε' t) :
    (forward e he hε (backward e he hε M)).L ≅ M.L :=
  (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (curvePullback_hom_inv e he t)).app M.L ≪≫
    (Scheme.Modules.pullbackId _).app M.L

def forward_pullbackAlong_iso {T T' : Scheme.{u}} {t : T ⟶ Spec (.of R)}
    {t' : T' ⟶ Spec (.of R)} (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε t) :
    (forward e he hε (M.pullbackAlong ψ)).L ≅ ((forward e he hε M).pullbackAlong ψ).L :=
  pullbackAlong_iso e.hom he hε ψ M



end MazurTransfer.CurveIsoRigidifiedLineBundleTransport
#print axioms MazurTransfer.CurveIsoRigidifiedLineBundleTransport.forward_backward_iso
#print axioms MazurTransfer.CurveIsoRigidifiedLineBundleTransport.backward_forward_iso


