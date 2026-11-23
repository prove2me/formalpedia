-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:41.85734+00:00
-- url     : https://prove2.me/theorems/d2a1f8d6-b52a-44ad-84f3-ba79f1a214f9
-- title:
--   Is Part Part Sec
-- statement:
--   Definitions and structural lemmas for Is Part Part Sec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsPartPartSec.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
namespace GlobalTheory.ZH.WtPart
section Alg
variable {A R X : Type} [CommRing A] [CommRing R] [AddCommGroup X]
  {f : A →+* R} {m : Multiplicative X →* R}
  (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _)))
def cf (χ : X) (s : R) : A := ((Equiv.ofBijective _ hb).symm s).coeff χ
theorem cf_apply (χ : X) (a : AddMonoidAlgebra A X) :
    cf hb χ (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _) a) = a.coeff χ :=
  congrArg (fun a : AddMonoidAlgebra A X => a.coeff χ) ((Equiv.ofBijective _ hb).symm_apply_apply a)
theorem cf_zero (χ : X) : cf hb χ 0 = 0 := by
  have := cf_apply hb χ 0
  rwa [map_zero] at this
theorem cf_add (χ : X) (s t : R) : cf hb χ (s + t) = cf hb χ s + cf hb χ t := by
  obtain ⟨a, rfl⟩ := hb.2 s
  obtain ⟨b, rfl⟩ := hb.2 t
  rw [← map_add, cf_apply, cf_apply, cf_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
open Classical in
theorem cf_mono (χ ψ : X) (b : A) :
    cf hb χ (f b * m (Multiplicative.ofAdd ψ)) = if ψ = χ then b else 0 := by
  rw [← AddMonoidAlgebra.liftNCRingHom_single f m (fun _ _ => Commute.all _ _), cf_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
def part (χ : X) (s : R) : R := f (cf hb χ s) * m (Multiplicative.ofAdd χ)
open Classical in
theorem part_mono (χ ψ : X) (b : A) :
    part hb χ (f b * m (Multiplicative.ofAdd ψ)) =
      if ψ = χ then f b * m (Multiplicative.ofAdd ψ) else 0 := by
  rw [part, cf_mono]
  split_ifs with h
  · rw [h]
  · rw [map_zero, zero_mul]
theorem part_map {A' R' : Type} [CommRing A'] [CommRing R'] {f' : A' →+* R'}
    {m' : Multiplicative X →* R'}
    (hb' : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f' m' (fun _ _ => Commute.all _ _)))
    (σ : R →+ R')
    (hσ : ∀ b ψ, ∃ b', σ (f b * m (Multiplicative.ofAdd ψ)) = f' b' * m' (Multiplicative.ofAdd ψ))
    (χ : X) (s : R) : σ (part hb χ s) = part hb' χ (σ s) := by
  obtain ⟨a, rfl⟩ := hb.2 s
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp only [map_zero, part, cf_zero, zero_mul]
  | add x y hx hy =>
    simp only [part] at hx hy
    simp only [map_add, part, cf_add, add_mul, hx, hy]
  | single ψ b =>
    obtain ⟨b', e⟩ := hσ b ψ
    rw [AddMonoidAlgebra.liftNCRingHom_single, e, part_mono, part_mono]
    split_ifs
    · exact e
    · exact map_zero σ
theorem constr_rel {K M M' N : Type} [CommGroup M] [CommGroup M'] [CommGroup N]
    (b : Module.Basis K ℤ X) (u : K → M) (u' : K → M') (c : K → N) (σ : M →* M') (τ : N →* M')
    (h : ∀ k, σ (u k) = τ (c k) * u' k) (ψ : X) :
    σ (Additive.toMul (b.constr ℤ (fun k => Additive.ofMul (u k)) ψ)) =
      τ (Additive.toMul (b.constr ℤ (fun k => Additive.ofMul (c k)) ψ)) *
        Additive.toMul (b.constr ℤ (fun k => Additive.ofMul (u' k)) ψ) := by
  simp only [Module.Basis.constr_apply, Finsupp.sum, toMul_sum, toMul_zsmul, toMul_ofMul, map_prod,
    map_zpow, h, mul_zpow, Finset.prod_mul_distrib]
end Alg
theorem rr {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl
theorem rapp {X Y : Scheme.{0}} (q : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    resG Y (q.preimage_mono h) ((q.app U).hom a) = (q.app V).hom (resG X h a) := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
    q.naturality]
  rfl
section Datum
variable {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G] (D : E.GtDatum G)
abbrev mono (j : E.ChartIdx) (V : E.B.left.Opens) (h : V ≤ E.chart j) :
    Multiplicative E.X →* Γ(G.left, D.q.left ⁻¹ᵁ V) :=
  (Units.coeHom _).comp (AddMonoidHom.toMultiplicativeLeft
    (E.basis.constr ℤ (fun k => Additive.ofMul
      (res (Scheme.Hom.preimage_mono D.q.left h) (D.u j k)))).toAddMonoidHom)
theorem res_mono {j j' : E.ChartIdx} {V W : E.B.left.Opens} (hV : V ≤ E.chart j')
    (hW : W ≤ E.chart j) (h : W ≤ V) (ψ : E.X) :
    ∃ c : Γ(E.B.left, W), resG _ (D.q.left.preimage_mono h) (mono D j' V hV (Multiplicative.ofAdd ψ)) =
      (D.q.left.app W).hom c * mono D j W hW (Multiplicative.ofAdd ψ) := by
  have hW' : W ≤ E.chart j ⊓ E.chart j' := le_inf hW (h.trans hV)
  refine ⟨_, congrArg Units.val (constr_rel E.basis
    (fun k => res (Scheme.Hom.preimage_mono D.q.left hV) (D.u j' k))
    (fun k => res (Scheme.Hom.preimage_mono D.q.left hW) (D.u j k))
    (fun k => res hW' (res (le_inf (inf_le_left.trans (E.chart_le j k))
      (inf_le_right.trans (E.chart_le j' k))) ((E.O (E.basis k)).L.g (j k) (j' k))))
    (res (D.q.left.preimage_mono h)) (pullU D.q.left W) (fun k => Units.ext ?_) ψ)⟩
  have e := congrArg (resG _ (D.q.left.preimage_mono hW')) (congrArg Units.val (D.trans j j' k))
  rw [Units.val_mul, map_mul] at e
  exact (rr _ _ _).trans ((rr _ _ _).symm.trans (e.trans (congrArg₂ (· * ·) (rapp _ _ _) (rr _ _ _))))
end Datum
variable {k : Type} [Field k] (Φ : FibPre k) {d : ℕ}
def partSec (φ : (Φ.H d).Sec) (α : Φ.E.X) : (Φ.H d).Sec where
  f l := part (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) α (φ.f l)
  compat l l' := by
    let q := Φ.D.q.left
    let I := {W : Φ.E.B.left.affineOpens // W.1 ≤ Φ.N₀.U l ⊓ Φ.N₀.U l'}
    refine Φ.G.left.sheaf.eq_of_locally_eq' (fun W : I => q ⁻¹ᵁ W.1.1) _
      (fun W => homOfLE (q.preimage_mono W.2)) (fun x hx => ?_) _ _ fun W => ?_
    · obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Φ.E.B.left) (x := q x)
        (U := Φ.N₀.U l ⊓ Φ.N₀.U l') hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hle⟩, hxW⟩
    have h₁ : W.1.1 ≤ Φ.N₀.U l := W.2.trans inf_le_left
    have h₂ : W.1.1 ≤ Φ.N₀.U l' := W.2.trans inf_le_right
    have hW : W.1.1 ≤ Φ.E.chart (Φ.ch l) := h₁.trans (Φ.le l)
    let w : Γ(Φ.E.B.left, W.1.1) := resG _ W.2 (Φ.N₀.g l l').1 ^ d
    have hw : resG _ (q.preimage_mono W.2) ((Φ.H d).g l l').1 = (q.app W.1.1).hom w := by
      change resG _ (q.preimage_mono W.2) (((pullU q _ (Φ.N₀.g l l')) ^ d).1) = _
      rw [Units.val_pow_eq_pow_val, map_pow, map_pow]
      exact congrArg (· ^ d) (rapp _ _ _)
    have e₁ := part_map (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l))
      (Φ.D.coord (Φ.ch l) W.1.1 W.1.2 hW) (resG _ (q.preimage_mono h₁)).toAddMonoidHom
      (fun b ψ => by
        obtain ⟨c, hc⟩ := res_mono Φ.D (Φ.le l) hW h₁ ψ
        refine ⟨resG _ h₁ b * c, (map_mul (resG _ (q.preimage_mono h₁)) _ _).trans ?_⟩
        rw [hc, rapp, map_mul, _root_.mul_assoc]) α (φ.f l)
    have e₂ := part_map (Φ.D.coord (Φ.ch l') (Φ.N₀.U l') (Φ.aff l') (Φ.le l'))
      (Φ.D.coord (Φ.ch l) W.1.1 W.1.2 hW)
      ((AddMonoidHom.mulLeft ((q.app W.1.1).hom w)).comp (resG _ (q.preimage_mono h₂)).toAddMonoidHom)
      (fun b ψ => by
        obtain ⟨c, hc⟩ := res_mono Φ.D (Φ.le l') hW h₂ ψ
        refine ⟨w * (resG _ h₂ b * c), (congrArg (_ * ·)
          (map_mul (resG _ (q.preimage_mono h₂)) _ _)).trans ?_⟩
        rw [hc, rapp, map_mul, map_mul, _root_.mul_assoc, _root_.mul_assoc]) α (φ.f l')
    have e₃ := congrArg (resG _ (q.preimage_mono W.2)) (φ.compat l l')
    have e₄ : resG _ (q.preimage_mono h₁) (φ.f l) =
        (q.app W.1.1).hom w * resG _ (q.preimage_mono h₂) (φ.f l') :=
      (rr _ _ _).symm.trans (e₃.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) hw (rr _ _ _))))
    refine (rr _ _ _).trans (e₁.trans ((congrArg _ e₄).trans (e₂.symm.trans ?_)))
    exact ((map_mul (resG _ (q.preimage_mono W.2)) _ _).trans (congrArg₂ (· * ·) hw (rr _ _ _))).symm
end GlobalTheory.ZH.WtPart
end


