-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBFr
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBFr
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:59:44.034845+00:00
-- url     : https://prove2.me/theorems/3b18a97d-f55c-4e2b-b293-c6e675227d61
-- title:
--   Germ BFr
-- statement:
--   Definitions and structural lemmas for Germ BFr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBFr.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jet_hom_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_eq_top_of_closedPoint_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
section Pt
variable {S Idx : Type} [CommRing S]
instance jetAug_isLocalHom (m : ℕ) : IsLocalHom ((jetAug : Jet S Idx m →ₐ[S] S) : Jet S Idx m →+* S) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨c, hc⟩ := @jet_exists_nil S Idx _ m a
  have hn : IsNilpotent ((jetAug : Jet S Idx m →ₐ[S] S) (a - algebraMap S _ c)) := hc.map _
  rw [map_sub, AlgHom.commutes] at hn
  have hcu : IsUnit c := by
    have := hn.neg.isUnit_add_left_of_commute ha (Commute.all _ _)
    simpa using this
  have := hc.isUnit_add_left_of_commute (hcu.map (algebraMap S (Jet S Idx m))) (Commute.all _ _)
  simpa using this
theorem pre_top [IsLocalRing S] (m : ℕ) {X : Scheme.{0}} (U : X.Opens) (ψ : Sp (Jet S Idx m) ⟶ X) (e : Sp S ⟶ X)
    (he : spMap ((jetAug : Jet S Idx m →ₐ[S] S) : Jet S Idx m →+* S) ≫ ψ = e) (hU : e ⁻¹ᵁ U = ⊤) : ψ ⁻¹ᵁ U = ⊤ := by
  apply ReciprocityTheory.ChartRestriction.G.DVR.eq_top_of_closedPoint_mem
  have h1 : (IsLocalRing.closedPoint S : Sp S) ∈ e ⁻¹ᵁ U := by rw [hU]; trivial
  have h2 : (spMap ((jetAug : Jet S Idx m →ₐ[S] S) : Jet S Idx m →+* S)).base (IsLocalRing.closedPoint S) =
      IsLocalRing.closedPoint (Jet S Idx m) :=
    IsLocalRing.comap_closedPoint ((jetAug : Jet S Idx m →ₐ[S] S) : Jet S Idx m →+* S)
  rw [← he] at h1
  show ψ.base (IsLocalRing.closedPoint (Jet S Idx m)) ∈ U
  rw [← h2]
  exact h1
theorem psum_one {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] [IsCommMonObj G] {T : Over X0} {n : ℕ}
    (I : Finset (Fin n)) : psum G (fun _ => (1 : T ⟶ G)) I = 1 := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => rfl
  | cons k l ih => exact (congrArg (padd G 1) ih).trans (_root_.one_mul (1 : T ⟶ G))
theorem aug_copy {d n : ℕ} (m : ℕ) (i : Fin n) :
    (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S).comp (jetCopy d m i) = jetAug := by
  apply jet_hom_ext
  intro p
  show MvPolynomial.aeval (fun _ => (0 : S))
      (MvPolynomial.aeval (fun q : Fin 1 × Fin d => (MvPolynomial.X (i, q.2) : MvPolynomial (Fin n × Fin d) S))
        (MvPolynomial.X p)) = MvPolynomial.aeval (fun _ => (0 : S)) (MvPolynomial.X p)
  simp
end Pt
section Axes
variable {S : Type} [CommRing S]
variable (d : ℕ)
abbrev axis0 (m : ℕ) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2
abbrev axis1 (m : ℕ) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun _ => 0] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2
end Axes
section Frames
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] [IsLocalRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
abbrev e0 : Sp S ⟶ t.G.left := (1 : overAt x0 S ⟶ t.G).left
theorem vec2 {α : Type*} (f : Fin 2 → α) : (![f 0, f 1] : Fin 2 → α) = f := by
  funext i
  fin_cases i <;> rfl
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}
variable {t x0 d x} in
theorem jpt_aug (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) {n : ℕ} (i : Fin n) :
    homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S) ≫ jptG t x0 d x m i = 1 := by
  rw [jptG, ← Category.assoc, homAt_comp, aug_copy, hch.zero m]
theorem psum_aug {m n : ℕ} (xs : Fin n → (jOG x0 d m n ⟶ t.G))
    (hxs : ∀ i, homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S) ≫ xs i = 1) (I : Finset (Fin n)) :
    homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S) ≫ psum t.G xs I = 1 :=
  (psum_hom (preHom (homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S))) xs I).trans
    ((congrArg (fun f => psum t.G f I) (funext hxs)).trans (psum_one t.G I))
theorem wchart_top (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) {m n : ℕ}
    (xs : Fin n → (jOG x0 d m n ⟶ t.G))
    (hxs : ∀ i, homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S) ≫ xs i = 1) :
    LB.wchart t.PP.L (cφG t xs) (fun _ => i0) = ⊤ := by
  refine top_unique fun y _ => Set.mem_iInter.2 fun I => ?_
  have h := pre_top m (t.PP.L.U i0) (cφG t xs I) (e0 t x0)
    (congrArg Over.Hom.left (psum_aug t x0 d xs hxs I.down)) hi0
  have : y ∈ (cφG t xs I) ⁻¹ᵁ t.PP.L.U i0 := by rw [h]; trivial
  exact this
variable {t x0 d x} in

def fr (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) (m : ℕ) :
    LB.Gen (LB.LinComb t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2)) :=
  cgen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (fun _ => i0)
    (wchart_top t x0 d i0 hi0 _ fun i => by rw [vec2 (fun i => jptG t x0 d x m i)]; exact jpt_aug hch m i)
end Frames
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB


