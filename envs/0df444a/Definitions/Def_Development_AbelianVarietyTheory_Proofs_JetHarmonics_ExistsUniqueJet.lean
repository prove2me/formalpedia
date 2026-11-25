-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueJet
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueJet
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T14:35:55.464343+00:00
-- url     : https://prove2.me/theorems/eb259b94-c8a8-4292-b7e9-9711131b4ca9
-- title:
--   Exists Unique Jet
-- statement:
--   Definitions and structural lemmas for Exists Unique Jet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsUniqueJet.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLieCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_zR_mem_ker
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.SeriesValue
open ReciprocityTheory.ChartRestriction.G.Chart GlobalTheory.JetSer GlobalTheory.ChartBaseChange GlobalTheory.TorsionCharacter ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev addOf)
variable {V : Type} [CommRing V] {G : Over (Spec (CommRingCat.of V))} [GrpObj G] {d : ℕ}
variable {O : Type} [CommRing O] [Algebra V O]
variable (V O d) in

def jetIn (m : ℕ) : JetR V (Fin d) m →ₐ[V] JetR O (Fin 1 × Fin d) m :=
  jetLift V (RingHom.ker (jetAug O _ m)) (ker_jetAug_pow _ m) (fun j => zR m (0, j)) (fun _ => zR_mem_ker m _)
def ValAt (x : Fam G (Fin d)) (u : PS O 1 d) {A : Type} [CommRing A] [Algebra O A] (m : ℕ)
    (g : Spec (CommRingCat.of A) ⟶ G.left) (z : Fin d → A) (k : A) : Prop :=
  ∃ ψ : JetR O (Fin 1 × Fin d) m →ₐ[O] A, (∀ q, ψ (zR m q) = z q.2) ∧
    g = Spec.map (CommRingCat.ofHom (ψ.toRingHom.comp (jetIn V d O m).toRingHom)) ≫ (x m).left ∧ k = ψ (toJet m u)
def HasVal (x : Fam G (Fin d)) (u : PS O 1 d) {A : Type} [CommRing A] [Algebra O A]
    (g : Spec (CommRingCat.of A) ⟶ G.left) (k : A) : Prop :=
  ∃ m z, ValAt x u m g z k
variable {x : Fam G (Fin d)} {u : PS O 1 d} {A : Type} [CommRing A] [Algebra O A]
omit [GrpObj G] in
theorem HasVal.map {g : Spec (CommRingCat.of A) ⟶ G.left} {k : A} (h : HasVal x u g k) {B : Type} [CommRing B]
    [Algebra O B] (θ : A →ₐ[O] B) : HasVal x u (Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ g) (θ k) := by
  obtain ⟨m, z, ψ, h1, h2, h3⟩ := h
  refine ⟨m, fun j => θ (z j), θ.comp ψ, fun q => congrArg θ (h1 q), ?_, congrArg θ h3⟩
  rw [h2, ← Category.assoc, ← Spec.map_comp]
  rfl
variable (V) in

def res {B : Type} [CommRing B] [Algebra O B] (θ : A →ₐ[O] B) :
    specV (algebraMap V O) B ⟶ specV (algebraMap V O) A :=
  Over.homMk (Spec.map (CommRingCat.ofHom θ.toRingHom)) (by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (RingHom.ext fun r => θ.commutes _))
def LimVal (x : Fam G (Fin d)) (u : PS O 1 d) (p : O) (g : Spec (CommRingCat.of A) ⟶ G.left) (k : A) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra O R] (θ : A →ₐ[O] R), IsNilpotent (algebraMap O R p) →
    HasVal x u (Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ g) (θ k)
variable {p : O}
omit [GrpObj G] in
theorem LimVal.map {g : Spec (CommRingCat.of A) ⟶ G.left} {k : A} (h : LimVal x u p g k) {B : Type} [CommRing B]
    [Algebra O B] (θ : A →ₐ[O] B) : LimVal x u p (Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ g) (θ k) := by
  intro R _ _ θ' hp
  have := h R (θ'.comp θ) hp
  rw [← Category.assoc, ← Spec.map_comp]
  exact this
end GlobalTheory.SeriesValue


