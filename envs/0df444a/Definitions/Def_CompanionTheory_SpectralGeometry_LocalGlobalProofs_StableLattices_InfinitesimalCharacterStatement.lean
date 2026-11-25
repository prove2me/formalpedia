-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatement
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatement
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:05:04.235567+00:00
-- url     : https://prove2.me/theorems/95f11b02-1446-56e0-a881-6a6ed88626cc
-- title:
--   Infinitesimal Character Statement
-- statement:
--   Definitions and structural lemmas for Infinitesimal Character Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InfinitesimalCharacterStatement.lean

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatementStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_PolF_add
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_PolF_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
open _root_.CompanionTheory.RgExh _root_.CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet qminor Tm)
section Poly
variable {A : Type*} [Ring A] [Algebra ℂ A]
def PolyFn (F : ℂ → A) : Prop := ∃ p : Polynomial A, ∀ u, F u = p.eval (algebraMap ℂ A u)
theorem PolyFn.const (c : A) : PolyFn (fun _ : ℂ => c) := ⟨Polynomial.C c, fun u => by simp⟩
theorem PolyFn.alg : PolyFn (fun u : ℂ => algebraMap ℂ A u) := ⟨Polynomial.X, fun u => by simp⟩
theorem PolyFn.add {F G : ℂ → A} (hF : PolyFn F) (hG : PolyFn G) : PolyFn (fun u => F u + G u) := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨q, hq⟩ := hG
  exact ⟨p + q, fun u => by simp [hp, hq]⟩
theorem PolyFn.mul {F G : ℂ → A} (hF : PolyFn F) (hG : PolyFn G) : PolyFn (fun u => F u * G u) := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨q, hq⟩ := hG
  refine ⟨p * q, fun u => ?_⟩
  show F u * G u = _
  rw [hp, hq]
  simp only [Polynomial.eval]
  rw [Polynomial.eval₂_mul_noncomm]
  intro k
  exact (Algebra.commutes u _).symm
theorem PolyFn.sum {ι : Type*} (s : Finset ι) {F : ι → ℂ → A} (h : ∀ i, PolyFn (F i)) :
    PolyFn (fun u => ∑ i ∈ s, F i u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PolyFn.const (0 : A)
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i).add ih
theorem PolyFn.list {m : ℕ} (F : Fin m → ℂ → A) (h : ∀ k, PolyFn (F k)) :
    PolyFn (fun u => (List.ofFn fun k => F k u).prod) := by
  induction m with
  | zero => simpa using PolyFn.const (1 : A)
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact (h 0).mul (ih _ fun k => h k.succ)
end Poly
section Restrict
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {S : Submodule ℂ V}
def Rs (G : Module.End ℂ S) (F : Module.End ℂ V) : Prop := ∀ x : S, ((G x : S) : V) = F x
theorem Rs.mul {G G' : Module.End ℂ S} {F F' : Module.End ℂ V} (h : Rs G F) (h' : Rs G' F') :
    Rs (G * G') (F * F') := fun x => by
  simp only [Module.End.mul_apply]
  rw [h, h']
theorem Rs.add {G G' : Module.End ℂ S} {F F' : Module.End ℂ V} (h : Rs G F) (h' : Rs G' F') :
    Rs (G + G') (F + F') := fun x => by
  simp only [LinearMap.add_apply, Submodule.coe_add]
  rw [h, h']
theorem Rs.alg (c : ℂ) : Rs (algebraMap ℂ (Module.End ℂ S) c) (algebraMap ℂ (Module.End ℂ V) c) :=
  fun x => by simp [Module.algebraMap_end_apply]
theorem Rs.zero : Rs (0 : Module.End ℂ S) (0 : Module.End ℂ V) := fun x => by simp
theorem Rs.one : Rs (1 : Module.End ℂ S) (1 : Module.End ℂ V) := fun x => by simp
theorem Rs.sum {ι : Type*} (s : Finset ι) {G : ι → Module.End ℂ S} {F : ι → Module.End ℂ V}
    (h : ∀ i, Rs (G i) (F i)) : Rs (∑ i ∈ s, G i) (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Rs.zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i).add ih
theorem Rs.intCast (z : ℤ) : Rs ((z : Module.End ℂ S)) ((z : Module.End ℂ V)) := by
  rw [← map_intCast (algebraMap ℂ (Module.End ℂ S)), ← map_intCast (algebraMap ℂ (Module.End ℂ V))]
  exact Rs.alg _
theorem Rs.list {m : ℕ} {G : Fin m → Module.End ℂ S} {F : Fin m → Module.End ℂ V}
    (h : ∀ k, Rs (G k) (F k)) : Rs (List.ofFn G).prod (List.ofFn F).prod := by
  induction m with
  | zero => simpa using Rs.one
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact (h 0).mul (ih fun k => h k.succ)
theorem Rs.tm {n : ℕ} {G : Fin n → Fin n → Module.End ℂ S} {F : Fin n → Fin n → Module.End ℂ V}
    (h : ∀ a b, Rs (G a b) (F a b)) (u : ℂ) (a b : Fin n) : Rs (Tm G u a b) (Tm F u a b) := by
  unfold Tm
  refine Rs.add ?_ (h a b)
  split_ifs
  · exact Rs.alg u
  · exact Rs.zero
theorem Rs.qdet {n : ℕ} {G : Fin n → Fin n → Module.End ℂ S} {F : Fin n → Fin n → Module.End ℂ V}
    (h : ∀ a b, Rs (G a b) (F a b)) (u : ℂ) : Rs (qdet G u) (qdet F u) := by
  unfold Formalism.REAL.qdet qminor
  exact Rs.sum _ fun σ => (Rs.intCast _).mul (Rs.list fun k => Rs.tm h _ _ _)
end Restrict
section Nil
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
end Nil
section Main
open Formalism.QuantumDeterminants (capP)
variable {n : ℕ}
end Main
end GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf


