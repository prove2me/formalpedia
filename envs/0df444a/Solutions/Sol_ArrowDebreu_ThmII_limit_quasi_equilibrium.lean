-- Prove2me | solution 1 for ArrowDebreu.ThmII.limit_quasi_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T02:14:06.307213+00:00
-- url     : https://prove2.me/submissions/df5de27e-8a72-49f4-bbf5-3fc36305d3dd

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_ThmII_AssumptionsII
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmII_economyEeps
open ArrowDebreu.Shared

open Filter Topology

open ArrowDebreu.Shared Filter Topology ArrowDebreu.ThmII in
theorem solution {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (εs : ℕ → ℝ) (hεs : ∀ k, 0 < εs k ∧ εs k ≤ 1 / (2 * ((productive E).card : ℝ)))
    (hεs0 : Tendsto εs atTop (𝓝 0))
    (as : ℕ → Player m n → Fin l → ℝ)
    (has : ∀ k, (economyEeps E (εs k)).IsEquilibriumPoint (as k))
    (a0 : Player m n → Fin l → ℝ) (hlim : Tendsto as atTop (𝓝 a0)) :
    ∀ i, ∀ x ∈ E.X i, E.u i (consOf a0 i) < E.u i x →
      priceOf a0 ⬝ᵥ consOf a0 i ≤ priceOf a0 ⬝ᵥ x := by
  intro i x hx hux
  have hcons : Tendsto (fun k => as k (Sum.inl i)) atTop (𝓝 (a0 (Sum.inl i))) :=
    ((continuous_apply (Sum.inl i)).tendsto a0).comp hlim
  have hmemk : ∀ k, as k (Sum.inl i) ∈ E.X i := fun k => (has k).1 (Sum.inl i) (Set.mem_univ _)
  have hx0 : a0 (Sum.inl i) ∈ E.X i :=
    (hE.II i).1.mem_of_tendsto hcons (Eventually.of_forall hmemk)
  have hu : Tendsto (fun k => E.u i (as k (Sum.inl i))) atTop (𝓝 (E.u i (a0 (Sum.inl i)))) :=
    ((hE.IIIa i) _ hx0).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hcons, Eventually.of_forall hmemk⟩)
  have hux' : E.u i (a0 (Sum.inl i)) < E.u i x := hux
  have hev : ∀ᶠ k in atTop, E.u i (as k (Sum.inl i)) < E.u i x :=
    hu.eventually (Iio_mem_nhds hux')
  have hle : ∀ᶠ k in atTop, (fun a : Player m n → Fin l → ℝ => priceOf a ⬝ᵥ consOf a i) (as k) ≤
      (fun a : Player m n → Fin l → ℝ => priceOf a ⬝ᵥ x) (as k) := by
    filter_upwards [hev] with k hk
    obtain ⟨hmem, hmax⟩ := (has k).2 (Sum.inl i)
    have hmem' : as k (Sum.inl i) ∈ E.X i ∧ priceOf (as k) ⬝ᵥ as k (Sum.inl i) ≤
        priceOf (as k) ⬝ᵥ E.ζ i +
          max 0 (∑ j, E.α i j * (priceOf (as k) ⬝ᵥ prodOf (as k) j)) := hmem
    show priceOf (as k) ⬝ᵥ as k (Sum.inl i) ≤ priceOf (as k) ⬝ᵥ x
    by_contra hcon
    push_neg at hcon
    have hxin : x ∈ (economyEeps E (εs k)).constr (Sum.inl i) (as k) := by
      show x ∈ E.X i ∧ priceOf (as k) ⬝ᵥ x ≤
        priceOf (as k) ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf (as k) ⬝ᵥ prodOf (as k) j))
      exact ⟨hx, le_trans hcon.le hmem'.2⟩
    have h1 := hmax x hxin
    have h2 : E.u i (Function.update (as k) (Sum.inl i) x (Sum.inl i)) ≤
        E.u i (as k (Sum.inl i)) := h1
    simp only [Function.update_self] at h2
    linarith
  have hc1 : Continuous (fun a : Player m n → Fin l → ℝ => priceOf a ⬝ᵥ consOf a i) :=
    Continuous.dotProduct (continuous_apply _) (continuous_apply _)
  have hc2 : Continuous (fun a : Player m n → Fin l → ℝ => priceOf a ⬝ᵥ x) :=
    Continuous.dotProduct (continuous_apply _) continuous_const
  exact le_of_tendsto_of_tendsto ((hc1.tendsto a0).comp hlim) ((hc2.tendsto a0).comp hlim) hle
