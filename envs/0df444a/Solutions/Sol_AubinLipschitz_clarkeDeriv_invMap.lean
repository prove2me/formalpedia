-- Prove2me | solution 1 for AubinLipschitz.clarkeDeriv_invMap
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:07:51.954735+00:00
-- url     : https://prove2.me/submissions/97d9d4a6-2381-47d3-adbc-760029263d75

import Mathlib
import Definitions.Def_AubinLipschitz_clarkeDeriv
import Definitions.Def_AubinLipschitz_invMap

namespace Aux_Q01_clarkeDeriv_invMap
open AubinLipschitz

theorem dist_swap' {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (a b : X × Y) : dist a.swap b.swap = dist a b := by
  simp only [Prod.dist_eq, Prod.fst_swap, Prod.snd_swap]
  exact max_comm _ _

theorem cone_swap {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (K : Set (X × Y)) (p v : X × Y) (h : v ∈ clarkeCone K p) :
    v.swap ∈ clarkeCone (Prod.swap ⁻¹' K) p.swap := by
  intro ε hε
  obtain ⟨α, hα, β, hβ, H⟩ := h ε hε
  refine ⟨α, hα, β, hβ, fun z hz t ht htβ => ?_⟩
  have hz2 : z.swap ∈ Metric.closedBall p α := by
    have := hz.2
    rw [Metric.mem_closedBall] at this ⊢
    rw [← dist_swap', Prod.swap_swap]
    exact this
  obtain ⟨w, hw, hwK⟩ := H z.swap ⟨hz.1, hz2⟩ t ht htβ
  refine ⟨w.swap, ?_, ?_⟩
  · rw [Metric.mem_closedBall] at hw ⊢
    rw [dist_swap']
    exact hw
  · have e : (z + t • w.swap).swap = z.swap + t • w := by
      ext <;> simp
    show (z + t • w.swap).swap ∈ K
    rw [e]
    exact hwK

end Aux_Q01_clarkeDeriv_invMap

open AubinLipschitz in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Set Y) (x₀ : X) (y₀ : Y) (h₀ : y₀ ∈ F x₀) :
    invMap (clarkeDeriv F x₀ y₀) = clarkeDeriv (invMap F) y₀ x₀ := by
  funext v
  ext u
  constructor
  · intro h
    exact Aux_Q01_clarkeDeriv_invMap.cone_swap (graphOf F) (x₀, y₀) (u, v) h
  · intro h
    exact Aux_Q01_clarkeDeriv_invMap.cone_swap (graphOf (invMap F)) (y₀, x₀) (v, u) h
