-- Prove2me | Definitions.Def_KServer_step_rev
-- name    : KServer_step_rev
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T13:27:54.81354+00:00
-- url     : https://prove2.me/theorems/6a6b907e-806f-4d19-8798-3fbb6b3c4dcc
-- title:
--   Theta functoriality and reversal of the BCR level step
-- statement:
--   The theta gluing of two copies of a metric space $U$ at marks $s \neq t$ is functorial: its helper distance is symmetric in the two marks, and invariant under distance-preserving maps. Consequently, a distance-preserving bijection $\varphi : U \to V$ that exchanges mark pairs ($\varphi(a) = b'$, $\varphi(b) = a'$) induces a distance-preserving bijection of the theta gluings $$\Theta(U; a, b) \;\cong\; \Theta(V; a', b').$$ Applied with $\varphi$ the reversal isometry of the three-copy chain, this reverses the whole BCR level step: the step over $(s,t)$ is isometric to the step over $(t,s)$ by a bijection exchanging the two marked endpoints. This supplies the second orientation of the chunk system at the next level of the BCR induction.
-- source:
--   BCR randomized k-server lower bound, theta-space geometry layer

import Mathlib
import Definitions.Def_KServer_glue2
import Definitions.Def_KServer_chain_rev

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace KServer

/-! ### Functoriality of the theta gluing, and reversal of the level step

The theta helper distance is symmetric in the two marks and invariant
under distance-preserving maps; hence a distance-preserving bijection of
the underlying spaces that exchanges the two marks induces a
distance-preserving bijection of the theta gluings.  Applied to the
chain reversal, this reverses the whole BCR level step, exchanging its
marked points. -/

variable {U V : Type*} [MetricSpace U] [MetricSpace V]

/-- The theta helper distance is symmetric in the two marks. -/
theorem thetaDist_swap (s t : U) (b1 : Bool) (x : U) (b2 : Bool) (y : U) :
    thetaDist t s b1 x b2 y = thetaDist s t b1 x b2 y := by
  unfold thetaDist
  split_ifs
  · rw [dist_comm t s,
      min_comm (dist x t + dist s t + dist s y) (dist x s + dist s t + dist t y)]
  · rw [min_comm (dist x t + dist t y) (dist x s + dist s y)]

/-- The theta helper distance is invariant under distance-preserving maps. -/
theorem thetaDist_map (φ : U → V) (hφ : ∀ a b, dist (φ a) (φ b) = dist a b)
    (s t : U) (b1 : Bool) (x : U) (b2 : Bool) (y : U) :
    thetaDist (φ s) (φ t) b1 (φ x) b2 (φ y) = thetaDist s t b1 x b2 y := by
  unfold thetaDist
  split_ifs <;> simp only [hφ]

namespace ThetaPoint

/-- The map of theta gluings induced by a bijection exchanging the marks. -/
def mapSwap (φ : U ≃ V) (a b : U) (a' b' : V)
    (ha : φ a = b') (hb : φ b = a') :
    ThetaPoint U a b → ThetaPoint V a' b'
  | Sum.inl x => Sum.inl (φ x)
  | Sum.inr x => Sum.inr ⟨φ x.1, by
      constructor
      · intro h
        rw [← hb] at h
        exact x.2.2 (φ.injective h)
      · intro h
        rw [← ha] at h
        exact x.2.1 (φ.injective h)⟩

/-- The bijection of theta gluings induced by a bijection exchanging the
marks. -/
def equivSwap (φ : U ≃ V) (a b : U) (a' b' : V)
    (ha : φ a = b') (hb : φ b = a') :
    ThetaPoint U a b ≃ ThetaPoint V a' b' where
  toFun := mapSwap φ a b a' b' ha hb
  invFun := mapSwap φ.symm a' b' a b
    (by rw [← hb, Equiv.symm_apply_apply]) (by rw [← ha, Equiv.symm_apply_apply])
  left_inv p := by
    rcases p with x | x
    · simp [mapSwap]
    · simp [mapSwap]
  right_inv p := by
    rcases p with x | x
    · simp [mapSwap]
    · simp [mapSwap]

/-- `mapSwap` preserves the theta distances. -/
theorem equivSwap_dist (φ : U ≃ V)
    (hφ : ∀ x y : U, dist (φ x) (φ y) = dist x y)
    (a b : U) (hab : a ≠ b) (a' b' : V) (hab' : a' ≠ b')
    (ha : φ a = b') (hb : φ b = a') (p q : ThetaPoint U a b) :
    letI := ThetaPoint.metric a' b' hab'
    letI := ThetaPoint.metric a b hab
    dist (equivSwap φ a b a' b' ha hb p) (equivSwap φ a b a' b' ha hb q)
      = dist p q := by
  letI := ThetaPoint.metric a' b' hab'
  letI := ThetaPoint.metric a b hab
  have key : ∀ (b1 : Bool) (x : U) (b2 : Bool) (y : U),
      thetaDist a' b' b1 (φ x) b2 (φ y) = thetaDist a b b1 x b2 y := by
    intro b1 x b2 y
    rw [← ha, ← hb, thetaDist_map φ hφ, thetaDist_swap]
  rcases p with x | x <;> rcases q with y | y
  · exact key false x false y
  · exact key false x true y.1
  · exact key true x.1 false y
  · exact key true x.1 true y.1
end ThetaPoint

namespace ThetaChain

variable {X : Type*} [MetricSpace X] (s t : X) (hst : s ≠ t)

/-- Reversal of the BCR level step: the theta gluing of the reversed
chains, with the marked endpoints exchanged. -/
noncomputable def stepRevEquiv : Step s t hst ≃ Step t s hst.symm :=
  ThetaPoint.equivSwap (Chain3.revEquiv s t hst)
    (Chain3.start s t) (Chain3.stop s t hst)
    (Chain3.start t s) (Chain3.stop t s hst.symm)
    (Chain3.rev_start s t hst) (Chain3.rev_stop s t hst)

/-- The step reversal preserves distances. -/
theorem stepRevEquiv_dist (p q : Step s t hst) :
    letI := stepMetric t s hst.symm
    letI := stepMetric s t hst
    dist (stepRevEquiv s t hst p) (stepRevEquiv s t hst q) = dist p q := by
  letI := chain3Metric X t s hst.symm
  letI := chain3Metric X s t hst
  exact ThetaPoint.equivSwap_dist (Chain3.revEquiv s t hst)
    (Chain3.rev_dist s t hst)
    (Chain3.start s t) (Chain3.stop s t hst) (start_ne_stop s t hst)
    (Chain3.start t s) (Chain3.stop t s hst.symm) (start_ne_stop t s hst.symm)
    (Chain3.rev_start s t hst) (Chain3.rev_stop s t hst) p q

/-- The step reversal exchanges the marked points. -/
theorem stepRevEquiv_stepS :
    stepRevEquiv s t hst (stepS s t hst) = stepT t s hst.symm := by
  show Sum.inl (Chain3.rev s t hst (Chain3.start s t))
    = Sum.inl (Chain3.stop t s hst.symm)
  rw [Chain3.rev_start]

theorem stepRevEquiv_stepT :
    stepRevEquiv s t hst (stepT s t hst) = stepS t s hst.symm := by
  show Sum.inl (Chain3.rev s t hst (Chain3.stop s t hst))
    = Sum.inl (Chain3.start t s)
  rw [Chain3.rev_stop]

end ThetaChain

end KServer


