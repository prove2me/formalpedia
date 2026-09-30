-- Prove2me | solution 1 for AlgMechDesign.LowerBound.revelation_principle
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:08:02.259697+00:00
-- url     : https://prove2.me/submissions/fcf30f91-a50e-4161-8169-7502e7a93055

import Definitions.Def_AlgMechDesign_LowerBound_Mechanism

set_option autoImplicit false
open AlgMechDesign.LowerBound
universe u

theorem solution {n k : ℕ} [NeZero n] {A : Fin n → Type u}
    (o : ((i : Fin n) → A i) → (Fin k → Fin n)) (p : ((i : Fin n) → A i) → Fin n → ℝ) {c : ℝ}
    (h : Implements o p c) :
    ∃ (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ),
      IsTruthful alloc pay ∧ IsApprox c alloc := by
  classical
  let σ : (i : Fin n) → (Fin k → ℝ) → A i := fun i ti =>
    if ht : IsAgentType ti then Classical.choose (h.1 i ti ht)
    else Classical.choose (h.1 i (fun _ => 1) (by intro j; norm_num))
  have hσ : ∀ i ti, IsAgentType ti → IsDominant o p i ti (σ i ti) := by
    intro i ti ht
    simpa [σ, ht] using Classical.choose_spec (h.1 i ti ht)
  let lift : (Fin n → Fin k → ℝ) → (i : Fin n) → A i := fun t i => σ i (t i)
  have hlift : ∀ (t : Fin n → Fin k → ℝ) (i : Fin n) (ti : Fin k → ℝ),
      lift (Function.update t i ti) = Function.update (lift t) i (σ i ti) := by
    intro t i ti
    funext l
    by_cases he : l = i
    · subst l
      simp [lift]
    · simp [lift, he]
  refine ⟨fun t => o (lift t), fun t => p (lift t), ?_, ?_⟩
  · intro d hd i ti ti' hti hti'
    have hdom := hσ i ti hti (lift d) (σ i ti')
    simpa only [utility, hlift, genUtility] using hdom
  · intro t ht y
    exact h.2 t ht (lift t) (fun i => hσ i (t i) (ht i)) y
