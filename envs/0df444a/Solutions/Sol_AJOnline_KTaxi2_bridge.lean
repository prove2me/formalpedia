-- Prove2me | solution 1 for AJOnline.KTaxi2.bridge
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:12:52.015503+00:00
-- url     : https://prove2.me/submissions/0dc99d32-f9a4-4a75-a2de-cf53026e5b49

import Mathlib
import Definitions.Def_AJOnline_KTaxi2

open AJGames AJOnline AJOnline.KTaxi2 KTaxi.Competitive.Supplement
open scoped ENNReal NNReal

/-- A complete play: the pairs (request, serving location) in order. -/
def flat (ps : List ((ℝ × ℝ) × ℝ)) : List Mv := ps.flatMap fun p => [Mv.req p.1, Mv.serve p.2]

theorem flat_snoc (ps : List ((ℝ × ℝ) × ℝ)) (q : ℝ × ℝ) (a : ℝ) :
    flat (ps ++ [(q, a)]) = flat ps ++ [Mv.req q] ++ [Mv.serve a] := by
  simp [flat, List.flatMap_append]

theorem cfg_flat_req (X : Multiset ℝ) (ps : List ((ℝ × ℝ) × ℝ)) (q : ℝ × ℝ) :
    cfg X (flat ps ++ [Mv.req q]) = cfg X (flat ps) := by
  induction ps generalizing X with
  | nil => simp [flat, cfg]
  | cons p ps ih => simpa [flat, cfg] using ih _

theorem cfg_flat_pair (X : Multiset ℝ) (ps : List ((ℝ × ℝ) × ℝ)) (q : ℝ × ℝ) (a : ℝ) :
    cfg X (flat ps ++ [Mv.req q] ++ [Mv.serve a]) = ((cfg X (flat ps)).erase a).cons q.2 := by
  induction ps generalizing X with
  | nil => simp [flat, cfg]
  | cons p ps ih => simpa [flat, cfg] using ih _

theorem algCost_flat_pair (ps : List ((ℝ × ℝ) × ℝ)) (q : ℝ × ℝ) (a : ℝ) :
    algCost (flat ps ++ [Mv.req q] ++ [Mv.serve a]) = algCost (flat ps) + edist a q.1 := by
  induction ps with
  | nil => simp [flat, algCost]
  | cons p ps ih =>
    simp only [flat, List.flatMap_cons, List.cons_append, List.nil_append] at ih ⊢
    simp only [algCost]
    rw [ih, add_assoc]

theorem reqs_append (s t : List Mv) : reqs (s ++ t) = reqs s ++ reqs t := by
  simp [reqs, List.filterMap_append]

theorem flat_req_valid (X : Multiset ℝ) (ps : List ((ℝ × ℝ) × ℝ)) (q : ℝ × ℝ)
    (hv : Valid X (flat ps)) : Valid X (flat ps ++ [Mv.req q]) := by
  induction ps generalizing X with
  | nil => trivial
  | cons p ps ih =>
    simp only [flat, List.flatMap_cons, List.cons_append, List.nil_append] at hv ⊢
    exact ⟨hv.1, ih _ hv.2⟩

theorem flat_pair_valid (X : Multiset ℝ) (ps : List ((ℝ × ℝ) × ℝ)) (q : ℝ × ℝ) (a : ℝ)
    (hv : Valid X (flat ps)) (ha : a ∈ cfg X (flat ps)) :
    Valid X (flat ps ++ [Mv.req q] ++ [Mv.serve a]) :=
  valid_snoc_serve X _ q a (flat_req_valid X ps q hv) (by simp) (by rw [cfg_flat_req]; exact ha)

/-- Expectations through a `bind`. -/
theorem tsum_bind_mul {α β : Type} (μ : PMF α) (h : α → PMF β) (g : β → ℝ≥0∞) :
    ∑' p, (μ.bind h) p * g p = ∑' a, μ a * ∑' p, h a p * g p := by
  simp_rw [PMF.bind_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  congr 1; funext a
  rw [← ENNReal.tsum_mul_left]
  congr 1; funext p; ring

/-- One step of the play-out of a memoryless policy from a complete play. -/
theorem playOut_step (A : MemorylessPolicy) (x₀ : Fin 2 → ℝ) (ps : List ((ℝ × ℝ) × ℝ))
    (q : ℝ × ℝ) (rs : List Mv) (hv : Valid (locations x₀) (flat ps)) :
    playOut (behOf A x₀) (flat ps) (Mv.req q :: rs) =
      (A.law (cfg (locations x₀) (flat ps)) q).bind fun a =>
        playOut (behOf A x₀) (flat ps ++ [Mv.req q] ++ [Mv.serve a]) rs := by
  rw [AJGames.playOut.eq_2, if_pos ⟨rfl, flat_req_valid _ ps q hv⟩]
  show (nextOf A x₀ (flat ps ++ [Mv.req q])).bind _ = _
  unfold nextOf
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, cfg_flat_req,
    PMF.bind_bind, PMF.pure_bind, Option.elim]

theorem expAlg_gen (A : MemorylessPolicy) (x₀ : Fin 2 → ℝ) :
    ∀ (qs : List (ℝ × ℝ)) (ps : List ((ℝ × ℝ) × ℝ)), Valid (locations x₀) (flat ps) →
      ∑' p, playOut (behOf A x₀) (flat ps) (qs.map Mv.req) p * algCost p =
        algCost (flat ps) + memorylessCost A (cfg (locations x₀) (flat ps)) qs := by
  intro qs
  induction qs with
  | nil =>
    intro ps _
    simp only [List.map_nil, playOut, memorylessCost, add_zero]
    rw [tsum_eq_single (flat ps)]
    · simp
    · intro b hb; simp [PMF.pure_apply, hb]
  | cons q qs ih =>
    intro ps hv
    rw [List.map_cons, playOut_step A x₀ ps q _ hv, tsum_bind_mul]
    set L := A.law (cfg (locations x₀) (flat ps)) q
    have hstep : ∀ a, L a * ∑' p, playOut (behOf A x₀) (flat ps ++ [Mv.req q] ++ [Mv.serve a]) (qs.map Mv.req) p * algCost p
        = L a * (algCost (flat ps) + (edist a q.1 +
          memorylessCost A (((cfg (locations x₀) (flat ps)).erase a).cons q.2) qs)) := by
      intro a
      by_cases hz : L a = 0
      · rw [hz, zero_mul, zero_mul]
      · have hmem : a ∈ cfg (locations x₀) (flat ps) :=
          A.supported _ q a (cfg_card _ _ hv (card_locations x₀)) hz
        have := ih (ps ++ [(q, a)]) (by rw [flat_snoc]; exact flat_pair_valid _ ps q a hv hmem)
        rw [flat_snoc, algCost_flat_pair, cfg_flat_pair] at this
        rw [this, add_assoc]
    simp_rw [hstep, mul_add]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    simp only [memorylessCost]
    congr 1
    apply tsum_congr; intro a
    ring

theorem expOpt_gen (A : MemorylessPolicy) (x₀ : Fin 2 → ℝ) (f : List (ℝ × ℝ) → ℝ≥0∞) :
    ∀ (qs : List (ℝ × ℝ)) (ps : List ((ℝ × ℝ) × ℝ)), Valid (locations x₀) (flat ps) →
      ∑' p, playOut (behOf A x₀) (flat ps) (qs.map Mv.req) p * f (reqs p) =
        f (reqs (flat ps) ++ qs) := by
  intro qs
  induction qs with
  | nil =>
    intro ps _
    simp only [List.map_nil, playOut, List.append_nil]
    rw [tsum_eq_single (flat ps)]
    · simp
    · intro b hb; simp [PMF.pure_apply, hb]
  | cons q qs ih =>
    intro ps hv
    rw [List.map_cons, playOut_step A x₀ ps q _ hv, tsum_bind_mul]
    set L := A.law (cfg (locations x₀) (flat ps)) q
    have hstep : ∀ a, L a * ∑' p, playOut (behOf A x₀) (flat ps ++ [Mv.req q] ++ [Mv.serve a]) (qs.map Mv.req) p * f (reqs p)
        = L a * f (reqs (flat ps) ++ q :: qs) := by
      intro a
      by_cases hz : L a = 0
      · rw [hz, zero_mul, zero_mul]
      · have hmem : a ∈ cfg (locations x₀) (flat ps) :=
          A.supported _ q a (cfg_card _ _ hv (card_locations x₀)) hz
        have := ih (ps ++ [(q, a)]) (by rw [flat_snoc]; exact flat_pair_valid _ ps q a hv hmem)
        rw [flat_snoc] at this
        rw [this, reqs_append, reqs_append]
        simp [reqs]
    simp_rw [hstep]
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem behOf_dependsOn (A : MemorylessPolicy) (x₀ : Fin 2 → ℝ) :
    (behOf A x₀).DependsOn fun s => (cfg (locations x₀) s, s.getLast?) := by
  intro s t h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  show nextOf A x₀ s = nextOf A x₀ t
  unfold nextOf
  rw [h2]
  cases t.getLast? with
  | none => rfl
  | some m => cases m with
    | req q => rw [h1]
    | serve a => rfl

/-- **The bridge.** A memoryless 2-taxi policy, read as a behaviour strategy, depends only on
(configuration, last move); against the request script `qs` its expected AJ cost is the platform's
`memorylessCost`, and its expected offline optimum is `optCost`. -/
theorem solution (A : MemorylessPolicy) (x₀ : Fin 2 → ℝ) :
    (behOf A x₀).DependsOn (fun s => (cfg (locations x₀) s, s.getLast?)) ∧
    ∀ qs : List (ℝ × ℝ),
      expAlg (costed x₀) (behOf A x₀) (qs.map Mv.req) = memorylessCost A (locations x₀) qs ∧
      expOpt (costed x₀) (behOf A x₀) (qs.map Mv.req) = optCost x₀ qs := by
  refine ⟨behOf_dependsOn A x₀, fun qs => ⟨?_, ?_⟩⟩
  · show ∑' p, playOut (behOf A x₀) [] (qs.map Mv.req) p * algCost p = _
    have := expAlg_gen A x₀ qs [] trivial
    have e1 : algCost (flat []) = 0 := rfl
    have e2 : cfg (locations x₀) (flat []) = locations x₀ := rfl
    rw [e1, e2, zero_add] at this
    exact this
  · show ∑' p, playOut (behOf A x₀) [] (qs.map Mv.req) p * optCost x₀ (reqs p) = _
    exact expOpt_gen A x₀ (optCost x₀) qs [] trivial

