-- Prove2me | Definitions.Def_KServer_shadow
-- name    : KServer_shadow
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T14:19:10.183213+00:00
-- url     : https://prove2.me/theorems/8f29ee54-427c-45ba-8058-31a34bb7f7d6
-- title:
--   Shadow evaders along nonexpansive projections
-- statement:
--   Let $X, Y$ be metric spaces, $\pi : Y \to X$ a nonexpansive map, and $G$ a transformation of request sets from $X$ to $Y$ such that $\pi$ maps $G(S)$ into $S$ and $G(S)$ is nonempty whenever $S$ is. An online evader $E$ on $Y$, playing after a fixed foreign history $h_0$ against the $G$-transformed requests, induces a shadow evader on $X$ whose position is the $\pi$-projection of $E$'s position. The shadow is again a valid online evader, its chunk costs are dominated by $E$'s chunk costs on the transformed chunks, bail times transport exactly along the transformation, and consequently its bail-aware cost at any price $p$ is dominated by $E$'s bail-aware cost at any price $p' \ge p$: $$\mathrm{bailCost}_{\mathrm{shadow}}(h, \chi, p) \le \mathrm{bailCost}_{E}(h_0 + G(h),\, G(\chi),\, p').$$ This is the engine that converts level-$w$ conditional cost premises into level-$(w{+}1)$ premises in the stage constructions of the BCR lower bound: $\pi$ is a nonexpansive retraction of the glued level step onto one embedded copy, and $G$ places a request into the step, possibly as a union over two copies or united with parking sets.
-- source:
--   BCR randomized k-server lower bound, stage construction layer

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_bail_append

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace KServer

/-! ### Shadow evaders along nonexpansive projections

An online evader on a large space `Y`, facing requests obtained from
requests on a small space `X` through a set transformation `G` (with a
projection `π : Y → X` mapping each `G S` into `S`, nonexpansively),
induces an online evader on `X` whose bail-aware cost it dominates.  This
is the engine turning the level-`w` cost premises into level-`w+1` cost
premises in the BCR stage constructions: `π` is a nonexpansive retraction
of the level step onto one copy, and `G` places a request into the step
(one or two embedded copies, possibly united with parking sets). -/

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- Transform a request sequence by a set map. -/
def reqMap (G : Set X → Set Y) (l : List (Set X)) : List (Set Y) :=
  l.map G

theorem reqMap_append (G : Set X → Set Y) (l l' : List (Set X)) :
    reqMap G (l ++ l') = reqMap G l ++ reqMap G l' := by
  unfold reqMap
  rw [List.map_append]

theorem reqMap_take (G : Set X → Set Y) (l : List (Set X)) (n : ℕ) :
    reqMap G (l.take n) = (reqMap G l).take n := by
  unfold reqMap
  rw [List.map_take]

theorem reqMap_length (G : Set X → Set Y) (l : List (Set X)) :
    (reqMap G l).length = l.length := by
  unfold reqMap
  rw [List.length_map]

theorem reqMap_flatten (G : Set X → Set Y) (L : List (List (Set X))) :
    reqMap G L.flatten = (L.map (reqMap G)).flatten := by
  unfold reqMap
  rw [List.map_flatten]

/-- The shadow of an evader on `Y` under a projection `π` compatible with
the request transformation `G`, after a fixed foreign prefix `h₀`. -/
noncomputable def shadowEvader (π : Y → X) (G : Set X → Set Y)
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    (E : EvaderAlgorithm Y) (h₀ : List (Set Y)) : EvaderAlgorithm X where
  pos l := π (E.pos (h₀ ++ reqMap G l))
  serves l S hS := by
    have h1 := E.serves (h₀ ++ reqMap G l) (G S) (hGne S hS)
    have he : h₀ ++ reqMap G (l ++ [S]) = (h₀ ++ reqMap G l) ++ [G S] := by
      rw [reqMap_append, List.append_assoc]
      rfl
    rw [← he] at h1
    exact hG S _ h1

/-- One appended request adds one movement step to the chunk cost. -/
theorem EvaderAlgorithm.costOn_concat (E : EvaderAlgorithm X)
    (h χ : List (Set X)) (S : Set X) :
    E.costOn h (χ ++ [S])
      = E.costOn h χ + dist (E.pos (h ++ χ)) (E.pos (h ++ χ ++ [S])) := by
  unfold EvaderAlgorithm.costOn
  rw [← List.append_assoc, E.cost_concat]
  ring

/-- **Shadow cost domination**: the shadow's chunk cost is dominated by the
original evader's chunk cost on the transformed chunk. -/
theorem shadow_costOn_le (π : Y → X) (G : Set X → Set Y)
    (hπ : ∀ y z : Y, dist (π y) (π z) ≤ dist y z)
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    (E : EvaderAlgorithm Y) (h₀ : List (Set Y)) (h χ : List (Set X)) :
    (shadowEvader π G hG hGne E h₀).costOn h χ
      ≤ E.costOn (h₀ ++ reqMap G h) (reqMap G χ) := by
  induction χ using List.reverseRecOn with
  | nil =>
    have h1 : (shadowEvader π G hG hGne E h₀).costOn h [] = 0 := by
      unfold EvaderAlgorithm.costOn
      rw [List.append_nil, sub_self]
    have h2 : reqMap G ([] : List (Set X)) = [] := rfl
    rw [h1, h2]
    exact E.costOn_nonneg _ _
  | append_singleton χ S ih =>
    rw [EvaderAlgorithm.costOn_concat, reqMap_append,
      show reqMap G [S] = [G S] from rfl,
      EvaderAlgorithm.costOn_concat]
    have hstep : dist ((shadowEvader π G hG hGne E h₀).pos (h ++ χ))
        ((shadowEvader π G hG hGne E h₀).pos (h ++ χ ++ [S]))
        ≤ dist (E.pos ((h₀ ++ reqMap G h) ++ reqMap G χ))
            (E.pos ((h₀ ++ reqMap G h) ++ reqMap G χ ++ [G S])) := by
      show dist (π (E.pos (h₀ ++ reqMap G (h ++ χ))))
          (π (E.pos (h₀ ++ reqMap G (h ++ χ ++ [S])))) ≤ _
      have e1 : h₀ ++ reqMap G (h ++ χ) = (h₀ ++ reqMap G h) ++ reqMap G χ := by
        rw [reqMap_append, List.append_assoc]
      have e2 : h₀ ++ reqMap G (h ++ χ ++ [S])
          = (h₀ ++ reqMap G h) ++ reqMap G χ ++ [G S] := by
        rw [reqMap_append, reqMap_append,
          show reqMap G [S] = [G S] from rfl]
        simp [List.append_assoc]
      rw [e1, e2]
      exact hπ _ _
    linarith [ih]

private theorem find?_congr3 {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.find?_cons]
    rw [h a (List.mem_cons_self ..)]
    cases q a
    · exact ih fun a ha => h a (List.mem_cons_of_mem _ ha)
    · rfl

/-- Bail times transport along the request transformation. -/
theorem shadow_bailTime (G : Set X → Set Y) (bail : List (Set Y) → Bool)
    (h₀ : List (Set Y)) (h χ : List (Set X)) :
    bailTime (fun l => bail (h₀ ++ reqMap G l)) h χ
      = bailTime bail (h₀ ++ reqMap G h) (reqMap G χ) := by
  unfold bailTime
  rw [reqMap_length]
  refine find?_congr3 _ _ _ fun q _ => ?_
  show bail (h₀ ++ reqMap G (h ++ List.take q χ)) = _
  congr 1
  rw [reqMap_append, reqMap_take, ← List.append_assoc]

/-- **Shadow bail-cost domination**: the shadow's bail-aware cost, with the
transported bail rule and any smaller price, is dominated by the original
evader's bail-aware cost. -/
theorem shadow_bailCost_le (π : Y → X) (G : Set X → Set Y)
    (hπ : ∀ y z : Y, dist (π y) (π z) ≤ dist y z)
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    (E : EvaderAlgorithm Y) (bail : List (Set Y) → Bool)
    (h₀ : List (Set Y)) (h χ : List (Set X)) {p p' : ℝ} (hp : p ≤ p') :
    (shadowEvader π G hG hGne E h₀).bailCost
        (fun l => bail (h₀ ++ reqMap G l)) h χ p
      ≤ E.bailCost bail (h₀ ++ reqMap G h) (reqMap G χ) p' := by
  unfold EvaderAlgorithm.bailCost
  rw [shadow_bailTime]
  rcases hq : bailTime bail (h₀ ++ reqMap G h) (reqMap G χ) with - | q
  · exact shadow_costOn_le π G hπ hG hGne E h₀ h χ
  · have h1 := shadow_costOn_le π G hπ hG hGne E h₀ h (χ.take q)
    rw [reqMap_take] at h1
    linarith

end KServer


