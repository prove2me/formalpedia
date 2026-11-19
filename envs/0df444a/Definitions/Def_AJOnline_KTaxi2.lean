-- Prove2me | Definitions.Def_AJOnline_KTaxi2
-- name    : AJOnline_KTaxi2
-- status  : Definition
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:30:08.894344+00:00
-- url     : https://prove2.me/theorems/f1f27c08-80d9-40b9-b4e0-f7f0a7733cc9
-- title:
--   The 2-taxi problem on $\mathbb R$ as a costed AJ game
-- statement:
--   Fix a labelled start $x_0\in\mathbb R^2$, with configuration $X_0=\{x_0(0),x_0(1)\}$ (a multiset).
--
--   - **Moves.** Opponent's moves are requests $\mathrm{req}(q)$, with $q=(q_1,q_2)\in\mathbb R^2$ the pickup and drop-off. Player's moves are $\mathrm{serve}(a)$, $a\in\mathbb R$, meaning the taxi standing at $a$ is sent.
--   - **Legal plays.** A legal play is a sequence $\mathrm{req}(q^1),\mathrm{serve}(a^1),\mathrm{req}(q^2),\mathrm{serve}(a^2),\dots$, possibly ending with one unanswered request. Each $a^i$ must lie in the current configuration $X_{i-1}$, and the configuration updates as
--   $$X_i=\{q^i_2\}+(X_{i-1}-\{a^i\}).$$
--   - **Costs.** The algorithm's cost of a play is $\sum_i|a^i-q^i_1|$, the empty drives. The offline optimum is the platform's $\mathrm{optCost}_{x_0}$ of its requests.
--   - **Policies as strategies.** A memoryless policy $A$ (a law over serving locations for each configuration and request, supported on occupied locations and lazy) becomes the behaviour strategy $\beta_A$. After a request $q$ in configuration $X$, $\beta_A$ draws the serving location from $A$'s law at $(X,q)$. Otherwise it does not move.
--
--   This arena connects the AJ vocabulary to the platform's memoryless 2-taxi results.
--
--   **Formalization Note** The arena depends on $x_0$. Serving from an unoccupied location is illegal; without this, serving from the pickup would cost nothing.
-- source:
--   C. Coester, Y. Huang, T.-Y. Poon, The k-Taxi Problem Is Competitive on All Metrics, STOC 2027 submission #96 (2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, §1 and Appendix C (hard 2-taxi model, memoryless policies), as formalized on this platform in KTaxi.Competitive.Supplement (MemorylessPolicy, memorylessCost, optCost)

import Mathlib
import Definitions.Def_AJOnline_CostedGame
import Definitions.Def_KTaxi_Competitive_Supplement_Memoryless

/-!
# The 2-taxi problem as a costed AJ game

Bridge from the platform's memoryless 2-taxi model
(`KTaxi.Competitive.Supplement.MemorylessPolicy`, `memorylessCost`, `optCost`) to
Abramsky–Jagadeesan games. Opponent's moves are requests `req q` (pickup `q.1`, drop-off `q.2`).
Player's moves are `serve a`, sending the taxi that stands at location `a`. After `req q, serve a`
the configuration `X` becomes `q.2 ::ₘ X.erase a`, as in `memorylessCost`.

**Formalization Note.** The arena depends on the labelled start `x₀`. A play is legal when it
alternates request, service, request, …, opens with a request, and every service sends a taxi from
an occupied location (`a ∈ X`). The algorithm's cost of a play is the sum of the empty-drive
distances `|a - q.1|`; serving the passenger from `q.1` to `q.2` is free, as in the platform's model.
The offline optimum of a play is `optCost x₀` of its requests.
-/

namespace AJOnline.KTaxi2

open AJGames KTaxi.Competitive.Supplement
open scoped ENNReal NNReal

/-- Moves: a request (Opponent) or the location of the taxi sent to serve it (Player). -/
inductive Mv
  | req (q : ℝ × ℝ)
  | serve (a : ℝ)

/-- Requests are Opponent moves, services are Player moves. -/
def lab : Mv → Pl
  | .req _ => Pl.O
  | .serve _ => Pl.P

/-- Legal plays from configuration `X`: request/service pairs, each service from an occupied
location, possibly followed by one unanswered request. -/
def Valid : Multiset ℝ → List Mv → Prop
  | _, [] => True
  | _, [.req _] => True
  | X, .req q :: .serve a :: rest => a ∈ X ∧ Valid ((X.erase a).cons q.2) rest
  | _, _ => False

theorem valid_prefix : ∀ (X : Multiset ℝ) (t s : List Mv), s <+: t → Valid X t → Valid X s
  | X, [], s, h, _ => by rw [List.prefix_nil.1 h]; trivial
  | X, [.req q], s, h, _ => by
    rcases List.prefix_cons_iff.1 h with h' | ⟨u, hu, hu'⟩
    · rw [h']; trivial
    · subst hu; rw [List.prefix_nil.1 hu']; trivial
  | X, .req q :: .serve a :: rest, s, h, ht => by
    rcases List.prefix_cons_iff.1 h with h' | ⟨u, hu, hu'⟩
    · rw [h']; trivial
    · subst hu
      rcases List.prefix_cons_iff.1 hu' with h'' | ⟨v, hv, hv'⟩
      · rw [h'']; trivial
      · subst hv
        exact ⟨ht.1, valid_prefix _ rest v hv' ht.2⟩
  | X, .req _ :: .req _ :: _, _, _, ht => ht.elim
  | X, .serve _ :: _, _, _, ht => ht.elim

theorem valid_head : ∀ (X : Multiset ℝ) (s : List Mv), Valid X s → ∀ m, s.head? = some m → lab m = Pl.O
  | _, [], _, m, hm => by simp at hm
  | _, [.req _], _, m, hm => by simp at hm; subst hm; rfl
  | _, .req _ :: .serve _ :: _, _, m, hm => by simp at hm; subst hm; rfl
  | _, .req _ :: .req _ :: _, ht, _, _ => ht.elim
  | _, .serve _ :: _, ht, _, _ => ht.elim

theorem valid_alt : ∀ (X : Multiset ℝ) (s : List Mv), Valid X s → Alt lab s
  | _, [], _ => List.isChain_nil
  | _, [.req _], _ => List.isChain_singleton _
  | X, .req q :: .serve a :: rest, ht => by
    have ih := valid_alt _ rest ht.2
    have hh := valid_head _ rest ht.2
    unfold Alt at ih ⊢
    refine List.IsChain.cons_cons (by simp [lab]) ?_
    cases rest with
    | nil => exact List.isChain_singleton _
    | cons m rest' =>
      refine List.IsChain.cons_cons ?_ ih
      rw [hh m rfl]; simp [lab]
  | _, .req _ :: .req _ :: _, ht => ht.elim
  | _, .serve _ :: _, ht => ht.elim

/-- The 2-taxi game from the labelled start `x₀`. -/
@[reducible] def game (x₀ : Fin 2 → ℝ) : AJGames.Game.{0} where
  M := Mv
  lab := lab
  pos := {s | Valid (locations x₀) s}
  nil_mem := trivial
  prefix_closed := fun s t h ht => valid_prefix _ t s h ht
  alt := fun s hs => valid_alt _ s hs

/-- The taxi configuration after a play, starting from `X`. -/
noncomputable def cfg : Multiset ℝ → List Mv → Multiset ℝ
  | X, .req q :: .serve a :: rest => cfg ((X.erase a).cons q.2) rest
  | X, _ => X

/-- The algorithm's cost of a play: the sum of the empty-drive distances. -/
noncomputable def algCost : List Mv → ℝ≥0∞
  | .req q :: .serve a :: rest => edist a q.1 + algCost rest
  | _ => 0

/-- The requests of a play. -/
def reqs (s : List Mv) : List (ℝ × ℝ) :=
  s.filterMap fun
    | .req q => some q
    | .serve _ => none

/-- The 2-taxi problem from the labelled start `x₀`, as a costed game. -/
noncomputable def costed (x₀ : Fin 2 → ℝ) : CostedGame.{0} where
  G := game x₀
  alg := algCost
  opt s := optCost x₀ (reqs s)

theorem cfg_card : ∀ (X : Multiset ℝ) (s : List Mv), Valid X s → X.card = 2 → (cfg X s).card = 2
  | _, [], _, h => h
  | _, [.req _], _, h => h
  | X, .req q :: .serve a :: rest, ht, h => by
    refine cfg_card _ rest ht.2 ?_
    rw [Multiset.card_cons, Multiset.card_erase_of_mem ht.1, h]; rfl
  | _, .req _ :: .req _ :: _, ht, _ => ht.elim
  | _, .serve _ :: _, ht, _ => ht.elim

theorem valid_snoc_serve : ∀ (X : Multiset ℝ) (s : List Mv) (q : ℝ × ℝ) (c : ℝ),
    Valid X s → s.getLast? = some (Mv.req q) → c ∈ cfg X s → Valid X (s ++ [Mv.serve c])
  | _, [], _, _, _, hl, _ => by simp at hl
  | X, [.req q'], q, c, _, hl, hc => ⟨hc, trivial⟩
  | X, .req q' :: .serve a :: rest, q, c, ht, hl, hc => by
    refine ⟨ht.1, valid_snoc_serve _ rest q c ht.2 ?_ hc⟩
    cases rest with
    | nil => simp at hl
    | cons m rest' => simpa using hl
  | _, .req _ :: .req _ :: _, _, _, ht, _, _ => ht.elim
  | _, .serve _ :: _, _, _, ht, _, _ => ht.elim

/-- The next-move distribution of a memoryless policy, read off the history. -/
noncomputable def nextOf (A : MemorylessPolicy) (x₀ : Fin 2 → ℝ) (s : List Mv) : PMF (Option Mv) :=
  match s.getLast? with
  | some (.req q) => (A.law (cfg (locations x₀) s) q).bind fun a => PMF.pure (some (Mv.serve a))
  | _ => PMF.pure none

theorem card_locations (x₀ : Fin 2 → ℝ) : (locations x₀).card = 2 := by
  simp [locations]

theorem nextOf_legal (A : MemorylessPolicy) (x₀ : Fin 2 → ℝ) (s : List Mv) (a : Mv)
    (ha : nextOf A x₀ s (some a) ≠ 0) :
    PlayerToMove (game x₀) s ∧ (game x₀).lab a = Pl.P ∧
      (s ∈ (game x₀).pos → s ++ [a] ∈ (game x₀).pos) := by
  unfold nextOf at ha
  cases hl : s.getLast? with
  | none => simp [hl] at ha
  | some m =>
    cases m with
    | serve b => simp [hl] at ha
    | req q =>
      simp only [hl, PMF.bind_apply, PMF.pure_apply] at ha
      obtain ⟨c, rfl, hc⟩ : ∃ c, a = Mv.serve c ∧ A.law (cfg (locations x₀) s) q c ≠ 0 := by
        by_contra hne
        push Not at hne
        apply ha
        apply ENNReal.tsum_eq_zero.2
        intro c
        by_cases h : some a = some (Mv.serve c)
        · rw [hne c (Option.some.inj h), zero_mul]
        · rw [if_neg h, mul_zero]
      refine ⟨⟨Mv.req q, hl, rfl⟩, rfl, fun hs => ?_⟩
      have hcard := cfg_card _ s hs (card_locations x₀)
      exact valid_snoc_serve _ s q c hs hl (A.supported _ q c hcard hc)

/-- A memoryless policy as a behaviour strategy: after a request `q` it draws the serving location
from `law (current configuration) q`; otherwise it does not move. -/
noncomputable def behOf (A : MemorylessPolicy) (x₀ : Fin 2 → ℝ) : BehStrategy (game x₀) where
  next := nextOf A x₀
  legal := nextOf_legal A x₀

end AJOnline.KTaxi2


