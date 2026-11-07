-- Prove2me | Definitions.Def_BlockSSM_Tracker_wordRes
-- name    : BlockSSM_Tracker_wordRes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:23:23.714808+00:00
-- url     : https://prove2.me/theorems/fbe7306c-8ea0-4a96-b21c-18cce93b30cf
-- title:
--   Restriction $F_s|_V$ of a word map to $V=\mathrm{aff}(R)$
-- statement:
--   For a tracker with reachable set $R$, put $V=\mathrm{aff}(R)$, the affine hull of $R$ in $\mathbb C^n$. Every word map sends $R$ into itself and is affine, so it sends $V$ into $V$. The module defines $V$ and the restriction $F_s|_V:V\to V$, the elements from which the transition monoid is built.
--
--   **Formalization Note** The fact that a word map preserves $V$ is proved in this module, together with the affine form of a transition. Multiplication of self-maps of $V$ is composition.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), §3.2 and Lemma 5, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_BlockSSM_Tracker_IsFiniteState

universe u

namespace BlockSSM

variable {G : Type u} {b : ℕ∞}

/-- The transition `f_g` as an affine map. -/
noncomputable def Tracker.stepAffine (T : Tracker G b) (g : G) : State T.n →ᵃ[ℂ] State T.n :=
  (LinearMap.pi fun i => (Matrix.mulVecLin (T.A g i)).comp
    (LinearMap.proj (R := ℂ) (φ := fun i => Fin (T.n i) → ℂ) i)).toAffineMap +
    AffineMap.const ℂ (State T.n) (T.c g)

theorem Tracker.stepAffine_apply (T : Tracker G b) (g : G) (h : State T.n) :
    T.stepAffine g h = T.step g h := by
  funext i
  simp [Tracker.stepAffine, Tracker.step]

/-- **The affine hull `V = aff(R)` of the reachable set.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), §3.2, p.3 (PDF p.4): "Fix a
finite-state tracker of dimension n, and put V = aff(R)." -/
def Tracker.hull (T : Tracker G b) : AffineSubspace ℂ (State T.n) :=
  affineSpan ℂ T.reach

theorem Tracker.step_mem_hull (T : Tracker G b) (g : G) {x : State T.n} (hx : x ∈ T.hull) :
    T.step g x ∈ T.hull := by
  have h1 : T.stepAffine g x ∈ (affineSpan ℂ T.reach).map (T.stepAffine g) :=
    AffineSubspace.mem_map_of_mem _ hx
  rw [AffineSubspace.map_span] at h1
  rw [T.stepAffine_apply] at h1
  refine affineSpan_mono ℂ ?_ h1
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  refine ⟨s ++ [g], ?_⟩
  simp [Tracker.wordMap, List.foldl_append, T.stepAffine_apply]

theorem Tracker.wordMap_mem_hull (T : Tracker G b) (s : List G) {x : State T.n}
    (hx : x ∈ T.hull) : T.wordMap s x ∈ T.hull := by
  induction s generalizing x with
  | nil => exact hx
  | cons g s ih => exact ih (T.step_mem_hull g hx)

/-- **The restriction `F_s|_V` of a word map to `V = aff(R)`.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Lemma 5, p.3 (PDF p.4).

**Formalization Note.** `Tracker.wordMap_mem_hull`, proved above, says that a word map sends `V`
into `V`. `Function.End` multiplication is composition, `(F * F') x = F (F' x)`. -/
def Tracker.wordRes (T : Tracker G b) (s : List G) : Function.End T.hull :=
  fun x => ⟨T.wordMap s x, T.wordMap_mem_hull s x.2⟩

end BlockSSM


