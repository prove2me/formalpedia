-- Prove2me | Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
-- name    : Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:18:19.029144+00:00
-- url     : https://prove2.me/theorems/3af60f3c-e9c1-4f0f-8fc0-a09447ac2752
-- title:
--   Tops Choice Part B
-- statement:
--   Definitions and structural lemmas for Tops Choice Part B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.G0.TopsWeightFunctionBounds
inductive St where
  | bad
  | good
  | run (K j d : ℕ) (al ev : Bool)
  deriving DecidableEq
def okG (L₂ j d : ℕ) (ev : Bool) : Bool :=
  if j = 0 then !ev else (decide ((d + 1) % 2 = 0) && decide (L₂ < 2 * (d + 1)))
def step (R L₂ : ℕ) : St → Bool → St
  | .bad, _ => .bad
  | .good, _ => .good
  | .run K j d al ev, false => .run K j (d + 1) al (!ev)
  | .run K j d al ev, true =>
      if j + 1 = R then
        (if (al && okG L₂ j d ev) = true then .good
         else if K ≤ 1 then .bad else .run (K - 1) 0 0 true (!ev))
      else .run K (j + 1) 0 (al && okG L₂ j d ev) (!ev)
def runS (R L₂ : ℕ) (s : St) (bs : List Bool) : St := bs.foldl (step R L₂) s
def Wt (R L₂ : ℕ) (δ : ℝ) : ℕ → St → ℝ
  | 0, s => if s = .bad then 1 else 0
  | m + 1, s => δ * Wt R L₂ δ m (step R L₂ s true) + (1 - δ) * Wt R L₂ δ m (step R L₂ s false)
def WF (R : ℕ) : St → Prop
  | .run _ j _ _ _ => j < R
  | _ => True
def aF (L₂ : ℕ) (δ : ℝ) : ℝ := 1 / 2 * (1 - L₂ * δ)
def eF (δ : ℝ) (d : ℕ) : ℝ := if d % 2 = 0 then (1 - δ) / (2 - δ) else 1 / (2 - δ)
def gF (L₂ : ℕ) (δ : ℝ) (j d : ℕ) (ev : Bool) : ℝ :=
  if j = 0 then (if ev = true then (1 - δ) / (2 - δ) else 1 / (2 - δ))
  else (1 - δ) ^ (L₂ / 2 - d) * eF δ (max d (L₂ / 2))
def GF (R L₂ : ℕ) (δ : ℝ) (j d : ℕ) (al ev : Bool) : ℝ :=
  if al = true then aF L₂ δ ^ (R - 1 - j) * gF L₂ δ j d ev else 0
def Phi (R L₂ : ℕ) (δ : ℝ) : St → ℝ
  | .bad => 1
  | .good => 0
  | .run K j d al ev => (1 - aF L₂ δ ^ R) ^ (K - 1) * (1 - GF R L₂ δ j d al ev)
section arith
variable {L₂ : ℕ} {δ : ℝ}
end arith
end Formalism.G0.TopsWeightFunctionBounds
noncomputable section
open scoped BigOperators
namespace Formalism.G0.TopsWeightFunctionBounds
section pot
variable {R L₂ : ℕ} {δ : ℝ}
end pot
end Formalism.G0.TopsWeightFunctionBounds
noncomputable section
open scoped BigOperators
namespace Formalism.G0.TopsWeightFunctionBounds
def wP (δ : ℝ) (U : Finset ℕ) (p : ℕ) : ℝ := if p ∈ U then δ else 1 - δ
section sums
variable {R L₂ : ℕ} {δ : ℝ}
def Lst (n i : ℕ) : List ℕ := (List.range (n - 1)).map (fun t => (i + t + 1) % n)
end sums
end Formalism.G0.TopsWeightFunctionBounds
noncomputable section
open scoped BigOperators
namespace Formalism.G0.TopsWeightFunctionBounds
section comb
variable (n : ℕ) (T : Finset ℕ) (L₂ R b K₀ : ℕ)
def cnt (t : ℕ) : ℕ := ((Finset.range (t + 1)).filter (fun d => (b + d) % n ∈ T)).card
def PRun (j t d : ℕ) (u : Fin j → ℕ) : Prop :=
  StrictMono u ∧ (∀ l, u l ≤ t) ∧ (∀ l, (b + u l) % n ∈ T) ∧ (∀ l, Even ((b + u l) % n)) ∧
  (∀ (l : Fin j) (h : l.val + 1 < j), L₂ < 2 * (u ⟨l.val + 1, h⟩ - u l) ∧
      ∀ x, u l < x → x < u ⟨l.val + 1, h⟩ → (b + x) % n ∉ T) ∧
  (∀ h : 0 < j, u ⟨j - 1, by omega⟩ = t - d)
def Inv (t : ℕ) : St → Prop
  | .bad => True
  | .good => GoodRun n T L₂ R b t
  | .run K j d al ev => 1 ≤ K ∧ K ≤ K₀ ∧ j < R ∧ d ≤ t ∧ ev = decide (Even (b + t)) ∧
      (b + (t - d)) % n ∈ T ∧ (∀ x, t - d < x → x ≤ t → (b + x) % n ∉ T) ∧
      cnt n T b t = 1 + R * (K₀ - K) + j ∧
      (al = true → ∃ u : Fin j → ℕ, PRun n T L₂ b j t d u)
def Ls (t m : ℕ) : List Bool := (List.range m).map (fun x => decide ((b + (t + 1 + x)) % n ∈ T))
end comb
def snocF {j : ℕ} (u : Fin j → ℕ) (v : ℕ) : Fin (j + 1) → ℕ :=
  fun l => if h : l.val < j then u ⟨l.val, h⟩ else v
def init (K : ℕ) (ev : Bool) : St := if K = 0 then .bad else .run K 0 0 true ev
end Formalism.G0.TopsWeightFunctionBounds
noncomputable section
open scoped BigOperators
namespace Formalism.G0.TopsWeightFunctionBounds
end Formalism.G0.TopsWeightFunctionBounds
namespace Formalism.G0
end Formalism.G0


