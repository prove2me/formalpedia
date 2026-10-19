-- Prove2me | Definitions.Def_AngelDevil_FiniteGame
-- name    : AngelDevil_FiniteGame
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-18T13:36:52.364498+00:00
-- url     : https://prove2.me/theorems/3524c509-2ef4-4572-9b71-7d0a30266b17
-- title:
--   Finite-game viability and history-based counterstrategies
-- statement:
--   Finite viability is defined recursively: zero further rounds are always viable; one more round is viable when every optional Devil selection admits a safe Angel landing with a viable remaining state. The finite Angel selects such a landing when one exists. A bad Devil move makes every safe landing nonviable when such a move exists. Burn-history reconstruction turns these state-based choices into a total history-only Devil strategy. Off-path choices and exhausted horizons have explicitly defined defaults.
-- source:
--   Mathe, The Angel of power 2 wins (2007), https://doi.org/10.1017/S0963548306008303, author manuscript pp. 1-2: determinacy observation and Claim 2.1; auxiliary formalization definitions.

import Definitions.Def_AngelDevil_FiniteHorizon

namespace AngelDevil

def advance (s : State) (d : Option Point) (v : Point) : State :=
  ⟨s.visited ++ [v], s.burned ++ [d]⟩

def Viable (p : Nat) : Nat → State → Prop
  | 0, _ => True
  | n+1, s => ∀ d : Option Point, ∃ v : Point,
      Jump p (current s) v ∧ some v ∉ s.burned ++ [d] ∧
      Viable p n (advance s d v)

noncomputable def finiteAngel (p T : Nat) : AngelStrategy := by
  classical
  intro h b
  exact if hv : ∃ v, Jump p (h.getLastD origin) v ∧ some v ∉ b ∧
      Viable p (T-h.length) ⟨h ++ [v], b⟩ then Classical.choose hv else origin

noncomputable def badMove (p n : Nat) (s : State) : Option Point := by
  classical
  exact if hd : ∃ d : Option Point, ∀ v,
      Jump p (current s) v → some v ∉ s.burned ++ [d] →
      ¬ Viable p n (advance s d v) then Classical.choose hd else none

/- Reconstruct a state-dependent Devil's own earlier selections from the
visited history. This preserves the mission's history-only Devil interface. -/
def simulatedBurns (choose : State → Option Point) (h : List Point) :
    List (Option Point) :=
  if _hnil : h = [] then [] else
  let prior := h.dropLast
  if prior = [] then [] else
  let b := simulatedBurns choose prior
  b ++ [choose ⟨prior, b⟩]
termination_by h.length
decreasing_by
  have hp := List.length_pos_iff.mpr _hnil
  simp only [List.length_dropLast]
  omega

def historyDevil (choose : State → Option Point) : DevilStrategy :=
  fun h => choose ⟨h, simulatedBurns choose h⟩

noncomputable def finiteDevil (p T : Nat) : DevilStrategy :=
  historyDevil (fun s => badMove p (T-s.visited.length) s)

end AngelDevil


