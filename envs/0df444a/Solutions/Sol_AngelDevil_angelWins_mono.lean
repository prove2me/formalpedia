-- Prove2me | solution 1 for AngelDevil.angelWins_mono
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-19T13:22:37.436089+00:00
-- url     : https://prove2.me/submissions/1ab1767e-a9a6-4fdb-961a-4b54c7e3a09d

import Definitions.Def_AngelDevil_KingGuard
import Definitions.Def_AngelDevil_FiniteGame
import Mathlib.Tactic.FinCases

set_option maxRecDepth 2000
set_option maxHeartbeats 2000000

namespace AngelDevil

theorem jump_mono {p q : Nat} (hpq : p ≤ q) {u v : Point}
    (h : Jump p u v) : Jump q u v := by
  unfold Jump at *
  omega

theorem survives_mono {p q : Nat} (hpq : p ≤ q)
    {A : AngelStrategy} {D : DevilStrategy} (h : Survives p A D) :
    Survives q A D := by
  intro n
  exact ⟨jump_mono hpq (h n).1, (h n).2⟩

theorem angelWins_mono {p q : Nat} (hpq : p ≤ q)
    (h : AngelWins p) : AngelWins q := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, fun D => survives_mono hpq (hA D)⟩

end AngelDevil

theorem solution {p q : Nat} (hpq : p ≤ q) (h : AngelDevil.AngelWins p) :
    AngelDevil.AngelWins q := AngelDevil.angelWins_mono hpq h
