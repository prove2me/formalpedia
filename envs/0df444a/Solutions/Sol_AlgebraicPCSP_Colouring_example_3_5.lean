-- Prove2me | solution 1 for AlgebraicPCSP.Colouring.example_3_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T00:53:08.28042+00:00
-- url     : https://prove2.me/submissions/857abd92-2dd1-48fe-aa1f-78636ef88b72

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Colouring_Minion
import Definitions.Def_AlgebraicPCSP_Colouring_Structures

open PCSPBLPAff.Symmetric
open AlgebraicPCSP.Colouring

def exampleMatrix : Fin 6 → Fin 3 → Fin 2 :=
  fun l c =>
    match c with
    | 0 => (![0, 0, 1, 1, 1, 0] : Fin 6 → Fin 2) l
    | 1 => (![0, 1, 0, 1, 0, 1] : Fin 6 → Fin 2) l
    | 2 => (![1, 0, 0, 0, 1, 1] : Fin 6 → Fin 2) l

theorem solution (k : ℕ) (hk : 2 ≤ k) :
    ¬ ∃ f ∈ (HMinion k hk).mem 2, ∃ g ∈ (HMinion k hk).mem 6, ∀ x y : Fin 2,
      f ![x, y] = g ![x, x, y, y, y, x] ∧ f ![x, y] = g ![x, y, x, y, x, y] ∧
        f ![x, y] = g ![y, x, x, x, y, y] := by
  rintro ⟨f, -, g, ⟨-, hg⟩, hfg⟩
  have hrows : ∀ l : Fin 6, exampleMatrix l ∈ (Hgraph 2).rel () := by
    intro l
    change ¬ (exampleMatrix l 0 = exampleMatrix l 1 ∧ exampleMatrix l 1 = exampleMatrix l 2)
    fin_cases l <;> decide
  have hcol := hg () exampleMatrix hrows
  change ¬ (g (fun l => exampleMatrix l 0) = g (fun l => exampleMatrix l 1) ∧
    g (fun l => exampleMatrix l 1) = g (fun l => exampleMatrix l 2)) at hcol
  have hc0 : (fun l => exampleMatrix l 0) = ![0, 0, 1, 1, 1, 0] := rfl
  have hc1 : (fun l => exampleMatrix l 1) = ![0, 1, 0, 1, 0, 1] := rfl
  have hc2 : (fun l => exampleMatrix l 2) = ![1, 0, 0, 0, 1, 1] := rfl
  rw [hc0, hc1, hc2] at hcol
  obtain ⟨h1, h2, h3⟩ := hfg 0 1
  exact hcol ⟨h1.symm.trans h2, h2.symm.trans h3⟩
