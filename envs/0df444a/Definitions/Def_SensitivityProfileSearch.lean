-- Prove2me | Definitions.Def_SensitivityProfileSearch
-- name    : SensitivityProfileSearch
-- status  : Definition
-- author  : @dmilosch
-- created : 2026-10-21T22:14:16.409977+00:00
-- url     : https://prove2.me/theorems/f7c7878e-9a45-40b5-a1ef-37df7b637c2d
-- title:
--   Deterministic interval-envelope dynamics for sensitivity profiles
-- statement:
--   This interface defines an arithmetic search at the proved labeling parameters
--
--   $$K=14055,\quad d=7027,\quad t=24,\quad w=22,\quad (v_0,\ldots,v_5)=(24,31,38,44,50,55).$$
--
--   A profile consists of two natural-number matrices. Its interval envelope replaces an entry indexed by $i\le j$ by the minimum over every contained interval $[a,b]\subseteq[i,j]$. Entries below the diagonal are set to zero. The normalized initial profile is the envelope of each input matrix. Each subsequent profile is obtained by applying the exact one-step recurrence from `SensitivityProfileCycle`, then taking its interval envelope. A finite list of recipes is repeated periodically.
--
--   `PositiveUpper` requires all upper-triangular initial input entries to be at least one. `ReturnsWithin` checks that the computed profile after one complete period is entrywise at most a specified natural number $R$ times the normalized initial profile. These definitions involve only finite index sets and natural-number arithmetic; they contain no unknown graph, labeling, Boolean function, or separation assertion.
-- source:
--   Original deterministic interval-envelope reduction of the recursive profiles in accepted Prove2Me submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a, https://prove2.me/theorems/46659a00-722d-4dc9-b28e-ef02d6a0c9c2. Exact source components: SensitivitySourceLabeling14055Q5.shared_labeling_source_below_14055_q5_lll and SensitivityNQ.rawZeroSourceCombined/rawOne. Authors: yousofy with Codex; retains OpenAI/math, Robin Kothari with Codex, and earlier community attribution. The arithmetic 2.15 orbit conjecture is new and is not proved by that source.

import Definitions.Def_SensitivityProfileCycle

/-!
A deterministic arithmetic search interface for recursive sensitivity profiles.
The recurrence is that of SensitivityProfileCycle, specialized to the proved
14055-vertex labeling parameters in accepted Prove2Me submission
a9d25c46-43bd-4fb1-826b-0ed075b8cf0a (yousofy with Codex, retaining the
OpenAI/math, Robin Kothari with Codex, and community attributions).
The interval envelope and periodic orbit below are new search interfaces.
No definition asserts that this fixed-parameter search reaches 2.15.
-/

set_option autoImplicit false
namespace SensitivityProfileSearch
open SensitivityProfileCycle

abbrev Matrix (n : ℕ) := Fin n → Fin n → ℕ

def intervals {n : ℕ} (i j : Fin n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun ab => i ≤ ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 ≤ j)

theorem intervals_nonempty {n : ℕ} {i j : Fin n} (hij : i ≤ j) :
    (intervals i j).Nonempty := by
  exact ⟨(i, j), by simp [intervals, hij]⟩

/-- Minimum over all nonempty subintervals; lower triangular entries are unused. -/
def envelope {n : ℕ} (A : Matrix n) (i j : Fin n) : ℕ :=
  if hij : i ≤ j then
    (intervals i j).inf' (intervals_nonempty hij) (fun ab => A ab.1 ab.2)
  else 0

structure Profile (n : ℕ) where
  zero : Matrix n
  one : Matrix n

def normalize {n : ℕ} (P : Profile n) : Profile n :=
  ⟨envelope P.zero, envelope P.one⟩

def cutoffs : Fin 6 → ℕ := ![24, 31, 38, 44, 50, 55]

/-- One deterministic stage at the known simultaneous-labeling parameters. -/
def step {n : ℕ} (C : Recipe n) (P : Profile n) : Profile n :=
  ⟨envelope (rawZeroSourceCombined 14055 24 (extendCutoffs cutoffs) 22 C P.zero P.one),
   envelope (rawOne 7027 C P.zero P.one)⟩

def periodicRecipe {n p : ℕ} (recipes : Fin (p+1) → Recipe n) (d : ℕ) : Recipe n :=
  recipes ⟨d % (p+1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩

def orbit {n p : ℕ} (recipes : Fin (p+1) → Recipe n) (initial : Profile n) :
    ℕ → Profile n
  | 0 => normalize initial
  | d+1 => step (periodicRecipe recipes d) (orbit recipes initial d)

def PositiveUpper {n : ℕ} (P : Profile n) : Prop :=
  ∀ i j, i ≤ j → 1 ≤ P.zero i j ∧ 1 ≤ P.one i j

/-- A return test on the explicitly computed orbit; no graph data are involved. -/
def ReturnsWithin {n p : ℕ} (recipes : Fin (p+1) → Recipe n)
    (initial : Profile n) (radius : ℕ) : Prop :=
  ∀ i j, i ≤ j →
    (orbit recipes initial (p+1)).zero i j ≤
      (normalize initial).zero i j * radius ∧
    (orbit recipes initial (p+1)).one i j ≤
      (normalize initial).one i j * radius

end SensitivityProfileSearch


