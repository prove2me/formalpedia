-- Prove2me | Definitions.Def_PrivGaussMS_GoalLayout
-- name    : PrivGaussMS_GoalLayout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:08:53.405401+00:00
-- url     : https://prove2.me/theorems/890b05cf-5e41-4d6f-b65a-937cee8ada4a
-- title:
--   Input and output layout of the mechanism on the published sampling real RAM
-- statement:
--   The goal theorem is about a program of the published real RAM `PolySampIso.Machine` (exact arithmetic on reals with rational literals, indirect addressing, $\sqrt{\cdot}$, $\exp$, $\log$, independent $\mathcal N(0,1)$ and $\mathrm{Exp}(1)$ draws, unit cost per executed instruction). This file fixes how a dataset and the public parameters are handed to the program and where the released batch is read.
--
--   1. Pointer registers hold $p[0]=d$, $p[1]=m$, $p[2]=n$; memory cells $0,1,2$ hold $\alpha,\delta,\varepsilon$; cell $3+i\,d+j$ holds coordinate $j$ of record $i$; every other cell is $0$.
--   2. Coordinate $l$ of released vector $j$ is read from cell $-1-(j\,d+l)$ at the first halting step.
--
--   **Formalization Note** The paper names no machine model; the published machine and these layouts are the reading of "uses $O(n^3)$ operations". Indices are 0-based.
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), Theorem B.1, pp.31–32 ('takes n records in ℝ^d and releases m vectors in ℝ^d … uses O(n³) operations')

import Mathlib
import Definitions.Def_PolySampIso_Machine
import Definitions.Def_PrivGaussMS_Basics

open MeasureTheory

namespace PrivGaussMS

/-!
# Input and output layout of the goal on the published `PolySampIso` real RAM

Moayedi, Yassaee, Ebrahimi, *Optimal Private Gaussian Multi-sampling*, STOC 2027 submission
(manuscript sha256 1838c582…), Theorem B.1, pp.31–32: "an (ε, δ)-differentially private mechanism
`M` that takes `n` records in `ℝ^d` and releases `m` vectors in `ℝ^d` … The mechanism uses `O(n³)`
operations." The paper names no machine model.

**Formalization Note.**
* The machine is the published `PolySampIso.Machine` (real RAM with exact `+ − × ÷`, rational
  literals, indirect addressing, `√`, `exp`, `log`, unit cost per executed instruction, and
  independent i.i.d. `N(0,1)` and `Exp(1)` streams; no floor). Only the initial state and the
  output cells are local.
* Input (`goalInput`): pointer registers `p[0] = d`, `p[1] = m`, `p[2] = n`, all others `0`;
  memory cells `0, 1, 2` hold `α, δ, ε`; cell `3 + i·d + j` holds coordinate `j` of record `i`
  (`i < n`, `j < d`, rows in order); every other cell is `0`; program counter, registers, stream
  cursors and work counter `0`, not halted.
* Output (`outputBatch`): coordinate `l` of output vector `j` is memory cell `−1 − (j·d + l)`
  (`j < m`, `l < d`). `goalOutput` reads it at the first halting step `PolySampIso.haltTime`.
-/

/-- The input memory of the goal: `α, δ, ε` in cells `0, 1, 2`, then the records row by row. -/
noncomputable def goalMem (d n : ℕ) (α δ ε : ℝ) (x : Fin n → Vec d) : ℤ → ℝ := fun a =>
  if a = 0 then α
  else if a = 1 then δ
  else if a = 2 then ε
  else if h : 3 ≤ a ∧ a < 3 + (n : ℤ) * d then
    have hi : (a - 3).toNat < n * d := by
      obtain ⟨N, hN⟩ : ∃ N : ℕ, N = n * d := ⟨_, rfl⟩
      have hc : (n : ℤ) * d = (N : ℤ) := by rw [hN]; push_cast; ring
      rw [← hN]; omega
    have hd : 0 < d := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hi
    WithLp.ofLp (x ⟨(a - 3).toNat / d, (Nat.div_lt_iff_lt_mul hd).2 hi⟩)
      ⟨(a - 3).toNat % d, Nat.mod_lt _ hd⟩
  else 0

/-- The initial state of a run on the dataset `x` with public parameters `d, m, n, α, δ, ε`. -/
noncomputable def goalInput (d m n : ℕ) (α δ ε : ℝ) (x : Fin n → Vec d) : PolySampIso.State :=
  ⟨⟨0, fun _ => 0,
      fun q => if q = 0 then (d : ℤ) else if q = 1 then (m : ℤ) else if q = 2 then (n : ℤ) else 0,
      goalMem d n α δ ε x⟩, 0, 0, false, 0⟩

/-- The released batch of a state: vector `j` has coordinate `l` in cell `−1 − (j·d + l)`. -/
noncomputable def outputBatch (d m : ℕ) (s : PolySampIso.State) : Fin m → Vec d :=
  fun j => WithLp.toLp 2 fun l => s.core.mem (-1 - ((j : ℤ) * d + l))

/-- The released batch of program `P` on the dataset `x` and the streams `ω`, read at the first
halting step. -/
noncomputable def goalOutput (P : PolySampIso.Program) (d m n : ℕ) (α δ ε : ℝ)
    (p : (Fin n → Vec d) × PolySampIso.Streams) : Fin m → Vec d :=
  outputBatch d m (PolySampIso.run P (goalInput d m n α δ ε p.1) p.2
    (PolySampIso.haltTime P (goalInput d m n α δ ε p.1) p.2))

end PrivGaussMS


