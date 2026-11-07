-- Prove2me | Definitions.Def_AvgValueAlloc_popAvg
-- name    : AvgValueAlloc_popAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:14.502457+00:00
-- url     : https://prove2.me/theorems/dae55809-c4e7-4602-8134-f9feb164090d
-- title:
--   History/live split of a population in uniform order
-- statement:
--   A **population** $P$ is a list of exactly $S+T$ items. Put it in a uniformly random order $\pi$; the first $S$ positions are the (unallocatable) history and the last $T$ the live stream. For a function $f$ of history and live stream,
--   $$
--   \mathrm{popAvg}(f,P)=\frac{1}{(S+T)!}\sum_{\pi\in S_{S+T}} f\bigl(\text{history}_\pi,\text{live}_\pi\bigr).
--   $$
--   With $S=0$ this is the random-order model on the fixed live multiset $Q=P$.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §1.1, p.2

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec

namespace AvgValueAlloc

open scoped ENNReal

/-- **History and live part of a population in a given order.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §1.1, p.2: "With history, P has exactly S + T
originals in uniform order: the first S unallocatable, the last T live; there is no hidden
remainder."

For a population `P : Fin (S + T) → Vec n` and an order `π`, position `i` holds `P (π i)`;
`histOf` is the first `S` positions, `liveOf` the last `T`. -/
def histOf {n : ℕ} (S T : ℕ) (P : Fin (S + T) → Vec n) (π : Equiv.Perm (Fin (S + T))) :
    Fin S → Vec n :=
  fun s => P (π (Fin.castAdd T s))

/-- The live part: the last `T` positions. -/
def liveOf {n : ℕ} (S T : ℕ) (P : Fin (S + T) → Vec n) (π : Equiv.Perm (Fin (S + T))) :
    Fin T → Vec n :=
  fun t => P (π (Fin.natAdd S t))

/-- **Average over a uniformly random order of a population.**
`popAvg S T f P = (1/(S+T)!) Σ_π f(history, live)`.

**Formalization Note.** The order is a uniformly random permutation of the `S + T` items. -/
noncomputable def popAvg {n : ℕ} (S T : ℕ) (f : (Fin S → Vec n) → (Fin T → Vec n) → ℝ≥0∞)
    (P : Fin (S + T) → Vec n) : ℝ≥0∞ :=
  (∑ π : Equiv.Perm (Fin (S + T)), f (histOf S T P π) (liveOf S T P π)) /
    ((S + T).factorial : ℝ≥0∞)

end AvgValueAlloc


