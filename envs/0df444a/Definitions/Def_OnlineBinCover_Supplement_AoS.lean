-- Prove2me | Definitions.Def_OnlineBinCover_Supplement_AoS
-- name    : OnlineBinCover_Supplement_AoS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:34:29.666745+00:00
-- url     : https://prove2.me/theorems/20944764-a497-488e-935d-a2cda0a909aa
-- title:
--   The adversarial-order-with-sample (AoS) protocol on the real RAM
-- statement:
--   In the **adversarial-order-with-sample (AoS)** model the algorithm knows $n$ and a sampling fraction $p\in(0,1)$ and receives a uniformly random subset $I_p\subseteq I$ of $m=\lfloor pn\rfloor$ items, available offline; the remaining $n-m$ items then arrive one at a time in an order chosen by an adversary, possibly after the sample is revealed. Sample items may be used in the solution.
--
--   On the real RAM this is the following protocol for a program $P$ with fuel $F$ per run and an **arrangement** $\pi$ of the items (positions $0,\dots,m-1$ list the sample, positions $m,\dots,n-1$ are the online arrival order):
--
--   1. the initial memory holds the integers $n,m$ and the reals $p, s_{\pi(0)},\dots,s_{\pi(m-1)}$;
--   2. one offline run of $F$ steps; the sample item at position $j$ receives the bin label stored in integer cell $-2-j$ after this run, before any online item is revealed;
--   3. the online sizes $s_{\pi(m)},\dots,s_{\pi(n-1)}$ are then fed one at a time, as in the base mission's online feed, each item labelled by integer cell $-1$ after its own run.
--
--   $A_{\mathrm{AoS}}(I)$ is the number of bins covered by the resulting labelling of **all** $n$ items.
--
--   **Formalization Note** `feedFrom` is the base mission's `feedState` fold started from an arbitrary state; `work` of the final state is the total time, offline run included.
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), §1.1, p.3 (PDF p.4), the AoS model

import Mathlib
import Definitions.Def_OnlineBinCover_Online
import Definitions.Def_OnlineBinCover_Blueprint

namespace OnlineBinCover.Supplement

/-!
# The adversarial-order-with-sample (AoS) protocol on the real RAM

Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…), §1.1 p.3 ("Approach for the AoS Model"; PDF
p.4) and Theorem 1.1.

The paper: "the algorithm knows `n` and `p` and receives a uniformly random subset `I_p ⊆ I` of
size `⌊pn⌋`. The items in `I_p` are available offline; the remaining items arrive one at a time in
adversarial order, possibly chosen after the sample is revealed. … sample items may be used in the
solution, and the algorithm competes against `OPT(I)`."

**Formalization Note.**
* *Machine.* Programs are those of the published real RAM `PNormReg.Machine`, run on the all-false
  tape `DetANN.detTape` (theorems require `DetANN.DetProgram`, which never reads the tape).
* *Arrangement.* An arrangement is a permutation `π` of the item labels: positions
  `0, …, m − 1` (with `m = ⌊pn⌋`, `sampleSize n p`) list the sample, positions `m, …, n − 1`
  are the online arrival order. Both the listing of the sample and the online order are chosen by
  the adversary (theorems quantify over every adversary).
* *Initial state.* Integer cells `0, 1` hold `n` and `m`; real cell `0` holds `p` and real cell
  `1 + j` the size of the `j`-th listed sample item (`j < m`); every other cell is `0`
  (`PNormReg.initState`).
* *Offline stage.* One run of `F` steps from the initial state. The sample item at position `j` is
  then given the bin label in integer cell `−2 − j` of the state after this run, read **before**
  the first online item is fed, so these labels are irrevocable.
* *Online stage.* From the state after the offline run the online sizes are fed one at a time with
  the published `feedLoad` (size in real cell `−2`; memories, cursor and work counter kept), each
  run for `F` steps; the online item's label is integer cell `−1` after its run. `work` of the last
  state is the total time, offline stage included.
* *Objective.* `aosValue` is the number of covered bins (published `covered`) of the labelling of
  all `n` items: sample items count.
-/

open Finset

/-- Feed the sizes of the list `x` one at a time from the state `st₀` (the published `feedLoad`,
`F` steps per item, all-false tape): the state after the first `t` of them. -/
noncomputable def feedFrom (P : PNormReg.Program) (F : ℕ) (st₀ : PNormReg.State) (x : List ℝ)
    (t : ℕ) : PNormReg.State :=
  (x.take t).foldl (fun st y => PNormReg.run P (feedLoad st y) DetANN.detTape F) st₀

/-- The sample size `⌊pn⌋`. -/
noncomputable def sampleSize (n : ℕ) (p : ℝ) : ℕ := ⌊p * (n : ℝ)⌋₊

/-- The AoS initial state: integer memory `[n, ⌊pn⌋]`, real memory `p` followed by the sample sizes
in the listing order of the arrangement `π`. -/
noncomputable def aosInit {n : ℕ} (s : Fin n → ℝ) (p : ℝ) (π : Equiv.Perm (Fin n)) :
    PNormReg.State :=
  PNormReg.initState [(n : ℤ), (sampleSize n p : ℤ)]
    (p :: (List.ofFn (s ∘ π)).take (sampleSize n p))

/-- The state after the offline run (`F` steps) on the sample. -/
noncomputable def aosOffline (P : PNormReg.Program) (F : ℕ) {n : ℕ} (s : Fin n → ℝ) (p : ℝ)
    (π : Equiv.Perm (Fin n)) : PNormReg.State :=
  PNormReg.run P (aosInit s p π) DetANN.detTape F

/-- The online sizes, in the arrival order of the arrangement: `s (π m), …, s (π (n − 1))`. -/
noncomputable def aosOnline {n : ℕ} (s : Fin n → ℝ) (p : ℝ) (π : Equiv.Perm (Fin n)) : List ℝ :=
  (List.ofFn (s ∘ π)).drop (sampleSize n p)

/-- The state after the offline run and the first `t` online items. -/
noncomputable def aosState (P : PNormReg.Program) (F : ℕ) {n : ℕ} (s : Fin n → ℝ) (p : ℝ)
    (π : Equiv.Perm (Fin n)) (t : ℕ) : PNormReg.State :=
  feedFrom P F (aosOffline P F s p π) (aosOnline s p π) t

/-- The bin label of the item at position `j` of the arrangement: integer cell `−2 − j` after the
offline run for a sample position `j < ⌊pn⌋`, integer cell `−1` after its own online run
otherwise. -/
noncomputable def aosLabelAt (P : PNormReg.Program) (F : ℕ) {n : ℕ} (s : Fin n → ℝ) (p : ℝ)
    (π : Equiv.Perm (Fin n)) (j : ℕ) : ℤ :=
  if j < sampleSize n p then (aosOffline P F s p π).integerMemory (-2 - (j : ℤ))
  else (aosState P F s p π (j - sampleSize n p + 1)).integerMemory (-1)

/-- `A_AoS(I)` for the arrangement `π`: the covered bins of the labelling of all items, sample
items included. -/
noncomputable def aosValue (P : PNormReg.Program) (F : ℕ) {n : ℕ} (s : Fin n → ℝ) (p : ℝ)
    (π : Equiv.Perm (Fin n)) : ℕ :=
  covered s (fun i => aosLabelAt P F s p π (π.symm i))

end OnlineBinCover.Supplement


