-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_BlockSchedule
-- name    : ConsistentSubmodular_Deterministic_Reduction_BlockSchedule
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:09:56.483208+00:00
-- url     : https://prove2.me/theorems/6a717023-8d2b-4ef2-9d18-72714c55ca49
-- title:
--   Block schedules: trajectories from per-block paths, protected-clock delays and core blocks
-- statement:
--   - `ConsistentSubmodular.BlockSchedule` $(n,b,R)$: a family of node sets $S_{i,j} \subseteq \{0,\dots,n-1\}$ for blocks $i\in\mathbb{N}$ and offsets $j\in\mathbb{N}$ such that consecutive blocks join, $S_{i,b} = S_{i+1,0}$ (each block includes its boundary state), and inside a block the recourse per step is at most $R$: $|S_{i,j+1}\triangle S_{i,j}|\le R$ for $j<b$.
--   - `BlockSchedule.trajectory` $(t)$: the global trajectory $S_{\lfloor t/b\rfloor,\ t \bmod b}$.
--   - `ProtectedClock.delay` $(C, i)$: for a protected clock $C$ with start times $s_i$, the delay $s_i-(i+1)b$ of block $i$ (a natural number, truncated subtraction).
--   - `ProtectedClock.coreBlocks` $(C, P)$: given operation paths $P_i$ with $P_0$ starting at $\emptyset$, $P_i$ ending where $P_{i+1}$ starts, and lengths $\le R\ell$, the block schedule with $S_{0,j} = \emptyset$ and $S_{i+1,j} = (P_i)_{R\,(j-\mathrm{delay}_i)}$, where $j-\mathrm{delay}_i$ is truncated subtraction. Thus block $i+1$ idles for the delay and then executes $R$ unit operations of $P_i$ per step.
--
--   The file also proves that the delay fits, $\mathrm{delay}_i+\ell\le b$, that a batch of $R$ operations of a path changes the set by at most $R$ elements even when delayed, and that the trajectory of the core blocks starts at $\emptyset$.
--
--   These constructions assemble the physical schedule of the core in the reduction of Section 3.2: each block executes its path inside the protected window so that per-step recourse stays bounded by $R$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/BlockSchedule.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_OperationPath
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ProtectedClock

noncomputable section

namespace ConsistentSubmodular

/-- Per-block schedules include their common boundary state. -/
structure BlockSchedule (n b R : ℕ) where
  node : ℕ → ℕ → Finset (Fin n)
  joins : ∀ i, node i b = node (i + 1) 0
  step : ∀ i j, j < b → recourse (node i (j + 1)) (node i j) ≤ R

namespace BlockSchedule

variable {n b R : ℕ} (S : BlockSchedule n b R)

def trajectory (t : ℕ) : Finset (Fin n) := S.node (t / b) (t % b)

@[simp] theorem trajectory_zero : S.trajectory 0 = S.node 0 0 := by simp [trajectory]

end BlockSchedule

namespace SetOperationPath

variable {n : ℕ} (P : SetOperationPath n)

theorem delayed_batch_recourse (R delay j : ℕ) :
    recourse (P.node (R * (j + 1 - delay))) (P.node (R * (j - delay))) ≤ R := by
  have hmono : R * (j - delay) ≤ R * (j + 1 - delay) :=
    Nat.mul_le_mul_left R (by omega)
  have hdiff : R * (j + 1 - delay) - R * (j - delay) ≤ R := by
    have hm := Nat.mul_le_mul_left R (show j + 1 - delay ≤ (j - delay) + 1 by omega)
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega
  exact (P.recourse_le_difference hmono).trans hdiff

end SetOperationPath

namespace ProtectedClock

variable {n b ell R : ℕ} {F : ℕ → ℝ} {η : ℝ}

variable (C : ProtectedClock F η b ell)

def delay (i : ℕ) : ℕ := C.start i - (i + 1) * b

theorem delay_fit (i : ℕ) : C.delay i + ell ≤ b := by
  have hl := C.lower i
  have hu := C.upper i
  have hh : C.start i + ell ≤ (i + 1) * b + b := by nlinarith
  dsimp [delay]
  omega

def coreBlocks (P : ℕ → SetOperationPath n)
    (hinitial : (P 0).node 0 = ∅)
    (hjoin : ∀ i, (P i).node (P i).length = (P (i + 1)).node 0)
    (hlen : ∀ i, (P i).length ≤ R * ell) : BlockSchedule n b R := by
  let seq : ℕ → ℕ → Finset (Fin n) := fun i j =>
    match i with
    | 0 => ∅
    | i + 1 => (P i).node (R * (j - C.delay i))
  refine { node := seq, joins := ?_, step := ?_ }
  · intro i
    cases i with
    | zero => simpa [seq] using hinitial.symm
    | succ i =>
      have hfit := C.delay_fit i
      have hfinish : (P i).length ≤ R * (b - C.delay i) :=
        (hlen i).trans (Nat.mul_le_mul_left R (by omega))
      simpa [seq, (P i).stationary _ hfinish] using hjoin i
  · intro i j _
    cases i with
    | zero => simp [seq, recourse]
    | succ i => exact (P i).delayed_batch_recourse R (C.delay i) j

theorem coreBlocks_initial (P : ℕ → SetOperationPath n) (hinitial hjoin hlen) :
    (C.coreBlocks (R := R) P hinitial hjoin hlen).trajectory 0 = ∅ := by
  simp [BlockSchedule.trajectory, coreBlocks]

end ProtectedClock

end ConsistentSubmodular

end


