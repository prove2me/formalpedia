-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ClockWindows
-- name    : ConsistentSubmodular_Deterministic_Reduction_ClockWindows
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:11:05.47561+00:00
-- url     : https://prove2.me/theorems/90d34abc-d79b-4f2a-bf84-81a70f8ea1b0
-- title:
--   Windows of a protected clock: old set, buffer, initial and terminal optimizers, fractional window family
-- statement:
--   Let $C$ be a protected clock with start times $s_i=C.\mathrm{start}(i)$, $X_t=\{e<t\}$ the arrived prefix, $f$ an objective on $[n]$, and $\kappa$ a core budget.
--
--   - `ProtectedClock.windowOld n i`: the old set of window $i$, $\mathrm{Old}_i=X_{s_i}$.
--   - `ProtectedClock.windowBuffer n i u`: the buffer after $u$ arrivals in window $i$, $Q_i(u)=X_{s_i+u}\setminus X_{s_i}$.
--   - `ProtectedClock.windowDuration i`: the duration $T_i=s_{i+1}-s_i$ (natural-number subtraction).
--   - `ProtectedClock.windowInitial f κ i`: the initial optimizer $\mathrm{Init}_i$, a best $\kappa$-subset of $\mathrm{Old}_i$ (the buffered optimizer with empty buffer), so that $f(\mathrm{Init}_i)=\mathrm{OPT}_\kappa(X_{s_i})$ is the prefix optimum.
--   - `ProtectedClock.windowTerminal f κ i`: the terminal optimizer $\mathrm{Term}_i$, a best $\kappa$-subset of $\mathrm{Old}_i$ for the buffer $Q_i(T_i)$, i.e. maximizing $f(Q_i(T_i)\cup B)$ over $B\subseteq\mathrm{Old}_i$, $|B|\le\kappa$.
--   - `ProtectedClock.fractionalWindows C f κ O N hN i`: for a certificate family $O$ and $N>0$, a chosen fractional window (in the sense of the preceding bundle) for window $i$, with old set $\mathrm{Old}_i$, buffer sequence $Q_i$, duration $T_i$, initial and terminal sets $\mathrm{Init}_i$, $\mathrm{Term}_i$, level $O.\mathrm{level}$ and segment budget $O.\mathrm{budget}(3N+1)$. It is obtained from the existence theorem for fractional windows, so it uses exactly the prescribed optimizers, including for zero-duration windows.
--
--   The file also proves basic facts: the buffer is empty at $u=0$, monotone in $u$, and disjoint from the old set; and the initial and terminal optimizers lie in the old set, have size at most $\kappa$, and attain the prefix optimum and the buffered optimum respectively.
--
--   These definitions cut the stream at the protected clock's start times into windows and supply, for each, the fractional geometry that the later rounding step converts into integral paths.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/ClockWindows.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FractionalWindow
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ProtectedClock

noncomputable section

namespace ConsistentSubmodular

namespace ProtectedClock

variable {F : ℕ → ℝ} {η : ℝ} {b ell : ℕ} (C : ProtectedClock F η b ell)

def windowOld (n i : ℕ) : Finset (Fin n) := arrivedPrefix n (C.start i)

def windowBuffer (n i u : ℕ) : Finset (Fin n) :=
  arrivedPrefix n (C.start i + u) \ C.windowOld n i

def windowDuration (i : ℕ) : ℕ := C.start (i + 1) - C.start i

@[simp] theorem windowBuffer_zero (n i : ℕ) : C.windowBuffer n i 0 = ∅ := by
  simp [windowBuffer, windowOld]

theorem windowBuffer_mono (n i : ℕ) : Monotone (C.windowBuffer n i) := by
  intro u v huv e he
  exact Finset.mem_sdiff.mpr ⟨arrivedPrefix_mono (Nat.add_le_add_left huv _)
    (Finset.mem_sdiff.mp he).1, (Finset.mem_sdiff.mp he).2⟩

variable {n : ℕ} (f : Objective n) (κ : ℕ)

def windowInitial (i : ℕ) : Finset (Fin n) := f.bufferedOptimizer (C.windowOld n i) ∅ κ

def windowTerminal (i : ℕ) : Finset (Fin n) :=
  f.bufferedOptimizer (C.windowOld n i) (C.windowBuffer n i (C.windowDuration i)) κ

theorem windowInitial_spec (i : ℕ) : C.windowInitial f κ i ⊆ C.windowOld n i ∧
    (C.windowInitial f κ i).card ≤ κ ∧
    f.value (C.windowInitial f κ i) = f.prefixOptimum κ (C.start i) := by
  have hs := f.bufferedOptimizer_spec (C.windowOld n i) ∅ κ
  exact ⟨hs.1, hs.2.1, by simp [windowInitial, Objective.prefixOptimum, Objective.bufferedOptimum, windowOld]⟩

theorem windowTerminal_spec (i : ℕ) : C.windowTerminal f κ i ⊆ C.windowOld n i ∧
    (C.windowTerminal f κ i).card ≤ κ ∧
    f.value (C.windowBuffer n i (C.windowDuration i) ∪ C.windowTerminal f κ i) =
      f.bufferedOptimum (C.windowOld n i) (C.windowBuffer n i (C.windowDuration i)) κ := by
  have hs := f.bufferedOptimizer_spec (C.windowOld n i) (C.windowBuffer n i (C.windowDuration i)) κ
  exact ⟨hs.1, hs.2.1, rfl⟩

theorem windowBuffer_disjoint (n i u : ℕ) : Disjoint (C.windowBuffer n i u) (C.windowOld n i) :=
  Finset.sdiff_disjoint

/-- The fractional family uses exactly the prescribed initial and terminal
optimizers, including zero-scale windows. Its geometry comes from the
certificates of the compressed windows. -/
def fractionalWindows (O : CertificateFamily) (N : ℕ) (hN : 0 < N) (i : ℕ) :
    FractionalWindow f (C.windowOld n i) (C.windowBuffer n i) (C.windowBuffer_mono n i)
      κ N (C.windowDuration i) (C.windowInitial f κ i) (C.windowTerminal f κ i)
      O.level (O.budget (3 * N + 1)) := by
  apply Classical.choice
  apply f.fractional_window O _ _ _ (C.windowBuffer_zero n i) (C.windowBuffer_disjoint n i)
    κ N _ hN
  · have hs := C.windowInitial_spec f κ i
    simpa only [Objective.prefixOptimum, windowOld, C.windowBuffer_zero, Finset.empty_union] using hs
  · exact C.windowTerminal_spec f κ i

end ProtectedClock

end ConsistentSubmodular

end


