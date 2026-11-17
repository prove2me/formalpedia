-- Prove2me | Definitions.Def_AdaptiveSparsify_Supplement_HalvingGame
-- name    : AdaptiveSparsify_Supplement_HalvingGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:52:03.991954+00:00
-- url     : https://prove2.me/theorems/3dee4ed9-90d9-438b-8482-2f5bbd9f04ac
-- title:
--   The adaptive row-halving game and the success event of Theorem 6
-- statement:
--   The game of Theorem 6, played on the published barrier-oracle RAM (no barrier reachable) between one program and an **adaptive adversary**.
--
--   1. The machine starts with $n$, $d$ in integer memory and $A\in\mathbb R^{n\times d}$ and $\kappa$ in real memory (the layout of the published Theorem 3 game).
--   2. Whenever the machine executes `yield`, the game records a **snapshot**: the current matrix and the array $\tilde\tau\in\mathbb R^n$ held in real cells $-1-i$. The adversary sees the history of all published arrays $\tilde\tau$ (never the tape or the rest of memory) and answers either with a row index $i$, which **halves** row $i$ ($a_i\leftarrow a_i/2$), or with stop. The answer is written to integer cell $-1$ ($i$, or $-1$ for stop) and the machine resumes. One halving per exchange, so a snapshot is published after every update. After a stop the machine must halt on its own.
--   3. **Halving cap.** A halving that would take some row past $C_0\log_2(n+2)$ halvings ends the game at once (the game is *breached*); the snapshots published before must still be correct.
--   4. Strategies are measurable functions of the history.
--
--   **Success** at constants $C,k$: at some step the game has ended (a breach, or a stop followed by a halt without fault), the machine's work is at most
--   $$C\big(nd+d^{3+\omega_0}\big)\big(\log(n+2)\big)^k,$$
--   and every snapshot $(A',\tilde\tau)$ satisfies
--   $$\tilde\tau_i\ge a_i'^\top\big(A'^\top A'+\kappa^{-1}I\big)^{-1}a_i'\ \text{for all } i,\qquad \sum_i\tilde\tau_i\le Cd\big(\log(n+2)\big)^k .$$
--
--   The left-hand side is the leverage score of row $i$ of the stacked matrix $[A';\kappa^{-1/2}I]$.
--
--   **Formalization Note** The cap is the standing assumption of §5 (Definition 5.4, p.35: "every row is halved for at most $O(\log n)$ times"). The first snapshot is the one for the initial matrix. Work counts machine steps only; reading $\tilde\tau$ costs the adversary nothing.
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Theorem 6, p.32; Definition 5.4, p.35; §5.4, pp.38–39

import Mathlib
import Definitions.Def_AdaptiveSparsify_DynamicGame

namespace AdaptiveSparsify

/-!
# The adaptive row-halving game of Theorem 6

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…),
Theorem 6, p.32 ("row halving, which is setting `a_i` to `a_i/2`", "after every update", "against an
adaptive adversary"), with the standing assumption of §5, Definition 5.4, p.35 ("every row is halved
for at most `O(log n)` times").

**Formalization Note.**
* The game follows the published `AdaptiveSparsify.DynamicGame` and reuses its input memory
  (`gameIntMem`, `gameRealMem`: `n`, `d` in integer cells `0, 1`; `A` row-major from real cell `0`, then
  `κ` in real cell `n d`). There is no Gram promise, and an update is a single halving.
* The machine runs until it executes `yield`. The game then records a snapshot (the current matrix
  and the array `τ̃` in real cells `-1 - i`) and shows the adversary the history of all published `τ̃`
  arrays; it never sees the tape or the rest of memory. The adversary answers with a row index `i`
  (halve row `i`) or `none` (stop). Integer cell `-1` then holds `i`, or `-1` for stop, and the machine
  resumes. After a stop the machine must halt on its own; a later `yield` is answered with stop again.
  One update per exchange, so a snapshot is published after every single halving. The first snapshot
  is the one for the initial matrix.
* The halving cap: a halving that would take row `i` past `C₀ log₂(n + 2)` halvings ends the game at
  that moment with `breached` set, and every snapshot published before must still be correct.
* Strategies are measurable in the `τ̃` history (each decision has measurable level sets).
* Work counts machine steps only; no barrier is reachable (`BarrierEnv.empty`).
-/

namespace Supplement

open Matrix

/-- An adaptive halving adversary: from the history of published arrays `τ̃`, the next row to halve,
or `none` to stop. -/
abbrev HalvingStrategy (n : ℕ) := List (Fin n → ℝ) → Option (Fin n)

/-- A halving strategy is measurable: for each history length, each decision has a measurable level
set. -/
def HalvingStrategy.Measurable {n : ℕ} (σ : HalvingStrategy n) : Prop :=
  ∀ (j : ℕ) (o : Option (Fin n)),
    MeasurableSet {h : Fin j → Fin n → ℝ | σ (List.ofFn h) = o}

/-- Halve row `i`: `a_i ← a_i / 2`. -/
noncomputable def halveRow {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (i : Fin n) :
    Matrix (Fin n) (Fin d) ℝ :=
  Function.update A i (fun k => A i k / 2)

/-- The cap `C₀ log₂(n + 2)` on the number of halvings of one row (Definition 5.4, p.35). -/
noncomputable def halvingCap (n : ℕ) (C₀ : ℝ) : ℝ := C₀ * Real.logb 2 ((n : ℝ) + 2)

/-- The state of the halving game: the machine, the current matrix, the snapshots (matrix, `τ̃`) in
order, the number of halvings of each row, and the stop and breach flags. -/
structure HalvingState (n d : ℕ) where
  machine : State
  rows : Matrix (Fin n) (Fin d) ℝ
  log : List (Matrix (Fin n) (Fin d) ℝ × (Fin n → ℝ))
  halvings : Fin n → ℕ
  stopped : Bool
  breached : Bool

/-- The initial state of the halving game. -/
noncomputable def halvingInit {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (κ : ℝ) : HalvingState n d :=
  ⟨init (gameIntMem n d) (gameRealMem A κ), A, [], fun _ => 0, false, false⟩

/-- The exchange at a `yield`: snapshot, then the adversary's answer. -/
noncomputable def halvingExchange {n d : ℕ} (σ : HalvingStrategy n) (C₀ : ℝ)
    (g : HalvingState n d) : HalvingState n d :=
  let τ : Fin n → ℝ := fun i => g.machine.core.mem (-1 - ((i : ℕ) : ℤ))
  let snap := g.log ++ [(g.rows, τ)]
  let act := if g.stopped then none else σ (snap.map Prod.snd)
  match act with
  | none =>
      { g with
        log := snap
        stopped := true
        machine := { g.machine with
          yielded := false
          integerMemory := Function.update g.machine.integerMemory (-1) (-1) } }
  | some i =>
      if ((g.halvings i + 1 : ℕ) : ℝ) ≤ halvingCap n C₀ then
        { g with
          log := snap
          rows := halveRow g.rows i
          halvings := Function.update g.halvings i (g.halvings i + 1)
          machine := { g.machine with
            yielded := false
            integerMemory := Function.update g.machine.integerMemory (-1) ((i : ℕ) : ℤ) } }
      else
        { g with log := snap, breached := true }

/-- One step of the halving game: a breached game stutters; a yielded machine exchanges; otherwise
the machine steps with no barrier. -/
noncomputable def halvingStep {n d : ℕ} (P : Program) (σ : HalvingStrategy n) (C₀ : ℝ)
    (ω : ℕ → ℝ) (g : HalvingState n d) : HalvingState n d :=
  if g.breached then g
  else if g.machine.yielded then halvingExchange σ C₀ g
  else { g with machine := step P BarrierEnv.empty ω g.machine }

/-- The halving game after `t` steps. -/
noncomputable def halvingRun {n d : ℕ} (P : Program) (σ : HalvingStrategy n)
    (A : Matrix (Fin n) (Fin d) ℝ) (κ C₀ : ℝ) (ω : ℕ → ℝ) (t : ℕ) : HalvingState n d :=
  (halvingStep P σ C₀ ω)^[t] (halvingInit A κ)

/-- The success event of Theorem 6: at some step the game has ended (the halving cap was breached,
or the adversary stopped and the machine then halted without fault), the work is at most
`C (n d + d^{3+ω₀}) (log(n + 2))^k`, and every snapshot satisfies
`τ̃_i ≥ a_i⊤(A⊤A + κ⁻¹I)⁻¹a_i` for all `i` and `∑ τ̃_i ≤ C d (log(n + 2))^k`. -/
def HalvingSuccess {n d : ℕ} (P : Program) (σ : HalvingStrategy n) (A : Matrix (Fin n) (Fin d) ℝ)
    (κ C₀ ω₀ C : ℝ) (k : ℕ) (ω : ℕ → ℝ) : Prop :=
  ∃ t : ℕ,
    ((halvingRun P σ A κ C₀ ω t).breached = true ∨
      ((halvingRun P σ A κ C₀ ω t).stopped = true ∧
        (halvingRun P σ A κ C₀ ω t).machine.halted = true ∧
        (halvingRun P σ A κ C₀ ω t).machine.faulted = false)) ∧
    ((halvingRun P σ A κ C₀ ω t).machine.work : ℝ) ≤
      C * ((n : ℝ) * d + (d : ℝ) ^ (3 + ω₀)) * (Real.log ((n : ℝ) + 2)) ^ k ∧
    ∀ snap ∈ (halvingRun P σ A κ C₀ ω t).log,
      (∀ i, leverage (snap.1ᵀ * snap.1 + κ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)) (snap.1 i) ≤
        snap.2 i) ∧
      ∑ i, snap.2 i ≤ C * d * (Real.log ((n : ℝ) + 2)) ^ k

end Supplement

end AdaptiveSparsify


