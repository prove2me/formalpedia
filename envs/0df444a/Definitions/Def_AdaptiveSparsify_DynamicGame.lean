-- Prove2me | Definitions.Def_AdaptiveSparsify_DynamicGame
-- name    : AdaptiveSparsify_DynamicGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:50.635804+00:00
-- url     : https://prove2.me/theorems/05db7cdd-3a7a-457a-bc22-75f8d547ac1f
-- title:
--   The adaptive row-update game and the success event of Theorem 3
-- statement:
--   The interaction of Theorem 3 between a program and an adaptive adversary, on a matrix with $n$ row slots.
--
--   An update $(i,v)$ sets row $i$ to $v$; $v=0$ deletes the row, and writing to an empty slot inserts one. A batch is a list of updates. The program runs until it executes `yield`. The game then records a snapshot, consisting of the current matrix and the array $\tilde\tau$ held in real cells $-1-i$, and shows the adversary the history of all arrays $\tilde\tau$ published so far. The adversary answers with the next batch, which is written into the machine's input memory, or with a stop signal, after which the program must halt on its own. After $Q$ batches the adversary is stopped.
--
--   The promise of the theorem binds along the run: a batch that takes the matrix outside $\kappa^{-1}I\preceq A^\top A\preceq\kappa I$, or the total number of updates above $C_0n$, ends the game at that moment. The run succeeds for constants $C,k$ when the game has ended (by such a breach, or by a stop followed by a halt without fault), when the machine's work is at most
--
--   $$C\big(nd+(Q+1)d^6\big)\big(\log(n+d+\kappa+2)\big)^k$$
--
--   for the number $Q$ of delivered batches, and when every snapshot satisfies $\tilde\tau_i\ge a_i^\top(A^\top A)^{-1}a_i$ for all $i$ and $\sum_i\tilde\tau_i\le Cd(\log(n+d+\kappa+2))^k$.
--
--   **Formalization Note** The adversary never sees the tape or the machine's other memory, and its strategy is a measurable function of the history of $\tilde\tau$: the bad event is bounded in outer measure, and an independence argument has no content against a non-measurable function of the history. The work counts machine steps only.
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Theorem 3, p.7; batches, p.7; Modify, Lemma 2.2, p.11; initialization cost, p.33

import Mathlib
import Definitions.Def_AdaptiveSparsify_Machine

namespace AdaptiveSparsify

/-!
# The adaptive leverage score game of Theorem 3

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…),
Theorem 3, p.7, with the batch convention of p.7 and the update form `Modify(i, v)` of Lemma 2.2,
p.11 ("where v = 0 is equivalent to deleting it").

**Formalization Note.**
* The matrix has `n` row slots. An update `(i, v)` sets row `i` to `v`; `v = 0` deletes it, and
  writing to an empty slot inserts. A batch is a list of updates, applied in order. This is the
  row-update convention of Lemma 2.2.
* The game runs the machine until it executes `yield`. Then it records a snapshot (the current
  matrix and the array `τ̃` in real cells `-1 - i`), and shows the adversary the whole history of `τ̃`
  arrays. The adversary never sees the tape or the machine's other memory. Reading `τ̃` costs the
  adversary nothing, and `work` counts machine steps only.
* The adversary answers with the next batch, or with `none` to stop. The batch is delivered into
  input memory: integer cell `-1` holds its length (`-1` for stop), integer cell `-2 - l` the slot of
  update `l`, and real cells `n d + 1 + l d + k` its row. After a stop, the machine must still halt
  on its own.
* The promise binds along the run: a batch that takes the matrix outside `κ⁻¹ I ⪯ A⊤A ⪯ κ I`, or the
  total update count above `C₀ n`, ends the game at that moment with `breached` set. Everything
  published up to that moment must still be correct, so an adversary breaching the promise on some
  tapes does not make the event vacuous on the others (trap 25). On tapes with no breach this is the
  printed promise.
* `Q` caps the number of batches: after `Q` batches the adversary is stopped. The time bound uses
  the number of batches actually delivered, plus one for the initial matrix, which p.33 charges as
  one more initialization (`Õ(nd + d^{3+ω})`): at no batches the printed `Õ(nd)` would ask for
  leverage overestimates of a tall matrix below the initialization cost of the paper's own proof.
* Strategies are measurable in the `τ̃` history. The bad event is bounded in outer measure, and the
  independence argument of pp.11, 37 has no content against a non-measurable function of the history.
-/

open Matrix

/-- A row update: slot and new row. -/
abbrev Update (n d : ℕ) := Fin n × (Fin d → ℝ)

/-- An adaptive adversary: from the history of published arrays `τ̃`, the next batch or `none`. -/
abbrev Strategy (n d : ℕ) := List (Fin n → ℝ) → Option (List (Update n d))

/-- A strategy is measurable in the history: for each history length, the stop/shape decision has
measurable level sets, and every entry of every delivered row is a measurable function of the history
(`0` when the update does not exist). -/
def Strategy.Measurable {n d : ℕ} (σ : Strategy n d) : Prop :=
  ∀ j : ℕ,
    (∀ shape : Option (List (Fin n)),
      MeasurableSet {h : Fin j → Fin n → ℝ |
        (σ (List.ofFn h)).map (List.map Prod.fst) = shape}) ∧
    (∀ (l : ℕ) (k : Fin d), _root_.Measurable (fun h : Fin j → Fin n → ℝ =>
      match (σ (List.ofFn h)).bind (fun b => b[l]?) with
      | some u => u.2 k
      | none => 0))

/-- Apply a batch of updates, in order. -/
def applyBatch {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (b : List (Update n d)) :
    Matrix (Fin n) (Fin d) ℝ :=
  b.foldl (fun A u => Function.update A u.1 u.2) A

/-- The promise of Theorem 3 on one matrix: `κ⁻¹ I ⪯ A⊤A ⪯ κ I`. -/
def GramPromise {n d : ℕ} (κ : ℝ) (A : Matrix (Fin n) (Fin d) ℝ) : Prop :=
  LoewnerLE (κ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)) (Aᵀ * A) ∧
    LoewnerLE (Aᵀ * A) (κ • (1 : Matrix (Fin d) (Fin d) ℝ))

/-- The state of the game. `log` holds the snapshots (matrix, `τ̃`) in order, `batches` and `size`
count the delivered batches and updates. -/
structure GameState (n d : ℕ) where
  machine : State
  rows : Matrix (Fin n) (Fin d) ℝ
  log : List (Matrix (Fin n) (Fin d) ℝ × (Fin n → ℝ))
  batches : ℕ
  size : ℕ
  stopped : Bool
  breached : Bool

/-- The integer input memory of the game: cell `0` holds `n`, cell `1` holds `d`. -/
def gameIntMem (n d : ℕ) : ℤ → ℤ := fun a => if a = 0 then n else if a = 1 then d else 0

/-- The real input memory of the game: the initial matrix in row-major order from cell `0`, then `κ`
in cell `n d`. Every other cell is `0`. -/
noncomputable def gameRealMem {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (κ : ℝ) : ℤ → ℝ := fun a =>
  if ha : 0 ≤ a ∧ a.toNat < n * d then
    A ⟨a.toNat / d, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact ha.2)⟩
      ⟨a.toNat % d, Nat.mod_lt _ (Nat.pos_of_ne_zero (by
        rintro h; have := ha.2; simp [h] at this))⟩
  else if a = ((n * d : ℕ) : ℤ) then κ
  else 0

/-- The initial game state. -/
noncomputable def gameInit {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (κ : ℝ) : GameState n d :=
  ⟨init (gameIntMem n d) (gameRealMem A κ), A, [], 0, 0, false, false⟩

/-- Deliver a batch into the machine's input memory and resume it. -/
noncomputable def deliver {n d : ℕ} (b : List (Update n d)) (s : State) : State :=
  { s with
    yielded := false
    integerMemory := fun a =>
      if a = -1 then (b.length : ℤ)
      else if h : -2 - a ∈ Set.Ico (0 : ℤ) b.length then
        (((b[(-2 - a).toNat]'(by
          have := h.2; have := h.1; omega)).1 : ℕ) : ℤ)
      else s.integerMemory a
    core := { s.core with
      mem := fun a =>
        let o := a - ((n * d + 1 : ℕ) : ℤ)
        if h : 0 ≤ o ∧ 0 < d ∧ o.toNat / d < b.length then
          (b[o.toNat / d]'h.2.2).2 ⟨o.toNat % d, Nat.mod_lt _ h.2.1⟩
        else s.core.mem a } }

/-- The exchange at a `yield`: snapshot, then the adversary's answer. -/
noncomputable def exchange {n d : ℕ} (σ : Strategy n d) (κ C₀ : ℝ) (Q : ℕ) (g : GameState n d) :
    GameState n d := by
  classical
  exact
    let τ : Fin n → ℝ := fun i => g.machine.core.mem (-1 - ((i : ℕ) : ℤ))
    let snap := g.log ++ [(g.rows, τ)]
    let act := if g.batches < Q then σ (snap.map Prod.snd) else none
    match act with
    | none =>
        { g with
          log := snap
          stopped := true
          machine := { g.machine with
            yielded := false
            integerMemory := Function.update g.machine.integerMemory (-1) (-1) } }
    | some b =>
        let rows' := applyBatch g.rows b
        let size' := g.size + b.length
        if GramPromise κ rows' ∧ (size' : ℝ) ≤ C₀ * n then
          { g with
            log := snap
            rows := rows'
            batches := g.batches + 1
            size := size'
            machine := deliver b g.machine }
        else
          { g with log := snap, breached := true }

/-- One step of the game: a breached game stutters; a yielded machine exchanges; otherwise the
machine steps. No barrier is reachable (`BarrierEnv.empty`). -/
noncomputable def gameStep {n d : ℕ} (P : Program) (σ : Strategy n d) (κ C₀ : ℝ) (Q : ℕ)
    (ω : ℕ → ℝ) (g : GameState n d) : GameState n d :=
  if g.breached then g
  else if g.machine.yielded then exchange σ κ C₀ Q g
  else { g with machine := step P BarrierEnv.empty ω g.machine }

/-- The game after `t` steps. -/
noncomputable def gameRun {n d : ℕ} (P : Program) (σ : Strategy n d)
    (A : Matrix (Fin n) (Fin d) ℝ) (κ C₀ : ℝ) (Q : ℕ) (ω : ℕ → ℝ) (t : ℕ) : GameState n d :=
  (gameStep P σ κ C₀ Q ω)^[t] (gameInit A κ)

/-- `log(n + d + κ + 2)`, the logarithm of Theorem 3. -/
noncomputable def gameLog (n d : ℕ) (κ : ℝ) : ℝ := Real.log ((n : ℝ) + d + κ + 2)

/-- The success event of Theorem 3: at some step the game has ended (the promise was breached, or the
adversary stopped and the machine then halted without fault), the machine's work is at most
`C (n d + (Q + 1) d⁶) (log)^k` for the number `Q` of delivered batches, and every snapshot satisfies
`τ̃_i ≥ a_i⊤(A⊤A)⁻¹a_i` for all `i` and `∑ τ̃_i ≤ C d (log)^k`. -/
def GameSuccess {n d : ℕ} (P : Program) (σ : Strategy n d) (A : Matrix (Fin n) (Fin d) ℝ)
    (κ C₀ : ℝ) (Q : ℕ) (C : ℝ) (k : ℕ) (ω : ℕ → ℝ) : Prop :=
  ∃ t : ℕ,
    let g := gameRun P σ A κ C₀ Q ω t
    (g.breached = true ∨
      (g.stopped = true ∧ g.machine.halted = true ∧ g.machine.faulted = false)) ∧
    (g.machine.work : ℝ) ≤
      C * ((n : ℝ) * d + ((g.batches : ℝ) + 1) * (d : ℝ) ^ 6) * (gameLog n d κ) ^ k ∧
    ∀ snap ∈ g.log,
      (∀ i, leverage (snap.1ᵀ * snap.1) (snap.1 i) ≤ snap.2 i) ∧
      ∑ i, snap.2 i ≤ C * d * (gameLog n d κ) ^ k

end AdaptiveSparsify


