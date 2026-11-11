-- Prove2me | Definitions.Def_DistLTLSynth_Char_Automata
-- name    : DistLTLSynth_Char_Automata
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:15:50.132776+00:00
-- url     : https://prove2.me/theorems/353c80bf-4f8a-4c9c-8334-4e8871feb7ed
-- title:
--   Deterministic parity automata, parity condition, and finite codes of automata over Γ
-- statement:
--   A **deterministic parity automaton** over $\alpha$ is $(S, s_0, \delta, \chi)$ with initial state $s_0$, transition function $\delta:S\times\alpha\to S$ and priorities $\chi:S\to\mathbb N$; it has finitely many states when $S$ is finite. Its run on $w$ is $s_0, \delta(s_0,w_1), \dots$, and $w$ is accepted iff the least priority occurring infinitely often along the run is even. A message adversary is **ω-regular** iff it is the language of such an automaton with finitely many states.
--
--   For algorithms that take an automaton as input, a **code** $(n,\text{trans},\text{prios})$ describes the automaton over $\Gamma$ with states $\{0,\dots,n\}$, initial state $0$, $\delta(s,g)=\text{trans}[3s+\mathrm{idx}(g)] \bmod (n+1)$ and $\chi(s)=\text{prios}[s]$ (missing entries read as $0$), where $\mathrm{idx}$ numbers $(1\to2),(1\leftrightarrow2),(1\leftarrow2)$ as $0,1,2$.
--
--   **Formalization Note.** Every finite deterministic parity automaton over $\Gamma$ is, up to renaming its states, described by a code.
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), p. 2 (PDF 3), §1.1; p. 12 (PDF 13), §3.3.1; p. 35 (PDF 36), Definition 7.6 (parity acceptance)

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model

namespace DistLTLSynth.Char

/-- The parity condition on a sequence of priorities: the least priority occurring
infinitely often exists and is even. -/
def ParityCond (c : ℕ → ℕ) : Prop :=
  ∃ p : ℕ, Even p ∧ (∃ᶠ n in Filter.atTop, c n = p) ∧ ∀ᶠ n in Filter.atTop, p ≤ c n

/-- A deterministic parity automaton over the alphabet `α` with state type `S`: initial
state, transition function and priority map (§3.3, Definition 7.6). It has finitely many
states when `S` is a `Fintype`. -/
structure DPA (S α : Type) : Type where
  init : S
  step : S → α → S
  prio : S → ℕ

/-- The unique run on an infinite word: `run w 0 = init`, `run w (n+1) = step (run w n) (w n)`. -/
def DPA.run {S α : Type} (M : DPA S α) (w : ℕ → α) : ℕ → S
  | 0 => M.init
  | n + 1 => M.step (M.run w n) (w n)

/-- `M` accepts `w` iff the least priority occurring infinitely often along its run is even. -/
def DPA.Accepts {S α : Type} (M : DPA S α) (w : ℕ → α) : Prop :=
  ParityCond (fun n => M.prio (M.run w n))

/-- The language of `M`. -/
def DPA.lang {S α : Type} (M : DPA S α) : Set (ℕ → α) := {w | M.Accepts w}

/-- Index of a communication graph (`0, 1, 2` for `(1 → 2), (1 ↔ 2), (1 ← 2)`). -/
def CommGraph.idx : CommGraph → ℕ
  | CommGraph.oneToTwo => 0
  | CommGraph.both => 1
  | CommGraph.twoToOne => 2

/-- A finite description of a deterministic parity automaton over `Γ`, used as the input of
algorithms: `(n, trans, prios)` describes the automaton with states `Fin (n + 1)`, initial
state `0`, `step s g = trans[3 s + idx g] mod (n + 1)` and `prio s = prios[s]` (missing
entries read as `0`). -/
abbrev DPACode : Type := ℕ × List ℕ × List ℕ

/-- The automaton described by a code. -/
def DPACode.toDPA (c : DPACode) : DPA (Fin (c.1 + 1)) CommGraph where
  init := ⟨0, Nat.succ_pos _⟩
  step s g := ⟨(c.2.1.getD (3 * s.val + g.idx) 0) % (c.1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  prio s := c.2.2.getD s.val 0

/-- The message adversary recognized by a code. -/
def DPACode.lang (c : DPACode) : Set (ℕ → CommGraph) := c.toDPA.lang

end DistLTLSynth.Char


