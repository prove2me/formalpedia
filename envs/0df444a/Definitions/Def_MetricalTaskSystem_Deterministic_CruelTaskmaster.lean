-- Prove2me | Definitions.Def_MetricalTaskSystem_Deterministic_CruelTaskmaster
-- name    : MetricalTaskSystem_Deterministic_CruelTaskmaster
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:09:21.896879+00:00
-- url     : https://prove2.me/theorems/0c177e24-6d02-437a-98ac-106ff1fdd2b5
-- title:
--   The cruel taskmaster $M(\varepsilon)$ and the ratio $w_{\mathbf T}(A)$ on an infinite task sequence
-- statement:
--   For an infinite task sequence $\mathbf T=T^1T^2\cdots$ and an on-line algorithm $A$, the competitive ratio of $A$ with respect to $\mathbf T$ is
--   $$w_{\mathbf T}(A)=\limsup_{m\to\infty}\frac{c_A(T^1\cdots T^m)}{c_0(T^1\cdots T^m)}\in[-\infty,+\infty].$$
--
--   For $\varepsilon>0$, the **cruel taskmaster** $M(\varepsilon)$ plays against $A$: at step $i$ it presents the $\varepsilon$-elementary task
--   $$T^i(\sigma(i-1))=\varepsilon,\qquad T^i(s)=0\quad (s\neq\sigma(i-1)),$$
--   where $\sigma(i-1)$ is the state $A$ currently occupies, and $A$ then chooses $\sigma(i)$. The resulting infinite sequence is denoted $\mathbf T(\varepsilon)$. The file also defines $\min_{i\neq j} d(i,j)$ for a state set with at least two elements.
--
--   These objects enter the lower bound $w(S,d)\ge 2n-1$ (Lemma 2.1 and Theorem 2.2).
--
--   **Formalization Note** The limsup is taken in `EReal` of the real quotients; a prefix with $c_0=0$ contributes the value $0$ (real division by zero), which does not affect the limsup when $c_0\to\infty$. The adversary's sequence is built by recursion together with $A$'s states: `cruelState A s₀ ε i` is $\sigma(i)$ and `cruelSeq A s₀ ε i` is the task $T^{i+1}$.
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), pp. 748-749, Section 2 (cruel taskmaster strategy M(ε); definition of w_T(A))

import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model

namespace MetricalTaskSystem.Deterministic

/-- The prefix `T¹ ⋯ Tᵐ` of an infinite task sequence `T : ℕ → S → ℝ`
(where `T i` is the paper's `T^{i+1}`). -/
def prefixSeq {S : Type} (T : ℕ → S → ℝ) (m : ℕ) : Fin m → S → ℝ :=
  fun i => T i

/-- The competitive ratio of `A` with respect to an infinite task sequence (p. 748–749):
`w_T(A) = limsup_{m → ∞} c_A(T¹ ⋯ Tᵐ) / c₀(T¹ ⋯ Tᵐ)`, computed in `EReal` (it may be `+∞`).
The quotient is the real quotient, so a prefix with `c₀ = 0` contributes the value `0`;
this does not affect the `limsup` when `c₀ → ∞`. -/
noncomputable def ratioLimsup {S : Type} [Fintype S] [DecidableEq S] (d : S → S → ℝ)
    (A : OnlineAlgorithm S) (s₀ : S) (T : ℕ → S → ℝ) : EReal :=
  Filter.limsup
    (fun m : ℕ => ((onlineCost d A s₀ (prefixSeq T m) / offlineOpt d s₀ (prefixSeq T m) : ℝ) :
      EReal))
    Filter.atTop

/-- The `ε`-elementary task with its nonzero entry at state `u`:
`T(u) = ε` and `T(s) = 0` for `s ≠ u` (p. 748). -/
def elemTask {S : Type} [DecidableEq S] (ε : ℝ) (u : S) : S → ℝ :=
  fun s => if s = u then ε else 0

/-- The states `[σ(0), σ(1), …, σ(i)]` of algorithm `A` played against the **cruel taskmaster**
`M(ε)` (p. 748): `σ(0) = s₀`, the task `T^{j}` is the `ε`-elementary task at `σ(j − 1)`, and
`σ(j) = A(s₀, [T¹, …, T^j])`. -/
def cruelStates {S : Type} [DecidableEq S] (A : OnlineAlgorithm S) (s₀ : S) (ε : ℝ) :
    ℕ → List S
  | 0 => [s₀]
  | i + 1 =>
    let l := cruelStates A s₀ ε i
    l ++ [A s₀ (l.map (elemTask ε))]

/-- The state `σ(i)` of `A` against the cruel taskmaster `M(ε)`. -/
def cruelState {S : Type} [DecidableEq S] (A : OnlineAlgorithm S) (s₀ : S) (ε : ℝ) (i : ℕ) :
    S :=
  (cruelStates A s₀ ε i).getLastD s₀

/-- The infinite task sequence `T(ε)` produced by `M(ε)` in response to `A` (p. 748–749):
its `(i+1)`-st task (index `i`) is `ε` at `σ(i)` and `0` elsewhere. -/
def cruelSeq {S : Type} [DecidableEq S] (A : OnlineAlgorithm S) (s₀ : S) (ε : ℝ) :
    ℕ → S → ℝ :=
  fun i => elemTask ε (cruelState A s₀ ε i)

/-- `min_{i ≠ j} d(i, j)`, defined when `S` has at least two states. -/
noncomputable def minOffDiag {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S]
    (d : S → S → ℝ) : ℝ :=
  (Finset.univ.filter (fun p : S × S => p.1 ≠ p.2)).inf'
    (by
      obtain ⟨a, b, hab⟩ := exists_pair_ne S
      exact ⟨(a, b), by simpa using hab⟩)
    (fun p => d p.1 p.2)

end MetricalTaskSystem.Deterministic


