-- Prove2me | Definitions.Def_NKtLB_NTIME
-- name    : NKtLB_NTIME
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:01:21.188829+00:00
-- url     : https://prove2.me/theorems/83fce5fa-c18b-44d3-b575-33095def770b
-- title:
--   $\mathsf{NTIME}[T(n)]$
-- statement:
--   For $T:\mathbb N\to\mathbb N$, $\mathsf{NTIME}[T(n)]$ is the class of languages $L\subseteq\{0,1\}^*$ decided by a nondeterministic machine in time $O(T(n))$. There are a machine $M$ and a constant $c$ such that, for every input $x$, with $\tau=c\,T(|x|)+c$: every guess $w\in\{0,1\}^\tau$ makes $M$ (input $x$, no oracle) halt within $\tau$ steps with output $0$ or $1$, and $x\in L$ if and only if some guess makes it output $1$.
--
--   **Formalization Note** The paper uses the standard class without defining it. Time $O(T)$ rather than exactly $T$ gives the larger class, and hence the stronger lower bounds. The guess is read sequentially from the guess tape.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 8, p.12; Lemma 45, p.30 (standard class, not defined in the paper)

import Mathlib
import Definitions.Def_NKtLB_Machine

namespace NKtLB

/-- **`NTIME[T(n)]`** (used in Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 8, p.12, and Lemma 45, p.30; standard, not defined in
the paper): the languages `L ⊆ {0,1}^*` decided by a nondeterministic machine of the model of §3.2
in time `O(T(n))`. There are a machine `M` and `c ∈ ℕ` such that, for every `x`, with `τ = c·T(|x|) + c`:
every guess `w ∈ {0,1}^τ` makes `M` (input `x`, oracle `∅`) halt within `τ` steps with output `0`
or `1`, and `x ∈ L` iff some guess makes it output `1`.

**Formalization Note.** `O(T)` time (not exactly `T`) gives the larger class, hence the stronger
lower bounds. The guess is read sequentially from the guess tape. -/
def NTIME (T : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ (M : Machine) (c : ℕ), ∀ x : List Bool,
    (∀ w : List Bool, w.length = c * T x.length + c →
      M.HaltsWith ∅ ⟨x, [], w, []⟩ (c * T x.length + c) [Sym.zero] ∨
      M.HaltsWith ∅ ⟨x, [], w, []⟩ (c * T x.length + c) [Sym.one]) ∧
    (x ∈ L ↔ ∃ w : List Bool, w.length = c * T x.length + c ∧
      M.HaltsWith ∅ ⟨x, [], w, []⟩ (c * T x.length + c) [Sym.one])}

end NKtLB


