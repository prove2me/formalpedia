-- Prove2me | Definitions.Def_HypercliqueFalse_SolvedWithin
-- name    : HypercliqueFalse_SolvedWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:29:54.969752+00:00
-- url     : https://prove2.me/theorems/e110b86d-4050-4ab4-9913-55c63d9df8e2
-- title:
--   Solved within a real time bound on the word RAM, at a global scale $s$
-- statement:
--   Let $Q$ be a problem of the published word RAM (`TrulySubcubicAPSP`): instances are indexed by a natural number $s$, each instance $x$ has an input list of integers, an acceptance condition and an output condition. Let $\mathrm{bound}(s, x) \in \mathbb R$ be a time bound. **$Q$ is solved within $\mathrm{bound}$** if for every exponent $\kappa \in \mathbb N$ there are one program $P$, a width factor $b$ and a constant $C$ such that, for every scale $s$ and every instance $x$ of scale $s$ all of whose input integers have absolute value at most $s^\kappa$, and for every word width
--   $$
--   W \ge b\,(\lfloor \log_2 s\rfloor + 1),
--   $$
--   the program $P$, started on the memory holding $s$ in cell $0$ and the input from cell $1$ on, halts within some $t \le C\cdot \mathrm{bound}(s,x) + C$ steps with the right verdict and the right output.
--
--   This is the paper's model of computation, "the word RAM model with words of $\Theta(\log n)$ bits", in which "all integers arising in the algorithms are polynomially bounded". The scale $s$ plays the role of the paper's global $n$: it fixes the word size and the bound on the integers. The time bound may depend on the instance's own dimensions, which are at most $s$ in every problem of this mission; this lets a statement cover the small blocks of a large instance that the algorithms of Lemmas 4.2 and 4.3 and of Theorem 2.1 process with the large instance's machine.
--
--   **Formalization Note** The additive constant $C$ replaces the published `BigO`'s restriction to $n \ge 2$, since real powers vanish at $0$. Correctness is required at every width above the threshold, with no upper bound on $W$, as in the published `Problem.SolvedInTime`.
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 2, Model of Computation, p.4

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM

set_option autoImplicit false

open TrulySubcubicAPSP

namespace HypercliqueFalse

/-- **Solved within a real time bound, at a global scale.** Fischer, *The Hyperclique Hypothesis is
False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 2, "Model of Computation",
p.4: "We work in the word RAM model with words of Θ(log n) bits. All integers arising in the
algorithms are polynomially bounded (assuming that the input integers are)".

`SolvedWithin Q bound` says: for every exponent `κ` there are one program `P` of the published word
RAM, a width factor `b` and a constant `C` such that for every scale `s` and every instance `x` of
scale `s` whose input integers have absolute value at most `s ^ κ`, at every word width
`W ≥ b · (⌊log₂ s⌋ + 1)` the program solves `x` (the published `Problem.SolvedBy`: cell 0 holds `s`,
the input follows, `P` halts with the right verdict and output) within some `t ≤ C · bound s x + C`
steps.

**Formalization Note.** The scale `s` is the paper's global `n`: it fixes the word size and the
bound on the integers, while `bound` may depend on the instance's own dimensions (each at most
`s` in every problem of this mission). The additive `C` stands in for the published `BigO`'s
"for `n ≥ 2`": real powers vanish at `0`. Correctness at every width above the threshold, with no
upper bound on `W`, is the published machine's convention. -/
def SolvedWithin (Q : Problem) (bound : (s : ℕ) → Q.Instance s → ℝ) : Prop :=
  ∀ κ : ℕ, ∃ (P : List Instr) (b : ℕ) (C : ℝ), ∀ (s : ℕ) (x : Q.Instance s),
    (∀ a ∈ Q.input x, a.natAbs ≤ s ^ κ) → ∀ W ≥ b * (Nat.log2 s + 1),
      ∃ t : ℕ, (t : ℝ) ≤ C * bound s x + C ∧ Q.SolvedBy x P W t

end HypercliqueFalse


