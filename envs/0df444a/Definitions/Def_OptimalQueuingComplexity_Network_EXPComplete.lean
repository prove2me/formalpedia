-- Prove2me | Definitions.Def_OptimalQueuingComplexity_Network_EXPComplete
-- name    : OptimalQueuingComplexity_Network_EXPComplete
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T09:15:54.765149+00:00
-- url     : https://prove2.me/theorems/f07155c3-6730-4e6e-8a51-a10d58797204
-- title:
--   EXP, polynomial-time reductions, EXP-hardness and EXP-completeness
-- statement:
--   Let $P$ be a decision problem on a type $\alpha$ of instances, presented through a binary encoding $\mathrm{enc} : \alpha \to \{0,1\}^*$.
--
--   * $P$ is in **EXP** if there are a multi-stack Turing machine $T$ and a polynomial $p$ with natural coefficients such that, for every instance $a$, $T$ started on $\mathrm{enc}(a)$ halts within $\mathrm{time}(|\mathrm{enc}(a)|)$ steps with the single output bit "$P(a)$ holds", where
--   $$\mathrm{time}(n) \le 2^{p(n)} \quad \text{for all } n.$$
--   * A problem $P$ (instances $\alpha$, encoding $e_\alpha$) **polynomial-time reduces** to $Q$ (instances $\beta$, encoding $e_\beta$) if there is a map $f : \alpha \to \beta$ such that a Turing machine transforms $e_\alpha(a)$ into $e_\beta(f(a))$ within $q(|e_\alpha(a)|)$ steps for a polynomial $q$, and $P(a) \iff Q(f(a))$ for every $a$.
--   * $Q$ is **EXP-hard** if every language $L \subseteq \{0,1\}^*$ in EXP (with the identity encoding) polynomial-time reduces to $Q$, and **EXP-complete** if it is in EXP and EXP-hard.
--
--   This is the paper's definition: "EXP is the class of all problems solvable in time $2^{n^k}$ for some $k$. EXP-complete problems are the problems in EXP to which every other problem in EXP is efficiently reducible."
--
--   **Formalization Note.** Machines are Mathlib's `Turing.FinTM2` via `Turing.TM2ComputableInTime` (for EXP) and `Turing.TM2ComputableInPolyTime` (for reductions); the bound $2^{p(n)}$ with $p$ an arbitrary polynomial is equivalent to $2^{n^k}$ for some $k$. Hardness quantifies over every EXP language.
-- source:
--   Papadimitriou & Tsitsiklis, The Complexity of Optimal Queuing Network Control, Math. Oper. Res. 24(2) (1999), p. 294, definition of EXP and EXP-completeness

import Mathlib

namespace OptimalQueuingComplexity.Network

/-- **EXP** (Papadimitriou & Tsitsiklis 1999, p. 294: "EXP is the class of all problems solvable
in time `2^{n^k}` for some `k`"). A decision problem `P` on instances of type `α`, presented to a
Turing machine through the binary encoding `enc : α → List Bool`, is in EXP if some multi-stack
Turing machine (Mathlib's `Turing.FinTM2`) reads `enc a` and outputs the single bit
`[g a]`, where `g a = true ↔ P a`, within `time (enc a).length` steps, and the time function is
bounded by `2 ^ p(n)` for a polynomial `p` with natural coefficients. For a language
`L : Language Bool` take `α = List Bool`, `enc = id` and `P = (· ∈ L)`. -/
def InEXP {α : Type} (enc : α → List Bool) (P : α → Prop) : Prop :=
  ∃ (g : α → Bool) (h : Turing.TM2ComputableInTime enc (fun b : Bool => [b]) g)
    (p : Polynomial ℕ), (∀ a, g a = true ↔ P a) ∧ ∀ n, h.time n ≤ 2 ^ p.eval n

/-- Polynomial-time many-one reduction (Karp reduction) of the problem `P` (instances `α`,
encoding `ea`) to the problem `Q` (instances `β`, encoding `eb`): a map `f : α → β` that a
Turing machine computes in polynomial time on encodings (it reads `ea a` and writes
`eb (f a)` within `q((ea a).length)` steps for a polynomial `q`), such that
`P a ↔ Q (f a)` for every instance `a`. -/
def PolyReduces {α β : Type} (ea : α → List Bool) (P : α → Prop) (eb : β → List Bool)
    (Q : β → Prop) : Prop :=
  ∃ f : α → β, Nonempty (Turing.TM2ComputableInPolyTime ea eb f) ∧ ∀ a, P a ↔ Q (f a)

/-- **EXP-hardness**: every language in EXP polynomial-time many-one reduces to `Q`. -/
def EXPHard {β : Type} (eb : β → List Bool) (Q : β → Prop) : Prop :=
  ∀ L : Language Bool, InEXP (id : List Bool → List Bool) (fun w => w ∈ L) →
    PolyReduces (id : List Bool → List Bool) (fun w => w ∈ L) eb Q

/-- **EXP-completeness** (p. 294: "EXP-complete problems are the problems in EXP to which every
other problem in EXP is efficiently reducible"): `Q` is in EXP and EXP-hard. -/
def EXPComplete {β : Type} (eb : β → List Bool) (Q : β → Prop) : Prop :=
  InEXP eb Q ∧ EXPHard eb Q

end OptimalQueuingComplexity.Network


