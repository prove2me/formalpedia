-- Prove2me | Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete
-- name    : OptimalQueuingComplexity_Restless_PSPACEComplete
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T11:28:32.795665+00:00
-- url     : https://prove2.me/theorems/3c010a8c-fcc9-4221-bfae-aa81ef5d9e25
-- title:
--   PSPACE, polynomial-time many-one reductions, PSPACE-hardness and PSPACE-completeness
-- statement:
--   Let $P$ be a decision problem on a type of instances, presented through a binary encoding $\mathrm{enc}$.
--
--   1. $P$ is **in PSPACE** if there are a multi-stack Turing machine $M$ and a polynomial $p$ with natural coefficients such that, for every instance $a$, the machine started on $\mathrm{enc}(a)$ halts with the single output bit "$a \in P$", and every configuration it reaches from its initial configuration satisfies
--   $$\sum_{k} \bigl|\text{stack}_k\bigr| \;\le\; p\bigl(|\mathrm{enc}(a)|\bigr),$$
--   the sum running over the machine's finitely many stacks.
--   2. $P$ **polynomial-time many-one reduces** to a problem $Q$ (with encoding $\mathrm{enc}'$) if there is a map $f$ from instances of $P$ to instances of $Q$ that a Turing machine computes in polynomial time on encodings (it reads $\mathrm{enc}(a)$ and writes $\mathrm{enc}'(f(a))$ within $q(|\mathrm{enc}(a)|)$ steps for a polynomial $q$) and such that $P(a) \iff Q(f(a))$ for every $a$.
--   3. $Q$ is **PSPACE-hard** if every language $L \subseteq \{0,1\}^*$ in PSPACE polynomial-time many-one reduces to $Q$, and **PSPACE-complete** if moreover $Q$ is in PSPACE.
--
--   These are the standard complexity notions the paper uses in Section 3 ("PSPACE-hard", "PSPACE-complete").
--
--   **Formalization Note.** Machines are Mathlib's bundled multi-stack machines `Turing.FinTM2`; time is Mathlib's `Turing.TM2ComputableInPolyTime`. Mathlib has no space measure, so the space bound is a new definition: it counts all symbols on all stacks, the input stack included, which changes nothing up to the choice of the polynomial. The machine's internal state and labels range over finite types, and every pushed symbol is a function of the internal state, so the stack length is a faithful measure of space. A language is treated as a problem on bit strings with the identity encoding.
-- source:
--   Papadimitriou & Tsitsiklis, The Complexity of Optimal Queuing Network Control, Math. Oper. Res. 24(2) (1999), p. 294, Section 1 ("PSPACE is the class of problems solvable in polynomial space"; completeness under efficient reductions) and p. 303, Theorem 4 (PSPACE-hard); standard definitions

import Mathlib

namespace OptimalQueuingComplexity.Restless

/-- **PSPACE**: decidability in polynomial space by a multi-stack Turing machine.

A decision problem `P` on instances of type `α`, presented to the machine through the binary
encoding `enc : α → List Bool`, is in PSPACE if some bundled multi-stack Turing machine
(Mathlib's `Turing.FinTM2`, packaged as `Turing.TM2Computable`) started on `enc a` halts on
**every** instance `a` with the single output bit `[g a]`, where `g a = true ↔ P a`, and a
polynomial `p` with natural coefficients bounds the space: every configuration reachable from the
initial configuration on `enc a` has total stack length `∑ k, |stack k| ≤ p(|enc a|)`, the sum running over the
machine's finitely many stacks.

Mathlib has no space measure; this definition is new. The space count is the total number of
symbols on **all** stacks, the input stack included (so the input itself is counted; since
`p` is an arbitrary polynomial this changes nothing up to the choice of `p`). The internal state
and the function labels of a `FinTM2` range over finite types, and every pushed symbol is a
function of the finite internal state, so a reachable configuration of size `s` carries
`O(s)` bits of information. For a language `L : Language Bool` take `α = List Bool`,
`enc = id` and `P = (· ∈ L)`. -/
def InPSPACE {α : Type} (enc : α → List Bool) (P : α → Prop) : Prop :=
  ∃ (g : α → Bool) (h : Turing.TM2Computable enc (fun b : Bool => [b]) g) (p : Polynomial ℕ),
    (∀ a, g a = true ↔ P a) ∧
    ∀ (a : α) (cfg : h.tm.Cfg),
      StateTransition.Reaches h.tm.step
        (Turing.initList h.tm (List.map h.inputAlphabet.invFun (enc a))) cfg →
      ∑ k ∈ @Finset.univ h.tm.K h.tm.kFin, (Turing.TM2.Cfg.stk cfg k).length ≤
        p.eval (enc a).length

/-- Polynomial-time many-one reduction (Karp reduction) of the problem `P` (instances `α`,
encoding `ea`) to the problem `Q` (instances `β`, encoding `eb`): a map `f : α → β` that a
Turing machine computes in polynomial time on encodings (it reads `ea a` and writes
`eb (f a)` within `q((ea a).length)` steps for a polynomial `q`), such that
`P a ↔ Q (f a)` for every instance `a`. -/
def PolyReduces {α β : Type} (ea : α → List Bool) (P : α → Prop) (eb : β → List Bool)
    (Q : β → Prop) : Prop :=
  ∃ f : α → β, Nonempty (Turing.TM2ComputableInPolyTime ea eb f) ∧ ∀ a, P a ↔ Q (f a)

/-- **PSPACE-hardness**: every language in PSPACE polynomial-time many-one reduces to `Q`. -/
def PSPACEHard {β : Type} (eb : β → List Bool) (Q : β → Prop) : Prop :=
  ∀ L : Language Bool, InPSPACE (id : List Bool → List Bool) (fun w => w ∈ L) →
    PolyReduces (id : List Bool → List Bool) (fun w => w ∈ L) eb Q

/-- **PSPACE-completeness**: `Q` is in PSPACE and PSPACE-hard. -/
def PSPACEComplete {β : Type} (eb : β → List Bool) (Q : β → Prop) : Prop :=
  InPSPACE eb Q ∧ PSPACEHard eb Q

end OptimalQueuingComplexity.Restless


