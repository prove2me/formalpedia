-- Prove2me | Definitions.Def_SemAC02_IsSemRefutation
-- name    : SemAC02_IsSemRefutation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:27:49.667468+00:00
-- url     : https://prove2.me/theorems/137b94c5-9a13-4573-8f07-63f5df746fd6
-- title:
--   Depth-$d$ semantic AC0[2]-Frege refutation
-- statement:
--   Let $F$ be a family of AC0[2] circuits. A **depth-$d$ semantic AC0[2]-Frege refutation** of $F$ is a nonempty sequence of circuits $\pi=(A_1,\dots,A_L)$, each of depth at most $d$, in which every line $A_k$ is
--
--   1. an axiom from $F$,
--   2. a Boolean tautology, or
--   3. a semantic consequence of at most two earlier lines: there are $i,j<k$ (possibly $i=j$) with $[A_i]\cap[A_j]\subseteq[A_k]$, where $[A]$ is the set of assignments satisfying $A$;
--
--   and whose last line is the constant-zero circuit. Its size $\mathrm{size}(\pi)$ is the number of distinct rooted subcircuits occurring in its lines.
--
--   Semantic systems allow every sound inference of arity two, so lower bounds for them apply to every syntactic Frege system of bounded fan-in with the same lines.
--
--   **Formalization Note** The constant-zero circuit is `Circ.const false`. Lines are arbitrary list presentations; normalising a refutation gives a refutation of no larger depth or size.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), §2.2, p.18; inference rule p.16, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_SemAC02_Circ

namespace SemAC02

/-- A **depth-`d` semantic AC0[2]-Frege refutation** of a family of circuits `F`
(Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), §2.2, p.18; the inference rule p.16): a nonempty
sequence of circuits `π`, every one of depth at most `d`, such that every line is

* an axiom from `F`,
* a Boolean tautology (true under every assignment), or
* a semantic consequence of at most two earlier lines: there are `i, j < k` (`i = j` allowed,
  covering one-premise inferences) with `[π i] ∩ [π j] ⊆ [π k]`, i.e. every assignment satisfying
  both premises satisfies the conclusion;

and whose last line is the constant-zero circuit.

**Formalization Note** The size of `π` is `proofSize π`, the number of distinct subterms of its
lines. Lines are arbitrary list presentations of circuits; normalising a refutation (flattening,
deduplicating, cancelling) gives a refutation in the paper's sense of no larger depth or size,
so lower bounds over this notion are exactly the paper's. The constant-zero circuit is
`Circ.const false`. -/
def IsSemRefutation {V : Type} (d : ℕ) (F : Set (Circ V)) (π : List (Circ V)) : Prop :=
  (∀ A ∈ π, A.depth ≤ d) ∧
  (∀ (k : ℕ) (hk : k < π.length),
    π[k] ∈ F ∨
    (∀ x : V → Bool, π[k].eval x = true) ∨
    (∃ (i j : ℕ) (hi : i < k) (hj : j < k), ∀ x : V → Bool,
      (π[i]'(hi.trans hk)).eval x = true → (π[j]'(hj.trans hk)).eval x = true →
        π[k].eval x = true)) ∧
  π.getLast? = some (Circ.const false)

end SemAC02


