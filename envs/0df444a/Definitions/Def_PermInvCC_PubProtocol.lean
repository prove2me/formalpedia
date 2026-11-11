-- Prove2me | Definitions.Def_PermInvCC_PubProtocol
-- name    : PermInvCC_PubProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:24:04.121463+00:00
-- url     : https://prove2.me/theorems/97c86d20-fd1f-42ea-ba31-c1d48fd04efc
-- title:
--   Public-coin protocols, their output probabilities and worst-case cost
-- statement:
--   An **interactive public-coin protocol** draws a public coin value $\omega$ from a distribution $\mu$ on a finite set $\Omega$ and then runs a deterministic protocol tree that depends on $\omega$. For an input pair $(x,y)$ and a property $A$ of outputs, $\Pr_\omega[A(\text{output})]$ is the probability over the coins. The **cost** is the worst case of the number of communicated bits, over all inputs and all coin values.
--
--   This is the model behind $R^{\mathrm{pub}}$ and the protocols of Lemmas 3.3 and 3.4.
--
--   **Formalization Note** The output is the leaf label, known to both parties; this is the "both parties output" convention, which costs at most one bit more than Bob alone outputting (Definition 2.1). Private coins are subsumed by public coins. The cost is the maximal tree depth over the coins; branches no input reaches can be removed, so the least cost of a protocol for a task is its worst-case number of bits.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Definition 2.1, p.9

import Mathlib
import Definitions.Def_PermInvCC_ProtoTree

namespace PermInvCC

/-- An **interactive public-coin protocol** with outputs in `α` (Y. Huang and Z. Ye,
arXiv:2609.40116, held version sha256 fe1797dd…, Definition 2.1, p.9): a finite set `Ω` of
public coin values drawn from a distribution `μ`, and for each coin value `ω` a deterministic
protocol tree `tree ω`.

**Formalization Note.** The output is the leaf label, determined by the transcript and the
public coins, so it is known to both parties (the paper's remark "requiring both parties to
output changes the costs by at most one bit", p.9). Private coins are not needed: public coins
subsume them. Finitely many coin values lose nothing on finite input sets, where there are only
finitely many distinct trees of bounded depth. -/
structure PubProtocol (X Y α : Type) where
  /-- the public coin values -/
  Ω : Type
  [instFintype : Fintype Ω]
  /-- the law of the public coins -/
  μ : PMF Ω
  /-- the deterministic protocol run for each coin value -/
  tree : Ω → ProtoTree X Y α

attribute [instance] PubProtocol.instFintype

namespace PubProtocol

variable {X Y α : Type}

/-- The output on `(x, y)` for the coin value `ω`. -/
def run (P : PubProtocol X Y α) (ω : P.Ω) (x : X) (y : Y) : α := (P.tree ω).eval x y

open Classical in
/-- `Pr_ω[ property of the output on (x, y) ]`, the probability over the public coins that the
output on `(x, y)` satisfies `A`. -/
noncomputable def prob (P : PubProtocol X Y α) (x : X) (y : Y) (A : α → Prop) : ℝ :=
  ∑ ω, if A (P.run ω x y) then (P.μ ω).toReal else 0

/-- The **worst-case cost**: the largest number of bits communicated, over all coin values and
all inputs (the depth of every tree, maximized over coins).

**Formalization Note.** The depth counts every root-to-leaf path. Branches no input reaches can
be cut off without changing any output, so the least cost of a protocol computing a function is
the paper's worst-case number of communicated bits. -/
def cost (P : PubProtocol X Y α) : ℕ := Finset.univ.sup fun ω => (P.tree ω).depth

end PubProtocol

end PermInvCC


