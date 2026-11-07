-- Prove2me | Definitions.Def_LowDepthPRF_Game
-- name    : LowDepthPRF_Game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:34:32.37227+00:00
-- url     : https://prove2.me/theorems/da46574d-79ff-4097-9ad6-afe8b1d282f7
-- title:
--   Games, distinguishing advantage, $(q,t,\epsilon)$-indistinguishability
-- statement:
--   A **game** is a probabilistic experiment. An outcome $\omega$ is drawn uniformly from a nonempty finite set $\Omega$ and gives the adversary a sample (on its input wires) and an oracle. For an adversary $A$, a circuit with oracle gates and one output bit, and games $G_0,G_1$ with the same interface, the **advantage** is
--
--   $$\mathrm{Adv}_A(G_0,G_1)=\bigl|\Pr[A\text{ outputs }1\text{ in }G_0]-\Pr[A\text{ outputs }1\text{ in }G_1]\bigr|.$$
--
--   $G_0\approx_{q,t,\epsilon}G_1$ (**$(q,t,\epsilon)$-indistinguishable**, Definition 3.2) means that every well-formed adversary of size at most $t$ with at most $q$ oracle gates has advantage **strictly less** than $\epsilon$. $G_0\approx_{q,\infty,\epsilon}G_1$ means the same for adversaries of every size.
--
--   These are the games through which every security notion of the paper is stated.
--
--   **Formalization Note** Every experiment in the paper samples uniformly from finite sets, so a probability is a ratio of cardinalities. Adversaries are non-uniform: any circuit is allowed. A game without an oracle has oracle arities $0$, and one without a sample has sample length $0$. The paper uses these relations with $\epsilon>0$. Perfect indistinguishability ($\epsilon=0$) is encoded separately (see `NWiseIndep`).
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Definition 3.2, p.11 (pdf 13)

import Mathlib
import Definitions.Def_LowDepthPRF_Circuit

namespace LowDepthPRF

/-!
# Games, distinguishing advantage, (q, t, ε)-indistinguishability

Ding, Jain, Komargodski, *Pseudorandom Functions in NC¹ from LWE/LPN/CDH*, arXiv:2608.25213
(sha256 89a55849…), Definition 3.2, p.11.

**Formalization Note.**
* Every experiment of the paper samples from a finite set uniformly, so a game is a nonempty
  finite type `Ω` of equally likely outcomes; outcome `ω` hands the adversary a sample of `n` bits
  (`sample ω`, on its input wires) and an oracle (`oracle ω`). A game with no oracle uses
  `oa = ob = 0`; a game with no sample uses `n = 0`.
* `uprob P` is the uniform probability `#{ω | P ω} / #Ω`.
* An adversary is a well-formed circuit with oracle gates (`Circuit oa ob n 1`) and one output
  bit; it is non-uniform (any circuit). "Size-`t`" is size `≤ t` (with an oracle gate counting 1)
  and "at most `q` oracle queries" is at most `q` oracle gates.
* `Indist G₀ G₁ q t ε` is `G₀ ≈_{q,t,ε} G₁`: every such adversary has advantage **strictly less**
  than `ε`. `IndistAll G₀ G₁ q ε` is `G₀ ≈_{q,∞,ε} G₁` (adversaries of every size). The paper
  uses these with `ε > 0`; perfect indistinguishability (`ε = 0`) is not encoded through them
  (see `NWiseIndep`).
-/

/-- Uniform probability of an event over a finite type. -/
noncomputable def uprob {Ω : Type} [Fintype Ω] (P : Ω → Prop) : ℝ := by
  classical exact ((Finset.univ.filter P).card : ℝ) / (Fintype.card Ω : ℝ)

/-- A probabilistic experiment ("game"): a uniformly drawn outcome determines the sample of `n`
bits and the oracle `(Fin oa → Bool) → (Fin ob → Bool)` given to the adversary. -/
structure Game (n oa ob : ℕ) where
  /-- The finite set of equally likely outcomes. -/
  Ω : Type
  [fin : Fintype Ω]
  [ne : Nonempty Ω]
  /-- The sample given to the adversary on its input wires. -/
  sample : Ω → Fin n → Bool
  /-- The oracle the adversary's oracle gates query. -/
  oracle : Ω → (Fin oa → Bool) → (Fin ob → Bool)

attribute [instance] Game.fin Game.ne

namespace Game

variable {n oa ob : ℕ}

/-- `Pr[A outputs 1 in G]`. -/
noncomputable def prOne (G : Game n oa ob) (A : Circuit oa ob n 1) : ℝ :=
  uprob (fun ω : G.Ω => A.eval (G.oracle ω) (G.sample ω) 0 = true)

end Game

/-- `Adv_A(G₀, G₁) = |Pr[A outputs 1 in G₀] − Pr[A outputs 1 in G₁]|`. -/
noncomputable def adv {n oa ob : ℕ} (A : Circuit oa ob n 1) (G₀ G₁ : Game n oa ob) : ℝ :=
  |G₀.prOne A - G₁.prOne A|

/-- Definition 3.2: `G₀ ≈_{q,t,ε} G₁` — every well-formed adversary of size at most `t` making at
most `q` oracle queries has advantage less than `ε`. -/
def Indist {n oa ob : ℕ} (G₀ G₁ : Game n oa ob) (q : ℕ) (t ε : ℝ) : Prop :=
  ∀ A : Circuit oa ob n 1, A.WF → (A.size : ℝ) ≤ t → A.queries ≤ q → adv A G₀ G₁ < ε

/-- `G₀ ≈_{q,∞,ε} G₁`: every well-formed adversary, of any size, making at most `q` oracle
queries has advantage less than `ε`. -/
def IndistAll {n oa ob : ℕ} (G₀ G₁ : Game n oa ob) (q : ℕ) (ε : ℝ) : Prop :=
  ∀ A : Circuit oa ob n 1, A.WF → A.queries ≤ q → adv A G₀ G₁ < ε

end LowDepthPRF


