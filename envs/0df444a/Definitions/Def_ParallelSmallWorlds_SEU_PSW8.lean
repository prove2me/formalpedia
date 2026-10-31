-- Prove2me | Definitions.Def_ParallelSmallWorlds_SEU_PSW8
-- name    : ParallelSmallWorlds_SEU_PSW8
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:52:11.26093+00:00
-- url     : https://prove2.me/theorems/e93d892c-cc34-4599-97b2-19e13f6ee1bc
-- title:
--   Axiom PSW8: conditional likelihood
-- statement:
--   **Axiom PSW8** says: for all events $R,S,T$ with $T\succ_\Theta\emptyset$,
--
--   $$(R\mid T)\succeq_\Theta(S\mid T)\iff R\cap T\succeq_\Theta S\cap T,$$
--
--   where $(R\mid T)\succeq_\Theta(S\mid T)$ means that the decision maker holds $R$ at least as likely as $S$ when she knows that $T$ has occurred. It is the axiom behind Bayesian updating.
-- source:
--   French, Axiomatising the Bayesian Paradigm in Parallel Small Worlds, author's accepted manuscript OPRE-2018-05-258 (WRAP 118263), Axiom PSW8, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_ParallelSmallWorlds_SEU_SmallWorld

namespace ParallelSmallWorlds.SEU

/-- **Axiom PSW8 (conditional likelihood).**
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), Axiom PSW8, p.22 (PDF p.23): "∀R,S,T ∈ Qw with
T ≻Θw ∅: (R | T) ⪰Θw (S | T) ⟺ R ∩ T ⪰Θw S ∩ T."

Here `(R | T) ⪰Θw (S | T)` is the primitive relation `W.condLik R S T`. -/
def PSW8 {Θ C : Type*} (W : SmallWorld Θ C) : Prop :=
  ∀ R ∈ W.Q, ∀ S ∈ W.Q, ∀ T ∈ W.Q, W.strictLik (Sum.inl T) (Sum.inl ∅) →
    (W.condLik R S T ↔ W.lik (Sum.inl (R ∩ T)) (Sum.inl (S ∩ T)))

end ParallelSmallWorlds.SEU


