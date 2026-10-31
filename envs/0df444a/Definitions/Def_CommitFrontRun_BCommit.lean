-- Prove2me | Definitions.Def_CommitFrontRun_BCommit
-- name    : CommitFrontRun_BCommit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:38:27.595465+00:00
-- url     : https://prove2.me/theorems/cdf064aa-499b-4bca-a923-4f2ab9a3849c
-- title:
--   $B$'s commit options: none, clone, or a guess $\sigma\in\Sigma$
-- statement:
--   After observing that $A$ sent a commit message, $B$ chooses one of:
--
--   1. **none**: no commit message;
--   2. **clone**: the same commit message as $A$, $\sigma_{B,1}=\sigma_{A,1}$;
--   3. **guess** $\sigma$: a commit message of his own for a message $\sigma\in\Sigma$, which he may later reveal.
--
--   A clone can never be opened by $B$: a reveal of $A$'s message from $B$'s address does not match $A$'s commitment $S(\mathrm{addr},\sigma_A)$, so the smart contract treats it as invalid. Lemma 1 of the paper is about this option.
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, §3, pp.13–14; Lemma 1, p.15

import Mathlib

namespace CommitFrontRun

/-- **B's commit options in the commit block.**
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, §3, pp.13–14, and Lemma 1, p.15.

After observing that A sent a commit message, B either sends no commit message (`none`), sends
the same commit message as A (`clone`, σ_{B,1} = σ_{A,1}), or commits to a message of his own,
S(addr_B, σ) for some σ ∈ Σ (`guess σ`).

**Formalization Note** A cloned commit can never be opened by B: a reveal of σ_A from B's
address does not match S(addr, σ_A) (pp.13–14), so the clone carries no reveal option. -/
inductive BCommit (Msg : Type) where
  | none
  | clone
  | guess (σ : Msg)
  deriving DecidableEq, Fintype

end CommitFrontRun


