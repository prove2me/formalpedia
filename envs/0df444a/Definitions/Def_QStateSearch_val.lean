-- Prove2me | Definitions.Def_QStateSearch_val
-- name    : QStateSearch_val
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:21:29.633785+00:00
-- url     : https://prove2.me/theorems/74b76431-b6bd-4c38-80d1-71771fc2f80c
-- title:
--   Optimal value $\mathrm{val}_W(V)$
-- statement:
--   For an oracle $W$,
--   $$
--   \mathrm{val}_W(V)=\max_P\ \mathrm{Acc}_W(V,P),
--   $$
--   the maximum over deterministic classical provers. By Lemma 1 of the paper this is also the maximum over all quantum provers.
--
--   **Formalization Note** The maximum is written as a supremum. $\mathrm{Acc}_W(V,P)$ depends on $P$ only through its replies at the finitely many transcripts of the protocol, so the supremum is attained.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 2.2, p.9

import Mathlib
import Definitions.Def_QStateSearch_AccW

namespace QStateSearch

/-- `val V O = val_O(V) = max_P Acc_O(V, P)`, the optimal acceptance probability over
deterministic classical provers.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 2.2, p.9: "define val_W(V) = max_P Acc_W(V, P), where the maximum is over
deterministic classical provers."

**Formalization Note.** `⨆` replaces `max`. `Acc_O(V, P)` depends on `P` only through its
replies at the finitely many transcripts the step list produces, so the family has finitely many
values and the supremum is attained (the paper's Lemma 1 / proof of Theorem 4, p.13). -/
noncomputable def val {D : ℕ} {W : Type} [Fintype W] [DecidableEq W] (V : Verifier D W) (O : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  ⨆ P : Prover, AccW V O P

end QStateSearch


