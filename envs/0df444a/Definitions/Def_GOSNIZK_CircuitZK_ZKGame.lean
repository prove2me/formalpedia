-- Prove2me | Definitions.Def_GOSNIZK_CircuitZK_ZKGame
-- name    : GOSNIZK_CircuitZK_ZKGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:28.144224+00:00
-- url     : https://prove2.me/theorems/b0f5f516-523c-4bde-a0bf-84fe771d0388
-- title:
--   The real oracle $P(\sigma,\cdot,\cdot)$ and the simulation oracle $S(\sigma,\tau,\cdot,\cdot)$ of the zero-knowledge game (§2, p. 5)
-- statement:
--   The oracles of the zero-knowledge game for Circuit SAT take a query $(C, w)$: a NAND circuit $C$ on any number of wires and a candidate witness $w$.
--
--   1. The **real oracle** $P(\sigma, \cdot, \cdot)$, with $\sigma = ck$, answers $(C, w)$ with a fresh proof $P(ck, C, w)$ of Figure 3 if $C(w) = 1$, and with *failure* otherwise.
--   2. The **simulation oracle** $S(\sigma, \tau, \cdot, \cdot)$, with $\sigma = ck$ and $\tau = tk$, answers $(C, w)$ with a fresh simulated proof $S_2(ck, tk, C)$ if $C(w) = 1$, and with *failure* otherwise.
--
--   The witness is used by the simulation oracle only to decide whether $C(w) = 1$, exactly as in the paper's definition $S(\sigma, \tau, x, w) = S_2(\sigma, \tau, x)$ for $(x, w) \in R$.
--
--   **Formalization Note** A query is a pair $(n, (C, w))$ with $n$ the number of wires; an answer is an optional proof, with `none` for failure.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 5, Section 2 (Computational or Perfect (adaptive multi-theorem) zero-knowledge)

import Mathlib
import Definitions.Def_GOSNIZK_CircuitZK_Protocol
import Definitions.Def_GOSNIZK_CircuitZK_Adversary

namespace GOSNIZK.CircuitZK

/-- An oracle query of the zero-knowledge game (Groth, Ostrovsky, Sahai, J. ACM 59(3) (2012), authors' version of
March 7, 2011, §2, p. 5): a circuit on any number `n` of wires together with a candidate witness. -/
abbrev Query : Type := Σ n : ℕ, Circuit n × (Fin n → Bool)

variable {N : ℕ} {R C CK XK TK Rp Pf : Type} [AddCommGroup R] [CommGroup C]
  [Fintype R] [Nonempty R] [Fintype Rp] [Nonempty Rp]

/-- The real oracle `P(σ, ·, ·)` (p. 5): on `(C, w)` it returns a proof `P(σ, C, w)` of Figure 3 if `C(w) = 1`, and
failure (`none`) otherwise. -/
noncomputable def realOracle (S : Scheme N R C CK XK TK Rp Pf) (ck : CK) (q : Query) :
    PMF (Option (Proof C Pf)) :=
  if q.2.1.Sat q.2.2 then (prove S ck q.2.1 q.2.2).map some else PMF.pure none

/-- The simulation oracle `S(σ, τ, ·, ·)` (p. 5): on `(C, w)` it returns `S₂(σ, τ, C)` if `C(w) = 1`, and failure
(`none`) otherwise. The witness is used only for that test. -/
noncomputable def simOracle (S : Scheme N R C CK XK TK Rp Pf) (ck : CK) (tk : TK) (q : Query) :
    PMF (Option (Proof C Pf)) :=
  if q.2.1.Sat q.2.2 then (simulate S ck tk q.2.1).map some else PMF.pure none

end GOSNIZK.CircuitZK


