-- Prove2me | Definitions.Def_MantriCVQ_C1
-- name    : MantriCVQ_C1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:08.24888+00:00
-- url     : https://prove2.me/theorems/68186b41-e485-476e-af46-46f66b132174
-- title:
--   Certificate complexity $\mathrm{C}_1(H,z)$
-- statement:
--   A **1-certificate** of $H:\mathbb F_2^K\to\mathbb F_2$ at $z$ is a set $S\subseteq[K]$ such that $H(z')=1$ for every $z'$ of the whole cube that agrees with $z$ on $S$. The **certificate complexity** $\mathrm C_1(H,z)$ is the least size of a 1-certificate at $z$.
--
--   **Formalization Note** When $H(z)=1$ the whole set of coordinates is a certificate, so the infimum is over a nonempty set. Every use in this mission has $H(z)=1$.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3, p. 13 (PDF p. 15)

import Mathlib

namespace MantriCVQ

/-- A `1`-certificate of `H` at `z` (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3, p. 13
(PDF p. 15)): a set `S` of coordinates such that `H(z') = 1` for every `z'` of the whole cube that
agrees with `z` on `S`. -/
def IsOneCert {K : ℕ} (H : (Fin K → Bool) → Bool) (z : Fin K → Bool) (S : Finset (Fin K)) : Prop :=
  ∀ z' : Fin K → Bool, (∀ i ∈ S, z' i = z i) → H z' = true

/-- The certificate complexity `C₁(H, z)`: the least size of a `1`-certificate of `H` at `z`.

**Formalization Note** When `H z = true` the whole set of coordinates is a certificate, so the
infimum is over a nonempty set of naturals. Every use in this mission has `H z = true`. -/
noncomputable def C1 {K : ℕ} (H : (Fin K → Bool) → Bool) (z : Fin K → Bool) : ℕ :=
  sInf {c | ∃ S : Finset (Fin K), S.card = c ∧ IsOneCert H z S}

end MantriCVQ


