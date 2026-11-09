-- Prove2me | Definitions.Def_QStateSearch_Reg
-- name    : QStateSearch_Reg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:30.275201+00:00
-- url     : https://prove2.me/theorems/fcfc08b4-6c11-4a16-9f88-a3180e1af2e7
-- title:
--   The verifier register $\{0,1\}\times[D]\times W$
-- statement:
--   The verifier's quantum register is
--   $$
--   \mathcal R_{D,W}=\{0,1\}\times[D]\times W,
--   $$
--   a control qubit, the $D$-dimensional **oracle-input register** on which the oracle acts, and a private workspace $W$, which may be any finite set. A pure state of the verifier is a vector of $\mathbb C^{\mathcal R_{D,W}}$.
--
--   The control qubit is what makes every oracle call controlled; the workspace collects all of the verifier's private registers, including those that hold received prover messages and deferred measurement outcomes.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Sections 2.1–2.2, pp.8–10

import Mathlib

namespace QStateSearch

/-- The verifier's register `Reg D W = Fin 2 × Fin D × W`: a control qubit, the
`D`-dimensional oracle-input register, and a private workspace `W` (any finite type).

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Sections 2.1–2.2, pp.8–10 ("controlled oracle calls are allowed"; "the verifier …
may retain arbitrary private quantum registers").

**Formalization Note.** The paper's verifier holds arbitrary private registers; they are
collected into one finite workspace `W`. The control qubit is the first factor; every oracle
call acts on the second factor controlled on the first. -/
abbrev Reg (D : ℕ) (W : Type) : Type := Fin 2 × Fin D × W

end QStateSearch


