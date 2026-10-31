-- Prove2me | Definitions.Def_MayersBC_bcjlDensity
-- name    : MayersBC_bcjlDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:57:55.132813+00:00
-- url     : https://prove2.me/theorems/17559af8-bfec-4ace-ac0e-a634ecbdf8e0
-- title:
--   Honest BCJL commitment state $\rho_b$
-- statement:
--   The density operator of the $n$ photons when Alice honestly commits to $b$ is
--
--   $$
--   \rho_b = \sum_{\theta, c} p(\theta, c \mid b)\, |c\rangle_\theta\langle c|_\theta ,
--   $$
--
--   the density operator of the mixture of BB84 product states with the honest commitment distribution. Security against Bob asks that $\rho_0$ and $\rho_1$ be hard to distinguish; Mayers' attack starts from a purification of $\rho_0$.
--
--   **Formalization Note** The code $C$ and the string $r$ are explicit parameters; the paper suppresses them in its notation.
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section b, p.4

import Mathlib
import Definitions.Def_MayersBC_mixtureDensity
import Definitions.Def_MayersBC_bb84State
import Definitions.Def_MayersBC_bcjlProb

namespace MayersBC

/-- Mayers, arXiv:quant-ph/9603015v3, section b, p.4: the density operator of the photons when
Alice honestly commits to `b`, `ρ_b = Σ_{θ,c} p(θ, c|b) (|c⟩⟨c|)_θ`.

**Formalization Note.** `mixtureDensity (bcjlProb C r b) (fun w => bb84State w.1 w.2)`;
`(C, r)` are explicit parameters (suppressed in the paper's notation, p.4). -/
noncomputable def bcjlDensity {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (r : Fin n → ZMod 2) (b : ZMod 2) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  mixtureDensity (bcjlProb C r b) (fun w : Opening n => bb84State w.1 w.2)

end MayersBC


