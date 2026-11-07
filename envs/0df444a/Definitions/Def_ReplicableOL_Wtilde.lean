-- Prove2me | Definitions.Def_ReplicableOL_Wtilde
-- name    : ReplicableOL_Wtilde
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:51:14.847193+00:00
-- url     : https://prove2.me/theorems/3b30b739-7289-46d9-a63e-8950cbe26d4a
-- title:
--   The variable $\widetilde W$
-- statement:
--   The variable $\widetilde W=|X|-V+N$, which by the regret identity equals $\mathrm{Reg}_T+\Gamma$. Its mean is $A$ and its fourth moment is controlled for every causal learner.
--
--   **Formalization Note** A function of `(θ, S)` at a fixed seed.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Lemma 3.4(c), p.12

import Mathlib
import Definitions.Def_ReplicableOL_Xterm
import Definitions.Def_ReplicableOL_Vterm
import Definitions.Def_ReplicableOL_Nterm

namespace ReplicableOL

/-- **The variable $\widetilde W$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Lemma 3.4(c), p.12. `W̃ := |X| − V + N`.

**Formalization Note.** A function of `(θ, S)` at a fixed seed. -/
noncomputable def Wtilde {k L : ℕ} (Δ : ℝ) (Φ : EpochRule k L) (θ : Fin k → ℝ) (S : Bits k L) : ℝ :=
  |Xterm θ S| - Vterm Δ Φ θ S + Nterm Φ θ S

end ReplicableOL


