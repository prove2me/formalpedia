-- Prove2me | Definitions.Def_SingleInteraction_Supplement_Embedding
-- name    : SingleInteraction_Supplement_Embedding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:05:45.027415+00:00
-- url     : https://prove2.me/theorems/18099f44-205e-4b2d-81f7-822661d4e9d2
-- title:
--   Pinned $|-\rangle$, real pinned states and the lifted family of Theorem 74
-- statement:
--   Data used to state Theorem 74:
--
--   1. the amplitudes of $|-\rangle=(|0\rangle-|1\rangle)/\sqrt2$;
--   2. a pinned instance has a **real pinned state** when every computational-basis amplitude of $|\psi_{\mathrm{pin}}\rangle=C_{\mathrm{pin}}|0^p\rangle$ is real;
--   3. for a family $\{h^{(n)}\}$, the output family $\hat h^{(n')}=S(h^{(n'-2)})$ for $n'\ge3$ and $\hat h^{(n')}=0$ for $n'<3$ (p.87), with $S$ the stoquastic embedding of eq. (57).
--
--   **Formalization Note** The lifted family follows p.87 exactly, including its value $0$ at $n'<3$.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §7.2, Theorem 74 and its proof, pp.85–87

import Mathlib
import Definitions.Def_SingleInteraction_Supplement_Interactions
import Definitions.Def_SingleInteraction_Supplement_Pinned

namespace SingleInteraction

namespace Supplement

/-!
# Data of the stoquastic embedding (Theorem 74)

Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version,
sha256 19ddc444…), §7.2, pp.85–87: Theorem 74 reduces a `p`-pinned instance whose pinned state has real
amplitudes to a `(p+1)`-pinned stoquastic instance in which the new sign qubit is pinned to `|−⟩`; for
`DSIH` the output family is `ĥ(n′) = S(h(n′−2))` for `n′ ≥ 3` and `ĥ(n′) = 0` for smaller `n′` (p.87).

**Formalization Note**
* `minusAmp b` is the amplitude of `|−⟩ = (|0⟩ − |1⟩)/√2` at the bit `b`.
* `RealPinned p x`: every amplitude of the pinned state `|ψpin⟩ = Cpin|0^p⟩` of `x` is real.
* `stoqLiftFam hfam n′` is `S(h^(n′−2))` (`stoqEmbed`, eq. (57)) for `n′ ≥ 3` and `0` otherwise,
  exactly as on p.87. -/

/-- The amplitude of `|−⟩ = (|0⟩ − |1⟩)/√2` at the computational-basis bit `b`. -/
noncomputable def minusAmp (b : Fin 2) : ℂ :=
  (if b = 0 then (1 : ℂ) else -1) / (Real.sqrt 2 : ℂ)

/-- The pinned state of a pinned instance has real amplitudes in the computational basis. -/
def RealPinned (p : ℕ) (x : PinnedInstance) : Prop :=
  ∀ s : Fin p → Fin 2, (pinState p x.gates s).im = 0

/-- The output family `ĥ(n′) = S(h^(n′−2))` for `n′ ≥ 3`, `0` for `n′ < 3` (p.87). -/
noncomputable def stoqLiftFam {k : ℕ} (hfam : ℕ → Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ) (n : ℕ) :
    Matrix (Fin (k + 1 + 1) → Fin 2) (Fin (k + 1 + 1) → Fin 2) ℂ :=
  if 3 ≤ n then stoqEmbed (hfam (n - 2)) else 0

end Supplement

end SingleInteraction


