-- Prove2me | Definitions.Def_ShorAdditivityEquiv_minOutputEntropy
-- name    : ShorAdditivityEquiv_minOutputEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:28:31.646139+00:00
-- url     : https://prove2.me/theorems/35bb1e02-9305-4a45-8203-14345df4d231
-- title:
--   Minimum output entropy $\min_{|\phi\rangle} H(N(|\phi\rangle\langle\phi|))$ of a channel
-- statement:
--   For a quantum channel $N$ with input space $\mathcal H_{\mathrm{in}}$, the minimum output entropy is
--   $$
--   \min_{|\phi\rangle} H\big(N(|\phi\rangle\langle\phi|)\big),
--   $$
--   "where $H$ is the von Neumann entropy and the minimization is taken over all vectors $|\phi\rangle$ in the input space of the channels". By concavity of the entropy, minimizing over mixed inputs gives the same value. Its additivity under tensor products is statement (i) of Theorem 1.
--
--   **Formalization Note** The minimum ranges over **unit** vectors (so $|\phi\rangle\langle\phi|$ is a state) and is encoded as the real infimum. For a channel with a nonempty input space the set is nonempty, bounded below by $0$, and the infimum is attained. $H$ is `QAlgorithms.vnEntropy` (bits).
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, Theorem 1 (i), p. 5 (also p. 4)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Information

open QAlgorithms

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, Theorem 1 (i), p.5 (also p.4): the minimum output entropy
`min_{|φ⟩} H(N(|φ⟩⟨φ|))` of a channel `N`, "where H is the von Neumann entropy and the
minimization is taken over all vectors |φ⟩ in the input space of the channels".

**Formalization Note.** The minimum ranges over **unit** vectors `φ` (`|φ⟩⟨φ|` is then a
state), and is encoded as the real infimum `sInf`. For a channel with a nonempty input space
the set is nonempty and bounded below by `0`, and the infimum is attained (the unit sphere is
compact and the entropy is continuous), so `sInf` is the paper's minimum. `H` is
`QAlgorithms.vnEntropy` (bits). -/
noncomputable def minOutputEntropy {I O : Type} [Fintype I] [Fintype O] [DecidableEq O]
    (N : Superop I O) : ℝ :=
  sInf {r | ∃ φ : EuclideanSpace ℂ I, ‖φ‖ = 1 ∧ r = vnEntropy (N (pureDensity φ))}

end ShorAdditivityEquiv


