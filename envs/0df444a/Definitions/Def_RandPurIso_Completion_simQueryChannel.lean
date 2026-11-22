-- Prove2me | Definitions.Def_RandPurIso_Completion_simQueryChannel
-- name    : RandPurIso_Completion_simQueryChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:29:51.498381+00:00
-- url     : https://prove2.me/theorems/163c9733-b2c6-4c1a-8ae8-699d09ce2fd7
-- title:
--   The simulator's query $\Phi^V$ on $\lceil\log_2(M+1)\rceil$ qubits
-- statement:
--   The register $\mathcal H([M])$ is encoded in binary on $w=\lceil\log_2(M+1)\rceil$ qubits. The simulator's oracle is $\Phi_{\hat V}$ with $\hat V|\mathrm{bin}\,x\rangle=\sum_yV_{yx}|\mathrm{bin}\,y\rangle$ for $x<N$, $\hat V=0$ on every other string, and $|\perp\rangle=|\mathrm{bin}\,M\rangle$: one forward application of $V$, inputs outside $\mathcal H([N])$ failing to $\perp$ (p. 30: "measuring $\{\Pi_{M_0},\Pi_{M_1}\}$, outputting $\perp$ if the result is $\Pi_{M_1}$, and otherwise applying $V$").
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Theorem 5.4, pp. 29–30

import Mathlib
import Definitions.Def_RandPurIso_Completion_qubitChannel
open Matrix

namespace RandPurIso.Completion

open ShiShallow

/-- Number of qubits of the `H([M])` register: `⌈log₂(M + 1)⌉`, enough for the strings `bin y`,
`y < M`, and one more string `bin M` used as `|⊥⟩`. -/
def qw (M : ℕ) : ℕ := Nat.clog 2 (M + 1)

/-- **The query channel `Φ^V` given to the simulator** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Theorem 5.4, p. 29: "makes at most one
query to its oracle", the oracle being `Φ^V`; p. 30: "`V₁ = D^V Π_{M0}` is implementable by measuring
`{Π_{M0}, Π_{M1}}`, outputting ⊥ if the result is `Π_{M1}`, and otherwise applying `V`").

On `qw M` qubits: `Φ_{V̂}` with `V̂|bin x⟩ = Σ_y V_{yx} |bin y⟩` for `x < N` and `V̂ = 0` on every other
string, and `|⊥⟩ = |bin M⟩`. The channel never exposes `V`'s entries beyond one application. -/
noncomputable def simQueryChannel {N M : ℕ} (V : Matrix (Fin M) (Fin N) ℂ) :
    Matrix (Bits (qw M)) (Bits (qw M)) ℂ → Matrix (Bits (qw M)) (Bits (qw M)) ℂ :=
  qubitChannel V (fun x => binEnc (qw M) x.val) (fun y => binEnc (qw M) y.val) (binEnc (qw M) M)

end RandPurIso.Completion


