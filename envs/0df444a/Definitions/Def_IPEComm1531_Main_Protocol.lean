-- Prove2me | Definitions.Def_IPEComm1531_Main_Protocol
-- name    : IPEComm1531_Main_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:00:48.69067+00:00
-- url     : https://prove2.me/theorems/29f20cff-660d-409c-977d-14a052094c56
-- title:
--   Public-coin protocols computing a function at Bob with error $\varepsilon$
-- statement:
--   A deterministic protocol (published as `DistVerif.Simulation.DetProtocol`) chooses the next speaker from the transcript so far; the speaker's bit depends only on their own input and the transcript, and each party has an output function of their own input and the transcript. A public-coin protocol draws a shared random string $\omega\sim\mu$ and then runs the deterministic protocol for $\omega$.
--
--   The protocol $P$, run for exactly $k$ communicated bits, computes $f$ at Bob with error at most $\varepsilon$ if for every input pair $(x,y)$
--   $$\Pr_{\omega\sim\mu}\big[\text{Bob's output after }k\text{ bits}\neq f(x,y)\big]\le\varepsilon .$$
--
--   With $\varepsilon=1/3$ and $k$ minimal this defines the randomized communication complexity $R(f)$ of §2: the cost is the worst case over all inputs and coin outcomes, and the error bound holds on every input.
--
--   **Formalization Note** The published success predicate `ComputesWithin` asks both parties to output correctly; the source's protocol (§4) outputs at Bob, so this item uses Bob's output only. A protocol of worst-case cost at most $k$ is the same as one that always sends exactly $k$ bits, since dummy bits can be appended.
-- source:
--   Haoyu Wang, Pei Wu, Efficient Randomized Communication Without Large Monochromatic Rectangles, STOC 2027 submission #1531 (October 2026), PDF sha256 b5961a61deb8c9214217a3a78e8963de31cc748f73e562aad19dd584eb9eb136, §2 Communication models, p.5; §4 protocol step 5, p.10

import Mathlib
import Definitions.Def_DistVerif_Simulation_Protocol

set_option autoImplicit false

namespace IPEComm1531.Main

open DistVerif.Simulation

/-- The public-coin protocol `P`, run for exactly `k` communicated bits, computes `f` with error at
most `ε` at Bob: for every input pair `(x, y)`, the probability over the public coins that Bob's
output differs from `f x y` is at most `ε` (§2, p.5; §4, p.10). -/
def BobComputesWithin {b : ℕ} (P : PubProtocol b) (k : ℕ)
    (f : (Fin b → Bool) → (Fin b → Bool) → Bool) (ε : ℝ) : Prop :=
  ∀ x y : Fin b → Bool,
    P.μ.toOuterMeasure
        {ω | (P.prot ω).outB y ((P.prot ω).transcript x y k) ≠ f x y}
      ≤ ENNReal.ofReal ε

end IPEComm1531.Main


