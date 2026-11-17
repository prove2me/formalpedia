-- Prove2me | Definitions.Def_SuperlatSVP_Supplement_SolvesSVPWithProb
-- name    : SuperlatSVP_Supplement_SolvesSVPWithProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:35:30.207+00:00
-- url     : https://prove2.me/theorems/35bbca0e-53f2-44b3-9f36-81e72f4c045e
-- title:
--   Solving SVP on a rational basis with success probability $\ge c$ within given bit time and bit space
-- statement:
--   This definition extends the mission's success notion for the **shortest vector problem** (SVP) from probability $2/3$ to an arbitrary success probability $c$.
--
--   The machine is the published randomized log-cost rational RAM `TwMSOCount.Main`, which reads fair coins. An instance is an invertible basis $B\in\mathbb Q^{n\times n}$. Its input word is $n$ followed by the entries of $B$ row by row, and $\ell$ is the total bit length of that word. A program $P$ **solves SVP on $B$ within time $T$ and space $S$ with exponent $K$ and probability $c$** when:
--
--   1. on every coin tape the run of $P$ on the input word halts, with bit time at most $T\cdot(\ell+1)^K$ and bit space at most $S\cdot(\ell+1)^K$;
--   2. the event that the output is the integer coefficient vector $x$ of a shortest nonzero vector $Bx$ of $L(B)=B\mathbb Z^n$ is measurable and has probability at least $c$ under fair coins.
--
--   Theorem 4.9 uses it with a constant $c>0$.
--
--   **Formalization Note** The input word, the input length, the success event and the machine are the published ones (`SuperlatSVP.SolvesSVPWithin`); only the probability $2/3$ becomes the parameter $c$.
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), Theorem 4.9, p.38 (PDF p.38); §2, p.14

import Mathlib
import Definitions.Def_SuperlatSVP_SolvesSVPWithin

open MeasureTheory TwMSOCount.Main
open scoped ENNReal

namespace SuperlatSVP.Supplement

/-- Solving SVP on a rational basis `B` with success probability at least `c`, within bit time
`T·(ℓ+1)^K` and bit space `S·(ℓ+1)^K`, `ℓ = inputBits B`. Hhan, Kim, Kim, Laarhoven,
*Superlattice methods for the shortest vector problem and discrete Gaussian sampling*, STOC 2027
submission (manuscript sha256 fcf5b14f…ba), Theorem 4.9, p.38 (PDF p.38): "there exists a
randomized algorithm solving SVP with constant probability"; §2, p.14: "All parameters … are
implicitly parameterized by the dimension n and the bit-length of the input basis".

1. on **every** coin tape the run of `P` on the input word `encBasis B` halts, with bit time at most
   `T·(ℓ+1)^K` and bit space at most `S·(ℓ+1)^K`;
2. the success event `svpSuccess P B` (output the coefficient vector of a shortest nonzero vector of
   `L(B)`) is measurable and has probability at least `c` under fair coins.

**Formalization Note.** This is the published `SuperlatSVP.SolvesSVPWithin` with the fixed
probability `2/3` replaced by a parameter `c`; the input word, the input length, the success event
and the machine (`TwMSOCount.Main`, bit time and bit space) are the published ones, reused. -/
def SolvesSVPWithProb (P : Program) (K : ℕ) (T S c : ℝ) {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  (∀ τ : ℕ → Bool, ∃ s : RunStats, runStats P τ (Config.init (encBasis B)) = some s ∧
      (s.time : ℝ) ≤ T * ((inputBits B : ℝ) + 1) ^ K ∧
      (s.space : ℝ) ≤ S * ((inputBits B : ℝ) + 1) ^ K) ∧
    MeasurableSet (svpSuccess P B) ∧
    ENNReal.ofReal c ≤ coinTape (svpSuccess P B)

end SuperlatSVP.Supplement


