-- Prove2me | Definitions.Def_GaussDiffSVP_SolvesSVPWithProb
-- name    : GaussDiffSVP_SolvesSVPWithProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:04.247651+00:00
-- url     : https://prove2.me/theorems/c7410194-0e00-4bd6-bdf0-015bac2af60a
-- title:
--   Solving SVP with success probability $p$ within bit time $T(\ell+1)^K$ and bit space $S(\ell+1)^K$
-- statement:
--   Let $P$ be a program of the randomized log-cost rational RAM (the published machine `TwMSOCount.Main`), let $B \in \mathbb Q^{n\times n}$ be a basis of the lattice $L = B\mathbb Z^n$, and write $\ell$ for the bit length of the input word of $B$ (the dimension, then the entries row by row). The program **solves SVP on $B$ within bit time $T(\ell+1)^K$ and bit space $S(\ell+1)^K$ with probability at least $p$** if:
--
--   1. on **every** coin tape the run halts, with bit time at most $T(\ell+1)^K$ and bit space at most $S(\ell+1)^K$;
--   2. on **every** coin tape the output is the integer coefficient vector $x \in \mathbb Z^n$ of a nonzero lattice vector $Bx \ne 0$;
--   3. the event that the output $x$ gives a shortest nonzero vector of $L$ (that is, $\|Bx\|\le\|By\|$ for every nonzero $y\in\mathbb Z^n$) is measurable and has probability at least $p$ under fair coins.
--
--   This is the success notion of Theorem 1.3: resource bounds on every execution ("All resource bounds hold on every execution", App. C.1.1), every output a nonzero lattice vector, and a quantitative success probability.
--
--   **Formalization Note** It reuses the published input encoding, input length, output encoding and success event of `SuperlatSVP` (not its fixed-$2/3$ predicate). The paper's word RAM is read as the log-cost RAM with bit costs; App. C.1.1 states that the same leading exponents hold with bit costs.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 1.3, p.7; §1.2, p.6; App. C.1.1, p.80

import Mathlib
import Definitions.Def_SuperlatSVP_SolvesSVPWithin

open MeasureTheory TwMSOCount.Main SuperlatSVP
open scoped ENNReal

namespace GaussDiffSVP

/-- A randomized program solves SVP on the rational basis `B` within bit time `T·(ℓ+1)^K` and
bit space `S·(ℓ+1)^K` with success probability at least `p` (Gao–Han–Hu, *Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 1.3, p.7; §1.2,
p.6; App. C.1.1, p.80):

1. on **every** coin tape the run halts, with bit time at most `T·(ℓ+1)^K` and bit space at most
   `S·(ℓ+1)^K`, where `ℓ = inputBits B` ("their time and bit space bounds hold on every
   execution", p.6; "All resource bounds hold on every execution", p.80);
2. on **every** coin tape the output is the coefficient vector `x ∈ ℤⁿ` of a nonzero lattice
   vector `Bx` ("Every output is a nonzero vector of L", p.7);
3. the success event (output a shortest nonzero vector, `SuperlatSVP.svpSuccess`) is measurable
   and has probability at least `p` under fair coins.

**Formalization Note.** The machine is the published randomized log-cost rational RAM
`TwMSOCount.Main` (bit time; bit space counts address and content bits of every cell ever
written, maximized over the run); App. C.1.1 states that the same leading exponents hold with bit
costs. The input is the word `SuperlatSVP.encBasis B`; the output is the integer coefficient
vector of the returned lattice vector, written by `SuperlatSVP.encIntVec`. -/
def SolvesSVPWithProb (P : Program) (K : ℕ) (T S p : ℝ) {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) :
    Prop :=
  (∀ τ : ℕ → Bool, ∃ s : RunStats, runStats P τ (Config.init (encBasis B)) = some s ∧
      (s.time : ℝ) ≤ T * ((inputBits B : ℝ) + 1) ^ K ∧
      (s.space : ℝ) ≤ S * ((inputBits B : ℝ) + 1) ^ K) ∧
    (∀ τ : ℕ → Bool, ∃ x : Fin n → ℤ, B.mulVec (fun i => (x i : ℚ)) ≠ 0 ∧
      callOutput P (Config.init (encBasis B)) τ = some (encIntVec x)) ∧
    MeasurableSet (svpSuccess P B) ∧
    ENNReal.ofReal p ≤ coinTape (svpSuccess P B)

end GaussDiffSVP


