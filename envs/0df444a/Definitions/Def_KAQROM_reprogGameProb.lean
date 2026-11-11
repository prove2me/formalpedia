-- Prove2me | Definitions.Def_KAQROM_reprogGameProb
-- name    : KAQROM_reprogGameProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:31:55.673874+00:00
-- url     : https://prove2.me/theorems/d2724fc8-d951-4b61-925a-fe6164de7717
-- title:
--   The random reprogramming game of Lemma 3.5
-- statement:
--   Fix a full function $F_0:X\to Y$, a randomized classical algorithm $C$ given by a discrete distribution $p$ on its coins and an output map $c\mapsto R_c$ to partial functions, an initial state $\rho$ of a distinguisher $D$, a $q$-query quantum algorithm for $D$, and for each coin value $c$ a two-outcome measurement. The challenger samples $c\sim p$, sets $F_1=F_0[R_c]$, and gives $D$ quantum oracle access to $F_b$; after the oracle access is removed the coins $c$ are revealed and $D$ measures. The game value is
--   $$
--   \Pr[D\text{ outputs }1\mid b]=\sum_c p(c)\,\Pr[\text{outcome }1\mid F_b,c].
--   $$
--   The companion quantity $\Pr_{R\leftarrow C}[x\in\mathrm{Dom}(R)]=\sum_{c:\,x\in\mathrm{Dom}(R_c)}p(c)$ enters the bound of Lemma 3.5.
--
--   **Formalization Note** $D$'s first message $(F_0,C)$ is fixed. Coins range over any type with a discrete distribution, so $C$ may use unboundedly many coins; all sums converge because the summands are bounded by $p(c)$.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Lemma 3.5, p.19

import Mathlib
import Definitions.Def_KAQROM_Instrument
import Definitions.Def_KAQROM_Oracle
import Definitions.Def_KAQROM_QAlg

namespace KAQROM

open Matrix

/-- **The random reprogramming game of Lemma 3.5** (p.19), for a fixed first message of the
distinguisher `D`: the full function `F₀`, and the randomized classical algorithm `C` given by its
coin distribution `p` and its output `R = out c`, a partial function. The
challenger samples the coins `c`, sets `F₁ = F₀[R]`, and gives `D` (initial state `ρ`, a `q`-query
algorithm `A`) quantum oracle access to `F_b`; after the oracle access is removed the coins are
revealed and `D` outputs a bit by the coin-dependent measurement `meas c`. This is
`Pr[D outputs 1 | b]`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Lemma 3.5, p.19
(after [KS24, Lemma 3], [ABKM22, Lemma 3]).

**Formalization Note.** The coins of `C` range over any type with a discrete probability
distribution (`PMF`), so `C` may use unboundedly many coins. The output bit is the outcome `true`
of a two-outcome measurement (an instrument onto the trivial register) chosen by the revealed
coins. -/
noncomputable def reprogGameProb {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ}
    {C Rin W Rout ι : Type} [Fintype Rin] [Fintype W] [Fintype Rout] [Fintype ι]
    [DecidableEq Rin] [DecidableEq W] [DecidableEq Rout] {q : ℕ} (F0 : Oracle X ℓ)
    (p : PMF C) (out : C → PartialOracle X ℓ) (ρ : Matrix Rin Rin ℂ)
    (A : QAlg X ℓ Rin W Rout Unit ι q) (meas : C → Instrument Bool Rout Unit ι) (b : Bool) : ℝ :=
  ∑' c, (p c).toReal * ((meas c).apply true
    (A.run (if b then reprogramP F0 (out c) else F0) ρ ())).trace.re

/-- `Pr_{R ← C}[x ∈ Dom(R)]` for the coin distribution `p` and output map `out` (Lemma 3.5,
p.19). -/
noncomputable def reprogMass {X : Type} {ℓ : ℕ} {C : Type} (p : PMF C)
    (out : C → PartialOracle X ℓ) (x : X) : ℝ :=
  ∑' c, if (out c x).isSome then (p c).toReal else 0

end KAQROM


