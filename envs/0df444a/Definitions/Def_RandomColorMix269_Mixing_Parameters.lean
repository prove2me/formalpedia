-- Prove2me | Definitions.Def_RandomColorMix269_Mixing_Parameters
-- name    : RandomColorMix269_Mixing_Parameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:28.275289+00:00
-- url     : https://prove2.me/theorems/70fb7fa4-5657-4953-9477-d16581c5e0f6
-- title:
--   §§5.4–5.5 — the constants $b$, $r$, $a$, $C_r$, $C_{LD}$, $B$ and the blocks $B_u=S\cup\{u\}$
-- statement:
--   All constants of §§5.4–5.5 are computed from the numerical parameters and the graph. With $D=\lfloor(1+\eta/3)d\rfloor$, $b=q^{-(D+1)}$ (Proposition 5.11). For the mark probability $p$ of Lemma 5.10, $\zeta=p/4$ and $r=\lfloor\zeta N\rfloor$ with $N=|U|$. With the spectral-independence constant $C_{SI}$,
--   $$
--   a=\Big(\frac{4C_{SI}}{b^2}+2\Big)\ln\frac4\zeta+2,\qquad C_r=\Big(\frac{N-R_0}{r-R_0}\Big)^{R_0},\ R_0=\Big\lceil\frac{4C_{SI}\ln n}{b^2}\Big\rceil,
--   $$
--   $$
--   C_{LD}=2C_r\cdot4b^{-(3K\ln n+1)},\qquad B=a+3K\ln(1/b)+3 .
--   $$
--   The random-block failure probability is the fraction of $r$-subsets $T\subseteq U$ for which some component of $G[S\cup T]$ has more than $K\ln n$ vertices. For $u\in U$ the block is $B_u=S\cup\{u\}$, and the block dynamics $\mathcal L_{\mathcal B}=\sum_{u\in U}(P_u-I)$, $P_uf=\mathbb E_\mu[f\mid X(U\setminus\{u\})]$, has Dirichlet form $\sum_{u\in U}\mathbb E_\mu[\mathrm{Var}(f\mid X(U\setminus\{u\}))]$ (p.36).
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #269 (October 2026), PDF sha256 467638f1abc0f57df1bc0dcd9abfd308eb90ddbaf4947dac3eefa5f293ac6f05, pp.33–36 (§5.4 parameter choices, Proposition 5.15 proof p.35, §5.5 p.36)

import Definitions.Def_RandomColorMix269_Mixing_Geometry
import Definitions.Def_RandomColorMix269_Mixing_Entropy

open scoped Classical BigOperators
open Finset
set_option autoImplicit false
noncomputable section

namespace RandomColorMix269.Mixing

/-! §§5.4–5.5 pp.33–38: all constants and blocks are computed from
numerical parameters and the actual graph, without conclusion fields. -/
variable {V : Type*} [Fintype V] [DecidableEq V]

def marginalLower (q D : ℕ) : ℝ := ((q : ℝ) ^ (D + 1))⁻¹

def blockSize (p : ℝ) (N : ℕ) : ℕ := ⌊p / 4 * N⌋₊

def exponentA (Csi b p : ℝ) : ℝ := (4 * Csi / b^2 + 2) * Real.log (4 / (p / 4)) + 2

def chosenBlockFactor (N : ℕ) (Csi b p : ℝ) (n : ℕ) : ℝ :=
  factorBound N (blockSize p N) (Rzero (Csi * Real.log n) b)

def localEntropyConstant (Cr b K : ℝ) (n : ℕ) : ℝ :=
  2 * Cr * 4 * b ^ (-(3 * K * Real.log n + 1))

def polynomialExponent (Csi b p K : ℝ) : ℝ :=
  exponentA Csi b p + 3 * K * Real.log (1 / b) + 3

def randomBlockFailure (G : SimpleGraph V) (D : ℕ) (p K : ℝ) : ℝ :=
  subsetAverage (lowRegion G D) (blockSize p (lowRegion G D).card)
    (fun T => if SmallComponents G (buffer G D ∪ T)
      (K * Real.log (Fintype.card V)) then 0 else 1)

def bufferBlocks (G : SimpleGraph V) (D : ℕ) (u : lowRegion G D) : Finset V :=
  buffer G D ∪ {u.val}

def bufferEnergy (G : SimpleGraph V) (q D : ℕ) : ((V → Fin q) → ℝ) → ℝ :=
  weightedEnergy (MarkovMixing.properColoringDist G q) (bufferBlocks G D) (fun _ => 1)

end RandomColorMix269.Mixing


