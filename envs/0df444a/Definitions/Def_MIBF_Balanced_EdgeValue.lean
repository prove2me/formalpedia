-- Prove2me | Definitions.Def_MIBF_Balanced_EdgeValue
-- name    : MIBF_Balanced_EdgeValue
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:57:26.006581+00:00
-- url     : https://prove2.me/theorems/16916c77-29ab-4ead-8ee5-1290f7f4b8f3
-- title:
--   The extended Jeffreys edge cost $j$, four-moment tuples and laws $S(M)$, and the unrestricted edge value $\zeta(M)$ (bits and nats)
-- statement:
--   Let $H(t) = -t\log_2 t - (1-t)\log_2(1-t)$ be the binary entropy in bits (the published `GeneralCK.H`, with $H(0)=H(1)=0$) and $h(t) = -t\ln t-(1-t)\ln(1-t)$ the binary entropy in nats (`Real.binEntropy`), so $h = (\ln 2)\,H$. Write $J(t) = \log_2\frac{1-t}{t}$ (bits, `GeneralCK.J`) and $J_e(t)=\ln\frac{1-t}{t}$ (nats, `natJ`) for $0<t<1$.
--
--   **Edge cost.** The symmetrised (Jeffreys) edge cost is, for $u,w\in(0,1)$,
--   $$j(u,w)=\tfrac12\,(u-w)\bigl(J(w)-J(u)\bigr)=\tfrac12\bigl(D(u\Vert w)+D(w\Vert u)\bigr)\ \ge 0 ,$$
--   in bits (`GeneralCK.interiorCost`), and $j_e = (\ln 2)\, j$ is the same formula with $J_e$ (`natInteriorCost`). On the closed square it is extended lower-semicontinuously: $j(0,0)=j(1,1)=0$ and $j=+\infty$ at every other boundary point of $[0,1]^2$. The extended costs `edgeCost` (bits) and `edgeCostNat` (nats) take values in $[0,+\infty]$ and are $+\infty$ off the closed square as well.
--
--   **Four-moment tuples.** A four-moment tuple is $M=(\mu_u,\mu_w,e_u,e_w)$ with $0\le\mu_u,\mu_w\le1$, $0\le e_u\le H(\mu_u)$, $0\le e_w\le H(\mu_w)$ (`IsFourMomentTuple`; `IsFourMomentTupleNat` uses $h$ in place of $H$).
--
--   **Laws and edge value.** $S(M)$ is the set of joint laws of a pair $(U,W)$ of $[0,1]$-valued random variables with
--   $$\mathbb E U=\mu_u,\quad \mathbb E W=\mu_w,\quad \mathbb E H(U)=e_u,\quad \mathbb E H(W)=e_w ,$$
--   with no other restriction (no ordering of $U$ and $W$, no independence, no finite support). The unrestricted edge value is
--   $$\zeta(M)=\inf_{(U,W)\in S(M)}\ \mathbb E\, j(U,W)\ \in[0,+\infty],$$
--   with the boundary conventions above, and $\zeta(M)=+\infty$ if $S(M)$ is empty. `zeta` is in bits; `zetaNat` is the same object with $h$ and $j_e$, so `zetaNat` $=(\ln 2)\cdot$`zeta` at corresponding tuples.
--
--   These are the objects of the balanced Bellman inequality: $\zeta(M)$ is the least expected cost of a cube edge whose two endpoint values have the prescribed means and mean entropies.
--
--   **Formalization Note** A joint law is a probability measure $\mu$ on $\mathbb R\times\mathbb R$ with $\mu([0,1]^2)=1$; the moment conditions are Bochner integrals of the bounded continuous functions $p\mapsto p_1$, $p\mapsto p_2$, $H(p_1)$, $H(p_2)$, which are integrable for such $\mu$. The expectation of $j$ is the lower Lebesgue integral of the $[0,+\infty]$-valued extended cost, and $\zeta$ is an infimum in $[0,+\infty]$ (the infimum of the empty set is $+\infty$). The interior value is `ENNReal.ofReal` of the real formula, which is exact because $j\ge0$ on $(0,1)^2$.
-- source:
--   Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (held version, sha256 35793b82…1f9f), p. 7, eqs. (4)–(5), p. 8, Definition 2.1, eqs. (11)–(12); [Full] = arXiv:2609.24931v2 reproduced in the held PDF, [Full] pp. 10–11 (PDF 32–33), eqs. (10), (13)

import Mathlib
import Definitions.Def_GeneralCK_bellman

namespace MIBF.Balanced

open MeasureTheory
open scoped ENNReal

/-- The extended Jeffreys edge cost in bits on the closed unit square: the interior
formula `(u - w) (J w - J u) / 2` (as `GeneralCK.interiorCost`, which is nonnegative on
`(0,1)²`), the value `0` at the diagonal corners `(0,0)` and `(1,1)`, and `+∞` at every
other point (every other boundary point of `[0,1]²`, and points off the square). -/
noncomputable def edgeCost (u w : ℝ) : ℝ≥0∞ :=
  if 0 < u ∧ u < 1 ∧ 0 < w ∧ w < 1 then ENNReal.ofReal (GeneralCK.interiorCost u w)
  else if (u = 0 ∧ w = 0) ∨ (u = 1 ∧ w = 1) then 0
  else ⊤

/-- Natural-log log-odds `J(t) = ln((1 - t)/t)`, the derivative of the binary entropy
in nats on `0 < t < 1`. -/
noncomputable def natJ (t : ℝ) : ℝ := Real.log ((1 - t) / t)

/-- Interior Jeffreys cost in nats: `j(u, w) = (u - w) (J(w) - J(u)) / 2`. -/
noncomputable def natInteriorCost (u w : ℝ) : ℝ := (u - w) * (natJ w - natJ u) / 2

/-- The extended Jeffreys edge cost in nats, with the same boundary conventions as
`edgeCost`: interior formula on `(0,1)²`, `0` at `(0,0)` and `(1,1)`, `+∞` elsewhere. -/
noncomputable def edgeCostNat (u w : ℝ) : ℝ≥0∞ :=
  if 0 < u ∧ u < 1 ∧ 0 < w ∧ w < 1 then ENNReal.ofReal (natInteriorCost u w)
  else if (u = 0 ∧ w = 0) ∨ (u = 1 ∧ w = 1) then 0
  else ⊤

/-- A four-moment tuple `(mu, mw, eu, ew)` for the entropy function `ent`:
`0 ≤ mu, mw ≤ 1`, `0 ≤ eu ≤ ent mu`, `0 ≤ ew ≤ ent mw`. -/
def IsFourMomentTupleWith (ent : ℝ → ℝ) (mu mw eu ew : ℝ) : Prop :=
  0 ≤ mu ∧ mu ≤ 1 ∧ 0 ≤ mw ∧ mw ≤ 1 ∧ 0 ≤ eu ∧ eu ≤ ent mu ∧ 0 ≤ ew ∧ ew ≤ ent mw

/-- Four-moment tuple with entropies in bits (`GeneralCK.H`). -/
def IsFourMomentTuple (mu mw eu ew : ℝ) : Prop :=
  IsFourMomentTupleWith GeneralCK.H mu mw eu ew

/-- Four-moment tuple with entropies in nats (`Real.binEntropy`). -/
def IsFourMomentTupleNat (mu mw eu ew : ℝ) : Prop :=
  IsFourMomentTupleWith Real.binEntropy mu mw eu ew

/-- The set `S(M)` of joint laws of `(U, W)` on `[0,1]²` with the four moments
`E U = mu`, `E W = mw`, `E ent(U) = eu`, `E ent(W) = ew`: probability measures on `ℝ × ℝ`
giving full mass to the closed unit square. -/
def fourMomentLawsWith (ent : ℝ → ℝ) (mu mw eu ew : ℝ) : Set (Measure (ℝ × ℝ)) :=
  {μ | IsProbabilityMeasure μ ∧ μ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) = 1 ∧
    ∫ p, p.1 ∂μ = mu ∧ ∫ p, p.2 ∂μ = mw ∧
    ∫ p, ent p.1 ∂μ = eu ∧ ∫ p, ent p.2 ∂μ = ew}

/-- Joint laws with the four moments, entropies in bits. -/
def fourMomentLaws (mu mw eu ew : ℝ) : Set (Measure (ℝ × ℝ)) :=
  fourMomentLawsWith GeneralCK.H mu mw eu ew

/-- Joint laws with the four moments, entropies in nats. -/
def fourMomentLawsNat (mu mw eu ew : ℝ) : Set (Measure (ℝ × ℝ)) :=
  fourMomentLawsWith Real.binEntropy mu mw eu ew

/-- The unrestricted edge value in bits: the infimum of `E j(U, W)` (extended cost, in
`[0, +∞]`) over all joint laws in `fourMomentLaws`; `+∞` when there is no such law. -/
noncomputable def zeta (mu mw eu ew : ℝ) : ℝ≥0∞ :=
  ⨅ μ ∈ fourMomentLaws mu mw eu ew, ∫⁻ p, edgeCost p.1 p.2 ∂μ

/-- The unrestricted edge value in nats: the infimum of `E j(U, W)` (natural-log extended
cost) over all joint laws in `fourMomentLawsNat`. -/
noncomputable def zetaNat (mu mw eu ew : ℝ) : ℝ≥0∞ :=
  ⨅ μ ∈ fourMomentLawsNat mu mw eu ew, ∫⁻ p, edgeCostNat p.1 p.2 ∂μ

end MIBF.Balanced


