-- Prove2me | Definitions.Def_IDivGeom_ExpFam_Setting
-- name    : IDivGeom_ExpFam_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T16:56:40.845029+00:00
-- url     : https://prove2.me/theorems/d80c8be9-3668-4a7e-9ae3-4a7c4521d119
-- title:
--   Variation distance, I-projection, moment sets ℰ(a), the sets A_R and T_R, and the value function F (§1, §3)
-- statement:
--   Throughout, $P, Q, R$ denote probability distributions (PD's) on one measurable space $(X,\mathcal X)$, and $I(P\|Q)$ is the I-divergence (Kullback–Leibler information) of (1.1): $I(P\|Q)=\int \log p_Q\,dP$ if $P\ll Q$, and $+\infty$ otherwise, with the conventions (1.3) $\log 0=-\infty$, $\log\frac a0=+\infty$, $0\cdot(\pm\infty)=0$. This file collects the objects used by the existence theorem for I-projections under moment constraints.
--
--   1. **Variation distance** (1.6). For PD's $P, Q$,
--   $$|P-Q| = \int |p_R - q_R|\,dR,$$
--   where $R$ is any PD dominating both; the value does not depend on $R$.
--   2. **Convex set of PD's.** A set $\mathcal E$ of PD's is convex if $\alpha P + (1-\alpha)P' \in \mathcal E$ whenever $P, P'\in\mathcal E$ and $0\le\alpha\le1$.
--   3. **I-projection** (1.5). If $\mathcal E$ meets the I-sphere $S(R,\infty)=\{P: I(P\|R)<\infty\}$, a PD $Q\in\mathcal E$ with
--   $$I(Q\|R)=\min_{P\in\mathcal E} I(P\|R)$$
--   is called the I-projection of $R$ on $\mathcal E$.
--   4. **Moment sets.** For real-valued measurable functions $f_1,\dots,f_k$ on $X$ and $a=(a_1,\dots,a_k)$, $\mathcal E(a_1,\dots,a_k)$ is the set of PD's $P$ for which every $f_i$ is $P$-integrable and $\int f_i\,dP = a_i$, $i=1,\dots,k$.
--   5. **The set $A_R$.** $A_R\subseteq E^k$ is the set of $(a_1,\dots,a_k)$ such that $\mathcal E(a_1,\dots,a_k)$ contains some $P$ with $I(P\|R)<\infty$.
--   6. **The set $T_R$** of (3.16):
--   $$T_R=\Big\{(t_1,\dots,t_k): \exp\textstyle\sum_{i=1}^k t_i f_i(x)\ \text{is $R$-integrable}\Big\}.$$
--   7. **The value function** of (3.18):
--   $$F(a_1,\dots,a_k)=\inf_{P\in\mathcal E(a_1,\dots,a_k)} I(P\|R)\in[0,\infty],$$
--   which equals $+\infty$ when $\mathcal E(a_1,\dots,a_k)$ is empty or contains no PD of finite I-divergence from $R$, so it is finite exactly on $A_R$.
--
--   These are the objects in which Theorem 3.3 and the steps of its proof are stated.
--
--   **Formalization Note** The I-divergence is Mathlib's `klDiv`, valued in $[0,\infty]$: for probability measures it is $\infty$ unless $P\ll Q$ and the log-likelihood ratio is $P$-integrable, and since the negative part of $p\log p$ is integrable this is exactly (1.1) with (1.3). The variation distance uses $P+Q$ as the dominating measure (it dominates both; the page allows any dominating PD and the value is the same). The I-projection carries the clause $I(Q\|R)<\infty$, which is the page's presupposition that $\mathcal E$ meets $S(R,\infty)$. Convex combinations use weights $\alpha\in[0,1]$ in $\mathbb R_{\ge0}$. $E^k$ is `Fin k → ℝ` with the product (Euclidean) topology; the page's (3.16) prints $(t_1,\dots,t_n)$, a misprint for $(t_1,\dots,t_k)$. $F$ is an infimum in $[0,\infty]$ with $R$ (not the misprinted $Q$ of (3.18)) as the reference measure. The moment-set definition is stated for a general index type and used with $\{1,\dots,k\}$ = `Fin k`. Items 1–4 (variation distance, convex sets, I-projection, moment sets) are the shared definitions of the series, imported from the module `IDivGeom.IPFP.Setting`; this file defines items 5–7 on top of them.
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), pp. 146–147 (PDF 1–2), (1.1)–(1.6); p. 151 (PDF 6), case (A); p. 156 (PDF 11), (3.16) and Theorem 3.3; p. 157 (PDF 12), (3.18)

import Mathlib
import Definitions.Def_IDivGeom_IPFP_Setting

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal NNReal

namespace IDivGeom.ExpFam

variable {X : Type*} [MeasurableSpace X]

/-- `A_R`: the moment vectors `a` for which `ℰ(a)` meets the I-sphere `S(R, ∞)`. -/
def finiteSet {k : ℕ} (f : Fin k → X → ℝ) (R : Measure X) : Set (Fin k → ℝ) :=
  {a | ∃ P ∈ IDivGeom.IPFP.momentSet f a, klDiv P R ≠ ⊤}

/-- `T_R` of (3.16): the parameters `t` with `exp (∑ i, t i * f i)` integrable under `R`. -/
def expIntegrableSet {k : ℕ} (f : Fin k → X → ℝ) (R : Measure X) : Set (Fin k → ℝ) :=
  {t | Integrable (fun x => Real.exp (∑ i, t i * f i x)) R}

/-- `F(a) = inf_{P ∈ ℰ(a)} I(P‖R)` of (3.18), in `[0, ∞]` (equal to `∞` when `ℰ(a)` is empty). -/
noncomputable def valueFn {k : ℕ} (f : Fin k → X → ℝ) (R : Measure X) (a : Fin k → ℝ) : ℝ≥0∞ :=
  ⨅ P ∈ IDivGeom.IPFP.momentSet f a, klDiv P R

end IDivGeom.ExpFam


