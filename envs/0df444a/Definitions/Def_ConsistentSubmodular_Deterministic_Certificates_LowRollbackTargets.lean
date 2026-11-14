-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackTargets
-- name    : ConsistentSubmodular_Deterministic_Certificates_LowRollbackTargets
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:09:08.156575+00:00
-- url     : https://prove2.me/theorems/c45453b3-e2f2-4c82-82b7-64ed44314c91
-- title:
--   Target-row quantities of low-parameter rollback: deficit, shifted benchmark, gap, ceiling and the polynomials $U,V,Y,M_1,M_2$
-- statement:
--   An atomic profile $P$ with stages $0,\dots,m$ consists of finitely many atoms $a$, each with a pool $\pi(a)\in\{0,\dots,m\}$, a nonempty label set $\Lambda_a\subseteq\{0,\dots,m\}$ with $i\le\pi(a)$ for every $i\in\Lambda_a$, and a weight $w_a\ge 0$. Its derived quantities at stage $t$ are the baseline $b_t=\sum_{\pi(a)<t}w_a$, the residual $\rho_i(t)=\sum_{\pi(a)\ge t,\ i\in\Lambda_a}w_a$, the designated value $g_t=\rho_t(t)$, the benchmark $P_t=b_t+g_t$, and, for a point $p$ of the simplex, the value $V_t(p)=b_t+\sum_{\pi(a)\ge t}w_a\bigl(1-\prod_{i\in\Lambda_a}(1-p_i)\bigr)$.
--
--   Throughout, $P$ is an atomic profile, $t,a,h$ are stages, $k$ is the (real) selector parameter, and division by $k$ follows the Lean convention that $x/0=0$.
--
--   - `deficit` $P\,t$: $1-g_t$. `shifted` $P\,t$: $P_t-1$. `gap` $P\,i\,t$: $g_t-\rho_i(t)$. All three are abbreviations; in particular $\mathrm{gap}(t,t)=0$.
--   - `Active` $P\,t$: $b_t<3g_t$.
--   - `ParentEligible` $P\,a\,t\,k$: $(k-1)\,\mathrm{deficit}(t)+(4-k)\,\mathrm{deficit}(a)\le\mathrm{gap}(a,t)$.
--   - `ceiling` $k\,d_0$: $2-\dfrac3k+\dfrac{3(4-k)d_0}{k}$.
--   - `U` $k\,d_0\,d\,p\,W$: $d-2\,\mathrm{ceiling}(k,d_0)+3p-(3-k)W$.
--   - `V` $k\,d_0\,d\,p\,\delta$: $p+(3-2k)(d+\delta)-2(4-k)d_0$.
--   - `VHigh` $k\,d_0\,d\,p\,\delta$: $p-(k-2)-(k-1)(3-k)(d+\delta)-(4-k)^2d_0$.
--   - `Y` $k\,d_0\,d\,p\,\delta\,P$: $\dfrac{(k-1)(3-k)}{k}\bigl(P-(k-1)(d+\delta)-(4-k)d_0\bigr)+\dfrac{k^2-3k+3}{k}\,p-\mathrm{ceiling}(k,d_0)$.
--   - `M₁` $k\,T\,P_t\,z\,u$: $T+P_t-(3-k)z-ku$, and `M₂` $k\,T\,P_t\,z\,u$: $T+P_t-(4-k)z-(k-1)u$, where $P_t$ is a real argument.
--   - `suffRow` $P\,a\,h\,t\,k$: the sufficient row $b_t+(1-k/4)\rho_a(t)+(k/4)\rho_h(t)-\tfrac14\min(\rho_a(t),\rho_h(t))$, the lower bound for the value at stage $t$ of the mixture of $\delta_a$ and $\delta_h$ with mass $k/4$ on $h$.
--
--   The file also records the identity $\mathrm{gap}(t,t)=0$.
--
--   These quantities are the scalar targets of the low-parameter rollback argument: they bound the rows of a parent and a child in terms of deficits, so that the failed parent tests can be turned into the sufficient-row inequality $\tfrac34P_t\le\mathrm{suffRow}$ at later stages in the construction of certificates for Theorem 7.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollbackTargets.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_AtomicFacts

noncomputable section

namespace ConsistentSubmodular

namespace LowRollback

variable {m aCount : ℕ}

abbrev deficit (P : AtomicProfile m aCount) (t : Fin (m + 1)) : ℝ := 1 - P.designated t

abbrev shifted (P : AtomicProfile m aCount) (t : Fin (m + 1)) : ℝ := P.benchmark t - 1

abbrev gap (P : AtomicProfile m aCount) (i t : Fin (m + 1)) : ℝ :=
  P.designated t - P.residual i t

def Active (P : AtomicProfile m aCount) (t : Fin (m + 1)) : Prop :=
  P.baseline t < 3 * P.designated t

def ParentEligible (P : AtomicProfile m aCount) (a t : Fin (m + 1)) (k : ℝ) : Prop :=
  (k - 1) * deficit P t + (4 - k) * deficit P a ≤ gap P a t

def ceiling (k d₀ : ℝ) : ℝ := 2 - 3 / k + 3 * (4 - k) * d₀ / k

def U (k d₀ d p W : ℝ) : ℝ := d - 2 * ceiling k d₀ + 3 * p - (3 - k) * W

def V (k d₀ d p δ : ℝ) : ℝ := p + (3 - 2 * k) * (d + δ) - 2 * (4 - k) * d₀

def VHigh (k d₀ d p δ : ℝ) : ℝ :=
  p - (k - 2) - (k - 1) * (3 - k) * (d + δ) - (4 - k) ^ 2 * d₀

def Y (k d₀ d p δ P : ℝ) : ℝ :=
  ((k - 1) * (3 - k) / k) * (P - (k - 1) * (d + δ) - (4 - k) * d₀)+
    ((k ^ 2 - 3 * k + 3) / k) * p - ceiling k d₀

def M₁ (k T Pt z u : ℝ) : ℝ := T + Pt - (3 - k) * z - k * u

def M₂ (k T Pt z u : ℝ) : ℝ := T + Pt - (4 - k) * z - (k - 1) * u

@[simp] theorem gap_self (P : AtomicProfile m aCount) (t : Fin (m + 1)) : gap P t t = 0 := sub_self _

def suffRow (P : AtomicProfile m aCount) (a h t : Fin (m + 1)) (k : ℝ) : ℝ :=
  P.baseline t + (1 - k / 4) * P.residual a t + (k / 4) * P.residual h t-
    min (P.residual a t) (P.residual h t) / 4

end LowRollback

end ConsistentSubmodular

end


