-- Prove2me | Definitions.Def_PrivacyParadox_Alloc_Model
-- name    : PrivacyParadox_Alloc_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:11.228236+00:00
-- url     : https://prove2.me/theorems/5a31a5f1-8122-4986-a089-a9f5a6c6eb69
-- title:
--   §2–§3.3, App. C pp. 22–25 — group mechanism at a fixed profile (payment (15)–(16), utility (4), truthfulness (6), participation (12)–(13), virtual cost (20)); program (39); Q, R (52)–(53)
-- statement:
--   This file fixes the two layers of the data-acquisition model of Liao, Su, Ziani, Wierman and Huang at a fixed desired participation profile $\theta^*$.
--
--   **Layer 1: one group of agents.** A group has costs in the support $\mathcal C=[c_{\min},c_{\max}]$ with a density $f$ and distribution function $F(c)=\int_{c_{\min}}^{c} f(x)\,dx$. A participant with cost $c$ suffers the privacy cost $h(c)=c\,b$ (Assumption 2), a non-participant suffers $g(c)$, and a participant enjoys the benefit $\bar w=w(\bar\theta)$. The threshold $\hat c\in\mathcal C$ satisfies $\bar\theta=F(\hat c)$, equation (14). The standing assumptions are: $c_{\min}<c_{\max}$; $0\le b<1$; $g(c)\le h(c)\le c$ on $\mathcal C$; $g$ continuous and non-decreasing; $c\mapsto h(c)-g(c)$ strictly increasing; $f$ continuous and positive on $\mathcal C$ with total mass $F(c_{\max})=1$; $\bar\theta=F(\hat c)>0$.
--
--   For an allocation rule $A$ (selection probability as a function of the reported cost) the paper's payment (15)–(16) is
--   $$
--   P(\tilde c)=\tilde c-h(\tilde c)+\frac{1}{A(\tilde c)}\Big((1-b)\int_{\tilde c}^{c_{\max}}A(z)\,dz+\tau\Big),\qquad
--   \tau=h(\hat c)-g(\hat c)-(1-b)\int_{\hat c}^{c_{\max}}A(z)\,dz-\bar w .
--   $$
--   For a menu $(A,P)$, the expected utility (4) of a participant with true cost $c$ reporting $\tilde c$ is $\bar u(\tilde c\mid c)=A(\tilde c)\,[P(\tilde c)-c+h(c)]-h(c)+\bar w$. The menu is *truthful* (6) if $\bar u(\tilde c\mid c)\le \bar u(c\mid c)$ for all $c,\tilde c\in\mathcal C$, and *strictly truthful* (footnote 4) if the inequality is strict for $\tilde c\ne c$. An agent with cost $c$ *joins* (12) if some report $\tilde c\in\mathcal C$ gives $\bar u(\tilde c\mid c)\ge -g(c)$, and the menu *induces* the profile (13) if $\int_{c_{\min}}^{c_{\max}}\mathbf 1[\text{the agent with cost } c \text{ joins}]\,f(c)\,dc=F(\hat c)$. The virtual cost (20) is $\phi(c)=c-h(c)+(1-b)F(c)/f(c)$.
--
--   **Layer 2: the discrete min-max program (39) after sorting.** Cells $k=1,\dots,K$ carry weights $\pi_k>0$ with $\sum_k\pi_k=\bar\theta^*$ and sorted virtual costs $0<\phi_1<\dots<\phi_K$; further data are $\gamma\in(0,1]$, $\bar\theta^*\in(0,1]$, the number of agents $s\ge1$, the budget $B$ and the constant $l$ of (51), with (40) $B/s-l>0$. The objective is
--   $$
--   U(A,p)=\frac{\gamma}{s(\bar\theta^*)^2}\Big(\sum_{k}\pi_k\frac{p_k}{A_k}-\frac{1}{\bar\theta^*}\Big(\sum_k\pi_kp_k\Big)^2\Big)+(1-\gamma)(1-\bar\theta^*)\Big(1-\frac{1}{\bar\theta^*}\sum_k\pi_kp_k\Big),
--   $$
--   an allocation $A$ is feasible if $0<A_k\le1$ and $\sum_k\pi_k\phi_kA_k+l\le B/s$, and an adversary choice $p$ is admissible if $0\le p_k\le1$. The auxiliary quantities (52)–(53) are
--   $$
--   Q(m,z)=\sum_{k\le m}\pi_k\phi_k+\sqrt{\phi_m/z}\sum_{k>m}\pi_k\sqrt{\phi_k},\qquad
--   R(m,z)=2\gamma\Big(\frac{z}{\phi_m}\sum_{k\le m}\pi_k\phi_k+\sum_{k>m}\pi_k\Big)+(\bar\theta^*)^2(1-\bar\theta^*)(1-\gamma)s .
--   $$
--   The file also names the bracket $G_k(A,p)=\frac{\gamma}{s(\bar\theta^*)^2}\big(\frac1{A_k}-\frac2{\bar\theta^*}\sum_j\pi_jp_j\big)-\frac1{\bar\theta^*}(1-\bar\theta^*)(1-\gamma)$ of Lemma 2 and the clipped allocation $\min\{1,\sqrt{\gamma p_k/(s(\bar\theta^*)^2\lambda\phi_k)}\}$ of Lemma 3, (45).
--
--   These objects carry the paper's two main theorems: Theorem 1 characterizes truthful mechanisms that induce the desired participation, and Theorem 2 solves the program (39).
--
--   **Formalization Note** At the fixed profile, the dependence of $h,g,b,w$ on the participation rates and correlation strengths is not part of either theorem and is dropped. Two hypotheses are added to the page's: $b<1$ (Assumption 1 gives only $h\le c$), and, in the program, $A_k>0$ instead of $A_k\ge0$, because Lean's division gives $p/0=0$ where the paper's objective is $+\infty$. Participation (12) is encoded with "some report" in place of "the best report", which agrees whenever the maximum is attained (in particular under truthfulness). Cells are indexed $1,\dots,K$ as in the paper; values of the sequences outside that range are never used. The virtual costs are assumed strictly increasing as the sorted list on p. 25 prints them.
-- source:
--   Liao, Su, Ziani, Wierman, Huang, arXiv:2105.14262v1, pp. 5–9, 13, 22–25, (4), (6), (12)–(16), (20), (39)–(40), (51)–(53), Lemmas 2–3

import Mathlib

namespace PrivacyParadox.Alloc

open MeasureTheory

/-! ## Layer 1: one group of agents at a fixed desired participation profile θ*

Liao–Su–Ziani–Wierman–Huang, arXiv:2105.14262v1, §2–§3.3 (pp. 5–9) and Definition 9 (p. 13).
At the fixed profile the privacy costs are functions of the cost `c` alone:
`h c = c * b` (Assumption 2, `b = b(θ_i; α_i)`), `g c = g(c, θ_i; α_i)`, and `wbar = w(θ̄)`. -/

/-- The data of one group `i` at the fixed profile θ*: cost support `[cmin, cmax]`, the slope `b`
of the participation privacy cost `h(c) = c·b`, the non-participation privacy cost `g`, the
participation benefit `wbar = w(θ̄)`, the cost density `f`, and the threshold `chat = ĉ_i` of (14). -/
structure GroupData where
  cmin : ℝ
  cmax : ℝ
  b : ℝ
  g : ℝ → ℝ
  wbar : ℝ
  f : ℝ → ℝ
  chat : ℝ

namespace GroupData

variable (G : GroupData)

/-- Privacy cost of a participant, Assumption 2: `h(c) = c · b`. -/
def h (c : ℝ) : ℝ := c * G.b

/-- The cost support `C = [cmin, cmax]` (p. 8). -/
def C : Set ℝ := Set.Icc G.cmin G.cmax

/-- Cumulative distribution function `F(c) = ∫_{cmin}^{c} f`. The participation rate of the
group is `θ̄_i = F(ĉ_i)` (14). -/
noncomputable def F (c : ℝ) : ℝ := ∫ x in G.cmin..c, G.f x

/-- Standing assumptions of the group at the fixed profile: Assumption 1 (p. 6) in the cost
variable, Assumption 2, the density on the support (p. 8), `ĉ_i` in the support with
`θ̄_i = F(ĉ_i) > 0` (p. 9). `b < 1` is added (Assumption 1 gives only `h ≤ c`). -/
def Standing : Prop :=
  G.cmin < G.cmax ∧ 0 ≤ G.b ∧ G.b < 1 ∧
  (∀ c ∈ G.C, G.g c ≤ G.h c ∧ G.h c ≤ c) ∧
  ContinuousOn G.g G.C ∧ MonotoneOn G.g G.C ∧
  StrictMonoOn (fun c => G.h c - G.g c) G.C ∧
  ContinuousOn G.f G.C ∧ (∀ c ∈ G.C, 0 < G.f c) ∧ G.F G.cmax = 1 ∧
  G.chat ∈ G.C ∧ 0 < G.F G.chat

/-- The constant `τ(θ_i, α_i)` of (16), p. 9, for the allocation rule `A`. -/
noncomputable def tau (A : ℝ → ℝ) : ℝ :=
  G.h G.chat - G.g G.chat - (1 - G.b) * (∫ z in G.chat..G.cmax, A z) - G.wbar

/-- The payment rule (15), p. 9, for the allocation rule `A`, at the reported cost `c'`. -/
noncomputable def pay (A : ℝ → ℝ) (c' : ℝ) : ℝ :=
  c' - G.h c' + (1 / A c') * ((1 - G.b) * (∫ z in c'..G.cmax, A z) + G.tau A)

/-- Expected utility (4), p. 7, of a participant with true cost `c` who reports `c'`, under the
menu `(A, P)`: `ū(c'|c) = A(c')[P(c') − c + h(c)] − h(c) + w(θ̄)`. -/
def ubar (A P : ℝ → ℝ) (c' c : ℝ) : ℝ :=
  A c' * (P c' - c + G.h c) - G.h c + G.wbar

/-- Truthfulness, Definition 1, (5)–(6), p. 7, for true and reported costs in the support. -/
def Truthful (A P : ℝ → ℝ) : Prop :=
  ∀ c ∈ G.C, ∀ c' ∈ G.C, G.ubar A P c' c ≤ G.ubar A P c c

/-- Strict truthfulness, footnote 4, p. 9. -/
def StrictTruthful (A P : ℝ → ℝ) : Prop :=
  ∀ c ∈ G.C, ∀ c' ∈ G.C, c' ≠ c → G.ubar A P c' c < G.ubar A P c c

/-- Participation decision (12), p. 8: an agent with cost `c` joins (`d_i(c|θ) = 1`) iff some
report gives participation utility at least `−g(c)`. -/
def Joins (A P : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ c' ∈ G.C, -G.g c ≤ G.ubar A P c' c

/-- The menu `(A, P)` induces the desired participation rate `θ̄_i = F(ĉ_i)` at equilibrium,
Definition 7, (13), p. 9. -/
def Induces (A P : ℝ → ℝ) : Prop :=
  ∫ c in G.cmin..G.cmax, Set.indicator {c | G.Joins A P c} G.f c = G.F G.chat

/-- Virtual cost (20), Definition 9, p. 13: `φ(c) = c − h(c) + (1 − b) F(c) / f(c)`. -/
noncomputable def phi (c : ℝ) : ℝ := c - G.h c + (1 - G.b) * G.F c / G.f c

end GroupData

/-! ## Layer 2: the discrete min-max program (39) after sorting (App. C, pp. 23–25)

Cells `k = 1, …, K` with probability `pr k = π_k`, sorted virtual cost `phi k = φ_k`; `theta = θ̄*`,
`gam = γ`, `s` the number of agents, `B` the budget and `l` the constant (51). -/

/-- Parameters of the discrete program (39) in the sorted indexing of p. 25. -/
structure Prog where
  K : ℕ
  pr : ℕ → ℝ
  phi : ℕ → ℝ
  theta : ℝ
  gam : ℝ
  s : ℕ
  B : ℝ
  l : ℝ

namespace Prog

variable (P : Prog)

/-- Standing assumptions of the discrete program: `K ≥ 1`, positive weights and virtual costs,
strictly increasing sorted virtual costs (p. 25), `Σ π_k = θ̄*` (p. 27), `0 < θ̄* ≤ 1`,
`0 < γ ≤ 1`, `s > 0`, and (40) `B/s − l > 0` (p. 23). -/
def Standing : Prop :=
  1 ≤ P.K ∧ (∀ k ∈ Finset.Icc 1 P.K, 0 < P.pr k ∧ 0 < P.phi k) ∧
  StrictMonoOn P.phi (Set.Icc 1 P.K) ∧ ∑ k ∈ Finset.Icc 1 P.K, P.pr k = P.theta ∧
  0 < P.theta ∧ P.theta ≤ 1 ∧ 0 < P.gam ∧ P.gam ≤ 1 ∧ 0 < P.s ∧
  0 < P.B / P.s - P.l

/-- The objective `U(A, p)` of (39), p. 23. -/
noncomputable def U (A p : ℕ → ℝ) : ℝ :=
  P.gam / (P.s * P.theta ^ 2) *
      (∑ k ∈ Finset.Icc 1 P.K, P.pr k * p k / A k
        - 1 / P.theta * (∑ k ∈ Finset.Icc 1 P.K, P.pr k * p k) ^ 2)
    + (1 - P.gam) * (1 - P.theta) * (1 - 1 / P.theta * ∑ k ∈ Finset.Icc 1 P.K, P.pr k * p k)

/-- Feasible allocations of (39): `0 < A_k ≤ 1` and the budget `Σ π_k φ_k A_k + l ≤ B/s`. -/
def FeasA (A : ℕ → ℝ) : Prop :=
  (∀ k ∈ Finset.Icc 1 P.K, 0 < A k ∧ A k ≤ 1) ∧
  ∑ k ∈ Finset.Icc 1 P.K, P.pr k * P.phi k * A k + P.l ≤ P.B / P.s

/-- Admissible adversary choices of (39): `0 ≤ p_k ≤ 1`. -/
def AdmP (p : ℕ → ℝ) : Prop := ∀ k ∈ Finset.Icc 1 P.K, 0 ≤ p k ∧ p k ≤ 1

/-- `Q(m, z)` of (52), p. 25. -/
noncomputable def Q (m : ℕ) (z : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 m, P.pr k * P.phi k
    + Real.sqrt (P.phi m / z) * ∑ k ∈ Finset.Icc (m + 1) P.K, P.pr k * Real.sqrt (P.phi k)

/-- `R(m, z)` of (53), p. 25. -/
noncomputable def R (m : ℕ) (z : ℝ) : ℝ :=
  2 * P.gam * (z / P.phi m * ∑ k ∈ Finset.Icc 1 m, P.pr k * P.phi k
      + ∑ k ∈ Finset.Icc (m + 1) P.K, P.pr k)
    + P.theta ^ 2 * (1 - P.theta) * (1 - P.gam) * P.s

/-- The bracket of Lemma 2, p. 23, whose sign decides the adversary's best response in cell `k`:
`γ/(s θ̄*²)·(1/A_k − (2/θ̄*) Σ_j π_j p_j) − (1/θ̄*)(1 − θ̄*)(1 − γ)`. -/
noncomputable def Gk (A p : ℕ → ℝ) (k : ℕ) : ℝ :=
  P.gam / (P.s * P.theta ^ 2) * (1 / A k - 2 / P.theta * ∑ j ∈ Finset.Icc 1 P.K, P.pr j * p j)
    - 1 / P.theta * (1 - P.theta) * (1 - P.gam)

/-- The allocation (45) of Lemma 3, p. 24, for multiplier `lam = λ*`:
`A*_k = min{1, √(γ p_k / (s θ̄*² λ* φ_k))}`. -/
noncomputable def clipA (p : ℕ → ℝ) (lam : ℝ) (k : ℕ) : ℝ :=
  min 1 (Real.sqrt (P.gam * p k / (P.s * P.theta ^ 2 * lam * P.phi k)))

end Prog

end PrivacyParadox.Alloc


