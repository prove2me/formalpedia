-- Prove2me | Definitions.Def_RandomSizeStable_Stability_RankCutCert
-- name    : RandomSizeStable_Stability_RankCutCert
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-20T17:25:29.121657+00:00
-- url     : https://prove2.me/theorems/80231dfc-d9d5-4093-89d3-15c4834e3ccb
-- title:
--   Rank-cut certificate at D* (STOC 2027 #1342) — witness data and the cell predicate
-- statement:
--   Witness data for a rank-cut certificate (the hypotheses of Lemma 5, p. 13) at the draw law $D^\star$ of Figure 3 with $C_0 = 113609/200000$, and the predicates that per-cell statements assert. All objects are explicit:
--
--   - `phi x` $= \tfrac{19}{73}x + \tfrac{35}{146}x^2 + \tfrac12 x^{32}$ (the PGF of $D^\star$ as a polynomial), `Phi x` $= \tfrac{19}{146}x^2 + \tfrac{35}{438}x^3 + \tfrac{1}{66}x^{33}$, `mu` $= 1085/4818$, `C0` $= 113609/200000$, `b` $= 2840189/5000000$.
--   - For $j < 9$: intervals $[\mathrm{lo}_j, \mathrm{hi}_j]$ (`lo`, `hi`: $[49/100, b], [21/50, 49/100], \dots, [0, 3/100]$), slopes `eta j` (the paper's $\eta_j$) and cutoffs `h j` $\approx 0.96$–$0.98$ (rationals).
--   - `tail j x` $= C_0$ for $x \le b$, $\eta_j(\phi(h_j) - \phi(x)) - (h_j - x)$ for $b < x < h_j$, and $0$ for $x \ge h_j$.
--   - `rho j y` $=\mathrm{lo}_j$ if $y < \mathrm{lo}_j$; $y$ if $\mathrm{lo}_j \le y \le \mathrm{hi}_j$; $b$ if $\mathrm{hi}_j < y < b$; $y$ if $y \ge b$.
--   - `B a p A` $= \Phi(a) + \Phi(A) - \Phi(a + A - p) - p\mu$.
--   - `G1 j lam tau a p` $=$ `tail j a` $- a - \mathrm{lam}\cdot B(a,p,1) - \mathrm{tau}\,(\mu - \phi(\rho_j(a)))$, and `G2 j lam tau a p A` $=$ `tail j a` $-$ `tail j A` $- a - \mathrm{lam}\cdot B(a,p,A) - \mathrm{tau}\,(\mu - \phi(\rho_j(A)))$.
--   - `lamCell l0 l1 l2 p` $= (l_0 + l_1 p)/(1-p) + l_2 p/(\mu p - \Phi(p))$ and `tauCell t0 t1 p` $= p(t_0 + t_1 p)$ (Lean's division, so $x/0 = 0$).
--   - `CellOK p0 p1 l0 l1 l2 t0 t1`: for every $p$ with $0 < p < 1$ and $p_0 \le p \le p_1$, `lamCell` $\ge 0$, every `tauCell` $\ge 0$, and for every $j$ and all $0 \le a \le p \le A \le 1$ both $G_1 \ge 0$ and $G_2 \ge 0$ with these multipliers.
--   - `P1OK t0 t1`: for every $j$ and $0 \le a \le 1$, $a + (t_{0,j} + t_{1,j})(\mu - \phi(\rho_j(a))) \le$ `tail j a`.
--
--   Certified cells covering $(0,1)$ together with `P1OK` give the certificate: the rank measure $\nu_j$ is an atom at $b$ plus the density $\eta_j\phi' - 1$ on $(b, h_j)$, whose tail is `tail j`.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), p. 13-16, Lemma 5 (rank-cut criterion) at the draw law of Figure 3: witness data for a certificate.

import Mathlib

/-!
Witness data for a rank-cut certificate of the draw law D* (STOC 2027 #1342, Lemma 5), C0 = 113609/200000.
Global part only: the per-p-cell multipliers lam, tau are explicit literals in the cell statements.
-/

set_option autoImplicit false

noncomputable section

namespace RandomSizeStable.Stability.RankCutCert

/-- The PGF of D* as a polynomial. -/
def phi (x : ℝ) : ℝ := 19 / 73 * x + 35 / 146 * x ^ 2 + x ^ 32 / 2

/-- The primitive of `phi` vanishing at 0. -/
def Phi (x : ℝ) : ℝ := 19 / 146 * x ^ 2 + 35 / 438 * x ^ 3 + x ^ 33 / 66

/-- E[1/(D*+1)]. -/
def mu : ℝ := 1085 / 4818

/-- The constant C0. -/
def C0 : ℝ := 113609 / 200000

/-- The split point b. -/
def b : ℝ := 2840189 / 5000000

/-- Left ends of the root intervals J_j. -/
def lo (j : Fin 9) : ℝ := ![49 / 100, 21 / 50, 7 / 20, 3 / 10, 13 / 50, 21 / 100, 7 / 50, 3 / 100, 0] j

/-- Right ends of the root intervals J_j. -/
def hi (j : Fin 9) : ℝ :=
  ![2840189 / 5000000, 49 / 100, 21 / 50, 7 / 20, 3 / 10, 13 / 50, 21 / 100, 7 / 50, 3 / 100] j

/-- Density slopes eta_j. -/
def eta (j : Fin 9) : ℝ :=
  ![350540817 / 186650000, 362108663961 / 186650000000, 93594398139 / 46662500000,
    193849071801 / 93325000000, 198756643239 / 93325000000, 202963133043 / 93325000000,
    416793031413 / 186650000000, 108317112453 / 46662500000, 231006398403 / 93325000000] j

/-- Right ends h_j of the density parts. -/
def h (j : Fin 9) : ℝ :=
  ![19140111 / 19531250, 4890063411 / 5000000000, 1219935897 / 1250000000,
    4868611269 / 5000000000, 9720888189 / 10000000000, 2426730247 / 2500000000,
    4844454213 / 5000000000, 386464593 / 400000000, 4806920783 / 5000000000] j

/-- The tail function of the j-th rank measure: C0 up to b, then eta_j (phi h_j - phi x) - (h_j - x), then 0. -/
def tail (j : Fin 9) (x : ℝ) : ℝ :=
  if x ≤ b then C0 else if x < h j then eta j * (phi (h j) - phi x) - (h j - x) else 0

/-- The point of the j-th admissible root set used for a cut at y: lo_j below lo_j, y on J_j, b on (hi_j, b), y from b on. -/
def rho (j : Fin 9) (y : ℝ) : ℝ :=
  if y < lo j then lo j else if y ≤ hi j then y else if y < b then b else y

/-- The bracket Phi(a) + Phi(A) - Phi(a + A - p) - p mu. -/
def B (a p A : ℝ) : ℝ := Phi a + Phi A - Phi (a + A - p) - p * mu

/-- Slack of the cut inequality in the case r < A (worst A = 1, worst r = rho_j a). -/
def G1 (j : Fin 9) (lam tau a p : ℝ) : ℝ :=
  tail j a - a - lam * B a p 1 - tau * (mu - phi (rho j a))

/-- Slack of the cut inequality in the case r ≥ A (worst r = rho_j A). -/
def G2 (j : Fin 9) (lam tau a p A : ℝ) : ℝ :=
  tail j a - tail j A - a - lam * B a p A - tau * (mu - phi (rho j A))

/-- The multiplier lam on a p-cell: (l0 + l1 p)/(1 - p) + l2 p / (mu p - Phi p). -/
def lamCell (l0 l1 l2 p : ℝ) : ℝ := (l0 + l1 * p) / (1 - p) + l2 * p / (mu * p - Phi p)

/-- The multiplier tau_j on a p-cell: p (t0 + t1 p). -/
def tauCell (t0 t1 p : ℝ) : ℝ := p * (t0 + t1 * p)

/-- On the p-cell [p0, p1] (intersected with (0, 1)), the cell's multipliers are nonnegative and both
slacks G1, G2 are nonnegative. -/
def CellOK (p0 p1 l0 l1 l2 : ℝ) (t0 t1 : Fin 9 → ℝ) : Prop :=
  ∀ p : ℝ, 0 < p → p < 1 → p0 ≤ p → p ≤ p1 →
    0 ≤ lamCell l0 l1 l2 p ∧ (∀ j, 0 ≤ tauCell (t0 j) (t1 j) p) ∧
    ∀ (j : Fin 9) (a A : ℝ), 0 ≤ a → a ≤ p → p ≤ A → A ≤ 1 →
      0 ≤ G1 j (lamCell l0 l1 l2 p) (tauCell (t0 j) (t1 j) p) a p ∧
      0 ≤ G2 j (lamCell l0 l1 l2 p) (tauCell (t0 j) (t1 j) p) a p A

/-- The cut inequality at p = 1 with tau_j(1) = t0_j + t1_j. -/
def P1OK (t0 t1 : Fin 9 → ℝ) : Prop :=
  ∀ (j : Fin 9) (a : ℝ), 0 ≤ a → a ≤ 1 → a + (t0 j + t1 j) * (mu - phi (rho j a)) ≤ tail j a

end RandomSizeStable.Stability.RankCutCert


