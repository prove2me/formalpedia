-- Prove2me | Definitions.Def_QaryCVP_Supplement_thetaDist
-- name    : QaryCVP_Supplement_thetaDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:12:55.683127+00:00
-- url     : https://prove2.me/theorems/e4a1c3ab-6ab2-4576-8b99-cd035aed548c
-- title:
--   The distributions $p_a$, $r_a$ on $\mathbb Z$, the second moment $\mu(a)$, entropies over $\mathbb Z$, the bound $G(\alpha,w)$ and the padding conditions (39)
-- statement:
--   For $a>0$ let $\Theta(a)=\sum_{j\in\mathbb Z}e^{-aj^2}$ (48). Define the probability mass functions on $\mathbb Z$ (49)
--
--   $$p_a(j)=\frac{e^{-aj^2}}{\Theta(a)},\qquad r_a(j)=\begin{cases}p_a(0)+2p_a(1),&j=0,\\0,&|j|=1,\\p_a(j),&|j|\ge2,\end{cases}$$
--
--   and the second moment $\mu(a)=\sum_{j\in\mathbb Z}j^2p_a(j)$. For a distribution $p$ on $\mathbb Z$, $H(p)=-\sum_{j\in\mathbb Z}p(j)\log_2p(j)$ (with $0\log0=0$) is its Shannon entropy in bits. The module also defines:
--
--   1. the counting parameter: the $a>0$ with $\mu(a)=x$ (unique for $x>0$, since $\mu$ decreases strictly from $+\infty$ to $0$);
--   2. the range $\{a>0:\ \mathrm{lo}\le H(p_a)\le\mathrm{hi}\}$;
--   3. the repetition-cost bound (44), for $\alpha>0$ and $0\le w\le1$: $G(\alpha,w)=h(w)-\min\{1,\alpha+w\}\,h\big(w/\min\{1,\alpha+w\}\big)$, with $h$ the binary entropy;
--   4. the padding conditions (39) at $a$: $\frac{\lambda+\kappa p_a(1)}{1-\kappa}>\varepsilon$ and $\frac{\kappa(1-2p_a(1))-2\lambda}{1-\kappa}>2\varepsilon$.
--
--   These quantities fix the prescribed-coordinate enumeration, the sign counts and the cost formulas of the SVP algorithm.
--
--   **Formalization Note** Entropies are full series over $\mathbb Z$ (no truncation), computed with `Real.negMulLog` divided by $\ln 2$; the counting parameter is the infimum of the solution set, which for $x>0$ is a singleton.
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Definition A.1, (48) and (49), p.59; p.49 (choice of a); (44), p.56; (39), p.51

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_QaryCVP_ent3

namespace QaryCVP.Supplement

/-- The probability mass function `p_a(j) = e^{−aj²}/Θ(a)` on `Z` (49), p.59, with
`Θ(a) = Σ_{j∈Z} e^{−aj²}` the published theta sum `QaryCVP.theta` (48).
Kim, Kwon, Lee, Lee, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Definition A.1, (48)
and (49), p.59.

**Formalization Note.** Every statement uses it with `a > 0`, where the series converges. -/
noncomputable def pa (a : ℝ) (j : ℤ) : ℝ := Real.exp (-a * (j : ℝ) ^ 2) / theta a

/-- The second moment `µ(a) = Σ_{j∈Z} j² p_a(j)` (49), p.59 (a convergent series for `a > 0`). -/
noncomputable def muA (a : ℝ) : ℝ := ∑' j : ℤ, (j : ℝ) ^ 2 * pa a j

/-- The probability mass function `r_a` on `Z` (49), p.59: `r_a(0) = p_a(0) + 2p_a(1)`,
`r_a(±1) = 0`, `r_a(j) = p_a(j)` for `|j| ≥ 2`. -/
noncomputable def ra (a : ℝ) (j : ℤ) : ℝ :=
  if j = 0 then pa a 0 + 2 * pa a 1 else if |j| = 1 then 0 else pa a j

/-- Shannon entropy in bits of a distribution `p` on `Z`, `H(p) = −Σ_{j∈Z} p(j) log₂ p(j)` with
`0 log 0 = 0` (Definition 2.1, p.13, as used on p.59: "H denotes Shannon entropy computed with
base-2 logarithms").

**Formalization Note.** `Real.negMulLog x = −x ln x` (zero at `0`), summed over `Z` and divided by
`ln 2` (R11). For `p = p_a` or `r_a` with `a > 0` the series converges (Gaussian tails); a
non-summable series would give the junk value `0`, which no statement uses. -/
noncomputable def entZ (p : ℤ → ℝ) : ℝ := (∑' j : ℤ, Real.negMulLog (p j)) / Real.log 2

/-- The counting parameter `a > 0` with `µ(a) = x` (p.49: "Choose `a > 0` so that
`µ(a) = u/(n − 1)`; this determines `a` uniquely, since `µ` decreases strictly from `+∞` to `0`").

**Formalization Note.** Defined as the infimum of the solution set; for `x > 0` the set is a
singleton (Lemma A.2(3), p.59), so the infimum is the root. -/
noncomputable def aSolve (x : ℝ) : ℝ := sInf {a : ℝ | 0 < a ∧ muA a = x}

/-- The range of counting parameters `{a > 0 : lo ≤ H(p_a) ≤ hi}` over which the suprema of
Theorem 5.8 (41) and of (45) are taken. -/
def aRange (lo hi : ℝ) : Set ℝ := {a : ℝ | 0 < a ∧ lo ≤ entZ (pa a) ∧ entZ (pa a) ≤ hi}

/-- The repetition-cost bound (44), p.56: for `α > 0`, `0 ≤ w ≤ 1`,
`G(α, w) = h(w) − min{1, α + w} · h(w / min{1, α + w})`, `h` the binary entropy in bits. -/
noncomputable def Gfun (α w : ℝ) : ℝ :=
  binEnt w - min 1 (α + w) * binEnt (w / min 1 (α + w))

/-- The padding conditions (39), p.51, at the counting parameter `a`:
`(λ + κ p_a(1))/(1 − κ) > ε` and `(κ(1 − 2p_a(1)) − 2λ)/(1 − κ) > 2ε`. -/
def Padding39 (κ lam ε a : ℝ) : Prop :=
  ε < (lam + κ * pa a 1) / (1 - κ) ∧ 2 * ε < (κ * (1 - 2 * pa a 1) - 2 * lam) / (1 - κ)

end QaryCVP.Supplement


