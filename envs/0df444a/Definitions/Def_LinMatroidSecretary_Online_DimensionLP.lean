-- Prove2me | Definitions.Def_LinMatroidSecretary_Online_DimensionLP
-- name    : LinMatroidSecretary_Online_DimensionLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:43.723957+00:00
-- url     : https://prove2.me/theorems/7b62238a-07d6-4498-b7ab-edf320287267
-- title:
--   §2.1–§2.2, §3 — distributions on subspaces, the Dimension Invariant Inequality (1), µ_Y by (2), g_p by (3), LP(Y) and P(X, µ)
-- statement:
--   Throughout, $V=F^d$, subspaces are ordered by inclusion, $W\cap L$ and $W+L$ are meet and join, $\dim$ is the dimension, $\langle e\rangle$ is the span of $v_e$ and $\langle Y\rangle$ the span of $\{v_e:e\in Y\}$. A set $Y$ of elements is a finite subset of a value-ordered index set; for each $e\in Y$ a distribution $\mu_{Y-e}$ is given, and an acceptance probability $p(e,W)$ is attached to each $e\in Y$ and $W\in\operatorname{supp}\mu_{Y-e}$. Let $k\ge1$ be the sample size and $i=|Y|$.
--
--   1. **Distributions on subspaces.** A finitely supported $\mu:\{\text{subspaces of }V\}\to\mathbb R$ is a probability distribution on the subspaces of $S$ if $\mu\ge0$, $\sum_W\mu(W)=1$ and every $W$ in its support satisfies $W\le S$. $\mathbb E_{W\sim\mu}[f(W)]=\sum_W\mu(W)f(W)$.
--
--   2. **Dimension Invariant Inequality (1).** A distribution $\mu$ of a set of size $m$ satisfies (1) for $L$ if
--   $$\mathbb E_{W\sim\mu}[\dim(W\cap L)]\le\Bigl(1-\frac km\Bigr)\dim L,$$
--   and satisfies (1) if this holds for **every** subspace $L$ of $V$.
--
--   3. **The update (2).**
--   $$\mu_Y(U)=\frac1i\sum_{e\in Y}\ \sum_{W\in\operatorname{supp}\mu_{Y-e}}\mu_{Y-e}(W)\Bigl[(1-p(e,W))\mathbf 1[U=W]+p(e,W)\mathbf 1[U=W+\langle e\rangle]\Bigr].$$
--
--   4. **The quantities of (3).** $u_e(L)=\mathbb E_{W\sim\mu_{Y-e}}[\dim(W\cap L)]$, $\Delta_e(W,L)=\dim((W+\langle e\rangle)\cap L)-\dim(W\cap L)$ (a signed integer), and
--   $$g_p(L)=-(i-k)\dim L+\sum_{e\in Y}u_e(L)+\sum_{e\in Y}\mathbb E_{W\sim\mu_{Y-e}}\bigl[p(e,W)\,\Delta_e(W,L)\bigr].$$
--
--   5. **The polytope $P(Y,\mu)$ and $\mathrm{LP}(Y)$.** $p\in P(Y,\mu)$ when
--      - $0\le p(e,W)\le1$ for all $e\in Y$, $W\in\operatorname{supp}\mu_{Y-e}$;
--      - $p(e,W)=0$ for all $e\in Y$, $W\in\operatorname{supp}\mu_{Y-e}$ with $e\notin\mathrm{OPT}(Y)$ or $v_e\in W$;
--      - $\mathbb E_{W\sim\mu_{Y-e}}[p(e,W)]=\dfrac{k}{i-1}$ for every $e\in\mathrm{OPT}(Y)$.
--
--      $p$ is a feasible solution of $\mathrm{LP}(Y)$ when moreover $g_p(L)\le0$ for every $L\le\langle Y\rangle$.
--
--   6. **Standing hypotheses of §3.** A family $(\mu_{X-e})_{e\in X}$ satisfies them when each $\mu_{X-e}$ is a probability distribution on the subspaces of $\langle X-e\rangle$ satisfying (1) at size $|X-e|=|X|-1$.
--
--   These are the objects in which Lemmas 1, 2, 4, 5 and the chain construction of §3 are stated.
--
--   **Formalization Note** A distribution is a `Finsupp` from subspaces to $\mathbb R$, and expectations are sums over its support. The family $(\mu_{Y-e})$ is a function of $e$, and $p$ is a function on all pairs $(e,W)$; only the values with $e\in Y$, $W\in\operatorname{supp}\mu_{Y-e}$ (the paper's LP variables) enter any constraint or the formulas (2), (3). The quotient $k/(i-1)$ and $k/m$ are real divisions; every statement has $i>k\ge1$, so no denominator vanishes.
-- source:
--   Kristóf Bérczi, Shaddin Dughmi, Vasilis Livanos, Jose Soto, Victor Verdugo, The Strong Secretary Conjecture is True for Linear Matroids, STOC 2027 submission #608 (October 2026), §2.1 (PDF pp. 7–9, printed pp. 5–7: (1), (2), u_e, ∆_e, (3)), §2.2 (PDF p. 9, printed p. 7: LP(Y)), §3 (PDF p. 13, printed p. 11: standing hypotheses and P = P(X, µ))

import Mathlib
import Definitions.Def_LinMatroidSecretary_Online_Setting

/-!
# Distributions on subspaces, the Dimension Invariant Inequality and the acceptance LP

Bérczi, Dughmi, Livanos, Soto, Verdugo, *The Strong Secretary Conjecture is True for Linear
Matroids*, STOC 2027 submission #608, §2.1–§2.2 (PDF pp. 7–9) and §3 (PDF p. 13).

The ambient space is `V = Fin d → F`. Subspaces are `Submodule F V`; `dim` is `Module.finrank`,
`W ∩ L` is `W ⊓ L`, `W + L` is `W ⊔ L`, `⟨e⟩` is `span F {v e}` and `⟨Y⟩` is
`span F (v '' Y)`.

A set `Y` of elements is a `Finset ι` of an index type `ι` carrying the value order (a
`LinearOrder`); a family `μ : ι → Dist` records, for every `e ∈ Y`, the distribution
`μ e = µ_{Y−e}`; acceptance probabilities are a function `p : ι → Submodule F V → ℝ`, of which
only the values `p e W` with `e ∈ Y`, `W ∈ supp(µ_{Y−e})` (the LP variables of the paper) are
constrained or used.
-/

namespace LinMatroidSecretary.Online

open Finset

noncomputable section

variable {F : Type*} [Field F] {d : ℕ}

/-- A finitely supported real function on the subspaces of `Fin d → F`; a distribution on
subspaces when it is nonnegative and sums to one (`IsDistOn`). -/
abbrev Dist (F : Type*) [Field F] (d : ℕ) := Submodule F (Fin d → F) →₀ ℝ

/-- `E_{W∼µ}[f W] = ∑_{W ∈ supp µ} µ(W) f(W)`. -/
def expect (μ : Dist F d) (f : Submodule F (Fin d → F) → ℝ) : ℝ :=
  μ.sum fun W a => a * f W

/-- `µ` is a probability distribution supported on the subspaces of `S`. -/
def IsDistOn (μ : Dist F d) (S : Submodule F (Fin d → F)) : Prop :=
  (∀ W, 0 ≤ μ W) ∧ (μ.sum fun _ a => a) = 1 ∧ ∀ W ∈ μ.support, W ≤ S

/-- `dim(W ∩ L)` as a real number. -/
def dimInter (W L : Submodule F (Fin d → F)) : ℝ := (Module.finrank F ↥(W ⊓ L) : ℝ)

/-- The Dimension Invariant Inequality (1) for one subspace `L`, for a distribution `µ` of a set
of size `m` and sample size `k`:
`E_{W∼µ}[dim(W ∩ L)] ≤ (1 − k/m) dim(L)`. -/
def DimIneqAt (μ : Dist F d) (m k : ℕ) (L : Submodule F (Fin d → F)) : Prop :=
  expect μ (fun W => dimInter W L) ≤ (1 - (k : ℝ) / (m : ℝ)) * (Module.finrank F ↥L : ℝ)

/-- The Dimension Invariant Inequality (1) (PDF p. 6/8): (1) for **every** subspace `L` of the
ambient space. -/
def DimInvariant (μ : Dist F d) (m k : ℕ) : Prop :=
  ∀ L : Submodule F (Fin d → F), DimIneqAt μ m k L

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The span `⟨Y⟩` of the vectors of `Y`. -/
def spanOf (v : ι → Fin d → F) (Y : Finset ι) : Submodule F (Fin d → F) :=
  Submodule.span F (v '' (Y : Set ι))

/-- (2) (PDF p. 8/6): the distribution `µ_Y` obtained by choosing `e ∈ Y` uniformly, sampling
`W ∼ µ_{Y−e}` (here `μ e`) and accepting `e` with probability `p e W`:
`µ_Y(U) = (1/i) ∑_{e∈Y} ∑_{W∈supp µ_{Y−e}} µ_{Y−e}(W) [(1 − p(e,W)) 1[U = W] + p(e,W) 1[U = W + ⟨e⟩]]`,
with `i = |Y|`. -/
def muY (v : ι → Fin d → F) (Y : Finset ι) (μ : ι → Dist F d)
    (p : ι → Submodule F (Fin d → F) → ℝ) : Dist F d :=
  ((Y.card : ℝ)⁻¹) • ∑ e ∈ Y, (μ e).sum fun W a =>
    a • ((1 - p e W) • Finsupp.single W (1 : ℝ) +
      p e W • Finsupp.single (W ⊔ Submodule.span F {v e}) (1 : ℝ))

/-- `u_e(L) = E_{W∼µ_{Y−e}}[dim(W ∩ L)]` (PDF p. 8/6), with `μe = µ_{Y−e}`. -/
def ue (μe : Dist F d) (L : Submodule F (Fin d → F)) : ℝ :=
  expect μe fun W => dimInter W L

/-- `∆_e(W, L) = dim((W + ⟨e⟩) ∩ L) − dim(W ∩ L)` (PDF p. 8/6), computed in `ℝ`. -/
def Delta (v : ι → Fin d → F) (e : ι) (W L : Submodule F (Fin d → F)) : ℝ :=
  dimInter (W ⊔ Submodule.span F {v e}) L - dimInter W L

/-- (3) (PDF p. 8/6): with `i = |Y|`,
`g_p(L) = −(i − k) dim(L) + ∑_{e∈Y} u_e(L) + ∑_{e∈Y} E_{W∼µ_{Y−e}}[p(e,W) ∆_e(W, L)]`. -/
def gp (v : ι → Fin d → F) (Y : Finset ι) (k : ℕ) (μ : ι → Dist F d)
    (p : ι → Submodule F (Fin d → F) → ℝ) (L : Submodule F (Fin d → F)) : ℝ :=
  -((Y.card : ℝ) - (k : ℝ)) * (Module.finrank F ↥L : ℝ) + ∑ e ∈ Y, ue (μ e) L +
    ∑ e ∈ Y, expect (μ e) fun W => p e W * Delta v e W L

/-- The polytope `P = P(Y, µ)` (PDF p. 13/11): the first three constraint families of `LP(Y)`
(PDF p. 9/7), with `i = |Y|`:
1. `0 ≤ p(e,W) ≤ 1` for `e ∈ Y`, `W ∈ supp µ_{Y−e}`;
2. `p(e,W) = 0` for `e ∈ Y`, `W ∈ supp µ_{Y−e}` with `e ∉ OPT(Y)` or `e ∈ W`;
3. `E_{W∼µ_{Y−e}}[p(e,W)] = k/(i − 1)` for every `e ∈ OPT(Y)`. -/
def InP (v : ι → Fin d → F) (Y : Finset ι) (k : ℕ) (μ : ι → Dist F d)
    (p : ι → Submodule F (Fin d → F) → ℝ) : Prop :=
  (∀ e ∈ Y, ∀ W ∈ (μ e).support, 0 ≤ p e W ∧ p e W ≤ 1) ∧
  (∀ e ∈ Y, ∀ W ∈ (μ e).support, (e ∉ OPT F v Y ∨ v e ∈ W) → p e W = 0) ∧
  (∀ e ∈ OPT F v Y, expect (μ e) (p e) = (k : ℝ) / ((Y.card : ℝ) - 1))

/-- `p` is a feasible solution of `LP(Y)` (PDF p. 9/7): `p ∈ P(Y, µ)` and the fourth family
`g_p(L) ≤ 0` for every `L ≤ ⟨Y⟩`. -/
def LPFeasible (v : ι → Fin d → F) (Y : Finset ι) (k : ℕ) (μ : ι → Dist F d)
    (p : ι → Submodule F (Fin d → F) → ℝ) : Prop :=
  InP v Y k μ p ∧ ∀ L : Submodule F (Fin d → F), L ≤ spanOf v Y → gp v Y k μ p L ≤ 0

/-- The standing hypotheses of §3 (PDF p. 13/11) and of Lemma 2: for every `e ∈ X`, `μ e = µ_{X−e}`
is a probability distribution on the subspaces of `⟨X − e⟩` satisfying the Dimension Invariant
Inequality (1) at size `|X − e| = |X| − 1`. -/
def StandingFamily (v : ι → Fin d → F) (X : Finset ι) (k : ℕ) (μ : ι → Dist F d) : Prop :=
  ∀ e ∈ X, IsDistOn (μ e) (spanOf v (X.erase e)) ∧ DimInvariant (μ e) (X.erase e).card k

end

end LinMatroidSecretary.Online


