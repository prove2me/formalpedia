-- Prove2me | Definitions.Def_RiskUncSets_Distortion_Setting
-- name    : RiskUncSets_Distortion_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T12:07:36.809719+00:00
-- url     : https://prove2.me/theorems/56567337-e97a-46fc-874b-70e825f91b24
-- title:
--   Defs. 2.1–2.2, 4.1–4.7, (1), (3), CVaR, (4), (5) — risk measures on a finite Ω, generating families, CVaR, Choquet integral, distortion risk measures, restricted simplex, q-permutohull
-- statement:
--   This file fixes the vocabulary of Bertsimas and Brown's link between risk measures and uncertainty sets. Throughout, the sample space is finite, $\Omega = \{\omega_1, \dots, \omega_N\}$, and a random variable (a *position*, read as a reward) is a vector $X \in \mathbb R^N$, $X_i = X(\omega_i)$. Inequalities between random variables are statewise. We write $\Delta^N = \{p \in \mathbb R^N_+ : e'p = 1\}$ for the probability simplex and $\mathbb E_q[X] = \sum_i q_i X_i$ for the expectation under $q \in \Delta^N$.
--
--   1. **Risk measure** (Definition 2.1). A function $\mu : \mathbb R^N \to \mathbb R$ such that $X \ge Y$ implies $\mu(X) \le \mu(Y)$ (monotonicity) and $\mu(X + c) = \mu(X) - c$ for every constant $c \in \mathbb R$ (translation invariance).
--   2. **Coherent risk measure** (Definition 2.2). A risk measure that is convex, $\mu(\lambda X + (1-\lambda) Y) \le \lambda \mu(X) + (1-\lambda)\mu(Y)$ for $\lambda \in [0,1]$, and positively homogeneous, $\mu(\lambda X) = \lambda \mu(X)$ for $\lambda \ge 0$.
--   3. **Generating family** (display (1)). A set $\mathcal Q \subseteq \Delta^N$ *generates* $\mu$ if for every $X$
--   $$\mu(X) = \sup_{q \in \mathcal Q} \mathbb E_q[-X],$$
--   the supremum being a least upper bound in $\mathbb R$.
--   4. **Conditional value-at-risk** (p. 1485). Under a probability vector $p$ and for $\alpha \in (0,1]$,
--   $$\mathrm{CVaR}_\alpha(X) = \inf_{\nu \in \mathbb R} \Big\{ \nu + \tfrac1\alpha \mathbb E_p[(-\nu - X)^+] \Big\}.$$
--   For $\alpha \in (0,1]$ the function of $\nu$ is bounded below by $\mathbb E_p[-X]$, so the infimum is a genuine real number.
--   5. **The weights $q^\alpha$** (proof of Theorem 4.2, p. 1489). Under the uniform distribution, $q^\alpha$ puts weight $1/(N\alpha)$ on the $\lfloor N\alpha \rfloor$ smallest order statistics and the remaining mass $(N\alpha - \lfloor N\alpha\rfloor)/(N\alpha)$ on the next one.
--   6. **Comonotone pairs and comonotonic measures** (Definition 4.1). $X, Y$ are comonotone if $(X(\omega) - X(\omega'))(Y(\omega) - Y(\omega')) \ge 0$ for all $\omega, \omega'$; $\mu$ is comonotonic if $\mu(X + Y) = \mu(X) + \mu(Y)$ for all comonotone $X, Y$.
--   7. **Set functions** (Definition 4.2). A set function $g : 2^\Omega \to \mathbb R$ is monotone if $A \subseteq B$ implies $g(A) \le g(B)$; normalized if $g(\emptyset) = 0$ and $g(\Omega) = 1$; submodular if $g(A \cup B) + g(A \cap B) \le g(A) + g(B)$.
--   8. **Choquet integral** (Definition 4.3, display (3)).
--   $$\int X\,dg = \int_{-\infty}^0 \big(g(X > x) - 1\big)\,dx + \int_0^\infty g(X > x)\,dx.$$
--   9. **Law invariance** (Definition 4.4). $X$ and $Y$ have the same distribution under $p$ if $\sum_{i : X_i \le t} p_i = \sum_{i : Y_i \le t} p_i$ for every $t \in \mathbb R$; $\mu$ is law invariant under $p$ if it takes equal values on equally distributed random variables.
--   10. **Distortion risk measure** (Definition 4.5). A coherent risk measure that is comonotonic and law invariant.
--   11. **Uniform distribution** (Assumption 4.1). $\mathbb P\{\omega_i\} = 1/N$.
--   12. **Restricted simplex** (Definition 4.6). $\hat\Delta^N = \{q \in \Delta^N : q_1 \ge \cdots \ge q_N\}$.
--   13. **The measure (4).** For $q \in \mathbb R^N$, $\mu_q(X) = -\sum_{i=1}^N q_i x_{(i)}$, where $x_{(1)} \le \cdots \le x_{(N)}$ are the increasing order statistics of $X$.
--   14. **The generators $\hat q^j$ of (5).** $\hat q^j$ has entries $1/j$ in its first $j$ coordinates and $0$ elsewhere ($j = 1, \dots, N$); it corresponds to $\mathrm{CVaR}_{j/N}$.
--   15. **The $q$-permutohull** (Definition 4.7). For data $\mathcal A = \{a_1, \dots, a_N\} \subseteq \mathbb R^n$,
--   $$\Pi_q(\mathcal A) = \operatorname{conv}\Big(\Big\{\sum_{i=1}^N q_{\sigma(i)} a_i : \sigma \in S_N\Big\}\Big).$$
--
--   These objects are the vocabulary of every statement of the mission: the representation of coherent measures (Theorem 2.1), the induced uncertainty sets (Theorem 3.1), the characterization of distortion measures (Theorems 4.1, 4.2, Lemma 4.1) and the permutohull form of their risk constraints (Theorem 4.3).
--
--   **Formalization Note** $\Omega$ is `Fin N` and indices are 0-based: the paper's $q_1, \dots, q_N$ are `q 0, …, q (N-1)`, $q_1 \ge \dots \ge q_N$ is `Antitone q`, and `qhat j` for `j : Fin N` is the paper's $\hat q^{j+1}$. Order statistics are `X ∘ Tuple.sort X` (Mathlib's increasing sort). A probability measure on $\Omega$ is identified with its probability vector, and $\mathcal Q \subseteq \Delta^N$ is `stdSimplex ℝ (Fin N)`. The supremum (1) is `IsLUB`, which forces $\mathcal Q \neq \emptyset$. CVaR is a real infimum `⨅ v : ℝ`; it is used only for $\alpha \in (0,1]$, where the objective is bounded below. Set functions are real-valued on all subsets ($\mathcal F = 2^\Omega$); the codomain $[0,1]$ is stated separately where the paper uses it. The Choquet integral is written literally as two Lebesgue integrals over $(-\infty, 0]$ and $(0, \infty)$; on a finite $\Omega$ both integrands are bounded step functions with bounded support. "Same distribution" is equality of distribution functions under $p$.
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), pp. 1484–1490: Notation (p. 1484), Definitions 2.1 (p. 1484), 2.2 and CVaR (p. 1485), (1) (p. 1485), Assumption 3.1 (p. 1486), Definitions 4.1–4.3, (3) (p. 1487), 4.4, 4.5, Assumption 4.1 (p. 1488), Definition 4.6, (4), (5), q^α (p. 1489), Definition 4.7 (p. 1490)

import Mathlib

namespace RiskUncSets.Distortion

open MeasureTheory

/-- Definition 2.1 (p. 1484): `μ` is a *risk measure* on the random variables `X : Fin N → ℝ` of the
finite sample space `Ω = {ω₁, …, ω_N}` (`X` is a reward). Monotonicity: statewise `X ≥ Y` implies
`μ X ≤ μ Y`; translation invariance: `μ (X + c) = μ X - c`. -/
def IsRiskMeasure {N : ℕ} (μ : (Fin N → ℝ) → ℝ) : Prop :=
  (∀ X Y : Fin N → ℝ, (∀ i, Y i ≤ X i) → μ X ≤ μ Y) ∧
    ∀ (X : Fin N → ℝ) (c : ℝ), μ (fun i => X i + c) = μ X - c

/-- Definition 2.2 (p. 1485): a *coherent risk measure* is a risk measure that is convex and
positively homogeneous. -/
def IsCoherent {N : ℕ} (μ : (Fin N → ℝ) → ℝ) : Prop :=
  IsRiskMeasure μ ∧
    (∀ (X Y : Fin N → ℝ) (t : ℝ), 0 ≤ t → t ≤ 1 →
      μ (t • X + (1 - t) • Y) ≤ t * μ X + (1 - t) * μ Y) ∧
    ∀ (X : Fin N → ℝ) (t : ℝ), 0 ≤ t → μ (t • X) = t * μ X

/-- Display (1) of Theorem 2.1 (p. 1485): the family `Q` of probability vectors *generates* `μ`, i.e.
`Q ⊆ Δᴺ` and `μ(X) = sup_{q ∈ Q} E_q[-X]` for every `X`, the supremum being a least upper bound
(which forces `Q` to be nonempty). -/
def Generates {N : ℕ} (Q : Set (Fin N → ℝ)) (μ : (Fin N → ℝ) → ℝ) : Prop :=
  Q ⊆ stdSimplex ℝ (Fin N) ∧
    ∀ X : Fin N → ℝ, IsLUB ((fun q : Fin N → ℝ => ∑ i, q i * (-X i)) '' Q) (μ X)

/-- Conditional value-at-risk (p. 1485) under the probability vector `p`:
`CVaR_α(X) = inf_{v ∈ ℝ} { v + (1/α) E_p[(-v - X)⁺] }`, used only for `α ∈ (0, 1]`, where the
function of `v` is bounded below by `E_p[-X]`. -/
noncomputable def cvar {N : ℕ} (p : Fin N → ℝ) (α : ℝ) (X : Fin N → ℝ) : ℝ :=
  ⨅ v : ℝ, (v + (1 / α) * ∑ i, p i * max (-v - X i) 0)

/-- The weight vector `q^α` of the proof of Theorem 4.2 (p. 1489), 0-based: weight `1/(Nα)` on the
`⌊Nα⌋` smallest order statistics (indices `0, …, ⌊Nα⌋ - 1`) and the remaining mass
`(Nα - ⌊Nα⌋)/(Nα)` on the next one (index `⌊Nα⌋`). -/
noncomputable def cvarWeight (N : ℕ) (α : ℝ) : Fin N → ℝ := fun i =>
  if (i : ℕ) + 1 ≤ ⌊(N : ℝ) * α⌋₊ then 1 / ((N : ℝ) * α)
  else if (i : ℕ) = ⌊(N : ℝ) * α⌋₊ then
    ((N : ℝ) * α - (⌊(N : ℝ) * α⌋₊ : ℝ)) / ((N : ℝ) * α)
  else 0

/-- Definition 4.1 (p. 1487): `X` and `Y` are *comonotone*. -/
def Comonotone {N : ℕ} (X Y : Fin N → ℝ) : Prop :=
  ∀ ω ω' : Fin N, 0 ≤ (X ω - X ω') * (Y ω - Y ω')

/-- Definition 4.1 (p. 1487): `μ` is *comonotonic*: additive on comonotone pairs. -/
def IsComonotonic {N : ℕ} (μ : (Fin N → ℝ) → ℝ) : Prop :=
  ∀ X Y : Fin N → ℝ, Comonotone X Y → μ (X + Y) = μ X + μ Y

/-- Definition 4.2 (p. 1487): a set function `g : 2^Ω → ℝ` is *monotone*. -/
def IsMonotoneSF {N : ℕ} (g : Set (Fin N) → ℝ) : Prop :=
  ∀ A B : Set (Fin N), A ⊆ B → g A ≤ g B

/-- Definition 4.2 (p. 1487): `g` is *normalized*: `g ∅ = 0`, `g Ω = 1`. -/
def IsNormalizedSF {N : ℕ} (g : Set (Fin N) → ℝ) : Prop :=
  g ∅ = 0 ∧ g Set.univ = 1

/-- Definition 4.2 (p. 1487): `g` is *submodular*. -/
def IsSubmodularSF {N : ℕ} (g : Set (Fin N) → ℝ) : Prop :=
  ∀ A B : Set (Fin N), g (A ∪ B) + g (A ∩ B) ≤ g A + g B

/-- Definition 4.3, display (3) (p. 1487): the Choquet integral
`∫ X dg = ∫_{-∞}^0 (g(X > x) - 1) dx + ∫_0^∞ g(X > x) dx`. -/
noncomputable def choquet {N : ℕ} (g : Set (Fin N) → ℝ) (X : Fin N → ℝ) : ℝ :=
  (∫ x in Set.Iic (0 : ℝ), (g {ω | x < X ω} - 1)) + ∫ x in Set.Ioi (0 : ℝ), g {ω | x < X ω}

/-- `X` and `Y` have the same distribution under the probability vector `p`: equal distribution
functions `t ↦ P(X ≤ t)` and `t ↦ P(Y ≤ t)`. -/
def SameDistribution {N : ℕ} (p : Fin N → ℝ) (X Y : Fin N → ℝ) : Prop :=
  ∀ t : ℝ, ∑ i ∈ Finset.univ.filter (fun i => X i ≤ t), p i =
    ∑ i ∈ Finset.univ.filter (fun i => Y i ≤ t), p i

/-- Definition 4.4 (p. 1488): `μ` is *law invariant* under `p`. -/
def IsLawInvariant {N : ℕ} (p : Fin N → ℝ) (μ : (Fin N → ℝ) → ℝ) : Prop :=
  ∀ X Y : Fin N → ℝ, SameDistribution p X Y → μ X = μ Y

/-- Definition 4.5 (p. 1488): a *distortion risk measure* (under `p`) is coherent, comonotonic and
law invariant. -/
def IsDistortion {N : ℕ} (p : Fin N → ℝ) (μ : (Fin N → ℝ) → ℝ) : Prop :=
  IsCoherent μ ∧ IsComonotonic μ ∧ IsLawInvariant p μ

/-- Assumption 4.1 (p. 1488): the uniform distribution `ℙ{ωᵢ} = 1/N`. -/
noncomputable def uniform (N : ℕ) : Fin N → ℝ := fun _ => 1 / (N : ℝ)

/-- Definition 4.6 (p. 1489): the restricted simplex `Δ̂ᴺ = {q ∈ Δᴺ : q₁ ≥ ⋯ ≥ q_N}`. -/
def restrictedSimplex (N : ℕ) : Set (Fin N → ℝ) :=
  {q | q ∈ stdSimplex ℝ (Fin N) ∧ Antitone q}

/-- The risk measure (4) of Theorem 4.2 (p. 1489): `μ_q(X) = -∑ᵢ qᵢ x₍ᵢ₎`, where
`x₍₁₎ ≤ ⋯ ≤ x₍N₎` are the increasing order statistics `X ∘ Tuple.sort X`. -/
noncomputable def muQ {N : ℕ} (q X : Fin N → ℝ) : ℝ :=
  -∑ i, q i * X (Tuple.sort X i)

/-- The generator `q̂^{j+1}` of (5) (p. 1489), 0-based `j`: `1/(j+1)` on the first `j+1` coordinates,
`0` elsewhere; it corresponds to `CVaR_{(j+1)/N}`. -/
noncomputable def qhat {N : ℕ} (j : Fin N) : Fin N → ℝ := fun i =>
  if (i : ℕ) ≤ (j : ℕ) then 1 / ((j : ℕ) + 1 : ℝ) else 0

/-- Definition 4.7 (p. 1490): the `q`-permutohull `Π_q(𝒜) = conv{∑ᵢ q_{σ(i)} aᵢ : σ ∈ S_N}` of the
data `𝒜 = {a₁, …, a_N} ⊆ ℝⁿ`. -/
def permutohull {N : ℕ} (q : Fin N → ℝ) {n : ℕ} (a : Fin N → Fin n → ℝ) : Set (Fin n → ℝ) :=
  convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin N) => ∑ i, q (σ i) • a i)

end RiskUncSets.Distortion


