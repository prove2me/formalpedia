-- Prove2me | Definitions.Def_PrivLearn_MaskedParity_Model
-- name    : PrivLearn_MaskedParity_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:16.035632+00:00
-- url     : https://prove2.me/theorems/f5788f46-7c74-434a-92e6-b669cb80ae6a
-- title:
--   MASKED-PARITY concepts c_{r,a}, the uniform inner product, err, labelled statistical queries and SQ learners
-- statement:
--   Fix $d\ge1$, a power of two. The **domain** is $D=\{0,1\}^d\times\{0,1\}^{\log d}\times\{0,1\}$, whose points are triples $u=(x,i,b)$; examples are drawn from the **uniform distribution** $\mathcal D$ on $D$, so $|D|=2^{d+\log d+1}$.
--
--   1. **MASKED-PARITY** (§5.3, p. 26) is the class of functions $c_{r,a}:D\to\{+1,-1\}$ indexed by $r\in\{0,1\}^d$ and $a\in\{0,1\}$:
--   $$c_{r,a}(x,i,b)=\begin{cases}(-1)^{r\odot x+a}&\text{if } b=0,\\ (-1)^{r_i}&\text{if } b=1,\end{cases}$$
--   where $r\odot x$ is the inner product of $r$ and $x$ modulo $2$ and $r_i$ is the $i$-th bit of $r$.
--   2. The **inner product** of $f,h:D\to\mathbb R$ (p. 29) is $\langle f,h\rangle=\frac1{|D|}\sum_{u\in D}f(u)h(u)=\mathbb E_{u\sim\mathcal D}[f(u)h(u)]$, and the **error** (p. 28) is $\mathrm{err}(f,h)=\Pr_{u\sim\mathcal D}[f(u)\neq h(u)]$.
--   3. A **statistical query** (p. 25, the oracle $SQ_{c,\mathcal X}$) is a function $g(u,y)$ of an example $u$ and a label $y$. Its true value on the target $c$ is $\mathbb E_{u\sim\mathcal D}[g(u,c(u))]$, and a real number $v$ is a **valid answer** of the SQ oracle to the query $(g,\tau)$ if
--   $$\bigl|v-\mathbb E_{u\sim\mathcal D}[g(u,c(u))]\bigr|\le\tau .$$
--   4. A **nonadaptive SQ learner with $t$ queries** (Definition 5.5, p. 19) fixes its queries $(g_k,\tau_k)_{k<t}$ before receiving any answer and outputs a hypothesis $h:D\to\mathbb R$ that is a function of the $t$ answers. A **two-round adaptive SQ learner** with $k_1$ and $k_2$ queries asks $k_1$ fixed queries, then $k_2$ queries (and tolerances) chosen as a function of the first answers, and outputs a hypothesis depending on all answers.
--
--   These are the objects of the separation between adaptive and nonadaptive statistical query learning in §5.3: MASKED-PARITY behaves like PARITY or its negation on the half $b=0$ and reveals one bit of $r$ on the half $b=1$.
--
--   **Formalization Note.** The index $i\in\{0,1\}^{\log d}$ is encoded as `Fin d`, a bijection when $d$ is a power of two, so the uniform distributions agree; the theorems assume $d=2^m$. Vectors in $\{0,1\}^d$ are `Fin d → ZMod 2` and $r\odot x$ is the dot product in `ZMod 2`; bits are 0-indexed. Concepts, hypotheses and queries are real-valued; labels $\pm1$ are real numbers. The paper's oracle allows non-Boolean query functions (p. 19: "The query function g does not have to be Boolean"), so queries are real-valued here and each theorem states the range it needs. Expectations are finite averages over the domain. Learners are deterministic; a randomized learner is a mixture over its coins and each statement then holds coin by coin.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 19 (Definitions 5.4, 5.5), p. 25 (the oracle SQ_{c,X}), p. 26 (MASKED-PARITY), pp. 28–29 (err and the inner product)

import Mathlib

namespace PrivLearn.MaskedParity

open Finset

/-- §5.3 (p. 26): the example domain `{0,1}^d × {0,1}^{log d} × {0,1}` of MASKED-PARITY, with the
index `i ∈ {0,1}^{log d}` encoded as `Fin d` (a bijection when `d` is a power of two). A point is
`u = (x, i, b)`. -/
abbrev Dom (d : ℕ) : Type := (Fin d → ZMod 2) × Fin d × ZMod 2

/-- §5.3 (p. 26): the MASKED-PARITY concept `c_{r,a}(x, i, b) = (−1)^{r⊙x+a}` if `b = 0` and
`(−1)^{r_i}` if `b = 1`, where `r ⊙ x` is the inner product modulo 2. Values `±1` in `ℝ`. -/
noncomputable def cMP {d : ℕ} (r : Fin d → ZMod 2) (a : ZMod 2) : Dom d → ℝ := fun u =>
  if u.2.2 = 0 then (-1 : ℝ) ^ ((r ⬝ᵥ u.1 + a).val) else (-1 : ℝ) ^ ((r u.2.1).val)

/-- p. 29: the inner product `⟨f, h⟩ = (1/|D|) ∑_{u ∈ D} f(u) h(u)` under the uniform distribution
on the domain `D`. -/
noncomputable def ip {d : ℕ} (f h : Dom d → ℝ) : ℝ :=
  (Fintype.card (Dom d) : ℝ)⁻¹ * ∑ u, f u * h u

/-- p. 28: `err(f, h) = Pr_{u ∼ 𝒟}[f(u) ≠ h(u)]` for the uniform distribution `𝒟` on the domain. -/
noncomputable def errMP {d : ℕ} (f h : Dom d → ℝ) : ℝ :=
  ((univ.filter fun u => f u ≠ h u).card : ℝ) / (Fintype.card (Dom d) : ℝ)

/-- p. 25: the true value `E_{u ∼ 𝒟}[g(u, c(u))]` of the labelled statistical query
`g : D × {+1, −1} → ℝ` on the target `c`, for the uniform distribution `𝒟` on the domain. A query
is a function of the example and of its label. -/
noncomputable def qval {d : ℕ} (c : Dom d → ℝ) (g : Dom d → ℝ → ℝ) : ℝ :=
  (Fintype.card (Dom d) : ℝ)⁻¹ * ∑ u, g u (c u)

/-- p. 25 (the oracle `SQ_{c,𝒳}`) and Definition 5.4 (p. 19): `v` is a valid answer of the
statistical query oracle to the query `(g, τ)` on the target `c` under the uniform distribution:
`|v − E_{u ∼ 𝒟}[g(u, c(u))]| ≤ τ`. -/
def IsLabeledSQAnswer {d : ℕ} (c : Dom d → ℝ) (g : Dom d → ℝ → ℝ) (τ v : ℝ) : Prop :=
  |v - qval c g| ≤ τ

/-- Definition 5.5 (p. 19): a nonadaptive SQ learner making `t` queries. It fixes its queries
`(g_k, τ_k)_{k < t}` before receiving any answer, and its output hypothesis is a function of the
`t` answers. (A randomized learner is a mixture of such learners over its coins.) -/
structure NonadaptiveSQLearner (X : Type*) (t : ℕ) where
  /-- the `k`-th query `g_k(u, y)` of the example `u` and the label `y` -/
  q : Fin t → X → ℝ → ℝ
  /-- the tolerance `τ_k` of the `k`-th query -/
  τ : Fin t → ℝ
  /-- the output hypothesis as a function of the answers -/
  out : (Fin t → ℝ) → X → ℝ

/-- Definition 5.5 (p. 19): an adaptive SQ learner with two rounds of communication, `k₁` queries
in the first round and `k₂` in the second. The second-round queries and tolerances may depend on
the first-round answers; the output hypothesis depends on all answers. -/
structure TwoRoundSQLearner (X : Type*) (k₁ k₂ : ℕ) where
  /-- first-round queries -/
  q₁ : Fin k₁ → X → ℝ → ℝ
  /-- first-round tolerances -/
  τ₁ : Fin k₁ → ℝ
  /-- second-round queries, as a function of the first-round answers -/
  q₂ : (Fin k₁ → ℝ) → Fin k₂ → X → ℝ → ℝ
  /-- second-round tolerances, as a function of the first-round answers -/
  τ₂ : (Fin k₁ → ℝ) → Fin k₂ → ℝ
  /-- the output hypothesis, as a function of all answers -/
  out : (Fin k₁ → ℝ) → (Fin k₂ → ℝ) → X → ℝ

end PrivLearn.MaskedParity


