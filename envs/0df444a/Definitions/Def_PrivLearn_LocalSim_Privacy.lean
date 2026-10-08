-- Prove2me | Definitions.Def_PrivLearn_LocalSim_Privacy
-- name    : PrivLearn_LocalSim_Privacy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:31.752607+00:00
-- url     : https://prove2.me/theorems/24830047-7771-4028-959e-8cec0ca3721b
-- title:
--   Neighbouring databases, ε-differential privacy, Lap(s), valid SQ answers and ε-local randomizers (Definitions 2.1, 5.1, 5.4)
-- statement:
--   A **database** of size $n$ over a domain $D$ is a vector $z=(z_1,\dots,z_n)\in D^n$, one entry per individual. Two databases $z,z'\in D^n$ are **neighbors** if they differ in exactly one entry: there is an index $i$ with $z_i\neq z'_i$ and $z_j=z'_j$ for every $j\neq i$.
--
--   1. A randomized algorithm $A$ on databases of size $n$, described by the law $A(z)$ of its output on each input $z$, is **$\varepsilon$-differentially private** (Definition 2.1) if for all neighbors $z,z'$ and every measurable set $S$ of outputs
--   $$\Pr[A(z)\in S]\le e^{\varepsilon}\,\Pr[A(z')\in S].$$
--   2. The **Laplace distribution** $\mathrm{Lap}(s)$ is the distribution on $\mathbb R$ with density $\frac{1}{2s}e^{-|x|/s}$.
--   3. Given a distribution $P$ on $D$, a query $g:D\to\mathbb R$ and a tolerance $\tau$, a number $v$ is a **valid answer of the SQ oracle** $SQ_P$ (Definition 5.4) if $|v-\mathbb E_{u\sim P}[g(u)]|\le\tau$.
--   4. A randomized map $R$ from $D$ to outputs $W$ is an **$\varepsilon$-local randomizer** (Definition 5.1) if $\Pr[R(u)\in S]\le e^{\varepsilon}\Pr[R(u')\in S]$ for all inputs $u,u'\in D$ and all measurable $S\subseteq W$: it is an $\varepsilon$-differentially private algorithm on databases of size one.
--
--   These are the privacy and query-access notions of the local model and the SQ model that the simulation of SQ algorithms by local algorithms connects.
--
--   **Formalization Note.** Databases are vectors `Fin n → D`, indexed from $0$. Algorithms and randomizers are identified with the laws of their outputs; their coins are inside those laws. Both privacy conditions are required on all measurable sets, which is equivalent to the pointwise form of Definition 5.1 when the output space is countable with the discrete σ-algebra and is the only meaningful form for real-valued (Laplace) outputs. `laplace s` is a probability measure only for $s>0$; every statement that uses it has $s>0$. The SQ oracle is adversarial: `IsSQAnswer` says which answers are valid, it does not pick one. Definition 5.4 restricts tolerances to $(0,1)$ and Boolean queries; the paper immediately allows real-valued $g:D\to[-b,b]$, which is the form used here. The paper's Laplace scale $\lambda$ is called `s` because `λ` is a Lean keyword.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 8 (§2.1, Definition 2.1, Lap(λ)), p. 19 (Definitions 5.1 and 5.4)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy

namespace PrivLearn.LocalSim

open MeasureTheory

/-- Definition 5.4 (p. 19): `v` is a valid answer of the SQ oracle to the query `(g, τ)` on the
distribution `P`: `|v − E_{u∼P}[g(u)]| ≤ τ`. -/
def IsSQAnswer {Dom : Type*} [MeasurableSpace Dom] (P : Measure Dom) (g : Dom → ℝ) (τ v : ℝ) : Prop :=
  |v - ∫ u, g u ∂P| ≤ τ

/-- Definition 5.1 (p. 19): `R` is an ε-local randomizer: an ε-differentially private algorithm on
databases of size 1, i.e. `Pr[R(u) ∈ S] ≤ e^ε Pr[R(u′) ∈ S]` for all inputs `u, u′`. -/
def IsLocalRandomizer {Dom W : Type*} [MeasurableSpace W] (R : Dom → Measure W) (ε : ℝ) : Prop :=
  ∀ u u' : Dom, ∀ S : Set W, MeasurableSet S → R u S ≤ ENNReal.ofReal (Real.exp ε) * R u' S

end PrivLearn.LocalSim


