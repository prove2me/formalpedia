-- Prove2me | Definitions.Def_PrivLearn_Generic_Privacy
-- name    : PrivLearn_Generic_Privacy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:16.91598+00:00
-- url     : https://prove2.me/theorems/1e433132-e54a-4b85-9a00-bb675b057c78
-- title:
--   Neighbouring databases, ε-differential privacy (Definition 2.1) and the Laplace distribution Lap(s)
-- statement:
--   A **database** of size $n$ over a domain $D$ is a vector $z=(z_1,\dots,z_n)\in D^n$, one entry per individual. Two databases $z,z'\in D^n$ are **neighbors** if they differ in exactly one entry: there is an index $i$ with $z_i\neq z'_i$ and $z_j=z'_j$ for every $j\neq i$ (Hamming distance $1$).
--
--   A randomized algorithm $A$ on databases of size $n$ is described by the law $A(z)$ of its output on each input $z$, a measure on the output space $O$. It is **$\varepsilon$-differentially private** (Definition 2.1) if for all neighbors $z,z'$ and every measurable set $S\subseteq O$ of outputs,
--
--   $$\Pr[A(z)\in S]\le e^{\varepsilon}\,\Pr[A(z')\in S].$$
--
--   The **Laplace distribution** $\mathrm{Lap}(s)$ is the distribution on $\mathbb R$ with density $\frac{1}{2s}e^{-|x|/s}$; it has mean $0$ and standard deviation $\sqrt2\,s$.
--
--   Differential privacy is the privacy notion of the whole paper: a learner is private when changing one individual's example changes the law of its output by at most a factor $e^{\varepsilon}$ on every event. The Laplace distribution is the noise of the paper's private algorithms (Theorem 2.3 and the learners built on it). These three objects are shared by the missions of the series on the generic private learner, the private parity learner and the local simulation of statistical queries.
--
--   **Formalization Note.** Databases are vectors `Fin n → D`, indexed from $0$. An algorithm is identified with the map $z\mapsto A(z)$ to the law of its output; its coins are inside that law. The condition is required on all measurable sets of outputs, which is equivalent to the pointwise form when the output space is countable with the discrete σ-algebra. The definition of differential privacy is a property of the family of laws and does not itself require each $A(z)$ to be a probability measure; every theorem that uses it assumes this (the family of zero measures would satisfy it trivially). `laplace s` is a probability measure only for $s>0$ (for $s\le0$ the formula gives the zero measure); every statement that uses it assumes $s>0$. The paper's scale $\lambda$ is called `s` because `λ` is a Lean keyword.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 8, §2.1, Definition 2.1 and the definition of Lap(λ)

import Mathlib

namespace PrivLearn.Generic

open MeasureTheory

/-- §2.1 (p. 8): databases `z, z′ ∈ Dⁿ` are neighbors if `z_i ≠ z′_i` for exactly one `i`. -/
def Neighbors {D : Type*} {n : ℕ} (z z' : Fin n → D) : Prop :=
  ∃ i : Fin n, z i ≠ z' i ∧ ∀ j : Fin n, j ≠ i → z j = z' j

/-- Definition 2.1 (p. 8): the randomized algorithm whose output on the database `z` has law
`A z` is ε-differentially private: `Pr[A(z) ∈ S] ≤ exp(ε) · Pr[A(z′) ∈ S]` for all neighbors and
all (measurable) sets of outputs. -/
def IsDP {D O : Type*} [MeasurableSpace O] {n : ℕ} (A : (Fin n → D) → Measure O) (ε : ℝ) : Prop :=
  ∀ z z' : Fin n → D, Neighbors z z' → ∀ S : Set O, MeasurableSet S →
    A z S ≤ ENNReal.ofReal (Real.exp ε) * A z' S

/-- Lap(s) (p. 8): the Laplace distribution with mean 0 and density `(1/2s) e^{−|x|/s}`. -/
noncomputable def laplace (s : ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (Real.exp (-|x| / s) / (2 * s))

end PrivLearn.Generic


