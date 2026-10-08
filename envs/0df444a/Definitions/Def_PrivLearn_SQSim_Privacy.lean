-- Prove2me | Definitions.Def_PrivLearn_SQSim_Privacy
-- name    : PrivLearn_SQSim_Privacy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:38.424211+00:00
-- url     : https://prove2.me/theorems/8b0122a5-5cef-48c6-a477-c85c45222840
-- title:
--   Neighbouring databases, ε-differential privacy (Definition 2.1), Lap(s), SQ answers (Definition 5.4) and local randomizers (Definition 5.1)
-- statement:
--   A **database** of size $n$ over a domain $D$ is a vector $z=(z_1,\dots,z_n)\in D^n$. Two databases are **neighbors** if they differ in exactly one entry.
--
--   1. A randomized algorithm $A$, described by the law $A(z)$ of its output on each database $z$, is **$\varepsilon$-differentially private** (Definition 2.1) if for all neighbors $z,z'$ and every measurable set $S$ of outputs, $\Pr[A(z)\in S]\le e^{\varepsilon}\Pr[A(z')\in S]$.
--   2. The **Laplace distribution** $\mathrm{Lap}(s)$ has density $\frac1{2s}e^{-|x|/s}$ on $\mathbb R$.
--   3. Given a probability distribution $P$ on $D$, a query function $g:D\to\mathbb R$ and a tolerance $\tau$, a real number $v$ is a **valid answer of the SQ oracle** (Definition 5.4) if
--
--   $$\bigl|v-\mathbb E_{u\sim P}[g(u)]\bigr|\le\tau .$$
--
--   4. A map $R$ from $D$ to laws on an output space $W$ is an **$\varepsilon$-local randomizer** (Definition 5.1) if $\Pr[R(u)\in S]\le e^{\varepsilon}\Pr[R(u')\in S]$ for all inputs $u,u'$ and every measurable $S\subseteq W$: it is an $\varepsilon$-differentially private algorithm on databases of size one.
--
--   These are the privacy and query notions shared by the five missions of the series on this paper. This mission uses the SQ-answer condition; the pointwise local-randomizer condition it uses for discrete outputs is in the file of local algorithms.
--
--   **Formalization Note.** Databases are vectors `Fin n → D`, indexed from $0$. Algorithms are identified with the laws of their outputs. The SQ answer condition uses the Bochner integral, so every theorem that uses it keeps the query function measurable and bounded. `laplace s` is a probability measure only for $s>0$. This file has the same text, up to the namespace, in every mission of the series.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 8 (§2.1, Definition 2.1, Lap(λ)) and p. 19 (Definitions 5.1 and 5.4)

import Mathlib

namespace PrivLearn.SQSim

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

/-- Definition 5.4 (p. 19): `v` is a valid answer of the SQ oracle to the query `(g, τ)` on the
distribution `P`: `|v − E_{u∼P}[g(u)]| ≤ τ`. -/
def IsSQAnswer {Dom : Type*} [MeasurableSpace Dom] (P : Measure Dom) (g : Dom → ℝ) (τ v : ℝ) : Prop :=
  |v - ∫ u, g u ∂P| ≤ τ

/-- Definition 5.1 (p. 19): `R` is an ε-local randomizer: an ε-differentially private algorithm on
databases of size 1, i.e. `Pr[R(u) ∈ S] ≤ e^ε Pr[R(u′) ∈ S]` for all inputs `u, u′`. -/
def IsLocalRandomizer {Dom W : Type*} [MeasurableSpace W] (R : Dom → Measure W) (ε : ℝ) : Prop :=
  ∀ u u' : Dom, ∀ S : Set W, MeasurableSet S → R u S ≤ ENNReal.ofReal (Real.exp ε) * R u' S

end PrivLearn.SQSim


