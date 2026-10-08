-- Prove2me | Definitions.Def_KellyReversibility_Genetics_Sampling
-- name    : KellyReversibility_Genetics_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:50:22.799448+00:00
-- url     : https://prove2.me/theorems/6377507c-2d8c-4bff-85a0-91ef768795c4
-- title:
--   Descriptions of labelled sets, sampling without replacement, and the allele frequency of a random individual
-- statement:
--   Let a finite set of individuals $\iota$ carry allelic types $x:\iota\to\alpha$.
--
--   1. **Allele counts.** For $i\in\mathbb N$, $a_i(x)$ is the number of allelic types $a$ that occur in the set and are carried by exactly $i$ individuals.
--   2. **Description.** The set has the description $\mathbf M=(M_1,M_2,\dots)$ if $a_i(x)=M_i$ for every $i$, i.e. "there are $M_i$ alleles represented by $i$ individuals in the set" (p. 147).
--   3. **Sampling without replacement.** For a population of $M$ labelled individuals $\{1,\dots,M\}$ with types $x$, and $m\le M$, a random sample of size $m$ is a uniformly random $m$-element subset $S$ of the population: each of the $\binom{M}{m}$ subsets has probability $\binom{M}{m}^{-1}$. The probability that the sample has description $\mathbf m$ is
--   $$P_x(\mathbf m)=\binom{M}{m}^{-1}\,\#\{S\subseteq\{1,\dots,M\}: |S|=m,\ x|_S \text{ has description } \mathbf m\}.$$
--   4. **Frequency of the allele of a random individual.** For $i\in\mathbb N$, $F_x(i)$ is the probability that an individual chosen uniformly from the population carries an allelic type represented by exactly $i$ individuals of the population:
--   $$F_x(i)=\frac{1}{M}\,\#\{j: \#\{k: x_k=x_j\}=i\}.$$
--
--   These are the objects of Theorem 7.1 (sampling) and of the proof of Corollary 7.5 (allele frequency of a random individual).
--
--   **Formalization Note** Descriptions are partitions `p : Nat.Partition n`, with $M_i$ = `p.parts.count i`; `HasDescription x p` requires equality for every $i\in\mathbb N$ (for $i=0$ both sides are $0$). The sample's types are the restriction of $x$ to the subtype of $S$. Both probabilities are defined by counting labelled individuals, not by a formula on descriptions. For $M=0$ the division in $F_x$ is by $0$; the theorems that use $F_x$ assume $M\ge 1$.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 147 (description of a set of individuals; Theorem 7.1) and p. 154 (proof of Corollary 7.5)

import Mathlib

namespace KellyReversibility.Genetics

open Classical in
/-- Kelly (1979), §7.1, p. 147. For a set of individuals `ι` labelled by their allelic types
`x : ι → α`, `alleleCount x i` is the number of allelic types represented by exactly `i`
individuals of the set. -/
noncomputable def alleleCount {ι α : Type*} [Fintype ι] (x : ι → α) (i : ℕ) : ℕ :=
  ((Finset.univ.image x).filter
    (fun a => (Finset.univ.filter (fun j => x j = a)).card = i)).card

/-- Kelly (1979), §7.1, p. 147: "a set of `n` individuals has the description
`M = (M₁, M₂, …)` if there are `Mᵢ` alleles represented by `i` individuals in the set".
The description is encoded as a partition `p` of `n` with `Mᵢ = p.parts.count i`. -/
def HasDescription {ι α : Type*} [Fintype ι] {n : ℕ} (x : ι → α) (p : Nat.Partition n) :
    Prop :=
  ∀ i : ℕ, alleleCount x i = p.parts.count i

open Classical in
/-- Sampling without replacement (Kelly 1979, Theorem 7.1, p. 147). The population is the set
`Fin M` of `M` labelled individuals with allelic types `x : Fin M → α`. A random sample of size
`m` is a uniformly random `m`-element subset `S ⊆ Fin M` (each of the `C(M, m)` subsets equally
likely). `sampleDescProb x m q` is the probability that the sample, with the types of its
members, has the description `q`. -/
noncomputable def sampleDescProb {α : Type*} {M : ℕ} (x : Fin M → α) (m : ℕ)
    (q : Nat.Partition m) : ℝ :=
  ((((Finset.univ : Finset (Fin M)).powersetCard m).filter
      (fun S : Finset (Fin M) => HasDescription (fun j : ↥S => x j.1) q)).card : ℝ) / (M.choose m : ℝ)

open Classical in
/-- Kelly (1979), proof of Corollary 7.5, p. 154. For a population `Fin M` with allelic types
`x`, the probability that the allelic type of a uniformly chosen individual is represented by
exactly `i` individuals of the population. -/
noncomputable def individualFreqProb {α : Type*} {M : ℕ} (x : Fin M → α) (i : ℕ) : ℝ :=
  ((Finset.univ.filter
      (fun j => (Finset.univ.filter (fun k => x k = x j)).card = i)).card : ℝ) / (M : ℝ)

end KellyReversibility.Genetics


