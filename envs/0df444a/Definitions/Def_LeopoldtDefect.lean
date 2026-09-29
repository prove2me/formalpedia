-- Prove2me | Definitions.Def_LeopoldtDefect
-- name    : LeopoldtDefect
-- status  : Definition
-- author  : @kbuzzard
-- created : 2026-09-09T09:31:37.529916+00:00
-- url     : https://prove2.me/theorems/ac4a508a-516a-43a1-b832-b47b03fca779
-- title:
--   The Leopoldt defect $\mathcal{D}_L(\mathbb{K})$ of a number field at $p$
-- statement:
--   This file sets up the objects that the statement of Leopoldt's conjecture refers to, following Section 1.1 of the source.
--
--   Let $p$ be a prime and let $\mathbb{K}$ be a number field with ring of integers $\mathcal{O}(\mathbb{K})$ and unit group $E = \mathcal{O}(\mathbb{K})^\times$. Four objects are defined.
--
--   1. **The primes above $p$.** $P = \{\wp \subset \mathcal{O}(\mathbb{K}) : (p) \subset \wp\}$, the set of non-zero prime ideals of $\mathcal{O}(\mathbb{K})$ containing $p$. This set is finite, and the finiteness is recorded so that it can be used as an instance.
--
--   2. **The semilocal units.** For $\wp \in P$ let $\mathbb{K}_\wp$ be the completion of $\mathbb{K}$ at $\wp$ and $\mathcal{O}_\wp \subset \mathbb{K}_\wp$ its valuation ring. The group of semilocal units at $p$ is the product of the local unit groups,
--   $$U \;=\; \prod_{\wp \in P} \mathcal{O}_\wp^{\times},$$
--   a commutative topological group. The diagonal embedding $\iota : E \to U$ sends a global unit to the tuple of its images under the completion maps.
--
--   3. **The $p$-adic closure of the global units.** With $U^{p^n} = \{u^{p^n} : u \in U\}$, and writing the product of two subgroups of the abelian group $U$ for their join,
--   $$\bar{E} \;=\; \bigcap_{n > 0} \iota(E) \cdot U^{p^n} \;\subseteq\; U .$$
--
--   4. **The Leopoldt defect.** Writing $\mathbb{Z}\text{-rk}(E) = r_1 + r_2 - 1$ for Dirichlet's unit rank and $\mathbb{Z}_p\text{-rk}(\bar{E})$ for the free $\mathbb{Z}_p$-rank of $\bar{E}$,
--   $$\mathcal{D}_L(\mathbb{K}) \;=\; \mathbb{Z}\text{-rk}(E) \;-\; \mathbb{Z}_p\text{-rk}(\bar{E}).$$
--   Leopoldt's conjecture for $\mathbb{K}$ at $p$ is the assertion $\mathcal{D}_L(\mathbb{K}) = 0$; the defect is positive exactly when units independent over $\mathbb{Z}$ become dependent $p$-adically after the diagonal embedding. For CM fields a positive defect is equivalent to the vanishing of the $p$-adic regulator.
--
--   These are the objects every statement in this mission is phrased in, so they fix the meaning of the goal theorem. They are also reusable for any $p$-adic question about global units: the semilocal unit group and the diagonal embedding are the standard setting for $p$-adic regulators, $p$-ramified class field theory, and the $\mathbb{Z}_p$-rank computations of Iwasawa theory.
--
--   **Formalization Note** Four conventions are fixed here. First, $\bar{E}$ is defined by the displayed intersection rather than as a topological closure; the source gives both descriptions, and the intersection avoids committing to a topology on $\prod_\wp \mathbb{K}_\wp$. The two can differ by a finite subgroup, which does not change the $\mathbb{Z}_p$-rank.
--
--   Second, the free $\mathbb{Z}_p$-rank of a subgroup $H$ is defined as the largest $n$ below a cut-off admitting a *continuous* injective homomorphism $\mathbb{Z}_p^n \to H$, the cut-off being taken to be $[\mathbb{K}:\mathbb{Q}]$ when the defect is formed. Continuity is essential, since as abstract groups $\mathbb{Z}_p^n$ embeds into $\mathbb{Z}_p$ for every $n$; and because $\mathbb{Z}_p^n$ is compact and the ambient group Hausdorff, such an injection is automatically a closed embedding. For a closed subgroup of $U$, isomorphic to a finite group times $\mathbb{Z}_p^d$, such injections exist exactly for $n \le d$. The cut-off is present only so that the supremum ranges over a visibly bounded set of naturals and never returns the junk value of a supremum of an unbounded set; since the $\mathbb{Z}_p$-rank of $U$ itself is $[\mathbb{K}:\mathbb{Q}]$, it never binds.
--
--   Third, the subtraction defining the defect is truncated subtraction of natural numbers; since the $\mathbb{Z}_p$-rank never exceeds the $\mathbb{Z}$-rank this is never triggered, and vanishing of the defect is equivalent to equality of the two ranks.
--
--   Fourth, the auxiliary constructions leading up to the defect are stated for an arbitrary natural number $p$, primality being assumed only where it is used, so they also carry (unused) meaning at $p = 0$ and $p = 1$.
-- source:
--   Preda Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544, Section 1.1 'Notations and fundamental facts' (pp. 2-3): the definitions of E(K), the set P of primes above p, K_p = prod_{wp in P} K_wp = K (x)_Q Q_p, the diagonal embedding iota, the semilocal units U, the p-adic closure Ebar = closure(iota(E)) = intersection_{n>0} iota(E).U^{p^n}, and the Leopoldt defect D_L(K) = Z-rk(E) - Z_p-rk(Ebar).

import Mathlib

/-!
# The Leopoldt defect of a number field at a prime `p`

This file formalises the objects of Section 1.1 ("Notations and fundamental facts") of

  Preda Mihăilescu, *On CM `ℤ_p`-extensions and the Leopoldt conjecture for CM fields*,
  arXiv:1105.4544,

which are what the statement of its Theorem 1 refers to.

Following the paper: `E = E(K) = 𝓞(K)ˣ` denotes the units of a number field `K`, and
`P = {℘ ⊂ 𝓞(K) : (p) ⊂ ℘}` the set of primes above `p`.  The paper puts
`K_p = ∏_{℘ ∈ P} K_℘ = K ⊗_ℚ ℚ_p`, lets `ι : K → K_p` be the diagonal embedding and
`U ⊂ K_p^×` be "the group of units, thus the product of local units at the same
completions".  It then defines the `p`-adic closure of the global units as

  `Ē = closure(ι(E)) = ⋂_{n > 0} ι(E) · U^{p^n}`

and the *Leopoldt defect* as

  `𝒟_L(K) = ℤ-rk(E) - ℤ_p-rk(Ē)`.

Leopoldt's conjecture for `K` at `p` is the assertion `𝒟_L(K) = 0`.
-/

namespace Leopoldt

open NumberField IsDedekindDomain

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]

/-- The set `P = {℘ ⊂ 𝓞(K) : (p) ⊂ ℘}` of primes of `𝓞 K` above `p`. -/
abbrev PrimesOver := {v : HeightOneSpectrum (𝓞 K) // (p : 𝓞 K) ∈ v.asIdeal}

instance : Finite (PrimesOver p K) := by
  have hpne : (p : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out (p := p.Prime)).ne_zero
  have hp0 : Ideal.span {(p : 𝓞 K)} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hpne
  apply Set.Finite.to_subtype
  refine (Ideal.finite_factors (R := 𝓞 K) hp0).subset ?_
  intro v hv
  exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)

/-- `U`: the group of semilocal units at `p`, that is the product `∏_{℘ | p} 𝓞_℘^×` of the
local units at the primes above `p`. -/
abbrev SemilocalUnits := ∀ v : PrimesOver p K, (v.1.adicCompletionIntegers K)ˣ

/-- `ι : E(K) → U`, the diagonal embedding of the global units into the semilocal units. -/
noncomputable def diagonalUnits : (𝓞 K)ˣ →* SemilocalUnits p K :=
  MonoidHom.pi fun v => Units.map (algebraMap (𝓞 K) (v.1.adicCompletionIntegers K)).toMonoidHom

/-- `Ē = ⋂_{n > 0} ι(E) · U^{p^n}`, the `p`-adic closure of the image of the global units
inside the semilocal units, exactly as the intersection is written in the source. -/
noncomputable def unitClosure : Subgroup (SemilocalUnits p K) :=
  ⨅ n : ℕ, ((diagonalUnits p K).range ⊔ (powMonoidHom (p ^ (n + 1))).range)

/-- The free `ℤ_p`-rank of a subgroup `H` of a commutative topological group, computed as the
largest `n ≤ bound` for which `ℤ_p^n` admits a continuous injective homomorphism into `H`.

For a closed subgroup of the semilocal units this is the usual free `ℤ_p`-rank: such a subgroup
is isomorphic to `Δ × ℤ_p^d` with `Δ` finite, and continuous injections from `ℤ_p^n` exist
exactly for `n ≤ d`.  Continuity is essential — as abstract groups `ℤ_p^n` embeds into `ℤ_p`
for every `n`; and since `ℤ_p^n` is compact and the target Hausdorff, a continuous injection is
automatically a closed embedding.

The `bound` is carried only so that the supremum is visibly taken over a bounded set and never
falls back on the junk value of `sSup` on an unbounded set of naturals.  Any `bound` at least as
large as the true rank yields the true rank. -/
noncomputable def zpRankBelow {G : Type*} [CommGroup G] [TopologicalSpace G]
    (bound : ℕ) (H : Subgroup G) : ℕ :=
  sSup {n : ℕ | n ≤ bound ∧ ∃ f : Multiplicative (Fin n → ℤ_[p]) →* G,
    Function.Injective f ∧ Continuous f ∧ ∀ x, f x ∈ H}

/-- The **Leopoldt defect** `𝒟_L(K) = ℤ-rk(E) - ℤ_p-rk(Ē)` of `K` at `p`.

`ℤ-rk(E) = r₁ + r₂ - 1` is Dirichlet's unit rank, which Mathlib provides as
`NumberField.Units.rank`.  The `ℤ_p`-rank of `Ē` is bounded by that of the whole semilocal unit
group `U`, which is `[K : ℚ]`, so taking `[K : ℚ]` as the bound never constrains it. -/
noncomputable def defect : ℕ :=
  Units.rank K - zpRankBelow p (Module.finrank ℚ K) (unitClosure p K)

/-- **Leopoldt's conjecture** for `K` at `p`: the Leopoldt defect vanishes. -/
def LeopoldtConjecture : Prop := defect p K = 0

end Leopoldt


