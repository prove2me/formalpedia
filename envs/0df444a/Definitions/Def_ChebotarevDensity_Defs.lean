-- Prove2me | Definitions.Def_ChebotarevDensity_Defs
-- name    : ChebotarevDensity_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-27T16:57:42.296812+00:00
-- url     : https://prove2.me/theorems/2c254387-3aa5-4a85-a59e-bcf179fadb7c
-- title:
--   Chebotarëv density theorem: densities, Frobenius substitutions, cycle patterns, decomposition types
-- statement:
--   Shared definitions for the statements of Chebotarëv's, Frobenius's and Dirichlet's density theorems over $\mathbb Q$, following Stevenhagen–Lenstra (1996).
--
--   1. **Analytic density.** A set $S$ of natural numbers has analytic (Dirichlet) density $\delta$ if
--   $$\lim_{s\to1^+}\frac{\sum_{p\in S,\ p\text{ prime}}p^{-s}}{\log\frac{1}{s-1}}=\delta .$$
--   2. **Natural density.** $S$ has natural density $\delta$ among the primes if $\#\{p\le x: p\in S\text{ prime}\}/\#\{p\le x: p\text{ prime}\}\to\delta$ as $x\to\infty$.
--   3. For $f\in\mathbb Z[X]$: its **splitting field** $K$ over $\mathbb Q$ (a number field) and **Galois group** $G=\mathrm{Gal}(K/\mathbb Q)$.
--   4. **Frobenius substitution.** $\sigma\in G$ is a Frobenius substitution of the prime $p$ if there is a prime ideal $\mathfrak Q\ni p$ of the ring of integers $\mathcal O_K$ with $\sigma(x)\equiv x^p\pmod{\mathfrak Q}$ for all $x\in\mathcal O_K$.
--   5. **Chebotarëv set.** For a conjugacy class $C$ of $G$: the set of primes $p$ with $p\nmid\Delta(f)$ having some Frobenius substitution in $C$.
--   6. **Cycle pattern** of $\sigma\in G$: the multiset of cycle lengths (fixed points included) of the permutation of the complex zeros of $f$ induced by $\sigma$.
--   7. **Decomposition type** of $f$ modulo a prime $p$: the multiset of degrees of the monic irreducible factors of $f \bmod p$ in $\mathbb F_p[X]$, with multiplicity; and the set of primes $p\nmid\Delta(f)$ with a given decomposition type.
--   8. **Frobenius cycle pattern** of $g\in\mathbb F_p[X]$: the cycle pattern of $x\mapsto x^p$ acting on the zeros of $g$ in its splitting field.
--
--   **Formalization Note** The discriminant is Mathlib's `Polynomial.discr`; the Frobenius condition uses Mathlib's `IsArithFrobAt`; cycle patterns use `Equiv.Perm.partition`. The file also registers the instance that the splitting field of a rational polynomial is a number field.
-- source:
--   P. Stevenhagen and H. W. Lenstra, Jr., "Chebotarëv and his density theorem", The Mathematical Intelligencer 18 (1996), no. 2, 26–37, https://doi.org/10.1007/BF03027290, pp. 30–34 (definitions of density, decomposition type, cycle pattern, Frobenius substitution)

import Mathlib

open Polynomial NumberField

namespace ChebotarevDensity

/-- The splitting field of a rational polynomial is a number field. -/
noncomputable instance splittingField_numberField (g : ℚ[X]) : NumberField g.SplittingField := {}

/-- Analytic (Dirichlet) density: a set `S` of natural numbers has density `δ` if
`(∑_{p ∈ S prime} p^{-s}) / log (1 / (s - 1)) → δ` as `s → 1⁺`. -/
def HasDirichletDensity (S : Set ℕ) (δ : ℝ) : Prop :=
  Filter.Tendsto
    (fun s : ℝ =>
      (∑' p : {p : ℕ // p.Prime ∧ p ∈ S}, ((p : ℕ) : ℝ) ^ (-s)) / Real.log (1 / (s - 1)))
    (nhdsWithin 1 (Set.Ioi 1)) (nhds δ)

open scoped Classical in
/-- Natural density among the primes: `#{p ≤ x : p ∈ S prime} / #{p ≤ x : p prime} → δ`. -/
def HasNaturalDensity (S : Set ℕ) (δ : ℝ) : Prop :=
  Filter.Tendsto
    (fun x : ℕ =>
      ((Finset.Iic x).filter (fun p => p.Prime ∧ p ∈ S)).card /
        (((Finset.Iic x).filter Nat.Prime).card : ℝ))
    Filter.atTop (nhds δ)

/-- An integer polynomial viewed as a rational polynomial. -/
noncomputable abbrev ratPoly (f : ℤ[X]) : ℚ[X] := f.map (Int.castRingHom ℚ)

/-- The splitting field `K = ℚ(α₁, …, αₙ)` of an integer polynomial `f`. -/
abbrev SplitField (f : ℤ[X]) : Type := (ratPoly f).SplittingField

/-- The Galois group `G = Gal(K/ℚ)` of an integer polynomial `f`. -/
abbrev GalGroup (f : ℤ[X]) : Type := (ratPoly f).Gal

/-- `σ ∈ G` is a Frobenius substitution of the prime `p`: there is a prime ideal `Q` of the
ring of integers of `K` containing `p` such that `σ x ≡ x ^ p (mod Q)` for every algebraic
integer `x` of `K`. -/
def IsFrobeniusAt (f : ℤ[X]) (p : ℕ) (σ : GalGroup f) : Prop :=
  ∃ Q : Ideal (𝓞 (SplitField f)), Q.IsPrime ∧ (p : 𝓞 (SplitField f)) ∈ Q ∧ IsArithFrobAt ℤ σ Q

/-- The set of primes `p ∤ Δ(f)` whose Frobenius substitution lies in the conjugacy class `C`. -/
def chebotarevSet (f : ℤ[X]) (C : ConjClasses (GalGroup f)) : Set ℕ :=
  {p | p.Prime ∧ ¬ (p : ℤ) ∣ f.discr ∧ ∃ σ ∈ C.carrier, IsFrobeniusAt f p σ}

open scoped Classical in
/-- The cycle pattern of `σ ∈ G`: the multiset of lengths of the cycles (including cycles of
length `1`) of the permutation induced by `σ` on the complex zeros of `f`. -/
noncomputable def cyclePattern (f : ℤ[X]) (σ : GalGroup f) : Multiset ℕ :=
  haveI : Fact ((ratPoly f).map (algebraMap ℚ ℂ)).Splits := ⟨IsAlgClosed.splits _⟩
  (Gal.galActionHom (ratPoly f) ℂ σ).partition.parts

/-- The decomposition type of `f` modulo the prime `p`: the multiset of degrees of the monic
irreducible factors of `f mod p` over `𝔽_p` (counted with multiplicity). -/
noncomputable def decompositionType (f : ℤ[X]) (p : ℕ) [Fact p.Prime] : Multiset ℕ :=
  (UniqueFactorizationMonoid.normalizedFactors (f.map (Int.castRingHom (ZMod p)))).map natDegree

/-- The set of primes `p ∤ Δ(f)` for which `f mod p` has decomposition type `t`. -/
def decompositionTypeSet (f : ℤ[X]) (t : Multiset ℕ) : Set ℕ :=
  {p | ∃ hp : p.Prime, ¬ (p : ℤ) ∣ f.discr ∧
    (haveI : Fact p.Prime := ⟨hp⟩; decompositionType f p) = t}

open scoped Classical in
/-- The cycle pattern of the Frobenius automorphism `x ↦ x ^ p`, acting on the zeros of a
polynomial `g` over `𝔽_p` in its splitting field. -/
noncomputable def frobeniusCyclePattern (p : ℕ) [Fact p.Prime] (g : (ZMod p)[X]) :
    Multiset ℕ :=
  haveI : Fact (g.map (algebraMap (ZMod p) g.SplittingField)).Splits :=
    ⟨SplittingField.splits g⟩
  (Gal.galActionHom g g.SplittingField
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) g.SplittingField)).partition.parts

end ChebotarevDensity


