-- Prove2me | Definitions.Def_Garrido_Amenability
-- name    : Garrido_Amenability
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-23T19:06:18.971412+00:00
-- url     : https://prove2.me/theorems/66ed88ff-6df9-4c35-af46-fb50c2a87c1f
-- title:
--   Amenability, invariant means, and the invariant extension property
-- statement:
--   Eight notions: the first two for a function on the subsets of a set, the other six
--   for a discrete group $G$.
--
--   **IsFinitelyAdditiveMeasure $m$.** A function $m : \mathcal{P}(X) \to [0,\infty]$ on *every*
--   subset of a type $X$ with $m(\emptyset) = 0$ and $m(s \cup t) = m(s) + m(t)$ whenever
--   $s \cap t = \emptyset$. This is the “finitely additive measure” the source speaks of throughout;
--   the source never defines the term, and $m(\emptyset) = 0$ is the standard axiom of a measure. Once
--   some set has finite nonzero measure it follows from additivity anyway, so it matters only in
--   degenerate cases.
--
--   **IsInvariant $G$ $m$.** The source uses “$G$-invariant” without a defining sentence (p. 4: “a
--   finitely additive $G$-invariant measure on $\mathcal{P}(X)$”), and spells out “left-invariant” only
--   inside Definition 1.12, quoted under IsAmenable. For $G$ acting on $X$ and
--   $m : \mathcal{P}(X) \to [0,\infty]$: $m(gs) = m(s)$ for every $g \in G$ and every $s \subseteq X$.
--   This is the source's “$G$-invariant”; for $G$ acting on itself by left multiplication it is
--   “left-invariant”.
--
--   **IsAmenable $G$.** p. 4 (Definition 1.12): “Let $G$ be a discrete (resp. locally compact) group.
--   A *measure on $G$* is a finitely additive measure $\mu$ on $\mathcal{P}(G)$ (respectively,
--   $\mathcal{B}(G)$, the Borel sets of $G$), with $\mu(G) = 1$ and which is left-invariant; that is,
--   $\mu(gA) = \mu(A)$ for every $g \in G$ and $A \subseteq G$. We say that $G$ is *amenable* (or
--   *‘mittelbar’* in the original German) if it has such a measure.” The bundle takes the discrete
--   clause: there is a finitely additive measure $m$ on $\mathcal{P}(G)$ with $m(G) = 1$ and
--   left-invariant ($m(gs) = m(s)$ for all $g \in G$). Only **finite** additivity is required, and $m$
--   is defined on *every* subset. The codomain is the extended nonnegative reals rather than the
--   source's $[0,1]$; this is equivalent, since finite additivity with $m(G)=1$ forces $m(s) \le 1$
--   for every $s$, and it matches the conclusion of Mathlib's `IsFoelner.amenable`, which writes the
--   additivity out rather than naming it; that theorem supplies $m(\emptyset) = 0$ through
--   $m(G) = 1$.
--
--   **lshift.** p. 4 (Definition 1.13, item 3): “$\int {}_gf \,\mathrm{d}\mu = \int f \,\mathrm{d}\mu$
--   for every $g \in G$ and $f \in L^\infty(G)$ where ${}_gf(h) := f(g^{-1}h)$.” Left translation on
--   $\ell^\infty(G)$: $({}_g f)(h) = f(g^{-1}h)$. Well-defined because $h \mapsto g^{-1}h$ is a
--   bijection, so the range of $|f|$ is unchanged.
--
--   **IsInvariantMean $G$ $m$.** p. 4 (Definition 1.13): “Let $G$ be a locally compact group equipped
--   with the Haar measure $\mu$. Recall that $L^\infty(G)$ is the set of (equivalence classes of)
--   essentially bounded measurable functions $f : G \to \mathbb{R}$ where a function is essentially
--   bounded if it is bounded outside a set of zero measure. If $G$ is discrete, $\mu$ is just the
--   counting measure and $L^\infty(G)$ becomes $\ell^\infty(G)$. Construct an integral on
--   $(G, \mathcal{B}(G), \mu)$, so $\int f \,\mathrm{d}\mu$ defines a linear functional on
--   $L^\infty(G)$ such that 1. $\int f \,\mathrm{d}\mu \ge 0$ if $f(g) \ge 0$ for all $g \in G$; 2.
--   $\int \mathbf{1}_G \,\mathrm{d}\mu = 1$ where $\mathbf{1}_G$ denotes the indicator function on
--   $G$; 3. $\int {}_gf \,\mathrm{d}\mu = \int f \,\mathrm{d}\mu$ for every $g \in G$ and
--   $f \in L^\infty(G)$ where ${}_gf(h) := f(g^{-1}h)$. Such a linear functional is a
--   *left-invariant mean on $G$*.” For a linear functional $m$ on $\ell^\infty(G)$: $m$ is positive
--   (if $f \ge 0$ pointwise then $m(f) \ge 0$), normalised (if $f$ is constantly $1$ then
--   $m(f) = 1$), and left-invariant ($m({}_g f) = m(f)$). Means are taken on
--   $\ell^\infty(G)$ — the *bounded* functions — not on all of $G \to \mathbb{R}$; normalisation
--   is phrased via constantly-$1$ functions rather than a multiplicative unit.
--
--   **HasInvariantMean $G$.** There is a linear functional $m$ on $\ell^\infty(G)$ that is a
--   left-invariant mean in the sense just defined — the source's “there is a left-invariant mean
--   on $G$” (p. 7, Theorem 2.7, item 2).
--
--   **HasInvariantExtensionProperty $G$.** p. 7 (Theorem 2.6, Invariant Extension Theorem): “Recall
--   Carathéodory’s Extension Theorem: If $\mathcal{R}$ is a subring of the boolean algebra
--   $\mathcal{A}$ and $\mu$ is a measure on $\mathcal{R}$, then $\mu$ can be extended to a measure
--   $\bar\mu$ on $\mathcal{A}$. If $G$ is an amenable group of automorphisms of $\mathcal{A}$ and
--   $\mathcal{R}$, $\mu$ are $G$-invariant, then $\bar\mu$ can be chosen to be $G$-invariant.” The
--   property itself has no defining sentence: p. 7 (Theorem 2.7, item 4) says only “$G$ satisfies the
--   Invariant Extension Theorem.” This definition stands in for that phrase. For every $G$-set $X$
--   **in any universe at or above $G$'s**, every
--   $G$-invariant family $R$ of subsets of $X$, every $G$-invariant $\mu$ on $R$, and every finitely
--   additive measure $\nu$ on $\mathcal{P}(X)$ extending $\mu$, there is a finitely additive measure
--   $\bar\mu$ on $\mathcal{P}(X)$ that extends $\mu$ and is $G$-invariant.
--
--   So the property quantifies over actions of $G$ on sets $X$, with the source's boolean algebra
--   $\mathcal{A}$ always all subsets of $X$; $R$ is an arbitrary family, not assumed to be a ring; and
--   the unrestricted extension $\nu$ is supplied as a *hypothesis*. The formal Theorem 2.6 and the
--   “(1) implies (4)” direction of Theorem 2.7 therefore cover power-set algebras only. The source
--   recalls Carathéodory's finitely additive extension theorem rather than proving it, and this
--   definition does the same, so the content is that amenability upgrades an arbitrary extension to
--   an invariant one. That recalled step, for a power set (a finitely additive measure on a ring of
--   subsets of $X$ extends to a finitely additive measure on all subsets of $X$), is the published
--   theorem
--   [`FinitelyAdditive.exists_extension_of_isSetRing`](https://prove2.me/theorems/f5d887ac-da22-470b-b85e-ffb4d158b540).
--   The theorems at the generality printed are published on their own, over the
--   [boolean-algebra definitions](https://prove2.me/theorems/fb7629dc-807c-4475-8fd7-4eadd64b7a70):
--   Theorem 2.6 for every boolean algebra,
--   [`Garrido.satisfiesInvariantExtensionTheorem_of_isAmenable`](https://prove2.me/theorems/fd60b45e-ed19-46cb-8614-20884bd62a75);
--   Theorem 2.7 with clause 4 at that generality,
--   [`Garrido.isAmenable_tfae_satisfiesInvariantExtensionTheorem`](https://prove2.me/theorems/068e952b-c377-4dce-a540-c47dde437fcc);
--   the recalled extension for a subring of any boolean algebra,
--   [`Garrido.exists_extension_of_isBooleanSubring`](https://prove2.me/theorems/f9d14432-d2b7-4276-8506-0a8c037323f0);
--   and Theorem 2.6 for power sets with no extension supplied,
--   [`Garrido.exists_invariant_extension_of_isSetRing`](https://prove2.me/theorems/d22d7370-b961-4f77-ac1b-80b4cef68870).
--
--   $X$ ranges over the universe `max u v`, for $G$ in universe `u` and `v` arbitrary, deliberately.
--   The source's property is about every $G$-set, and every $G$-set can be lifted into such a
--   universe. Theorem 2.7's “(4) implies (1)” direction instantiates the property at a copy of $G$
--   itself, which a universe below $G$'s would not contain. A universe independent of $G$'s would
--   make that direction false: a sufficiently large simple group containing a free subgroup acts
--   trivially on every set of a smaller universe, and so satisfies the property there, without
--   being amenable.
--
--   Two degenerate cases are worth naming. The conclusion imposes no normalisation on $\bar\mu$ and
--   ties it to $\nu$ only through $R$, so instances with $R = \emptyset$, or with $\mu$ identically
--   zero on $R$, are satisfied by the zero function. The property is nonetheless not vacuous, and
--   is exactly what Theorem 2.7 needs: taken at $X = G$ with
--   $R = \{\emptyset, G\}$, $\mu(\emptyset) = 0$ and $\mu(G) = 1$ — hypotheses a Dirac measure
--   satisfies — any $\bar\mu$ it returns has $\bar\mu(G) = 1$ and so witnesses amenability.
--
--   Throughout this bundle “invariant” means **left**-invariant; no name says so.
--
--   **IsSupramenable $G$.** p. 11 (Definition 3.9): “A group $G$ is *supramenable* if for every
--   $\varnothing \neq A \subseteq G$ there is a finitely additive left-invariant measure
--   $\mu : \mathcal{P}(G) \to [0, 1]$ such that $\mu(A) = 1$.” For every nonempty
--   $A \subseteq G$ there is a finitely additive left-invariant measure $m$ on $\mathcal{P}(G)$ with
--   $m(A) = 1$. Note this does not require $m(G) = 1$. Its values lie in $[0, \infty]$, not the
--   printed $[0, 1]$: with the printed codomain only the trivial group qualifies (take $A = \{1\}$;
--   invariance gives every singleton measure $1$, so two distinct elements would give a set of
--   measure $2$; published and proved as
--   [`GarridoPrinted.supramenable_iff_subsingleton`](https://prove2.me/theorems/ea6361ba-eaff-4873-ac72-c09a0dc0ad6e)),
--   and the proof of Theorem 3.10 obtains $m$ from Tarski's theorem, whose measures
--   take values in $[0, \infty]$.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 4, 7, 11, Definitions 1.12 and 1.13, Theorem 2.6, Definition 3.9; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf. Definition 3.9's supramenability is attributed in the source to Rosenblatt without a reference. It is defined, for an action on an arbitrary set, in J. M. Rosenblatt, "Invariant measures and growth conditions", Trans. Amer. Math. Soc. 193 (1974), 33–53, p. 33; https://doi.org/10.1090/S0002-9947-1974-0342955-9

import Mathlib

namespace Garrido

open scoped ENNReal Pointwise

universe u v

def IsFinitelyAdditiveMeasure {X : Type*} (m : Set X → ℝ≥0∞) : Prop :=
  m ∅ = 0 ∧ ∀ s t : Set X, Disjoint s t → m (s ∪ t) = m s + m t

def IsInvariant (G : Type*) {X : Type*} [SMul G X] (m : Set X → ℝ≥0∞) : Prop :=
  ∀ (g : G) (s : Set X), m (g • s) = m s

def IsAmenable (G : Type*) [Group G] : Prop :=
  ∃ m : Set G → ℝ≥0∞,
    IsFinitelyAdditiveMeasure m ∧
    m Set.univ = 1 ∧
    IsInvariant G m

noncomputable def lshift {G : Type*} [Group G] (g : G) (f : lp (fun _ : G => ℝ) ∞) :
    lp (fun _ : G => ℝ) ∞ :=
  ⟨fun h => (f : G → ℝ) (g⁻¹ * h), by
    have hf : BddAbove (Set.range fun i => ‖(f : G → ℝ) i‖) := memℓp_infty_iff.1 f.2
    refine memℓp_infty_iff.2 ?_
    have hrange : (Set.range fun h => ‖(f : G → ℝ) (g⁻¹ * h)‖)
        = Set.range fun h => ‖(f : G → ℝ) h‖ :=
      (Equiv.mulLeft g⁻¹).surjective.range_comp (fun h => ‖(f : G → ℝ) h‖)
    rw [hrange]
    exact hf⟩

def IsInvariantMean (G : Type*) [Group G] (m : lp (fun _ : G => ℝ) ∞ →ₗ[ℝ] ℝ) : Prop :=
  (∀ f : lp (fun _ : G => ℝ) ∞, (∀ g : G, 0 ≤ (f : G → ℝ) g) → 0 ≤ m f) ∧
  (∀ f : lp (fun _ : G => ℝ) ∞, (∀ g : G, (f : G → ℝ) g = 1) → m f = 1) ∧
  (∀ (g : G) (f : lp (fun _ : G => ℝ) ∞), m (lshift g f) = m f)

def HasInvariantMean (G : Type*) [Group G] : Prop :=
  ∃ m : lp (fun _ : G => ℝ) ∞ →ₗ[ℝ] ℝ, IsInvariantMean G m

def HasInvariantExtensionProperty (G : Type u) [Group G] : Prop :=
  ∀ (X : Type (max u v)) [MulAction G X] (R : Set (Set X)) (μ ν : Set X → ℝ≥0∞),
    (∀ (g : G) (s : Set X), s ∈ R → g • s ∈ R) →
    (∀ (g : G) (s : Set X), s ∈ R → μ (g • s) = μ s) →
    (∀ s ∈ R, ν s = μ s) →
    IsFinitelyAdditiveMeasure ν →
    ∃ μbar : Set X → ℝ≥0∞,
      IsFinitelyAdditiveMeasure μbar ∧
      (∀ s ∈ R, μbar s = μ s) ∧
      IsInvariant G μbar

def IsSupramenable (G : Type*) [Group G] : Prop :=
  ∀ A : Set G, A.Nonempty →
    ∃ m : Set G → ℝ≥0∞,
      IsFinitelyAdditiveMeasure m ∧
      m A = 1 ∧
      IsInvariant G m

end Garrido


