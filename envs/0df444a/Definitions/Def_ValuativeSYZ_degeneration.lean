-- Prove2me | Definitions.Def_ValuativeSYZ_degeneration
-- name    : ValuativeSYZ_degeneration
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T11:08:21.593973+00:00
-- url     : https://prove2.me/theorems/3b663fd2-0fd8-4370-92a1-147f76fc2ff2
-- title:
--   Interface for a polarised maximal Calabi--Yau degeneration and its non-archimedean pluripotential theory
-- statement:
--   This file provides the **interface** for the non-archimedean side of the mission: the data attached
--   to a polarised maximal degeneration of compact Calabi–Yau manifolds together with a chosen
--   semistable SNC model, and the results of non-archimedean pluripotential theory that the source
--   paper quotes in its §2 and uses freely afterwards.
--
--   Mathlib contains no Berkovich analytification, no dual complex, no essential skeleton and no
--   non-archimedean Monge–Ampère operator, so these are introduced as abstract data with the required
--   properties as hypotheses of the bundled structure. Instantiating the interface for an actual
--   degeneration is **not** part of this mission; everything downstream is stated for an arbitrary
--   instance.
--
--   The data are: a type standing for the Berkovich space $X_K^{\mathrm{an}}$ with a measurable
--   structure; a finite family of compact convex **faces** in a Euclidean space $\mathbb{R}^N$, whose
--   union is the dual complex $\Delta_{\mathcal{X}}$, together with the subfamily whose union is the
--   **essential skeleton** $\mathrm{Sk}(X)$; a retraction $r_{\mathcal{X}}$ from the Berkovich space to
--   $\mathbb{R}^N$ and an embedding $\mathrm{emb}_{\mathcal{X}}$ in the other direction with
--   $r_{\mathcal{X}} \circ \mathrm{emb}_{\mathcal{X}} = \mathrm{id}$ on the dual complex; the valued
--   field $K = \mathbb{C}((t))$ with its valuation; the graded family of section spaces
--   $H^0(X_K, lL)$ with their multiplication; and the valuation $v_x(s)$ of a section at a point of the
--   Berkovich space, read through a fixed trivialisation, so that $\log\lVert s\rVert(x) = -v_x(s)$.
--
--   **Maximality** of the degeneration is encoded by requiring the $n$-dimensional Hausdorff measure of
--   the skeleton to be positive and finite, where $n$ is the fibre dimension; the measure $\mu_0$ is the
--   normalised $n$-dimensional Hausdorff measure of the skeleton, pushed forward into the Berkovich
--   space.
--
--   The quoted results appearing as fields are: the uniform Lipschitz estimate for $l^{-1}v_{\cdot}(s)$
--   on each face (Lemma 2.3); the description of Fubini–Study potentials by equation (4) and of
--   $\mathrm{CPSH}(X_K^{\mathrm{an}}, L)$ as their uniform limits (§2.3); convexity and uniform Lipschitz
--   continuity of semipositive potentials on each face (Proposition 2.2); the Boucksom–Favre–Jonsson
--   theorem on existence and uniqueness up to an additive constant for the non-archimedean
--   Monge–Ampère equation (Theorem 2.4); and the domination principle (Lemma 2.6).
--
--   The file also defines, for an instance of the interface: the measure $\mu_0$; what it means for a
--   potential to be a **non-archimedean Calabi–Yau potential**, namely to be continuous semipositive
--   and to satisfy $\mathrm{MA}(\varphi) = (L^n)\mu_0$; **valuative independence** of a $K$-basis of
--   $H^0(X_K, lL)$ (Definition 1.5); and the **weak comparison property** of a potential
--   (Definitions 1.2 and 2.9).
-- source:
--   Yang Li, *Valuative independence and metric SYZ conjecture*, arXiv:2605.00516v1 (1 May 2026), https://arxiv.org/abs/2605.00516, pp. 2, 5-10, Definitions 1.2, 1.5, 2.9, Propositions 2.2, Lemmas 2.3, 2.6, Theorem 2.4, equations (4), (5)

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace ValuativeSYZ

/-- The normalised `n`-dimensional Lebesgue (Hausdorff) measure carried by the essential
skeleton `Sk`, viewed inside the ambient space `EuclideanSpace ℝ (Fin N)` of the dual
complex. -/
noncomputable def skeletonMeasure {N : ℕ} (n : ℕ) (Sk : Set (EuclideanSpace ℝ (Fin N))) :
    Measure (EuclideanSpace ℝ (Fin N)) :=
  (μH[(n : ℝ)] Sk)⁻¹ • (μH[(n : ℝ)]).restrict Sk

/--
`Degeneration Berk K Sect N n` is an interface for the non-archimedean data attached to a
polarised maximal degeneration of `n`-dimensional compact Calabi–Yau manifolds
`π : (X, L) → D*`, together with a chosen semistable SNC model, as recalled in Yang Li,
*Valuative independence and metric SYZ conjecture*, §2.

* `Berk` stands for the Berkovich analytification `X_K^an` of the base change to `K = ℂ((t))`;
* `K` is the valued field `ℂ((t))` and `valK` its `t`-adic valuation;
* `Sect l` stands for the space of sections `H⁰(X_K, lL)`, a `K`-vector space;
* `EuclideanSpace ℝ (Fin N)` is the ambient space in which the dual complex `Δ_X` of the
  chosen SNC model is realised as a finite union of compact convex faces;
* `n` is the complex dimension of the fibres, and the essential skeleton `Sk` is required to
  carry positive and finite `n`-dimensional Hausdorff measure, which is the maximality
  assumption `dim Sk(X) = n`.

The fields after the data are the standard results of non-archimedean pluripotential theory
that the paper quotes and uses: the uniform Lipschitz estimate for valuations of sections
(Lemma 2.3), the description of continuous semipositive potentials as uniform limits of
Fubini–Study potentials (§2.3), convexity and equi-Lipschitz continuity of such potentials on
the faces of the dual complex (Proposition 2.2), the Boucksom–Favre–Jonsson solution of the
non-archimedean Calabi conjecture (Theorem 2.4), and the domination principle (Lemma 2.6).
-/
structure Degeneration (Berk : Type) [MeasurableSpace Berk] (K : Type) [Field K]
    (Sect : ℕ → Type) [∀ l, AddCommGroup (Sect l)] [∀ l, Module K (Sect l)]
    (N n : ℕ) where
  /-- The faces of the dual complex `Δ_X` of the chosen semistable SNC model. -/
  faces : Finset (Set (EuclideanSpace ℝ (Fin N)))
  faces_convex : ∀ F ∈ faces, Convex ℝ F
  faces_compact : ∀ F ∈ faces, IsCompact F
  /-- The faces whose union is the essential skeleton. -/
  skFaces : Finset (Set (EuclideanSpace ℝ (Fin N)))
  skFaces_subset : skFaces ⊆ faces
  /-- The essential skeleton `Sk(X) ⊆ Δ_X`. -/
  Sk : Set (EuclideanSpace ℝ (Fin N))
  Sk_eq : Sk = ⋃ F ∈ skFaces, F
  /-- Maximality of the degeneration: `Sk(X)` is `n`-dimensional. -/
  Sk_hausdorff_pos : 0 < μH[(n : ℝ)] Sk
  Sk_hausdorff_lt_top : μH[(n : ℝ)] Sk < ⊤
  /-- The retraction map `r_X : X_K^an → Δ_X`. -/
  retract : Berk → EuclideanSpace ℝ (Fin N)
  /-- The embedding `emb_X : Δ_X → X_K^an` of the dual complex as quasi-monomial valuations. -/
  emb : EuclideanSpace ℝ (Fin N) → Berk
  emb_measurable : Measurable emb
  retract_emb : ∀ x ∈ ⋃ F ∈ faces, F, retract (emb x) = x
  /-- The `t`-adic valuation of `K = ℂ((t))`, normalised by `val t = 1`. -/
  valK : K → ℝ
  valK_mul : ∀ a b : K, a ≠ 0 → b ≠ 0 → valK (a * b) = valK a + valK b
  /-- Multiplication of sections, `H⁰(lL) ⊗ H⁰(l'L) → H⁰((l + l')L)`. -/
  mulSect : ∀ {l l' : ℕ}, Sect l → Sect l' → Sect (l + l')
  /-- `val x s` is the valuation at `x ∈ X_K^an` of the section `s`, read as a meromorphic
  function through a fixed local trivialisation of the reference model line bundle; so
  `log ‖s‖ (x) = - val x s`. -/
  val : ∀ {l : ℕ}, Berk → Sect l → ℝ
  val_smul : ∀ {l : ℕ} (a : K) (s : Sect l) (x : Berk), a ≠ 0 → s ≠ 0 →
    val x (a • s) = valK a + val x s
  val_mul : ∀ {l l' : ℕ} (s : Sect l) (s' : Sect l') (x : Berk),
    val x (mulSect s s') = val x s + val x s'
  /-- Lemma 2.3: the uniform Lipschitz estimate for `l⁻¹ val · (s)` on each face. -/
  val_lipschitz : ∃ C : ℝ, ∀ (l : ℕ) (s : Sect l) (F : Set (EuclideanSpace ℝ (Fin N)))
    (x y : EuclideanSpace ℝ (Fin N)), 0 < l → s ≠ 0 → F ∈ faces → x ∈ F → y ∈ F →
    |val (emb x) s - val (emb y) s| ≤ C * l * dist x y
  /-- The non-archimedean Fubini–Study potentials on `(X_K^an, L)`. -/
  FS : Set (Berk → ℝ)
  /-- Equation (4): a Fubini–Study potential is `l⁻¹ maxᵢ (log ‖sᵢ‖ - cᵢ)` for finitely many
  nonzero sections `sᵢ ∈ H⁰(X_K, lL)` generating `L^{⊗l}`. -/
  FS_eq : ∀ φ : Berk → ℝ, φ ∈ FS ↔ ∃ (l m : ℕ) (s : Fin m → Sect l) (cst : Fin m → ℝ)
    (hm : 0 < m), 0 < l ∧ (∀ i, s i ≠ 0) ∧ ∀ x : Berk,
      φ x = (l : ℝ)⁻¹ * (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr
        (Fin.pos_iff_nonempty.mp hm)) fun i => (-(val x (s i)) - cst i))
  /-- The continuous semipositive potentials `CPSH(X_K^an, L)`. -/
  CPSH : Set (Berk → ℝ)
  /-- §2.3: continuous semipositive potentials are exactly the uniform limits of
  Fubini–Study potentials. -/
  CPSH_eq : ∀ φ : Berk → ℝ, φ ∈ CPSH ↔ ∃ ψ : ℕ → Berk → ℝ, (∀ k, ψ k ∈ FS) ∧
    TendstoUniformly ψ φ Filter.atTop
  /-- Proposition 2.2: every continuous semipositive potential is convex on each face of the
  dual complex. -/
  cpsh_convex : ∀ φ ∈ CPSH, ∀ F ∈ faces, ConvexOn ℝ F (fun x => φ (emb x))
  /-- Proposition 2.2: continuous semipositive potentials are uniformly Lipschitz on the
  faces of the dual complex. -/
  cpsh_lipschitz : ∃ C : ℝ, ∀ φ ∈ CPSH, ∀ F ∈ faces, ∀ x ∈ F, ∀ y ∈ F,
    |φ (emb x) - φ (emb y)| ≤ C * dist x y
  /-- The degree `(Lⁿ) > 0`. -/
  deg : ℝ
  deg_pos : 0 < deg
  /-- The non-archimedean Monge–Ampère measure. -/
  MA : (Berk → ℝ) → Measure Berk
  MA_total : ∀ φ ∈ CPSH, MA φ Set.univ = ENNReal.ofReal deg
  /-- Theorem 2.4 (Boucksom–Favre–Jonsson), existence: the non-archimedean Monge–Ampère
  equation is solvable for every Radon probability measure supported on the dual complex. -/
  MA_exists : ∀ μ : Measure Berk, IsProbabilityMeasure μ →
    μ (emb '' (⋃ F ∈ faces, F))ᶜ = 0 → ∃ φ ∈ CPSH, MA φ = ENNReal.ofReal deg • μ
  /-- Theorem 2.4, uniqueness up to an additive constant. -/
  MA_unique : ∀ φ ∈ CPSH, ∀ ψ ∈ CPSH, MA φ = MA ψ → ∃ cst : ℝ, ∀ x, φ x = ψ x + cst
  /-- Lemma 2.6: the domination principle. -/
  MA_domination : ∀ φ ∈ CPSH, ∀ ψ ∈ CPSH, MA ψ (emb '' (⋃ F ∈ faces, F))ᶜ = 0 →
    (∀ᵐ x ∂(MA ψ), φ x ≤ ψ x) → ∀ x, φ x ≤ ψ x

namespace Degeneration

variable {Berk : Type} [MeasurableSpace Berk] {K : Type} [Field K]
  {Sect : ℕ → Type} [∀ l, AddCommGroup (Sect l)] [∀ l, Module K (Sect l)] {N n : ℕ}

/-- The measure `μ₀`: the normalised Lebesgue measure of the essential skeleton, pushed into
the Berkovich space along the embedding of the dual complex. -/
noncomputable def mu0 (D : Degeneration Berk K Sect N n) : Measure Berk :=
  Measure.map D.emb (skeletonMeasure n D.Sk)

/-- `φ` is a non-archimedean Calabi–Yau potential: a continuous semipositive potential
solving `MA(φ) = (Lⁿ) μ₀`, equation (5). -/
def IsNACYPotential (D : Degeneration Berk K Sect N n) (φ : Berk → ℝ) : Prop :=
  φ ∈ D.CPSH ∧ D.MA φ = ENNReal.ofReal D.deg • D.mu0

open scoped Classical in
/-- Definition 1.5: the `K`-basis `θ` of `H⁰(X_K, lL)` satisfies *valuative independence*:
for every point `x` of the essential skeleton, viewed as the valuation `val_x`, and every
family of coefficients `a` in `K` not all zero,
`val_x (∑ a_α θ_α) = min_{a_α ≠ 0} (val(a_α) + val_x(θ_α))`. -/
def ValuativeIndependent (D : Degeneration Berk K Sect N n) (l : ℕ) {A : Type} [Fintype A]
    (θ : Module.Basis A K (Sect l)) : Prop :=
  ∀ x ∈ D.Sk, ∀ a : A → K, ∀ h : (Finset.univ.filter fun α => a α ≠ 0).Nonempty,
    D.val (D.emb x) (∑ α, a α • θ α) =
      (Finset.univ.filter fun α => a α ≠ 0).inf' h
        (fun α => D.valK (a α) + D.val (D.emb x) (θ α))

/-- Definition 1.2 / 2.9: the chosen SNC model satisfies the *weak comparison property* for
the potential `φ` if there is an open subset `U` of the essential skeleton of full Lebesgue
measure over which `φ` factors through the retraction map `r_X`. -/
def WeakComparisonProperty (D : Degeneration Berk K Sect N n) (φ : Berk → ℝ) : Prop :=
  ∃ U : Set (EuclideanSpace ℝ (Fin N)), IsOpen U ∧ D.mu0 (D.emb '' (U ∩ D.Sk)) = 1 ∧
    ∀ x : Berk, D.retract x ∈ U ∩ D.Sk → φ x = φ (D.emb (D.retract x))

end Degeneration

end ValuativeSYZ


