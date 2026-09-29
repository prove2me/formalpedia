-- Prove2me | Definitions.Def_KontsevichHMS_AInfCategory
-- name    : KontsevichHMS_AInfCategory
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T02:50:37.824828+00:00
-- url     : https://prove2.me/theorems/b9c37f13-2193-4900-881d-5b94df7ca211
-- title:
--   $A_\infty$-categories (Kontsevich, ICM 1994, pp. 13--15)
-- statement:
--   A **$A_\infty$-category** over a commutative ring $R$, in the sense of Kontsevich's ICM address (pp. 13--15), consists of a class of objects together with $\mathbb{Z}$-graded $R$-modules of morphisms and higher compositions
--
--   $$m_n : \mathrm{Hom}(X_0,X_1) \otimes \cdots \otimes \mathrm{Hom}(X_{n-1},X_n) \longrightarrow \mathrm{Hom}(X_0,X_n), \qquad \deg m_n = 2-n,$$
--
--   satisfying the Stasheff identities, of which the first three say that $m_1$ is a differential, that $m_2$ is a morphism of complexes, and that $m_2$ is associative up to a homotopy given by $m_3$.
--
--   In this formalization all morphism spaces are carried by a single $R$-module $A$: the space of morphisms from $X$ to $Y$ is a submodule $\hom(X,Y) \subseteq A$, the degree-$d$ part is a submodule $\mathrm{gr}(d) \subseteq A$, and $A$ is required to be the internal direct sum of the pieces $\hom(X,Y) \cap \mathrm{gr}(d)$, so that $\mathrm{Hom}^d(X,Y)$ is recovered as that intersection. The compositions are packaged as a single map $m$ defined on lists: $m[f_1,\dots,f_n]$ is $m_n(f_1 \otimes \cdots \otimes f_n)$, with the convention that $m_2(f,g)$ is the composite '$f$ first, then $g$'. There is no curvature term: $m[\,] = 0$. The axioms require $m$ to be additive and $R$-homogeneous in each argument, to send a composable chain $X_0 \to X_1 \to \cdots \to X_n$ into $\hom(X_0,X_n)$ and to vanish on chains that are not composable, to raise degree by $2-n$, and to satisfy
--
--   $$\sum_{\substack{r+s+t=n \\ s \ge 1}} (-1)^{r+st}\, m_{r+1+t}\bigl(f_1,\dots,f_r,\, m_s(f_{r+1},\dots,f_{r+s}),\, f_{r+s+1},\dots,f_n\bigr) = 0$$
--
--   for every nonempty list $[f_1,\dots,f_n]$. The signs are those of the bar-construction normalization; the paper writes them as $\pm$.
--
--   The file also defines $\mathrm{Hom}^d(X,Y) = \hom(X,Y) \cap \mathrm{gr}(d)$ and the predicate of **strict unitality** for a family of endomorphisms $e_X$: each $e_X$ lies in $\mathrm{Hom}^0(X,X)$, it is a two-sided identity for $m_2$, and every composition $m_k$ with $k \neq 2$ vanishes when one of its arguments is some $e_X$.
-- source:
--   M. Kontsevich, Homological algebra of mirror symmetry, Proc. ICM Zurich 1994, arXiv:alg-geom/9411018, pp. 13-15, section 'A-infinity-algebras and categories'

import Mathlib

/-!
# A∞-categories (Kontsevich, ICM 1994, "Homological algebra of mirror symmetry", pp. 13-15)

A ℤ-graded A∞-category over a commutative ring `R` is encoded here as a single graded
`R`-module `A` (the total space of all morphisms) together with

* a decomposition of `A` into morphism components `hom X Y`, indexed by pairs of objects;
* a ℤ-grading `gr d`;
* higher compositions `m : List A → A`, where `m` applied to a list of length `n`
  is Kontsevich's `mₙ`, of degree `2 - n`;

subject to multilinearity, compatibility with the two decompositions, and the Stasheff
identities.
-/

universe u

open scoped BigOperators

variable (R : Type*) [CommRing R]

open Classical in
/-- A ℤ-graded A∞-category over `R`.

Morphism spaces appear as the components `hom X Y` of one graded module `A`:
`Homᵈ(X, Y)` is `hom X Y ⊓ gr d`.  The composition `m` takes the list
`[f₁, …, fₙ]` to Kontsevich's `mₙ(f₁ ⊗ ⋯ ⊗ fₙ)`, with `m₂(f, g)` the composition of
`f : X ⟶ Y` followed by `g : Y ⟶ Z`.  There is no curvature term: `m₀ = 0`. -/
structure AInfCategory where
  /-- The objects. -/
  Obj : Type u
  /-- The total space of morphisms. -/
  A : Type u
  [addCommGroup : AddCommGroup A]
  [module : Module R A]
  /-- `hom X Y` is the space of morphisms from `X` to `Y`, a component of `A`. -/
  hom : Obj → Obj → Submodule R A
  /-- `gr d` is the degree-`d` part of `A`. -/
  gr : ℤ → Submodule R A
  /-- `A` is the direct sum of the spaces `Homᵈ(X, Y) = hom X Y ⊓ gr d`. -/
  internal : DirectSum.IsInternal (fun p : Obj × Obj × ℤ => hom p.1 p.2.1 ⊓ gr p.2.2)
  /-- The higher compositions: `m [f₁, …, fₙ] = mₙ(f₁ ⊗ ⋯ ⊗ fₙ)`. -/
  m : List A → A
  /-- There is no curvature term `m₀`. -/
  m_nil : m [] = 0
  /-- Each `mₙ` is additive in every argument. -/
  m_add : ∀ (L₁ L₂ : List A) (a b : A),
    m (L₁ ++ (a + b) :: L₂) = m (L₁ ++ a :: L₂) + m (L₁ ++ b :: L₂)
  /-- Each `mₙ` is `R`-homogeneous in every argument. -/
  m_smul : ∀ (L₁ L₂ : List A) (r : R) (a : A),
    m (L₁ ++ (r • a) :: L₂) = r • m (L₁ ++ a :: L₂)
  /-- `mₙ` maps a composable chain `X 0 ⟶ X 1 ⟶ ⋯ ⟶ X n` into `hom (X 0) (X n)`. -/
  m_hom : ∀ (L : List A) (X : ℕ → Obj),
    (∀ i : Fin L.length, L.get i ∈ hom (X i) (X (i + 1))) →
    m L ∈ hom (X 0) (X L.length)
  /-- `mₙ` vanishes on a chain that is not composable. -/
  m_hom_zero : ∀ (L₁ L₂ : List A) (a b : A) (X Y Z W : Obj),
    a ∈ hom X Y → b ∈ hom Z W → Y ≠ Z → m (L₁ ++ a :: b :: L₂) = 0
  /-- `mₙ` has degree `2 - n`. -/
  m_gr : ∀ (L : List A) (d : List ℤ), List.Forall₂ (fun a k => a ∈ gr k) L d →
    m L ∈ gr (d.sum + 2 - L.length)
  /-- The Stasheff identities: for every nonempty list `[f₁, …, fₙ]`,
  `∑_{r + s + t = n, s ≥ 1} (-1)^(r + s*t) mᵣ₊₁₊ₜ(f₁, …, fᵣ, mₛ(fᵣ₊₁, …, fᵣ₊ₛ), …, fₙ) = 0`. -/
  stasheff : ∀ L : List A, L ≠ [] →
    ∑ r ∈ Finset.range (L.length + 1), ∑ s ∈ Finset.Icc 1 (L.length - r),
      ((-1 : R) ^ (r + s * (L.length - r - s))) •
        m (L.take r ++ m ((L.drop r).take s) :: L.drop (r + s)) = 0

namespace AInfCategory

variable {R}

attribute [instance] AInfCategory.addCommGroup AInfCategory.module

/-- The degree-`d` part of the space of morphisms from `X` to `Y`. -/
def homDeg (C : AInfCategory.{u} R) (X Y : C.Obj) (d : ℤ) : Submodule R C.A :=
  C.hom X Y ⊓ C.gr d

/-- `e` is a strict unit assignment for `C`: `e X` is a degree-zero endomorphism of `X`
which is a two-sided identity for `m₂` and which annihilates all higher compositions. -/
def IsStrictlyUnital (C : AInfCategory.{u} R) (e : C.Obj → C.A) : Prop :=
  (∀ X, e X ∈ C.homDeg X X 0) ∧
  (∀ (X Y : C.Obj) (f : C.A), f ∈ C.hom X Y → C.m [e X, f] = f ∧ C.m [f, e Y] = f) ∧
  (∀ (L₁ L₂ : List C.A) (X : C.Obj), L₁.length + L₂.length + 1 ≠ 2 →
    C.m (L₁ ++ e X :: L₂) = 0)

end AInfCategory


