-- Prove2me | Definitions.Def_BrionAntiAffine_IsSubGammaLattice
-- name    : BrionAntiAffine_IsSubGammaLattice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:49.63023+00:00
-- url     : https://prove2.me/theorems/ebab80b2-448a-48b0-8036-9efd1a2981c1
-- title:
--   $A^\vee(k_s)$, sub-$\Gamma_k$-lattices, and the lattice invariant
-- statement:
--   Let $k_s$ be the separable closure of $k$ and $\Gamma_k=\mathrm{Gal}(k_s/k)$. For a $k$-scheme $X$ write $X_{k_s}=X\times_k k_s$. For an abelian variety $A$ the group of $k_s$-points of the dual is
--
--   $$A^\vee(k_s)=\{L\in\mathrm{Pic}(A_{k_s}) : t_x^*L\cong L\ \text{ for all } x\in A(k_s)\},$$
--
--   where $t_x:(a,t)\mapsto(a\cdot x(t),t)$ is the translation of $A_{k_s}$ by $x$. The group $\Gamma_k$ acts on $\mathrm{Pic}(A_{k_s})$ by pullback along $\mathrm{id}_A\times\mathrm{Spec}(\sigma)$.
--
--   A **sub-$\Gamma_k$-lattice** of $A^\vee(k_s)$ is a subgroup $\Lambda\subset\mathrm{Pic}(A_{k_s})$ such that:
--
--   1. $\Lambda\subset A^\vee(k_s)$;
--   2. $\Lambda$ is finitely generated and torsion-free, hence free of finite rank;
--   3. $\sigma^*\Lambda\subset\Lambda$ for all $\sigma\in\Gamma_k$.
--
--   The case $\Lambda=0$ is allowed. The **lattice invariant** of a homomorphism $\alpha:G\to A$ is
--
--   $$\Lambda(G,\alpha)=\ker\bigl(\alpha_{k_s}^*:\mathrm{Pic}(A_{k_s})\to\mathrm{Pic}(G_{k_s})\bigr).$$
--
--   It is one half of the correspondence in Theorem 2.7.
--
--   **Formalization Note** $A^\vee(k_s)$ is encoded by translation invariance rather than algebraic equivalence to $0$. The two agree: $\varphi_L:A\to A^\vee$ vanishes on $A(k_s)$, which is dense in $A_{\bar k}$ since $A$ is smooth, and $\mathrm{Pic}(A_{k_s})\to\mathrm{Pic}(A_{\bar k})$ is injective. The base change is written `X ⊗ Tks k` in `Over (Spec k)`. The invariant is a `Set`, so that its being a subgroup is part of the theorem. On anti-affine groups it equals the image of the map $c$ of (2.3); compare Proposition 2.10, p.12.
-- source:
--   M. Brion, Anti-affine algebraic groups, arXiv:0710.5211v3, p.3 (Γk-lattice); §2.1, p.7 (A∨(ks)); Theorem 2.7(i), p.11

import Mathlib
import Definitions.Def_BrionAntiAffine_AntiAffineOver
import Definitions.Def_BrionAntiAffine_Pic

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace BrionAntiAffine

variable (k : Type u) [Field k]

/-- `Spec ks` as a `k`-scheme, for `ks` the separable closure of `k`. The base change `X_ks` of a
`k`-scheme `X` is written `X ⊗ Tks k`, with `.left` its underlying scheme. Brion,
arXiv:0710.5211v3, Notation and conventions, p.3. -/
def Tks : Sch k :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k))))

variable {k}

/-- The translation `t_x : A_ks → A_ks`, `(a, t) ↦ (a · x(t), t)`, by a point `x ∈ A(ks)`. A point
of `A(ks)` is a `k`-morphism `Tks k ⟶ A`. -/
def translation {A : Sch k} [GrpObj A] (x : Tks k ⟶ A) : A ⊗ Tks k ⟶ A ⊗ Tks k :=
  lift (lift (fst A (Tks k)) (snd A (Tks k) ≫ x) ≫ μ[A]) (snd A (Tks k))

/-- The group `A∨(ks)` inside `Pic(A_ks)`, as the set of classes `L` with `t_x^* L ≅ L` for every
`x ∈ A(ks)`. Brion, arXiv:0710.5211v3, §2.1, p.7: `A∨(ks)` is the set of classes algebraically
equivalent to `0` (`A` has a rational point, so `Pic_{A/k}(ks) = Pic(A_ks)`).

**Formalization Note.** Translation invariance is equivalent to algebraic triviality: the
homomorphism `φ_L : A → A∨` vanishes on `A(ks)`, which is dense in `A_k̄` since `A` is smooth, and
`Pic(A_ks) → Pic(A_k̄)` is injective; then Mumford, *Abelian varieties*, §8, applies. -/
def picZero (A : Sch k) [GrpObj A] : Set (Pic (A ⊗ Tks k).left) :=
  {L | ∀ x : Tks k ⟶ A, Pic.pullback (translation x).left L = L}

/-- The action of `σ ∈ Γk = Gal(ks/k)` on `Spec ks` as a `k`-scheme. -/
def galoisMap (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) : Tks k ⟶ Tks k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (σ : SeparableClosure k →+* SeparableClosure k))) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp)

/-- A sub-`Γk`-lattice of `A∨(ks)`: a subgroup of `Pic(A_ks)` contained in `A∨(ks)`, finitely
generated, torsion-free (so free of finite rank), and stable under the pullback action of `Γk`.
`Λ = 0` is allowed. Brion, arXiv:0710.5211v3, Notation and conventions, p.3, and Theorem 2.7(i),
p.11. -/
structure IsSubGammaLattice (A : Sch k) [GrpObj A] (Λ : Subgroup (Pic (A ⊗ Tks k).left)) : Prop where
  subset_picZero : (Λ : Set (Pic (A ⊗ Tks k).left)) ⊆ picZero A
  fg : Λ.FG
  torsionFree : ∀ L ∈ Λ, ∀ n : ℕ, n ≠ 0 → L ^ n = 1 → L = 1
  galois_stable : ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k), ∀ L ∈ Λ,
    Pic.pullback (A ◁ galoisMap σ).left L ∈ Λ

/-- The lattice invariant of `α : G ⟶ A`: the classes in `Pic(A_ks)` whose pullback to `G_ks` is
trivial, that is `ker(α_ks^* : Pic(A_ks) → Pic(G_ks))`. A `Set`, so that its being a subgroup
is part of the classification rather than a proof inside a definition.

**Formalization Note.** Theorem 2.7 of Brion, arXiv:0710.5211v3, p.11, names no map. Its proof sends
`(G, α)` to the image of `c : Λ → A∨(ks)` of (2.3) for `G/U`. On anti-affine groups this image is the
kernel above; compare Proposition 2.10, p.12, "Λ is the kernel of the pull-back map". -/
def latticeSet {G A : Sch k} (α : G ⟶ A) : Set (Pic (A ⊗ Tks k).left) :=
  {L | Pic.pullback (α ▷ Tks k).left L = 1}

end BrionAntiAffine


