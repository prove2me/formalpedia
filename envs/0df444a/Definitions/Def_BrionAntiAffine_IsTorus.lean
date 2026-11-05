-- Prove2me | Definitions.Def_BrionAntiAffine_IsTorus
-- name    : BrionAntiAffine_IsTorus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:42.752733+00:00
-- url     : https://prove2.me/theorems/41143349-0b8b-48a1-841b-426ea62a9558
-- title:
--   Tori, semi-abelian varieties, characters and eigensheaves
-- statement:
--   A **torus** over $k$ is a group scheme $T$ of finite type whose base change $T_{k_s}$ is split, i.e. isomorphic to $\mathbb G_m^n$; here this is a natural isomorphism of group-valued functors
--
--   $$T_{k_s}(S)\cong(\Gamma(S,\mathcal O_S)^\times)^n$$
--
--   on $k_s$-schemes $S$. A **semi-abelian variety** is an extension (2.1)
--
--   $$1\to T\to G\xrightarrow{\alpha} A\to 0$$
--
--   of an abelian variety by a torus.
--
--   The **character group** of $T$ is the group of $\lambda\in\Gamma(T_{k_s},\mathcal O)^\times$ with $\mu^*\lambda=\mathrm{pr}_1^*\lambda\cdot\mathrm{pr}_2^*\lambda$. For an extension (2.1), a function $f$ on $\alpha_{k_s}^{-1}(W)$ is an **eigenvector of weight $\lambda$** if $f(g\,i(t))=f(g)\lambda(t)$, i.e. $\rho^*f=\mathrm{pr}_1^*f\cdot\mathrm{pr}_2^*\lambda$, for the action $\rho$ of $T_{k_s}$ on $G_{k_s}$. The **eigensheaf** $\mathcal L_\lambda$ of (2.2) is the subsheaf of $\alpha_*(\mathcal O_{G_{k_s}})$ on $A_{k_s}$ of eigenvectors of weight $\lambda$; a class $L\in\mathrm{Pic}(A_{k_s})$ is its class if an invertible subsheaf representing $L$ has exactly these sections over every open set.
--
--   **Formalization Note** A $k_s$-scheme is given as a $k$-scheme $S$ with a map to $\mathrm{Spec}\,k_s$, and $T_{k_s}(S)$ is the same as the set of $k$-morphisms $S\to T$. The value $n=0$ is allowed. The published `AlgebraicGeometry_SplitTorusMu` (a spectrum of a group algebra, without a `GrpObj`) is not reused, since the statements here need the group law.
-- source:
--   M. Brion, Anti-affine algebraic groups, arXiv:0710.5211v3, §2.1, pp.6–7, (2.1)–(2.3)

import Mathlib
import Definitions.Def_BrionAntiAffine_IsExactSeq
import Definitions.Def_BrionAntiAffine_IsSubGammaLattice
import Definitions.Def_BrionAntiAffine_CechH1

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace BrionAntiAffine

variable {k : Type u} [Field k]

/-- Pullback of invertible functions along a morphism of `k`-schemes. -/
def pullUnits {X Y : Sch k} (f : X ⟶ Y) : (Γ(Y.left, ⊤))ˣ →* (Γ(X.left, ⊤))ˣ :=
  Units.map (f.left.appTop.hom : Γ(Y.left, ⊤) →+* Γ(X.left, ⊤)).toMonoidHom

/-- A splitting of `T` over `ks`: a natural isomorphism of group-valued functors between the points
of `T_ks` and `(Γ(-, ⊤)ˣ)ⁿ`, on `ks`-schemes `S`. A `ks`-point of `T_ks` valued in `S` is the same as
a `k`-morphism `S ⟶ T`, once `S` is given as a `k`-scheme with a map to `Spec ks`. -/
structure TorusSplitting (T : Sch k) [GrpObj T] (n : ℕ) where
  /-- The group isomorphism on `S`-points. -/
  e : ∀ (S : Sch k), (S ⟶ Tks k) → ((S ⟶ T) ≃* (Fin n → (Γ(S.left, ⊤))ˣ))
  natural : ∀ (S S' : Sch k) (s : S ⟶ Tks k) (f : S' ⟶ S) (x : S ⟶ T) (j : Fin n),
    e S' (f ≫ s) (f ≫ x) j = pullUnits f (e S s x j)

/-- `T` is a torus: of finite type over `k`, and split over `ks`, i.e. `T_ks ≅ 𝔾ₘⁿ`. Brion,
arXiv:0710.5211v3, §2.1, p.6, "as `T_ks := T ⊗_k ks` is split". `n = 0` is allowed. -/
def IsTorus (T : Sch k) [GrpObj T] : Prop :=
  IsFiniteTypeOver T ∧ ∃ n : ℕ, Nonempty (TorusSplitting T n)

/-- `G` is a semi-abelian variety: an extension (2.1) of an abelian variety by a torus. Brion,
arXiv:0710.5211v3, §2.1, p.6. -/
def IsSemiAbelian (G : Sch k) [GrpObj G] : Prop :=
  ∃ (T A : Sch k) (_ : GrpObj T) (_ : GrpObj A) (i : T ⟶ G) (α : G ⟶ A),
    IsTorus T ∧ IsAbelianVariety A ∧ IsExactSeq i α

/-- The character group `Λ` of the torus `T`, Brion, arXiv:0710.5211v3, p.7: invertible functions on
`T_ks` that are group-like relative to `ks`, i.e. `μ^* λ = pr₁^* λ · pr₂^* λ` on `(T × T)_ks`. -/
def characters (T : Sch k) [GrpObj T] : Subgroup (Γ((T ⊗ Tks k).left, ⊤))ˣ :=
  MonoidHom.eqLocus (pullUnits (μ[T] ▷ Tks k))
    (pullUnits (fst T T ▷ Tks k) * pullUnits (snd T T ▷ Tks k))

/-- The action `ρ : (G × T)_ks → G_ks`, `(g, t) ↦ g · i(t)`, of `T_ks` on `G_ks`. -/
def torusAction {T G : Sch k} [GrpObj G] (i : T ⟶ G) : (G ⊗ T) ⊗ Tks k ⟶ G ⊗ Tks k :=
  (lift (fst G T) (snd G T ≫ i) ≫ μ[G]) ▷ Tks k

/-- `f ∈ Γ(G_ks, α_ks⁻¹ W)` is an eigenvector of `T_ks` of weight `λ`, that is
`f(g · i(t)) = f(g) λ(t)`: the identity `ρ^* f = pr₁^* f · pr₂^* λ` on `(G × T)_ks`, on the open
`ρ⁻¹(α_ks⁻¹ W) ∩ pr₁⁻¹(α_ks⁻¹ W)`. -/
def IsEigenvector {T G A : Sch k} [GrpObj G] (i : T ⟶ G) (α : G ⟶ A)
    (lam : (Γ((T ⊗ Tks k).left, ⊤))ˣ) (W : (A ⊗ Tks k).left.Opens)
    (f : Γ((G ⊗ Tks k).left, (α ▷ Tks k).left ⁻¹ᵁ W)) : Prop :=
  let O : ((G ⊗ T) ⊗ Tks k).left.Opens :=
    (torusAction i).left ⁻¹ᵁ ((α ▷ Tks k).left ⁻¹ᵁ W) ⊓
      (fst G T ▷ Tks k).left ⁻¹ᵁ ((α ▷ Tks k).left ⁻¹ᵁ W)
  res _ (inf_le_left : O ≤ _) ((torusAction i).left.app ((α ▷ Tks k).left ⁻¹ᵁ W) f) =
    res _ (inf_le_right : O ≤ _) ((fst G T ▷ Tks k).left.app ((α ▷ Tks k).left ⁻¹ᵁ W) f) *
      res _ (le_top : O ≤ ⊤) ((snd G T ▷ Tks k).left.appTop lam.1)

/-- `L` is the class of the eigensheaf `L_λ` of (2.2), Brion, arXiv:0710.5211v3, p.7, "`L_λ` consists
of all eigenvectors of `T_ks` in `α_*(𝒪_{G_ks})` with weight `λ`": an invertible subsheaf `M` of
`α_*(𝒪_{G_ks})` on `A_ks` whose sections over each open `W` are exactly the eigenvectors of weight
`λ` on `α⁻¹ W`. -/
def IsEigenClass {T G A : Sch k} [GrpObj G] (i : T ⟶ G) (α : G ⟶ A)
    (lam : (Γ((T ⊗ Tks k).left, ⊤))ˣ) (L : Pic (A ⊗ Tks k).left) : Prop :=
  ∃ (M : (A ⊗ Tks k).left.Modules) (hM : Scheme.Modules.IsInvertible M)
    (φ : M ⟶ (Scheme.Modules.pushforward (α ▷ Tks k).left).obj
      (Pic.unitMod (G ⊗ Tks k).left)),
    L = Pic.mk M hM ∧ Mono φ ∧
      ∀ (W : (A ⊗ Tks k).left.Opens) (f : Γ((G ⊗ Tks k).left, (α ▷ Tks k).left ⁻¹ᵁ W)),
        (∃ m : Γ(M, W), (φ.app W).hom m = f) ↔ IsEigenvector i α lam W f

/-- `G` over `A` has torus kernel: `G` is a semi-abelian variety over `A`, with `α` the extension
(2.1). Brion, arXiv:0710.5211v3, §2.1, p.6. -/
def HasTorusKernel {A : Sch k} [GrpObj A] (G : AntiAffineOver A) : Prop :=
  ∃ (T : Sch k) (_ : GrpObj T) (i : T ⟶ G.G), IsTorus T ∧ IsExactSeq i G.α

end BrionAntiAffine


