-- Prove2me | Definitions.Def_BrionAntiAffine_IsExactSeq
-- name    : BrionAntiAffine_IsExactSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:40.121566+00:00
-- url     : https://prove2.me/theorems/fe4f28b0-4112-488c-9a25-45c17573c37c
-- title:
--   Exact sequences of group schemes, representations, actions, base change
-- statement:
--   This module fixes the shared vocabulary of Section 1 of the paper.
--
--   An **exact sequence** $1\to N\xrightarrow{i} G\xrightarrow{q} Q\to 1$ of group schemes of finite type means: $i$ and $q$ are homomorphisms, $q$ is faithfully flat and quasi-compact, and $i$ identifies $N$ with the kernel of $q$.
--
--   A **finite-dimensional linear representation** of $G$ is an invertible matrix $\rho$ over $\Gamma(G,\mathcal O_G)$ with
--
--   $$\mu^*\rho=\mathrm{pr}_1^*\rho\cdot\mathrm{pr}_2^*\rho,\qquad \eta^*\rho=1.$$
--
--   A **variety** is a separated, geometrically integral scheme of finite type. A **left action** of $G$ on $X$ is a morphism $a:G\times X\to X$ with the usual unit and associativity laws. A **fixed point** of $a$ is a closed point $x$ such that $a$ restricted to $G\times\mathrm{Spec}\,\kappa(x)$ is the second projection followed by the inclusion of $x$. The **base change** $G_K$ is $G\times_k\mathrm{Spec}\,K$ as a $K$-scheme. The **multiplication map** of $j_T:T\to G$, $j_U:U\to G$ is $(t,u)\mapsto j_T(t)j_U(u)$.
--
--   These enter Lemmas 1.1 and 1.3 and the decomposition (2.5).
--
--   **Formalization Note** All group schemes are of finite type, the convention of p.3. A representation in matrix form is a representation on $k^n$ with a chosen basis.
-- source:
--   M. Brion, Anti-affine algebraic groups, arXiv:0710.5211v3, pp.3–5 (conventions, Lemma 1.1, Lemma 1.3); §2.3, p.9

import Mathlib
import Definitions.Def_BrionAntiAffine_AntiAffineOver

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace BrionAntiAffine

variable {k : Type u} [Field k]

/-- An exact sequence of group schemes `1 → N → G → Q → 1`, Brion, arXiv:0710.5211v3, p.4–5: `q` is
a faithfully flat quasi-compact homomorphism, and `i` is a homomorphism identifying `N` with the
kernel of `q`. All three are of finite type over `k`, by the conventions of p.3. -/
structure IsExactSeq {N G Q : Sch k} [GrpObj N] [GrpObj G] [GrpObj Q] (i : N ⟶ G) (q : G ⟶ Q) :
    Prop where
  finiteType_N : IsFiniteTypeOver N
  finiteType_G : IsFiniteTypeOver G
  finiteType_Q : IsFiniteTypeOver Q
  isMonHom_i : IsMonHom i
  isMonHom_q : IsMonHom q
  flat : Flat q.left
  surjective : Surjective q.left
  quasiCompact : QuasiCompact q.left
  isKernel : IsPullback i (toUnit N) q η[Q]

/-- A finite-dimensional linear representation of `G` in matrix form: an invertible matrix `ρ` over
`Γ(G, ⊤)` with `μ^* ρ = pr₁^* ρ · pr₂^* ρ` in `Γ(G ⊗ G, ⊤)` and `η^* ρ = 1`. Used in Brion,
arXiv:0710.5211v3, Lemma 1.1(iii), p.4. -/
structure IsMatrixRep (G : Sch k) [GrpObj G] (n : ℕ) (ρ : Matrix (Fin n) (Fin n) Γ(G.left, ⊤)) :
    Prop where
  isUnit : IsUnit ρ
  map_mul : ρ.map μ[G].left.appTop.hom =
    ρ.map (fst G G).left.appTop.hom * ρ.map (snd G G).left.appTop.hom
  map_one : ρ.map η[G].left.appTop.hom = 1

/-- A variety: "a separated, geometrically integral scheme", of finite type over `k`. Brion,
arXiv:0710.5211v3, Notation and conventions, p.3. -/
structure IsVariety (X : Sch k) : Prop where
  finiteType : IsFiniteTypeOver X
  isSeparated : IsSeparated X.hom
  geometricallyIntegral : GeometricallyIntegral X.hom

/-- `a : G ⊗ X ⟶ X` is a left action of the group scheme `G` on `X`. -/
structure IsLeftAction {G X : Sch k} [GrpObj G] (a : G ⊗ X ⟶ X) : Prop where
  one_smul : η[G] ▷ X ≫ a = (λ_ X).hom
  mul_smul : μ[G] ▷ X ≫ a = (α_ G G X).hom ≫ G ◁ a ≫ a

/-- The inclusion `Spec κ(x) ⟶ X` of a point of `X`, as a `k`-morphism. -/
def pointMap (X : Sch k) (x : X.left) : Over.mk (X.left.fromSpecResidueField x ≫ X.hom) ⟶ X :=
  Over.homMk (X.left.fromSpecResidueField x)

/-- `x` is a fixed point of the action `a`: a closed point (Brion, arXiv:0710.5211v3, p.3, "a point
of a scheme will always mean a closed point") such that `a` restricted to `G × Spec κ(x)` is the
projection followed by the inclusion of `x`. -/
def IsFixedPoint {G X : Sch k} (a : G ⊗ X ⟶ X) (x : X.left) : Prop :=
  IsClosed ({x} : Set X.left) ∧ G ◁ pointMap X x ≫ a = snd G _ ≫ pointMap X x

/-- The base change `G_K = G ⊗_k K` of a `k`-scheme to a field extension `K/k`, as a `K`-scheme. -/
def baseChange (G : Sch k) (K : Type u) [Field K] [Algebra k K] : Sch K :=
  Over.mk (pullback.snd G.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))))

/-- The multiplication map `T × U → G`, `(t, u) ↦ j_T(t) · j_U(u)`, of two morphisms into a group
scheme. -/
def mulMap {T U G : Sch k} [GrpObj G] (jT : T ⟶ G) (jU : U ⟶ G) : T ⊗ U ⟶ G :=
  lift (fst T U ≫ jT) (snd T U ≫ jU) ≫ μ[G]

end BrionAntiAffine


