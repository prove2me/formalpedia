-- Prove2me | Definitions.Def_JinMaoSubsetSum_Cond41
-- name    : JinMaoSubsetSum_Cond41
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:40:15.144823+00:00
-- url     : https://prove2.me/theorems/06fe9b9e-5daa-4db8-8662-25cb5cf89aec
-- title:
--   Conditions (4.1): a fat group embedded in a proper progression with a small generating sub-multiset
-- statement:
--   Let $\Gamma$ be a lattice, $H\subseteq\operatorname{span}\Gamma$ an origin-symmetric polytope, $f:\operatorname{span}\Gamma\to\mathbb R$ linear, and $X'\subseteq X$ nonempty multisets with $\operatorname{supp}(X)\subseteq H\cap\Gamma$. For a fatness parameter $\lambda\ge 1$ and a bound $\Delta$, the **conditions (4.1)** are:
--
--   1. (4.1a) $f(\operatorname{supp}X)\subseteq[1,\Delta]\cap\mathbb Z$, and $f(H\cap\Gamma)$ is a proper progression;
--   2. (4.1b) $H\subseteq\dfrac{\lambda}{|X|}\,Z_0(X)$;
--   3. (4.1c) $X'$ is $(\operatorname{rank}\Gamma)$-generating for $H\cap\Gamma$.
--
--   They are the hypotheses under which one group of the partition (Theorem 4.2) can be solved (Lemma 4.3) and merged with the others (Lemma 4.4).
--
--   **Formalization Note** `Cond41 Γ H f X' X λ Δ` is the conjunction of the setting (discrete $\Gamma$, $H\subseteq\operatorname{span}\Gamma$ an origin-symmetric polytope, $X'\le X$ both nonempty, every element of $X$ in $H\cap\Gamma$, $\lambda\ge1$) and (4.1a)–(4.1c). The ambient space is $\mathbb R^m$ and $f$ is a linear map on it. $|X|$ and $Z_0(X)$ count multiplicity.
-- source:
--   Jin, Mao, Subset Sum in Almost-Linear Time, arXiv:2610.20742v1 (sha256 8b604948862d9188e922b8abf95831fde3a3699e26d39177d20a1460e31a926a), §4.1, conditions (4.1a)–(4.1c), p.18 (PDF p.20)

import Mathlib
import Definitions.Def_JinMaoSubsetSum_IsProgression

set_option autoImplicit false

namespace JinMaoSubsetSum

open scoped Pointwise

/-- **Conditions (4.1)** (Jin, Mao, *Subset Sum in Almost-Linear Time*, arXiv:2610.20742v1, §4.1,
p.18): "Let Γ be a lattice, H ⊆ span Γ be an origin-symmetric polytope, f : span Γ → ℝ be a
linear map, and X′ ⊆ X be two nonempty multisets with supp(X) ⊆ H ∩ Γ. For a fatness parameter
λ ≥ 1, define the following conditions:
f(supp X) ⊆ [1, ∆] ∩ ℤ, and f(H ∩ Γ) is a proper progression (see Definition 3.3), (4.1a)
H ⊆ (λ/|X|) Z_0(X) (recall Z_0(X) := Σ_{x∈X} [−x/2, x/2]), (4.1b)
X′ is (rank Γ)-generating for H ∩ Γ (see Definition 3.4). (4.1c)"

`Cond41 Γ H f X' X lam Δ` is the conjunction of the setting (Γ a discrete subgroup, `H ⊆ span Γ`
an origin-symmetric polytope, `X′ ≤ X` both nonempty, every element of `X` in `H ∩ Γ`, `λ ≥ 1`)
and (4.1a)–(4.1c).

**Formalization Note.** The ambient space is `ℝ^m`; `f` is a linear map on `ℝ^m` of which only the
restriction to `span Γ` matters. "f(H ∩ Γ) is a proper progression" is `IsProgression Γ H (rank Γ)`
(Definition 3.3 with `K = H`, `k = 1`) together with injectivity of `f` on `H ∩ Γ`. `|X|` counts
multiplicity, and `Z_0(X)` is the Minkowski sum over the multiset, with multiplicity. -/
def Cond41 {m : ℕ} (Γ : AddSubgroup (Fin m → ℝ)) (H : Set (Fin m → ℝ))
    (f : (Fin m → ℝ) →ₗ[ℝ] ℝ) (X' X : Multiset (Fin m → ℝ)) (lam Δ : ℝ) : Prop :=
  -- the setting
  DiscreteTopology Γ ∧
  H ⊆ (Submodule.span ℝ (Γ : Set (Fin m → ℝ)) : Set (Fin m → ℝ)) ∧
  IsOriginSymm H ∧ IsPolytope H ∧
  X' ≤ X ∧ X' ≠ 0 ∧ X ≠ 0 ∧ (∀ x ∈ X, x ∈ H ∧ x ∈ Γ) ∧ 1 ≤ lam ∧
  -- (4.1a)
  (∀ x ∈ X, ∃ z : ℤ, f x = z ∧ 1 ≤ z ∧ (z : ℝ) ≤ Δ) ∧
  IsProgression Γ H (rankOf Γ) ∧ IsSProper f H Γ 1 ∧
  -- (4.1b)
  H ⊆ (lam / (Multiset.card X : ℝ)) • zonotope0 X ∧
  -- (4.1c)
  IsSGenerating H Γ (rankOf Γ : ℝ) X'

end JinMaoSubsetSum


