-- Prove2me | Definitions.Def_IntLInfty_Kan_Manifold
-- name    : IntLInfty_Kan_Manifold
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:07.159484+00:00
-- url     : https://prove2.me/theorems/1ade2d88-1e93-47fd-af17-20f6fea744bf
-- title:
--   Definitions 1.2 and 4.1, pp. 3, 11 — split submanifolds, surjective submersions, horns, and the Kan condition for simplicial Banach spaces
-- statement:
--   Let $E$, $F$ be real Banach spaces.
--
--   1. A subset $M \subseteq E$ is a **$C^\infty$ split submanifold** if around every point of $M$ there is a $C^\infty$ diffeomorphism $\varphi$ between open subsets of $E$ which carries $M$ onto a closed complemented linear subspace of $E$ (intersected with the target of $\varphi$).
--   2. (Definition 4.1, with surjectivity.) A map $\kappa : E \to F$ is a **surjective submersion from $M \subseteq E$ onto $N \subseteq F$** if $\kappa(M) = N$ and for every $x \in M$ there are an open neighbourhood $U$ of $\kappa(x)$ and a $C^\infty$ map $s$ on $U$ with $s(\kappa(x)) = x$ and, for every $y \in U \cap N$, $s(y) \in M$ and $\kappa(s(y)) = y$.
--   3. For a family of sets $X_p$ with face maps $d_i : X_{p+1} \to X_p$ ($0 \le i \le p+1$), a map $\Lambda[m+1,j] \to X$ from the $j$-th horn is a tuple $(x_i)_{i \ne j}$ of $m$-simplices satisfying the simplicial identities $d_i x_k = d_{k-1} x_i$ for $i < k$ (nothing to check for $m = 0$). The restriction map $X_{m+1} \to \mathrm{Hom}(\Lambda[m+1,j], X)$ is $z \mapsto (d_i z)_{i \ne j}$.
--   4. (Definition 1.2.) A simplicial object with Banach spaces $X_p$ satisfies the **Kan condition** if for all $m \ge 1$ and $0 \le j \le m$ the set $\mathrm{Hom}(\Lambda[m,j],X)$ is a split submanifold of $\prod_{i\ne j} X_{m-1}$ and the restriction map $X_m \to \mathrm{Hom}(\Lambda[m,j],X)$ is a surjective submersion.
--
--   These notions are the paper's (Banach manifolds with Fréchet-smooth maps, covers = surjective submersions) specialized to subsets of Banach spaces.
--
--   **Formalization Note** `IsSplitSubmanifold`, `IsSurjSubmersionOn`, `HornCompat` (the identity $d_a x_{b+1} = d_b x_a$ for $a \le b$), `hornMap`, `HornSet`, `SatisfiesKan`. Smooth means `ContDiffOn ℝ ∞`. The local sections of Definition 4.1 are taken on open subsets of the ambient space, which is equivalent for split submanifolds. Mathlib's chart-based `IsSubmersion` is not used.
-- source:
--   Henriques, Integrating L∞-algebras, arXiv:math/0603563v2, p. 2, horns Λ[m, j]; p. 3, Definition 1.2; p. 11, Definition 4.1; p. 12, Corollary 4.5

import Mathlib
open scoped ContDiff

namespace IntLInfty.Kan

/-- `M` is a `C^∞` split submanifold of the Banach space `E`: around every point of `M` there is a
`C^∞` chart of `E` (with `C^∞` inverse) carrying `M` onto a closed complemented subspace `F`. -/
def IsSplitSubmanifold {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (M : Set E) : Prop :=
  ∀ x ∈ M, ∃ (F : Submodule ℝ E) (_ : F.ClosedComplemented) (φ : OpenPartialHomeomorph E E),
    x ∈ φ.source ∧ ContDiffOn ℝ ∞ φ φ.source ∧ ContDiffOn ℝ ∞ φ.symm φ.target ∧
    φ '' (M ∩ φ.source) = (F : Set E) ∩ φ.target

/-- Definition 4.1 (submersion), together with surjectivity, for a map `κ` from `M ⊆ E` onto
`N ⊆ F`: `κ` maps `M` onto `N`, and for every `x ∈ M` there are an open neighbourhood `U` of `κ x`
and a `C^∞` map `s` on `U` which is a section of `κ` over `U ∩ N` with values in `M` and `s (κ x) = x`. -/
def IsSurjSubmersionOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (κ : E → F) (M : Set E) (N : Set F) : Prop :=
  Set.MapsTo κ M N ∧ Set.SurjOn κ M N ∧
  ∀ x ∈ M, ∃ U : Set F, IsOpen U ∧ κ x ∈ U ∧ ∃ s : F → E, ContDiffOn ℝ ∞ s U ∧ s (κ x) = x ∧
    ∀ y ∈ U ∩ N, s y ∈ M ∧ κ (s y) = y

/-- Compatibility of a tuple `(xᵢ)_{i ≠ j}` of `m`-simplices, indexed by the facets of `Δ[m+1]`
other than the `j`-th, i.e. a map `Λ[m+1, j] → X`: `dₐ x_{b+1} = d_b xₐ` for `a ≤ b` (the
simplicial identity `dᵢ x_k = d_{k-1} xᵢ` for `i < k`). For `m = 0` there is nothing to check. -/
def HornCompat {X : ℕ → Type*} (face : ∀ p, Fin (p + 2) → X (p + 1) → X p) :
    (m : ℕ) → (j : Fin (m + 2)) → ({i : Fin (m + 2) // i ≠ j} → X m) → Prop
  | 0, _, _ => True
  | q + 1, j, x => ∀ a b : Fin (q + 2), a ≤ b → ∀ (ha : a.castSucc ≠ j) (hb : b.succ ≠ j),
      face q a (x ⟨b.succ, hb⟩) = face q b (x ⟨a.castSucc, ha⟩)

/-- The restriction map `X_{m+1} = Hom(Δ[m+1], X) → Hom(Λ[m+1, j], X)`, `z ↦ (dᵢ z)_{i ≠ j}`. -/
def hornMap {X : ℕ → Type*} (face : ∀ p, Fin (p + 2) → X (p + 1) → X p) (m : ℕ) (j : Fin (m + 2))
    (z : X (m + 1)) : {i : Fin (m + 2) // i ≠ j} → X m :=
  fun i => face m i.1 z

/-- `Hom(Λ[m+1, j], X)`, the compatible tuples. -/
def HornSet {X : ℕ → Type*} (face : ∀ p, Fin (p + 2) → X (p + 1) → X p) (m : ℕ) (j : Fin (m + 2)) :
    Set ({i : Fin (m + 2) // i ≠ j} → X m) :=
  {x | HornCompat face m j x}

/-- The Kan condition (Definition 1.2) for a simplicial object whose levels are Banach spaces
(faces only are needed): for all `m ≥ 1` and `0 ≤ j ≤ m`, `Hom(Λ[m, j], X)` is a `C^∞` split
submanifold of `∏_{i ≠ j} X_{m-1}` and the restriction `X_m → Hom(Λ[m, j], X)` is a surjective
submersion. -/
def SatisfiesKan (X : ℕ → Type*) [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace ℝ (X p)]
    (face : ∀ p, Fin (p + 2) → X (p + 1) → X p) : Prop :=
  ∀ (m : ℕ) (j : Fin (m + 2)), IsSplitSubmanifold (HornSet face m j) ∧
    IsSurjSubmersionOn (hornMap face m j) Set.univ (HornSet face m j)

end IntLInfty.Kan


