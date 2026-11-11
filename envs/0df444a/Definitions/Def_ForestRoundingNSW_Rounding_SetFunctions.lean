-- Prove2me | Definitions.Def_ForestRoundingNSW_Rounding_SetFunctions
-- name    : ForestRoundingNSW_Rounding_SetFunctions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:49:40.741635+00:00
-- url     : https://prove2.me/theorems/dce99228-159e-4419-a60b-4977a68a4fef
-- title:
--   Normalized, monotone and submodular set functions; partial derivatives of the multilinear extension (§2.1–2.2)
-- statement:
--   Let $X$ be a finite ground set and $f:2^X\to\mathbb R$ a set function. $f$ is **normalized** if $f(\emptyset)=0$, **monotone** if $f(S)\le f(T)$ whenever $S\subseteq T$, and **submodular** if $f(S)+f(T)\ge f(S\cup T)+f(S\cap T)$ for all $S,T\subseteq X$ (Definition 2.1). `IsNMS f` is the conjunction of the three; a normalized monotone function is automatically nonnegative, which is the paper's codomain $\mathbb R_{\ge 0}$.
--
--   The **multilinear extension** is the published polynomial
--   $$F(z)=\sum_{S\subseteq X} f(S)\prod_{j\in S}z_j\prod_{j\notin S}(1-z_j),$$
--   (Eq. (1)), defined for every $z\in\mathbb R^X$. For a function $G:\mathbb R^X\to\mathbb R$, the **partial derivative** $\partial_j G(z)$ is the derivative at $t=0$ of $t\mapsto G(z+te_j)$, second partials are iterates $\partial_j\partial_k G$, and the **gradient pairing** is $\nabla G(z)\cdot d=\sum_j d_j\,\partial_jG(z)$.
--
--   For $z\in[0,1]^X$ and $U\subseteq X$, `sampleExp z U g` is $\mathbb E[g(R)]$ for the random set $R\subseteq U$ that contains each $h\in U$ independently with probability $z_h$:
--   $$\mathbb E[g(R)]=\sum_{S\subseteq U}\prod_{h\in S}z_h\prod_{h\in U\setminus S}(1-z_h)\,g(S).$$
--   `restrict f R` is $T\mapsto f(T\cap R)$, a function on the subsets of $R$ seen on all of $2^X$; its multilinear extension is the multilinear extension over $R$ alone. `InUnitCube z` is $z\in[0,1]^X$.
--
--   **Formalization Note.** Set functions are `Finset X → ℝ` on a `Fintype X`; `Submodular` and `F` are the published `NonmonotoneSubmod.Shared` definitions, which add no condition.
-- source:
--   Feng, Hu, Li, Zhang, Correlated Forest Rounding for Unweighted Nash Social Welfare, STOC 2027 submission (manuscript sha256 0c7af642…), p. 12, §2.1, Definition 2.1; p. 14, §2.2, Eq. (1)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

/-!
# Set functions, the multilinear extension and its partial derivatives

Feng, Hu, Li, Zhang, *Correlated Forest Rounding for Unweighted Nash Social Welfare*, STOC 2027
submission (manuscript sha256 0c7af642…): §2.1 (p. 12: valuations are normalized and monotone,
Definition 2.1 submodularity), §2.2 (p. 14: the multilinear extension (1), its partial derivatives,
(2), Lemma 2.4).

Conventions.
* A set function on a finite ground type `X` is `f : Finset X → ℝ`. The paper's codomain `ℝ≥0`
  is implied by normalized and monotone (`f S ≥ f ∅ = 0`), so it is not a separate condition.
* `Submodular` is the published lattice inequality `NonmonotoneSubmod.Shared.Submodular`, and the
  multilinear extension is the published `NonmonotoneSubmod.Shared.F`, the polynomial
  `F f z = ∑_S f(S) ∏_{j ∈ S} z_j ∏_{j ∉ S} (1 - z_j)` on all of `X → ℝ` (Eq. (1)).
* `partialDeriv G j z` is `∂_j G(z)`, the derivative at `0` of `t ↦ G(z + t e_j)`; second
  partials are iterates, `∂_j ∂_k G = partialDeriv (partialDeriv G k) j`. Since `F f` is a
  polynomial, these derivatives exist everywhere, including the boundary of the unit cube.
* `gradDot G z d` is `∇G(z) · d = ∑_j d_j ∂_j G(z)`.
* `sampleExp z U g` is `E[g(R)]` for the random set `R ⊆ U` that contains each `h ∈ U`
  independently with probability `z_h`.
* `restrict f R` is `T ↦ f(T ∩ R)`: a function on the subsets of `R` viewed on all of `X`. Its
  multilinear extension at `z` is the multilinear extension over `R` alone.
-/

namespace ForestRoundingNSW.Rounding

variable {X : Type} [Fintype X] [DecidableEq X]

/-- Normalized: `f(∅) = 0`. -/
def Normalized (f : Finset X → ℝ) : Prop :=
  f ∅ = 0

/-- Monotone: `f(S) ≤ f(T)` whenever `S ⊆ T`. -/
def SetMonotone (f : Finset X → ℝ) : Prop :=
  ∀ S T : Finset X, S ⊆ T → f S ≤ f T

/-- Normalized, monotone and submodular (§2.1 and Definition 2.1). -/
def IsNMS (f : Finset X → ℝ) : Prop :=
  Normalized f ∧ SetMonotone f ∧ NonmonotoneSubmod.Shared.Submodular f

/-- The restriction `T ↦ f(T ∩ R)` of `f` to the subsets of `R`. -/
def restrict (f : Finset X → ℝ) (R : Finset X) : Finset X → ℝ :=
  fun T => f (T ∩ R)

/-- `z ∈ [0, 1]^X`. -/
def InUnitCube (z : X → ℝ) : Prop :=
  ∀ j, 0 ≤ z j ∧ z j ≤ 1

/-- The partial derivative `∂_j G(z)`: the derivative at `t = 0` of `t ↦ G(z + t e_j)`. -/
noncomputable def partialDeriv (G : (X → ℝ) → ℝ) (j : X) (z : X → ℝ) : ℝ :=
  deriv (fun t : ℝ => G (z + t • Pi.single j (1 : ℝ))) 0

/-- The gradient pairing `∇G(z) · d = ∑_j d_j ∂_j G(z)`. -/
noncomputable def gradDot (G : (X → ℝ) → ℝ) (z d : X → ℝ) : ℝ :=
  ∑ j, d j * partialDeriv G j z

/-- `E[g(R)]` for the random set `R ⊆ U` containing each `h ∈ U` independently with
probability `z h`. -/
noncomputable def sampleExp (z : X → ℝ) (U : Finset X) (g : Finset X → ℝ) : ℝ :=
  ∑ S ∈ U.powerset, (∏ h ∈ S, z h) * (∏ h ∈ U \ S, (1 - z h)) * g S

end ForestRoundingNSW.Rounding


