-- Prove2me | Definitions.Def_ProximalBanach_Hybrid_Basic
-- name    : ProximalBanach_Hybrid_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:04:35.097982+00:00
-- url     : https://prove2.me/theorems/4a5a9479-e280-4b44-ac69-fc175797d29d
-- title:
--   Duality mapping, smooth and uniformly smooth spaces, maximal monotone operators, φ, the generalized projection Q_C and the algorithm (3.1)
-- statement:
--   Let $E$ be a real normed space with dual $E^*$; the value of $f\in E^*$ at $x\in E$ is written $\langle x,f\rangle$. This file fixes the objects of Kamimura and Takahashi's paper.
--
--   1. The **(normalized) duality mapping** $J:E\to 2^{E^*}$ is
--   $$Jx=\{v\in E^*:\ \langle x,v\rangle=\|x\|^2=\|v\|^2\}.$$
--   2. $E$ is **smooth** if for all $x,y$ in the unit sphere $U=\{x:\|x\|=1\}$ the limit
--   $$\lim_{t\to0}\frac{\|x+ty\|-\|x\|}{t}\tag{2.1}$$
--   exists ($t$ real, $t\neq0$, from both sides). $E$ is **uniformly smooth** if the limit (2.1) is attained uniformly for $x,y\in U$: there is a function $D(x,y)$ such that for every $\varepsilon>0$ one $\delta>0$ serves all $x,y\in U$, i.e. $\bigl|\frac{\|x+ty\|-\|x\|}{t}-D(x,y)\bigr|<\varepsilon$ whenever $0<|t|<\delta$.
--   3. $E$ is **reflexive** if the canonical embedding $E\to E^{**}$ is surjective.
--   4. A multivalued operator $T:E\to 2^{E^*}$ is **monotone** if $\langle x_1-x_2,y_1-y_2\rangle\ge0$ whenever $y_i\in Tx_i$; it is **maximal monotone** if it is monotone and every monotone operator $T'$ with $Tx\subseteq T'x$ for all $x$ equals $T$ (its graph is not properly contained in the graph of another monotone operator). Its zero set is $T^{-1}0=\{x: 0\in Tx\}$.
--   5. For a single-valued map $J:E\to E^*$ (the duality mapping of a smooth space),
--   $$\varphi(x,y)=\|x\|^2-2\langle x,Jy\rangle+\|y\|^2 .$$
--   6. The **generalized projection**: $z=Q_Cx$ means $z\in C$ and $\varphi(z,x)\le\varphi(w,x)$ for every $w\in C$, i.e. $z$ attains $\inf\{\varphi(w,x):w\in C\}$ (2.3).
--   7. The **algorithm (3.1)**: given $x_0\in E$ and positive reals $r_n$, a run consists of sequences $x_n,y_n\in E$ and $v_n\in E^*$ with, for every $n\ge0$,
--   $$0=v_n+\frac1{r_n}(Jy_n-Jx_n),\quad v_n\in Ty_n,$$
--   $$H_n=\{z:\langle z-y_n,v_n\rangle\le0\},\qquad W_n=\{z:\langle z-x_n,Jx_0-Jx_n\rangle\le0\},\qquad x_{n+1}=Q_{H_n\cap W_n}x_0 .$$
--
--   These are the objects in terms of which the paper's Propositions 1–7, Theorem 6 and Theorem 8 are stated.
--
--   **Formalization Note** The pairing $\langle x,f\rangle$ is `f x`. The single-valued duality map is a function `J : E → StrongDual ℝ E` that every statement constrains by `∀ x, J x ∈ dualityMap x`; on a smooth space this determines `J` (property 2 of $J$ is a separate milestone). $Q_C$ and the run of (3.1) are relations (`IsGenProj`, `IsHybridRun`), not functions, so no choice is built in; existence and uniqueness of $Q_Cx$ is Proposition 3 and existence of a run is Proposition 7. The run is indexed from $0$ and its starting point is `x 0`; $W_0=E$ holds automatically.
-- source:
--   Kamimura and Takahashi, Strong convergence of a proximal-type algorithm in a Banach space, SIAM J. Optim. 13(3), 2003, pp. 939–942, §2 (definitions of monotone and maximal operators, smooth and uniformly smooth spaces (2.1), the duality mapping J, φ, Q_C via (2.3)) and §3 algorithm (3.1)

import Mathlib

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The (normalized) duality mapping of p. 939:
`J x = {v ∈ E* : ⟨x, v⟩ = ‖x‖² = ‖v‖²}`. The pairing `⟨x, v⟩` is `v x`. -/
def dualityMap (x : E) : Set (StrongDual ℝ E) :=
  {v | v x = ‖x‖ ^ 2 ∧ ‖v‖ ^ 2 = ‖x‖ ^ 2}

variable (E) in
/-- `E` is smooth (p. 939): for all `x, y` on the unit sphere the limit (2.1)
`lim_{t → 0} (‖x + t y‖ - ‖x‖) / t` exists (`t` real, `t ≠ 0`, two-sided). -/
def IsSmooth : Prop :=
  ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 →
    ∃ L : ℝ, Tendsto (fun t : ℝ => (‖x + t • y‖ - ‖x‖) / t) (𝓝[≠] (0 : ℝ)) (𝓝 L)

variable (E) in
/-- `E` is uniformly smooth (p. 939): the limit (2.1) is attained uniformly for
`x, y` on the unit sphere, i.e. one `δ` works for all unit `x, y`. -/
def IsUniformlySmooth : Prop :=
  ∃ D : E → E → ℝ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → ∀ t : ℝ, t ≠ 0 → |t| < δ →
      |(‖x + t • y‖ - ‖x‖) / t - D x y| < ε

variable (E) in
/-- `E` is reflexive: the canonical embedding `E → E**` is surjective. -/
def IsReflexive : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E)

/-- A multivalued operator `T : E → 2^{E*}` is monotone (p. 939):
`⟨x₁ - x₂, y₁ - y₂⟩ ≥ 0` whenever `y₁ ∈ T x₁`, `y₂ ∈ T x₂`. -/
def IsMonotoneOp (T : E → Set (StrongDual ℝ E)) : Prop :=
  ∀ x₁ x₂ : E, ∀ y₁ ∈ T x₁, ∀ y₂ ∈ T x₂, 0 ≤ (y₁ - y₂) (x₁ - x₂)

/-- A monotone operator is maximal (p. 939) if its graph is not properly contained in the
graph of any other monotone operator: every monotone `T'` whose graph contains that of `T`
equals `T`. -/
def IsMaximalMonotone (T : E → Set (StrongDual ℝ E)) : Prop :=
  IsMonotoneOp T ∧
    ∀ T' : E → Set (StrongDual ℝ E), IsMonotoneOp T' → (∀ x, T x ⊆ T' x) → T' = T

/-- The zero set `T⁻¹0 = {x ∈ E : 0 ∈ T x}`. -/
def zeros (T : E → Set (StrongDual ℝ E)) : Set E :=
  {x | (0 : StrongDual ℝ E) ∈ T x}

/-- The function `φ(x, y) = ‖x‖² - 2⟨x, J y⟩ + ‖y‖²` of p. 940, for a single-valued
duality map `J`. Note the order: `x` is paired with `J y`. -/
def phi (J : E → StrongDual ℝ E) (x y : E) : ℝ :=
  ‖x‖ ^ 2 - 2 * J y x + ‖y‖ ^ 2

/-- `IsGenProj J C x z` says `z = Q_C x` (p. 940, (2.3)): `z ∈ C` and `z` minimizes
`φ(·, x)` over `C`. -/
def IsGenProj (J : E → StrongDual ℝ E) (C : Set E) (x z : E) : Prop :=
  z ∈ C ∧ ∀ w ∈ C, phi J z x ≤ phi J w x

/-- The half-space `H_n = {z ∈ E : ⟨z - y_n, v_n⟩ ≤ 0}` of (3.1). -/
def halfH (v : ℕ → StrongDual ℝ E) (y : ℕ → E) (n : ℕ) : Set E :=
  {z | v n (z - y n) ≤ 0}

/-- The half-space `W_n = {z ∈ E : ⟨z - x_n, J x_0 - J x_n⟩ ≤ 0}` of (3.1). -/
def halfW (J : E → StrongDual ℝ E) (x : ℕ → E) (n : ℕ) : Set E :=
  {z | (J (x 0) - J (x n)) (z - x n) ≤ 0}

/-- `(x, y, v)` is a run of the algorithm (3.1) (p. 942) with operator `T`, duality map `J`
and parameters `r`, started at `x 0`: for every `n`,
`v_n ∈ T y_n`, `0 = v_n + (1/r_n)(J y_n - J x_n)` and `x_{n+1} = Q_{H_n ∩ W_n} x_0`. -/
def IsHybridRun (T : E → Set (StrongDual ℝ E)) (J : E → StrongDual ℝ E) (r : ℕ → ℝ)
    (x y : ℕ → E) (v : ℕ → StrongDual ℝ E) : Prop :=
  ∀ n : ℕ, v n ∈ T (y n) ∧ v n + (r n)⁻¹ • (J (y n) - J (x n)) = 0 ∧
    IsGenProj J (halfH v y n ∩ halfW J x n) (x 0) (x (n + 1))

end ProximalBanach.Hybrid


