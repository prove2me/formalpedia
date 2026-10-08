-- Prove2me | Definitions.Def_PDASNewton_Local_Setting
-- name    : PDASNewton_Local_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:07:52.735411+00:00
-- url     : https://prove2.me/theorems/6050b904-bcdc-4174-b2a1-be8b5d6ad7bd
-- title:
--   Definition 1, (3.1), (3.2), §2 algorithm, F and G_F — slanting functions, superlinear convergence, the primal-dual active set step
-- statement:
--   This module fixes the objects of the local convergence analysis of Hintermüller, Ito and Kunisch. The paper writes $A$ for a matrix and calligraphic $\mathcal{A}$, $\mathcal{I}$ for the active and inactive index sets; in Lean the matrix is `A` and the active set is a finite set of indices.
--
--   1. **Slanting function** (Definition 1, p. 2). Let $X, Z$ be real normed spaces, $F : X \to Z$, $U \subseteq X$, and $G : X \to \mathcal{L}(X, Z)$. Then $G$ is a slanting function for $F$ in $U$ if for every $x \in U$
--   $$\lim_{h \to 0} \frac{1}{\|h\|}\,\|F(x+h) - F(x) - G(x+h)h\| = 0. \qquad \text{(A)}$$
--   Boundedness of $\{G(x) : x \in U\}$ is **not** required.
--
--   2. **Superlinear convergence** (proof of Theorem 1.1, p. 3). A sequence $(x^k)$ converges superlinearly to $x^*$ if $x^k \to x^*$ and, for every $\eta > 0$, $\|x^{k+1} - x^*\| \le \eta\,\|x^k - x^*\|$ for all sufficiently large $k$.
--
--   3. **Problem (3.1)** (p. 6). For $A \in \mathbb{R}^{n \times n}$, $f, \psi \in \mathbb{R}^n$ and $c \in \mathbb{R}$, a pair $(y, \lambda)$ solves (3.1) if
--   $$Ay + \lambda = f, \qquad \lambda - \max(0, \lambda + c(y - \psi)) = 0,$$
--   the maximum taken componentwise.
--
--   4. **Active set, step and run** (§2, p. 4). For an iterate $(y, \lambda)$ the active set is $\mathcal{A} = \{i : \lambda_i + c(y - \psi)_i > 0\}$ and the inactive set $\mathcal{I} = \{i : \lambda_i + c(y-\psi)_i \le 0\}$ is its complement. A pair $(y', \lambda')$ follows $(y, \lambda)$ by one step (iii) if $Ay' + \lambda' = f$, $y'_i = \psi_i$ for $i \in \mathcal{A}$ and $\lambda'_i = 0$ for $i \in \mathcal{I}$. A run is a sequence $(y^k, \lambda^k)_{k \ge 0}$ with arbitrary initial data in which every pair follows its predecessor; the stopping option (iv) is not modelled.
--
--   5. **The map $F$** (p. 7). $F : \mathbb{R}^n \times \mathbb{R}^n \to \mathbb{R}^n \times \mathbb{R}^n$,
--   $$F(y, \lambda) = \bigl(Ay + \lambda - f,\ \lambda - \max(0, \lambda + c(y - \psi))\bigr),$$
--   so that (3.1) is $F(y, \lambda) = 0$.
--
--   6. **The candidate slanting function $G_m$ of (3.2)** (p. 6). For a fixed $\delta \in \mathbb{R}^n$, $G_m(y) = \operatorname{diag}(g_1(y_1), \dots, g_n(y_n))$ with $g_i(z) = 0$ if $z < 0$, $1$ if $z > 0$ and $\delta_i$ if $z = 0$.
--
--   7. **The system matrix $G_F$ of (2.4)** (p. 5). At $x = (y, \lambda)$ put $z = \lambda + c(y - \psi)$ and $g = $ the diagonal of $G_m(z)$ with $\delta = 0$. Then
--   $$G_F(x)(\delta y, \delta\lambda) = \bigl(A\,\delta y + \delta\lambda,\ (\delta\lambda_i - g_i\,(\delta\lambda_i + c\,\delta y_i))_i\bigr).$$
--   On the inactive set the second row is $\delta\lambda_i$ and on the active set it is $-c\,\delta y_i$, which is the block matrix (2.4).
--
--   These are the objects of Theorem 1.1, Lemma 3.1, Theorem 3.1 and the equivalence of the semismooth Newton step with the active set step.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with Lean's sup norm, pairs $(y, \lambda)$ carry the max of the two sup norms; in finite dimension every norm gives the same notions in (A) and in superlinear convergence. (A) is stated as `=o[𝓝 0]`, which is the limit of the quotient without dividing by $\|h\|$. $F$ and $G$ are total maps; the paper's domain $D \supseteq U$ plays no role because (A) only looks at points near $U$. The step and run are relations, so they make sense without assuming the step is uniquely solvable.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 2 Definition 1 (A); p. 3 proof of Theorem 1.1; pp. 4–5 §2 algorithm (i)–(iv) and (2.4); p. 6 (3.1), (3.2); p. 7 the map F and G_F

import Mathlib

namespace PDASNewton.Local

open Filter Topology Asymptotics Matrix

/-- Definition 1, p. 2, property (A): `G` is a slanting function for `F` in `U`, i.e. for every
`x ∈ U`, `‖F (x + h) - F x - G (x + h) h‖ / ‖h‖ → 0` as `h → 0`.
`F` and `G` are total; only their values near points of `U` matter. No boundedness of
`{G x : x ∈ U}` is required (the paper drops [CNQ]'s boundedness, p. 2). -/
def IsSlantingFunction {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : X → Z) (G : X → X →L[ℝ] Z) (U : Set X) : Prop :=
  ∀ x ∈ U, (fun h => F (x + h) - F x - G (x + h) h) =o[𝓝 0] (fun h => h)

/-- Superlinear convergence of `x k` to `xstar` (proof of Theorem 1.1, p. 3): convergence, and
for every `η > 0`, eventually `‖x (k+1) - xstar‖ ≤ η ‖x k - xstar‖`. Finite termination
(`x k = xstar` from some `k` on) satisfies it. -/
def ConvergesSuperlinearly {X : Type*} [NormedAddCommGroup X] (x : ℕ → X) (xstar : X) : Prop :=
  Tendsto x atTop (𝓝 xstar) ∧
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ‖x (k + 1) - xstar‖ ≤ η * ‖x k - xstar‖

variable {n : ℕ}

/-- Problem (3.1), p. 6: `A y + λ = f` and `λ - max(0, λ + c (y - ψ)) = 0` componentwise. -/
def IsSolution (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (y lam : Fin n → ℝ) : Prop :=
  A *ᵥ y + lam = f ∧ ∀ i, lam i - max 0 (lam i + c * (y i - ψ i)) = 0

/-- The active set `𝓐 = {i : λᵢ + c (y - ψ)ᵢ > 0}` of step (ii), p. 4.
The inactive set `𝓘 = {i : λᵢ + c (y - ψ)ᵢ ≤ 0}` is its complement. -/
noncomputable def activeSet (c : ℝ) (ψ y lam : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 0 < lam i + c * (y i - ψ i))

/-- One iteration (ii)–(iii) of the primal-dual active set algorithm, p. 4:
from `(y, λ)` to `(y', λ')` with `A y' + λ' = f`, `y' = ψ` on the active set
and `λ' = 0` on the inactive set of `(y, λ)`. -/
def IsStep (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (y lam y' lam' : Fin n → ℝ) : Prop :=
  A *ᵥ y' + lam' = f ∧
  (∀ i, 0 < lam i + c * (y i - ψ i) → y' i = ψ i) ∧
  (∀ i, lam i + c * (y i - ψ i) ≤ 0 → lam' i = 0)

/-- A run of the algorithm from arbitrary initial data `(y 0, lam 0)`: every consecutive pair of
iterates is related by one step. Step (iv)'s "Stop" is not modelled; a run is infinite. -/
def IsRun (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (y lam : ℕ → Fin n → ℝ) : Prop :=
  ∀ k, IsStep A f ψ c (y k) (lam k) (y (k + 1)) (lam (k + 1))

/-- The map `F : ℝⁿ × ℝⁿ → ℝⁿ × ℝⁿ` of p. 7,
`F(y, λ) = (A y + λ - f, λ - max(0, λ + c (y - ψ)))`; (3.1) is `F(y, λ) = 0`. -/
def Fmap (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ) :
    (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
  fun x => (A *ᵥ x.1 + x.2 - f, fun i => x.2 i - max 0 (x.2 i + c * (x.1 i - ψ i)))

/-- The diagonal of `G_m(y)` in (3.2), p. 6, for a fixed `δ ∈ ℝⁿ`:
`gᵢ(yᵢ) = 0` if `yᵢ < 0`, `1` if `yᵢ > 0`, `δᵢ` if `yᵢ = 0`. -/
noncomputable def gm (δ : Fin n → ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if y i < 0 then 0 else if 0 < y i then 1 else δ i

/-- `G_m(y) = diag(g₁(y₁), …, gₙ(yₙ))` of (3.2), p. 6, as a linear map:
`v ↦ (gᵢ(yᵢ) vᵢ)ᵢ`. -/
noncomputable def Gm (δ y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i => gm δ y i • ContinuousLinearMap.proj i)

/-- `G_F(x)`, the system matrix of (2.4), p. 5, at `x = (y, λ)`: the slanting function of `F`
built from `G_m` with `δ = 0` (p. 6). With `z = λ + c (y - ψ)` and `g = gm 0 z`,
`G_F(x) (dy, dl) = (A dy + dl, (dlᵢ - gᵢ (dlᵢ + c dyᵢ))ᵢ)`; on the inactive set (`zᵢ ≤ 0`) the
second row is `dlᵢ`, on the active set (`zᵢ > 0`) it is `-c dyᵢ`. -/
noncomputable def GF (A : Matrix (Fin n) (Fin n) ℝ) (ψ : Fin n → ℝ) (c : ℝ)
    (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  ((LinearMap.toContinuousLinearMap (Matrix.toLin' A)).comp
      (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)) +
    ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)).prod
  (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ) -
    (Gm 0 (x.2 + c • (x.1 - ψ))).comp
      (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ) +
        c • ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)))

end PDASNewton.Local


