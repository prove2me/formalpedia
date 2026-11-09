-- Prove2me | Definitions.Def_NadlerCLS_PNInstance
-- name    : NadlerCLS_PNInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:56:50.217709+00:00
-- url     : https://prove2.me/theorems/499e9e7e-284f-4b64-9395-bf4c36dda4d5
-- title:
--   Instances of $\beta$-Projected-Nadler
-- statement:
--   An instance of $\beta$-Projected-Nadler on $X=[0,1]^n$ consists of two well-behaved circuits and six rationals:
--
--   1. a projection circuit $\Pi(x,y)$ with $2n$ inputs and $n$ outputs, intended as an approximate nearest-point projection from $y$ to a set $F(x)$;
--   2. a metric circuit $d(a,b)$ with $2n$ inputs and one output;
--   3. parameters $\varepsilon_1,\varepsilon_2,L_P,L_d,D>0$ and $k\in(0,1)$ with $0<\varepsilon_2<\varepsilon_1(1-k)$.
--
--   The outputs are clipped to the intended ranges: $\Pi(x,y)\in[0,1]^n$ coordinatewise and $d(a,b)\in[0,D]$. Set $P(x)=\Pi(x,x)$ and $r(x)=d(x,P(x))$.
--
--   The **metric and completeness promise** says that on $X$ the clipped $d$ is a metric ($d(x,y)=0\iff x=y$, symmetry, triangle inequality) and that $(X,d)$ is complete: every $d$-Cauchy sequence in $X$ converges in $d$ to a point of $X$.
--
--   **Formalization Note** The input format `PNInstance.Valid` contains the numerical promise $0<\varepsilon_2<\varepsilon_1(1-k)$, which Remark 3.1 calls part of the input format; the metric and completeness promise is the separate predicate `PNInstance.MetricPromise`. The dimension $n$ is a parameter, not an instance field. `encPN` is the binary code of an instance.
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Definition 1, p.9; Remark 3.1, p.9; Remark C.7, p.38 (clipping)

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Quadratics
import Definitions.Def_NadlerCLS_Circ

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash Filter Topology

/-- An **instance of β-Projected-Nadler** on `X = [0, 1]ⁿ` (Xiong–Vlatakis-Gkaragkounis, *On the
Complexity of Finding Fixed Points for Set-Valued Contractions*, arXiv:2609.14101, held version of
2026-11-03, sha256 1fcc5a02…6dc485, Definition 1, p.9: "An instance consists of well-behaved
circuits Π, d, … and rational parameters ε1, ε2, LP, Ld, D > 0, and k ∈ (0, 1)").

`proj` is the projection circuit Π (inputs `(x, y)`, `n + n` of them; `n` outputs), `metric` the
metric circuit d (inputs `(a, b)`; one output), and `ε₁ ε₂ LP Ld D k` the rational parameters.

**Formalization Note** The dimension `n` is a parameter of the problem, not an instance field. -/
structure PNInstance (n : ℕ) where
  proj : Circ
  metric : Circ
  ε₁ : ℚ
  ε₂ : ℚ
  LP : ℚ
  Ld : ℚ
  D : ℚ
  k : ℚ

variable {n : ℕ}

/-- The **input format** of β-Projected-Nadler (Definition 1, p.9, and Remark 3.1, p.9: "The
numerical promise 0 < ε2 < ε1(1 − k) can be checked in polynomial time; therefore it can be
considered part of the input format"): Π and d are well-behaved circuits of the right arities,
`ε₁, ε₂, LP, Ld, D > 0`, `0 < k < 1`, and `ε₂ < ε₁ (1 − k)`. -/
def PNInstance.Valid (I : PNInstance n) : Prop :=
  I.proj.Valid (n + n) n ∧ I.metric.Valid (n + n) 1 ∧
  0 < I.ε₁ ∧ 0 < I.ε₂ ∧ 0 < I.LP ∧ 0 < I.Ld ∧ 0 < I.D ∧ 0 < I.k ∧ I.k < 1 ∧
  I.ε₂ < I.ε₁ * (1 - I.k)

/-- The projection `Π(x, y)`, clipped coordinatewise to `[0, 1]` (Remark C.7, p.38: "The ranges
P(X) ⊆ X and d(X, X) ⊆ [0, D] can be enforced syntactically by coordinate-wise clipping with min
and max gates"). -/
noncomputable def PNInstance.Pi (I : PNInstance n) (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => clip (I.proj.eval (Fin.append x y) i)

/-- The metric `d(a, b)`, clipped to `[0, D]` (Definition 1: "d : X × X → [0, D]"; Remark C.7). -/
noncomputable def PNInstance.dist (I : PNInstance n) (a b : Fin n → ℝ) : ℝ :=
  max 0 (min (I.D : ℝ) (I.metric.eval (Fin.append a b) (0 : Fin 1)))

/-- The diagonal map `P(x) = Π(x, x)` (Definition 1, p.9). -/
noncomputable def PNInstance.P (I : PNInstance n) (x : Fin n → ℝ) : Fin n → ℝ := I.Pi x x

/-- The residual `r(x) = d(x, P(x))` (Definition 1, p.9). -/
noncomputable def PNInstance.r (I : PNInstance n) (x : Fin n → ℝ) : ℝ := I.dist x (I.P x)

/-- The **metric and completeness promise** of Definition 1 (p.9: "(X, d) is a complete metric
space"; metric and completeness as on p.7): on `X = [0, 1]ⁿ`, `d(x, y) = 0 ↔ x = y`, `d` is
symmetric, satisfies the triangle inequality, and every `d`-Cauchy sequence in `X` converges in
`d` to a point of `X`. Nonnegativity holds by the clipping. -/
def PNInstance.MetricPromise (I : PNInstance n) : Prop :=
  (∀ x y : Fin n → ℝ, InCube x → InCube y → (I.dist x y = 0 ↔ x = y)) ∧
  (∀ x y : Fin n → ℝ, InCube x → InCube y → I.dist x y = I.dist y x) ∧
  (∀ x y z : Fin n → ℝ, InCube x → InCube y → InCube z →
    I.dist x z ≤ I.dist x y + I.dist y z) ∧
  (∀ u : ℕ → Fin n → ℝ, (∀ a, InCube (u a)) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ a ≥ N, ∀ b ≥ N, I.dist (u a) (u b) < ε) →
    ∃ x, InCube x ∧ Tendsto (fun a => I.dist (u a) x) atTop (𝓝 0))

/-- The binary code of an instance: the two circuits, then the six rationals. -/
def encPN (I : PNInstance n) : List Bool :=
  encCirc I.proj ++ encCirc I.metric ++ encRat I.ε₁ ++ encRat I.ε₂ ++ encRat I.LP ++
    encRat I.Ld ++ encRat I.D ++ encRat I.k

end NadlerCLS


