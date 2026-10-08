-- Prove2me | Definitions.Def_MifflinSemismooth_Extremal_Setting
-- name    : MifflinSemismooth_Extremal_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:34:11.757979+00:00
-- url     : https://prove2.me/theorems/37a4894b-393d-4553-83da-7f49ae8399df
-- title:
--   §3, p. 7 — extremal-valued functions: ∂ₓf, the active set A(x), and hypotheses (a)–(e), (d′), (e′)
-- statement:
--   This is the setting of §3 of Mifflin's report. Let $B\subseteq\mathbb R^n$ be open, $T$ a topological space, $U\subseteq T$, $f:\mathbb R^n\times T\to\mathbb R$ and $E:\mathbb R^n\to\mathbb R$. Write $\partial_x f(x,u)$ for the generalized gradient of $f(\cdot,u)$ at $x$ and $f^0_x(x,u;d)$, $f'_x(x,u;d)$ for the generalized and the ordinary directional derivative of $f(\cdot,u)$ at $x$. The **active set** at $x$ is
--   $$A(x)=\{u\in U:\ E(x)=f(x,u)\}.$$
--   The hypotheses of §3 are:
--
--   1. **(a)** $f$ is continuous on $B\times U$ (jointly, in the product topology).
--   2. **(b)** $f(\cdot,u)$ is Lipschitz on $B$ with one constant $K$ for all $u\in U$.
--   3. **(c)** $\partial_x f$ is upper semicontinuous on $B\times U$: if $(x_k,u_k)\to(x,u)$ in $B\times U$ and $g_k\in\partial_x f(x_k,u_k)$, then every accumulation point of $\{g_k\}$ lies in $\partial_x f(x,u)$.
--   4. **(d)** $E(x)=\max\{f(x,u):u\in U\}$ for every $x\in B$, the maximum being attained.
--   5. **(e)** for all $x\in B$, $u\in U$, $d\in\mathbb R^n$: $f'_x(x,u;d)$ exists and equals $f^0_x(x,u;d)$.
--   6. **(d′)** $E(x)=\min\{f(x,u):u\in U\}$ for every $x\in B$, the minimum being attained.
--   7. **(e′)** for all $x\in B$, $u\in U$, $d\in\mathbb R^n$: $f'_x(x,u;d)$ exists and equals $-f^0_x(x,u;-d)$.
--
--   These are the objects of Theorems 1–3: a pointwise maximum (or minimum) $E$ of a compact family of functions $f(\cdot,u)$.
--
--   **Formalization Note.** $f(x,u)$ is curried as `f x u`. $E$ is a given function constrained by (d) or (d′); it is not defined as a supremum, so no default value can enter, and (d) itself forces $U\ne\emptyset$. Upper semicontinuity (c) is stated in the sequential, accumulation-point form in which Proposition 1(d) of the paper glosses the term, not as Mathlib's neighbourhood notion `UpperHemicontinuous`. Hypotheses (e) and (e′) assert existence of the one-sided derivative with the stated value. Sequential compactness of $U$ is not part of these definitions; the theorems take `IsSeqCompact U` as a binder.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 7, §3, hypotheses (a)–(e), (d'), (e') and the set A(x)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
import Definitions.Def_MifflinSemismooth_Extremal_Basic

open Filter Topology

namespace MifflinSemismooth.Extremal

/-- Mifflin (1976), §3, p. 7: `∂ₓf(x, u)`, the generalized gradient of `f(·, u)` at `x`. -/
def partialGenGrad {n : ℕ} {T : Type*} (f : EuclideanSpace ℝ (Fin n) → T → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (u : T) : Set (EuclideanSpace ℝ (Fin n)) :=
  genGrad (fun y => f y u) x

/-- Mifflin (1976), §3, p. 7: the active set `A(x) = {u ∈ U : E(x) = f(x, u)}`. -/
def activeSet {n : ℕ} {T : Type*} (U : Set T) (f : EuclideanSpace ℝ (Fin n) → T → ℝ)
    (E : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : Set T :=
  {u | u ∈ U ∧ E x = f x u}

/-- Mifflin (1976), §3, p. 7, hypothesis (a): `f(x, u)` is continuous for `(x, u) ∈ B × U`. -/
def HypA {n : ℕ} {T : Type*} [TopologicalSpace T] (B : Set (EuclideanSpace ℝ (Fin n)))
    (U : Set T) (f : EuclideanSpace ℝ (Fin n) → T → ℝ) : Prop :=
  ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × T => f p.1 p.2) (B ×ˢ U)

/-- Mifflin (1976), §3, p. 7, hypothesis (b): `f(x, u)` is Lipschitz for `x ∈ B` uniformly
for `u ∈ U`. -/
def HypB {n : ℕ} {T : Type*} (B : Set (EuclideanSpace ℝ (Fin n))) (U : Set T)
    (f : EuclideanSpace ℝ (Fin n) → T → ℝ) : Prop :=
  ∃ K : NNReal, ∀ u ∈ U, LipschitzOnWith K (fun y => f y u) B

/-- Mifflin (1976), §3, p. 7, hypothesis (c): `∂ₓf(x, u)` is uppersemicontinuous for
`(x, u) ∈ B × U`, in the sense of Proposition 1(d) (p. 3): if `(x_k, u_k) → (x, u)` in `B × U`
and `g_k ∈ ∂ₓf(x_k, u_k)`, then every accumulation point of `{g_k}` lies in `∂ₓf(x, u)`. -/
def HypC {n : ℕ} {T : Type*} [TopologicalSpace T] (B : Set (EuclideanSpace ℝ (Fin n)))
    (U : Set T) (f : EuclideanSpace ℝ (Fin n) → T → ℝ) : Prop :=
  ∀ (xs : ℕ → EuclideanSpace ℝ (Fin n)) (us : ℕ → T) (gs : ℕ → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (u : T) (g : EuclideanSpace ℝ (Fin n)),
    (∀ k, xs k ∈ B) → (∀ k, us k ∈ U) → x ∈ B → u ∈ U →
    Tendsto xs atTop (𝓝 x) → Tendsto us atTop (𝓝 u) →
    (∀ k, gs k ∈ partialGenGrad f (xs k) (us k)) →
    MapClusterPt g atTop gs → g ∈ partialGenGrad f x u

/-- Mifflin (1976), §3, p. 7, hypothesis (d): `E(x) = max [f(x, u) : u ∈ U]` for each `x ∈ B`
(the maximum is attained). -/
def HypD {n : ℕ} {T : Type*} (B : Set (EuclideanSpace ℝ (Fin n))) (U : Set T)
    (f : EuclideanSpace ℝ (Fin n) → T → ℝ) (E : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ x ∈ B, IsGreatest ((fun u => f x u) '' U) (E x)

/-- Mifflin (1976), §3, p. 7, hypothesis (e): `f'ₓ(x, u; d) = f⁰ₓ(x, u; d)` for all
`(u, d) ∈ U × ℝⁿ`, at each `x ∈ B`. -/
def HypE {n : ℕ} {T : Type*} (B : Set (EuclideanSpace ℝ (Fin n))) (U : Set T)
    (f : EuclideanSpace ℝ (Fin n) → T → ℝ) : Prop :=
  ∀ x ∈ B, ∀ u ∈ U, QuasidiffAt (fun y => f y u) x

/-- Mifflin (1976), §3, p. 7, hypothesis (d'): `E(x) = min [f(x, u) : u ∈ U]` for each `x ∈ B`
(the minimum is attained). -/
def HypD' {n : ℕ} {T : Type*} (B : Set (EuclideanSpace ℝ (Fin n))) (U : Set T)
    (f : EuclideanSpace ℝ (Fin n) → T → ℝ) (E : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ x ∈ B, IsLeast ((fun u => f x u) '' U) (E x)

/-- Mifflin (1976), §3, p. 7, hypothesis (e'): `f'ₓ(x, u; d) = -f⁰ₓ(x, u; -d)` for all
`(u, d) ∈ U × ℝⁿ`, at each `x ∈ B`. -/
def HypE' {n : ℕ} {T : Type*} (B : Set (EuclideanSpace ℝ (Fin n))) (U : Set T)
    (f : EuclideanSpace ℝ (Fin n) → T → ℝ) : Prop :=
  ∀ x ∈ B, ∀ u ∈ U, ∀ d, HasDirDeriv (fun y => f y u) x d
    (-(ClarkeGradients.Shared.genDirDeriv (fun y => f y u) x (-d)))

end MifflinSemismooth.Extremal


