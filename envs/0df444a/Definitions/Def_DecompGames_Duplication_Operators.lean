-- Prove2me | Definitions.Def_DecompGames_Duplication_Operators
-- name    : DecompGames_Duplication_Operators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:14.774307+00:00
-- url     : https://prove2.me/theorems/8bc67393-2b63-4411-8dc0-7e36ad3b3bf4
-- title:
--   The projections Λⁱ, Πⁱ (A.1), flows C₁ and ⟨·,·⟩₁ (A.9)–(A.10), the weights Wⁱ (A.11), the gradients δⁱ, δ (A.13), the formula (A.15) for δⁱ*, and D (A.18) (Appendix A, pp. 24–28)
-- statement:
--   This module defines the operators of Appendix A used to prove Proposition 2.10 and Theorem 2.11. Notation is that of the definitions module: $\mu$ a measure vector with product measure $\mu(s)$, normalization $\bar\mu^i$, and $\gamma$ a co-measure vector.
--
--   1. **Projections** (A.1), p. 24. For $h\in C_0$,
--   $$\Lambda^i(h)(s^i,s^{-i})=\sum_{t^i\in S^i}\bar\mu^i(t^i)\,h(t^i,s^{-i}),\qquad \Pi^i=\mathrm{Id}_{C_0}-\Lambda^i,$$
--   and on games $\Lambda(g)=(\Lambda^1(g^1),\dots,\Lambda^n(g^n))$ (A.5), $\Pi(g)=(\Pi^1(g^1),\dots,\Pi^n(g^n))$ (A.6).
--   2. **The subspaces** $\mathsf{NSG}^i\subset C_0$ of functions $h(s^i,s^{-i})=\ell(s^{-i})$ (A.2) and $\mathsf{NoG}^i\subset C_0$ of functions with $\sum_{s^i}\mu^i(s^i)h(s^i,s^{-i})=0$ for every $s^{-i}$ (A.3).
--   3. **Flows** (A.9)–(A.10), p. 26. $C_1$ is the set of skew-symmetric $X:S\times S\to\mathbb R$, $X(s,t)=-X(t,s)$, with $\langle X,Y\rangle_1=\tfrac12\sum_{s,t\in S}\mu(s)\mu(t)X(s,t)Y(s,t)$.
--   4. **Comparable pairs and weights** (A.11). $(s,t)$ is $i$-comparable, $(s,t)\in E^i$, if $i$ is the unique player with $s^i\ne t^i$. With $\mu^{-i}(s^{-i})=\prod_{j\ne i}\mu^j(s^j)$ (2.2), $W^i(s,t)=1/\sqrt{\mu^{-i}(s^{-i})}$ if $(s,t)\in E^i$ and $0$ otherwise.
--   5. **Gradients** (A.13). $\delta^i(h)(s,t)=W^i(s,t)\big(h(t)-h(s)\big)$ and $\delta=\sum_i\delta^i$.
--   6. **Adjoints** (A.15). $\delta^{i*}X(s)=-\sum_{t\in S}\mu(t)W^i(s,t)X(s,t)$ and $\delta^*=\sum_i\delta^{i*}$; Proposition A.3 states that this is the adjoint of $\delta^i$ for $\langle\cdot,\cdot\rangle_1$ and $\langle\cdot,\cdot\rangle_0$.
--   7. **The embedding** (A.18). $D(g)=\sum_{i\in N}\delta^i(\gamma^ig^i)$.
--
--   These operators translate the classes of Definition 2.2 into kernels and images (Proposition A.5) and give the explicit decomposition of Lemma A.11.
--
--   **Formalization Note** Flows are functions `S → S → ℝ`; skew-symmetry is the separate predicate `IsFlow`, assumed where the paper restricts to $C_1$. $\delta^{i*}$ is *defined* by the explicit formula (A.15) rather than as an abstract adjoint. Junk values: $W^i$ uses `Real.sqrt`, which is the true square root because every theorem assumes $\mu>0$; $\bar\mu^i$ divides by $\mu^i(S^i)>0$. The pseudo-inverse $\delta^\dagger$ of p. 30 is not defined (Lemma A.11 is stated through the normal equation instead).
-- source:
--   Abdou, Pnevmatikos, Scarsini & Venel, Decomposition of Games: Some Strategic Considerations, arXiv:1901.06048v2, pp. 24–28, (A.1)–(A.3), (A.5)–(A.6), (A.9)–(A.11), (A.13), (A.15), (A.18); p. 7, (2.2)

import Mathlib
import Definitions.Def_DecompGames_Duplication_Games

namespace DecompGames.Duplication

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
  [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- `Λⁱ` (A.1a): `Λⁱ(h)(sⁱ, s⁻ⁱ) = ∑_{tⁱ ∈ Sⁱ} μ̄ⁱ(tⁱ) h(tⁱ, s⁻ⁱ)`, with the normalized `μ̄ⁱ`. -/
noncomputable def lam (μ : ∀ i, S i → ℝ) (i : ι) (h : (∀ i, S i) → ℝ) : (∀ i, S i) → ℝ :=
  fun s => ∑ a, normalized μ i a * h (Function.update s i a)

/-- `Πⁱ = Id_{C₀} − Λⁱ` (A.1b). -/
noncomputable def proj (μ : ∀ i, S i → ℝ) (i : ι) (h : (∀ i, S i) → ℝ) : (∀ i, S i) → ℝ :=
  fun s => h s - lam μ i h s

/-- `Λ(g) = (Λ¹(g¹), …, Λⁿ(gⁿ))` (A.5). -/
noncomputable def lamGame (μ : ∀ i, S i → ℝ) (g : Game ι S) : Game ι S :=
  fun i => lam μ i (g i)

/-- `Π(g) = (Π¹(g¹), …, Πⁿ(gⁿ))` (A.6). -/
noncomputable def projGame (μ : ∀ i, S i → ℝ) (g : Game ι S) : Game ι S :=
  fun i => proj μ i (g i)

/-- `NSGⁱ ⊂ C₀` (A.2): the functions `h` with `h(sⁱ, s⁻ⁱ) = ℓ(s⁻ⁱ)`, i.e. not depending on `sⁱ`. -/
def IsNSGi (i : ι) (h : (∀ i, S i) → ℝ) : Prop :=
  ∀ (s : ∀ j, S j) (a : S i), h (Function.update s i a) = h s

/-- `NoGⁱ ⊂ C₀` (A.3): the functions `h` with `∑_{sⁱ} μⁱ(sⁱ) h(sⁱ, s⁻ⁱ) = 0` for every `s⁻ⁱ`. -/
def IsNoGi (μ : ∀ i, S i → ℝ) (i : ι) (h : (∀ i, S i) → ℝ) : Prop :=
  ∀ s : ∀ j, S j, ∑ a, μ i a * h (Function.update s i a) = 0

/-- `C₁` (A.9): a flow is a skew-symmetric `X : S × S → ℝ`, `X(s, t) = −X(t, s)`. Flows are
encoded as functions `S → S → ℝ` together with this predicate. -/
def IsFlow (X : (∀ i, S i) → (∀ i, S i) → ℝ) : Prop :=
  ∀ s t, X s t = -X t s

/-- The inner product on flows (A.10): `⟨X, Y⟩₁ = ½ ∑_{s, t ∈ S} μ(s) μ(t) X(s, t) Y(s, t)`. -/
noncomputable def ip1 (μ : ∀ i, S i → ℝ) (X Y : (∀ i, S i) → (∀ i, S i) → ℝ) : ℝ :=
  (1 / 2) * ∑ s, ∑ t, productMeasure μ s * productMeasure μ t * X s t * Y s t

/-- `(s, t)` is an `i`-comparable profile pair (p. 26): `i` is the unique player with `sⁱ ≠ tⁱ`. -/
def IsComparable (i : ι) (s t : ∀ i, S i) : Prop :=
  s i ≠ t i ∧ ∀ j, j ≠ i → s j = t j

/-- `μ⁻ⁱ(s⁻ⁱ) = ∏_{j ≠ i} μʲ(sʲ)` (2.2). -/
def productMeasureExcept (μ : ∀ i, S i → ℝ) (i : ι) (s : ∀ i, S i) : ℝ :=
  ∏ j ∈ univ.erase i, μ j (s j)

open Classical in
/-- `Wⁱ` (A.11): `Wⁱ(s, t) = 1 / √(μ⁻ⁱ(s⁻ⁱ))` if `(s, t) ∈ Eⁱ`, `0` otherwise. -/
noncomputable def W (μ : ∀ i, S i → ℝ) (i : ι) (s t : ∀ i, S i) : ℝ :=
  if IsComparable i s t then 1 / Real.sqrt (productMeasureExcept μ i s) else 0

/-- The partial gradient `δⁱ : C₀ → C₁` (A.13): `δⁱ(h)(s, t) = Wⁱ(s, t)(h(t) − h(s))`. -/
noncomputable def delta (μ : ∀ i, S i → ℝ) (i : ι) (h : (∀ i, S i) → ℝ) :
    (∀ i, S i) → (∀ i, S i) → ℝ :=
  fun s t => W μ i s t * (h t - h s)

/-- The gradient `δ = ∑_{i ∈ N} δⁱ` (p. 26). -/
noncomputable def deltaAll (μ : ∀ i, S i → ℝ) (h : (∀ i, S i) → ℝ) :
    (∀ i, S i) → (∀ i, S i) → ℝ :=
  fun s t => ∑ i, delta μ i h s t

/-- `δⁱ*` given by the formula (A.15): `δⁱ*X(s) = −∑_{t ∈ S} μ(t) Wⁱ(s, t) X(s, t)`.
Proposition A.3 states that this is the adjoint of `δⁱ` for `⟨·,·⟩₁` and `⟨·,·⟩₀`. -/
noncomputable def deltaStar (μ : ∀ i, S i → ℝ) (i : ι) (X : (∀ i, S i) → (∀ i, S i) → ℝ) :
    (∀ i, S i) → ℝ :=
  fun s => -∑ t, productMeasure μ t * W μ i s t * X s t

/-- `δ* = ∑_{i ∈ N} δⁱ*` (p. 27). -/
noncomputable def deltaStarAll (μ : ∀ i, S i → ℝ) (X : (∀ i, S i) → (∀ i, S i) → ℝ) :
    (∀ i, S i) → ℝ :=
  fun s => ∑ i, deltaStar μ i X s

/-- The joint embedding operator `D : C₀ⁿ → C₁` (A.18): `D(g) = ∑_{i ∈ N} δⁱ(γⁱgⁱ)`. -/
noncomputable def embed (μ : ∀ i, S i → ℝ) (γ : ι → (∀ i, S i) → ℝ) (g : Game ι S) :
    (∀ i, S i) → (∀ i, S i) → ℝ :=
  fun s t => ∑ i, delta μ i (coScale γ i (g i)) s t

end DecompGames.Duplication


