-- Prove2me | Definitions.Def_SpreadMatchCircuit_Matching_Encoding
-- name    : SpreadMatchCircuit_Matching_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:37.069864+00:00
-- url     : https://prove2.me/theorems/04752b3f-d4ec-4bfa-ab0b-a3de7f8d2cc4
-- title:
--   The stage schedule, the maps $\mu_\ell,\pi_\ell$, and the decoder of §2.1
-- statement:
--   These are the objects of the proof of the Spread Matching Lemma (§2.1), in the source's order.
--
--   **Schedule.** For $t>1$ and $0<\varepsilon<1/2$ put $h=\lceil\log_2 t\rceil$ (the source writes $q$), and for $i\in[h]$,
--   $$J_i=\lceil 2^{i-h}\log(h/\varepsilon)\rceil,\qquad M=\sum_{i=1}^h J_i\,2^{(h-i)/2},\qquad S_i=\Big\lfloor\frac{\gamma n\,2^{(h-i)/2}}{M}\Big\rfloor.$$
--   A **stage family** is a family of mutually disjoint sets $W_{i,j}\subseteq[n]$, $i\in[h]$, $j\in[J_i]$, with $|W_{i,j}|=S_i$. The pairs $(i,j)$ are listed in increasing $i$, then increasing $j$; if $(i,j)$ is at location $\ell$ (numbered from $1$), then $W_\ell=W_{i,j}$, and $\bar W_\ell=\bigcup_{v\le\ell}W_v$ with $\bar W_0=\emptyset$. The thresholds at stage $\ell$ are $2^{h-i}$ and $2^{h-i+1}$.
--
--   **The maps.** Fix an ordering of all sets of edges and let $\mathcal Z$ be a family of matchings. Set $\pi_0(z)=z$ and
--   $$\pi_\ell(z)=\pi_{\ell-1}(\mu_\ell(z))\setminus G(\bar W_\ell),$$
--   where $\mu_\ell(z)$ is the first $u\in\mathcal Z$ minimizing $|\pi_{\ell-1}(u)\setminus G(\bar W_\ell)|$ subject to $\pi_{\ell-1}(u)\subseteq G(\bar W_\ell)\cup\pi_{\ell-1}(z)$ and $|\pi_{\ell-1}(u)|\le 2^{h-i+1}$, and $\mu_\ell(z)=z$ if no $u$ meets the constraints.
--
--   **The event.** $E_{\ell,a}$ holds at $z$, for $2^{h-i}\le a\le 2^{h-i+1}$, if $|\pi_{\ell-1}(z)|\le 2^{h-i+1}$ and $|\pi_\ell(z)|=a$.
--
--   **Consistency.** For $S\subseteq[n]$ and $f:[n]\to[a]$, the pair is consistent if (1) each edge $\{u,v\}$ of $\pi_{\ell-1}(\mu_\ell(z))$ either (a) has $\{u,v\}\subseteq S$, $\{u,v\}\in\pi_\ell(z)$ and $f(u)=f(v)$, or (b) has $\{u,v\}\cap S=\emptyset$ and $\{u,v\}\notin\pi_\ell(z)$; and (2) $f(u)\ne f(v)$ whenever $u,v$ belong to distinct edges of $\pi_\ell(z)$.
--
--   **The decoder.** For $T=W_\ell\cup V(\pi_\ell(z))$, the matching $z'$ is the first $u\in\mathcal Z$ with $|\pi_{\ell-1}(u)|\le 2^{h-i+1}$, $\pi_{\ell-1}(u)\subseteq G(\bar W_{\ell-1}\cup T)$, and such that every edge $\{v,w\}$ of $\pi_{\ell-1}(u)$ either (a) has $\{v,w\}\subseteq S$, $f(v)=f(w)$, $\{v,w\}\subseteq T$, or (b) has $\{v,w\}\cap S=\emptyset$.
--
--   Together these turn the encoding argument of §2.1 into functions of the sampled sets, so that its combinatorial steps can be stated exactly.
--
--   **Formalization Note** $\log_2$ is used for $h$, because the thresholds are dyadic, and the natural logarithm for $J_i$; the source leaves the base open and only universal constants depend on it. The ordering is an arbitrary `LinearOrder`, which covers the source's lexicographic order. The decoder has the default value $\emptyset$ when no $u$ qualifies; under the source's assumptions $\mu_\ell(z)$ qualifies, so the default is not reached. `stageAt` has a default value for $\ell$ outside $1,\dots,$`numStages`; statements restrict $\ell$ to that range. The condition $G(\bar W_{\ell-1}\cup T)$ is the source's $G(\bar W_\ell\cup V(\pi_\ell(z)))$, written so that $z'$ depends on $W_\ell$ and $V(\pi_\ell(z))$ only through $T$.
-- source:
--   Anup Rao, STOC 2027 submission #299 (October 2026), pp. 6–9, §2.1 (parameters p. 6; π, μ p. 7; E, consistency p. 8; decoder p. 9)

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_Graphs

namespace SpreadMatchCircuit.Matching

open Finset

/-! ### Choice under a fixed ordering of all matchings -/

/-- The first element of `F` under the fixed ordering `ord`, or `d` if `F` is empty. -/
noncomputable def firstOf {α : Type} (ord : LinearOrder α) (F : Finset α) (d : α) : α :=
  if h : F.Nonempty then @Finset.min' α ord F h else d

/-! ### The schedule of §2.1 (the source writes `q` for `stageCount`) -/

/-- `q = ⌈log₂ t⌉`. -/
noncomputable def stageCount (t : ℝ) : ℕ := ⌈Real.logb 2 t⌉₊

/-- `J_i = ⌈2^{i-q} log(q/ε)⌉`. -/
noncomputable def stageReps (t ε : ℝ) (i : ℕ) : ℕ :=
  ⌈(2 : ℝ) ^ ((i : ℤ) - (stageCount t : ℤ)) * Real.log ((stageCount t : ℝ) / ε)⌉₊

/-- `M = ∑_{i=1}^q J_i 2^{(q-i)/2}`. -/
noncomputable def stageWeight (t ε : ℝ) : ℝ :=
  ∑ i ∈ Icc 1 (stageCount t),
    (stageReps t ε i : ℝ) * (2 : ℝ) ^ (((stageCount t : ℝ) - (i : ℝ)) / 2)

/-- `S_i = ⌊γ n 2^{(q-i)/2} / M⌋`. -/
noncomputable def stageSize (n : ℕ) (t ε γ : ℝ) (i : ℕ) : ℕ :=
  ⌊γ * (n : ℝ) * (2 : ℝ) ^ (((stageCount t : ℝ) - (i : ℝ)) / 2) / stageWeight t ε⌋₊

/-- The pairs `(i, j)`, `i ∈ [q]`, `j ∈ [J_i]`, in the source's sampling order
`(1,1), (1,2), …, (2,1), …`. -/
noncomputable def stages (t ε : ℝ) : List (ℕ × ℕ) :=
  (List.range (stageCount t)).flatMap fun i' =>
    (List.range (stageReps t ε (i' + 1))).map fun j' => (i' + 1, j' + 1)

/-- The total number of stages. Stages are numbered `1, …, numStages t ε`. -/
noncomputable def numStages (t ε : ℝ) : ℕ := (stages t ε).length

/-- The pair `(i, j)` whose location in the sampling order is `ℓ`, i.e. `k(i, j) = ℓ`, for
`1 ≤ ℓ ≤ numStages t ε`. -/
noncomputable def stageAt (t ε : ℝ) (ℓ : ℕ) : ℕ × ℕ := (stages t ε).getD (ℓ - 1) (0, 0)

/-- The upper size threshold `2^{q-i+1}` at stage `ℓ = k(i, j)`. -/
noncomputable def stageBudget (t ε : ℝ) (ℓ : ℕ) : ℕ :=
  2 ^ (stageCount t - (stageAt t ε ℓ).1 + 1)

/-- The lower size threshold `2^{q-i}` at stage `ℓ = k(i, j)`. -/
noncomputable def stageFloor (t ε : ℝ) (ℓ : ℕ) : ℕ :=
  2 ^ (stageCount t - (stageAt t ε ℓ).1)

variable {n : ℕ}

/-- The family `{W_{i,j}}`: mutually disjoint subsets of `[n]` with `|W_{i,j}| = S_i`, for
`i ∈ [q]`, `j ∈ [J_i]`. -/
def IsStageFamily (t ε γ : ℝ) (W : ℕ → ℕ → Finset (Fin n)) : Prop :=
  (∀ p ∈ stages t ε, (W p.1 p.2).card = stageSize n t ε γ p.1) ∧
  (∀ p ∈ stages t ε, ∀ p' ∈ stages t ε, p ≠ p' → Disjoint (W p.1 p.2) (W p'.1 p'.2))

/-- `W_ℓ = W_{i,j}` for `ℓ = k(i, j)`. -/
noncomputable def flatW (t ε : ℝ) (W : ℕ → ℕ → Finset (Fin n)) (ℓ : ℕ) : Finset (Fin n) :=
  W (stageAt t ε ℓ).1 (stageAt t ε ℓ).2

/-- `W̄_ℓ = ⋃_{v ≤ ℓ} W_v`, with `W̄_0 = ∅`. -/
noncomputable def flatWbar (t ε : ℝ) (W : ℕ → ℕ → Finset (Fin n)) (ℓ : ℕ) : Finset (Fin n) :=
  (Icc 1 ℓ).biUnion (flatW t ε W)

/-! ### The maps `μ_ℓ` and `π_ℓ` -/

open scoped Classical in
/-- `μ_ℓ(z)`, given `prev = π_{ℓ-1}`, `Gℓ = G(W̄_ℓ)` and `b = 2^{q-i+1}`: the first matching `u`
of `𝒵` under `ord` that minimizes `|π_{ℓ-1}(u) \ G(W̄_ℓ)|` subject to
`π_{ℓ-1}(u) ⊆ G(W̄_ℓ) ∪ π_{ℓ-1}(z)` and `|π_{ℓ-1}(u)| ≤ b`; and `z` if no matching meets the
constraints. -/
noncomputable def chooseMu (ord : LinearOrder (Finset (Edge n))) (𝒵 : Finset (Finset (Edge n)))
    (prev : Finset (Edge n) → Finset (Edge n)) (Gℓ : Finset (Edge n)) (b : ℕ)
    (z : Finset (Edge n)) : Finset (Edge n) :=
  let F := 𝒵.filter fun u => prev u ⊆ Gℓ ∪ prev z ∧ (prev u).card ≤ b
  firstOf ord (F.filter fun u => ∀ v ∈ F, (prev u \ Gℓ).card ≤ (prev v \ Gℓ).card) z

/-- `π_ℓ` for the schedule of `t, ε` and the family `W`: `π_0(z) = z` and
`π_ℓ(z) = π_{ℓ-1}(μ_ℓ(z)) \ G(W̄_ℓ)`. -/
noncomputable def residual (ord : LinearOrder (Finset (Edge n))) (𝒵 : Finset (Finset (Edge n)))
    (t ε : ℝ) (W : ℕ → ℕ → Finset (Fin n)) : ℕ → Finset (Edge n) → Finset (Edge n)
  | 0 => fun z => z
  | ℓ + 1 => fun z =>
      residual ord 𝒵 t ε W ℓ
          (chooseMu ord 𝒵 (residual ord 𝒵 t ε W ℓ) (incident (flatWbar t ε W (ℓ + 1)))
            (stageBudget t ε (ℓ + 1)) z) \ incident (flatWbar t ε W (ℓ + 1))

/-- `μ_ℓ` for `ℓ ≥ 1`, built from `π_{ℓ-1}`. -/
noncomputable def stageMu (ord : LinearOrder (Finset (Edge n))) (𝒵 : Finset (Finset (Edge n)))
    (t ε : ℝ) (W : ℕ → ℕ → Finset (Fin n)) (ℓ : ℕ) (z : Finset (Edge n)) : Finset (Edge n) :=
  chooseMu ord 𝒵 (residual ord 𝒵 t ε W (ℓ - 1)) (incident (flatWbar t ε W ℓ))
    (stageBudget t ε ℓ) z

/-! ### The event `E_{ℓ,a}`, consistency, and the decoder -/

/-- The event `E_{ℓ,a}` at the matching `z`, for `2^{q-i} ≤ a ≤ 2^{q-i+1}`:
`|π_{ℓ-1}(z)| ≤ 2^{q-i+1}` and `|π_ℓ(z)| = a`. -/
def EventE (ord : LinearOrder (Finset (Edge n))) (𝒵 : Finset (Finset (Edge n)))
    (t ε : ℝ) (W : ℕ → ℕ → Finset (Fin n)) (ℓ a : ℕ) (z : Finset (Edge n)) : Prop :=
  stageFloor t ε ℓ ≤ a ∧ a ≤ stageBudget t ε ℓ ∧
  (residual ord 𝒵 t ε W (ℓ - 1) z).card ≤ stageBudget t ε ℓ ∧
  (residual ord 𝒵 t ε W ℓ z).card = a

/-- The event `D_{S,f}`: the pair `(W̄_ℓ, z)` is consistent with `S ⊆ [n]` and `f : [n] → [a]`.
(1) Every edge of `π_{ℓ-1}(μ_ℓ(z))` either (a) lies in `S`, belongs to `π_ℓ(z)` and has
`f(u) = f(v)`, or (b) misses `S` and does not belong to `π_ℓ(z)`. (2) Vertices of distinct edges
of `π_ℓ(z)` receive different `f`-values. -/
def IsConsistent (ord : LinearOrder (Finset (Edge n))) (𝒵 : Finset (Finset (Edge n)))
    (t ε : ℝ) (W : ℕ → ℕ → Finset (Fin n)) (ℓ : ℕ) (z : Finset (Edge n))
    {a : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin a) : Prop :=
  (∀ e ∈ residual ord 𝒵 t ε W (ℓ - 1) (stageMu ord 𝒵 t ε W ℓ z),
      (endpoints e ⊆ S ∧ e ∈ residual ord 𝒵 t ε W ℓ z ∧
        ∀ u ∈ endpoints e, ∀ v ∈ endpoints e, f u = f v) ∨
      (Disjoint (endpoints e) S ∧ e ∉ residual ord 𝒵 t ε W ℓ z)) ∧
  (∀ e ∈ residual ord 𝒵 t ε W ℓ z, ∀ e' ∈ residual ord 𝒵 t ε W ℓ z, e ≠ e' →
      ∀ u ∈ endpoints e, ∀ v ∈ endpoints e', f u ≠ f v)

open scoped Classical in
/-- The decoded matching `z'`, a function of `T = W_ℓ ∪ V(π_ℓ(z))`, `S`, `f` and the earlier sets:
the first `u ∈ 𝒵` under `ord` such that (1) `|π_{ℓ-1}(u)| ≤ 2^{q-i+1}` and
`π_{ℓ-1}(u) ⊆ G(W̄_{ℓ-1} ∪ T)`, and (2) every edge `{v, w}` of `π_{ℓ-1}(u)` either (a) has
`{v, w} ⊆ S`, `f(v) = f(w)` and `{v, w} ⊆ T`, or (b) misses `S`. If no such `u` exists the value
is `∅`. -/
noncomputable def decode (ord : LinearOrder (Finset (Edge n))) (𝒵 : Finset (Finset (Edge n)))
    (t ε : ℝ) (W : ℕ → ℕ → Finset (Fin n)) (ℓ : ℕ)
    (T : Finset (Fin n)) {a : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin a) : Finset (Edge n) :=
  firstOf ord
    (𝒵.filter fun u =>
      (residual ord 𝒵 t ε W (ℓ - 1) u).card ≤ stageBudget t ε ℓ ∧
      residual ord 𝒵 t ε W (ℓ - 1) u ⊆ incident (flatWbar t ε W (ℓ - 1) ∪ T) ∧
      ∀ e ∈ residual ord 𝒵 t ε W (ℓ - 1) u,
        (endpoints e ⊆ S ∧ (∀ v ∈ endpoints e, ∀ w ∈ endpoints e, f v = f w) ∧ endpoints e ⊆ T) ∨
        Disjoint (endpoints e) S)
    ∅

end SpreadMatchCircuit.Matching


