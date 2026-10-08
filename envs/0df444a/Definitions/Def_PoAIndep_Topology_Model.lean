-- Prove2me | Definitions.Def_PoAIndep_Topology_Model
-- name    : PoAIndep_Topology_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:10:31.60499+00:00
-- url     : https://prove2.me/theorems/01e617c5-e130-4978-b8ea-48bd8600697b
-- title:
--   §2–§5.1, pp. 5–18 — networks, simple paths, multicommodity flows, cost, Nash flows (Def. 2.1), standard latencies and marginal costs (Defs. 2.5–2.6), standard classes, anarchy value (Defs. 3.1–3.3)
-- statement:
--   This file fixes the model of nonatomic selfish routing used throughout the mission.
--
--   **Networks and paths.** A network is a finite directed multigraph $G=(V,E)$: every edge $e\in E$ has a tail $\mathrm{src}(e)$ and a head $\mathrm{tgt}(e)$, and parallel edges are allowed. A *simple $u$–$v$ path* is a nonempty sequence of edges $e_1,\dots,e_m$ with $\mathrm{src}(e_1)=u$, $\mathrm{tgt}(e_j)=\mathrm{src}(e_{j+1})$ and $\mathrm{tgt}(e_m)=v$, whose vertex sequence $u,\mathrm{tgt}(e_1),\dots,\mathrm{tgt}(e_m)$ has no repetition. In particular a simple path uses each edge at most once.
--
--   **Latency functions.** A *latency function* is a function $\ell:[0,\infty)\to\mathbb R$ that is nonnegative, differentiable and nondecreasing on $[0,\infty)$. It is *standard* (Definition 2.5) if $x\,\ell(x)$ is convex on $[0,\infty)$. Its *marginal cost function* (Definition 2.6) is
--   $$\ell^*(x)=\frac{d}{dx}\bigl(x\,\ell(x)\bigr),\qquad x\ge 0,$$
--   the derivative being one-sided at $x=0$.
--
--   **Instances.** An instance $(G,r,\ell)$ consists of a network, $k$ commodities with source $s_i$, sink $t_i$ and rate $r_i>0$, with at least one simple $s_i$–$t_i$ path for each $i$ (the paper's $\mathcal P_i\neq\emptyset$), and a latency function $\ell_e$ on every edge.
--
--   **Flows.** A flow $f$ assigns to each commodity $i$ and each simple $s_i$–$t_i$ path $P$ an amount $f^i_P\ge0$, only finitely many nonzero. It is *feasible* if $\sum_P f^i_P=r_i$ for every $i$. The edge flow is $f_e=\sum_i\sum_{P\ni e}f^i_P$, the path latency is $\ell_P(f)=\sum_{e\in P}\ell_e(f_e)$, and the cost is the path sum
--   $$C(f)=\sum_i\sum_P \ell_P(f)\,f^i_P .$$
--
--   **Nash flows** (Definition 2.1). A flow $f$ is at Nash equilibrium if for every commodity $i$, all simple $s_i$–$t_i$ paths $P_1,P_2$ with $f^i_{P_1}>0$ and every $\delta\in(0,f^i_{P_1}]$, the flow $\tilde f$ obtained by moving $\delta$ units of commodity $i$ from $P_1$ to $P_2$ satisfies $\ell_{P_1}(f)\le\ell_{P_2}(\tilde f)$.
--
--   **Classes and the anarchy value.** A class $\mathcal L$ of latency functions is *standard* (Definition 3.1) if it contains a function that is nonzero somewhere on $[0,\infty)$ and all its members are standard. It *contains the constants* if it contains $\ell(x)=c$ for every $c>0$, and it is *diverse* (Definition 4.3) if for every $c>0$ it contains some $\ell$ with $\ell(0)=c$. The anarchy value of a latency function (Definition 3.2) is
--   $$\alpha(\ell)=\sup_{r>0:\ \ell(r)>0}\bigl[\lambda\mu+(1-\lambda)\bigr]^{-1},\qquad \lambda\in[0,1],\ \ell^*(\lambda r)=\ell(r),\ \mu=\frac{\ell(\lambda r)}{\ell(r)},$$
--   and the anarchy value of a class (Definition 3.3) is $\alpha(\mathcal L)=\sup_{0\neq\ell\in\mathcal L}\alpha(\ell)\in[1,\infty]$.
--
--   **Special networks.** $G_m$ is the network with one source, one sink and $m\ge1$ parallel edges from source to sink, carrying one commodity; $G_2$ is the case $m=2$. Finally, $\mathcal L_p$ is the set of polynomials of degree at most $p$ with nonnegative coefficients (§5.1).
--
--   These objects are the vocabulary of every statement of the mission: the goal compares Nash and minimum-cost flows across all networks, and the two-link network $G_2$ is an instance of the same general model, so statements about all instances apply to it verbatim.
--
--   **Formalization Note.** Latency functions are functions $\mathbb R\to\mathbb R$ of which only the values on $[0,\infty)$ matter; differentiability and monotonicity are required on $[0,\infty)$ only, and $\ell^*$ is the derivative within $[0,\infty)$. A flow stores one finitely supported path flow per commodity (the paper's $f:\mathcal P\to\mathbb R^+$ coincides with this whenever the source–sink pairs are distinct). Paths are nonempty, so a commodity with $s_i=t_i$ has no path and is excluded by the nonemptiness assumption. In Definition 2.1 the moved flow is written with finitely supported functions; when $P_1=P_2$ it equals $f$ and the condition is trivial, as on the page. The anarchy values take values in $[0,\infty]$; $\alpha(\ell)$ is the supremum over all admissible pairs $(r,\lambda)$, which equals the page's value because the page notes that $[\lambda\mu+(1-\lambda)]^{-1}$ does not depend on the choice of $\lambda$. The supremum in $\alpha(\mathcal L)$ runs over all of $\mathcal L$; a function vanishing on $(0,\infty)$ contributes the empty supremum $0$, so this equals the supremum over nonzero members.
-- source:
--   Roughgarden, The price of anarchy is independent of the network topology (journal-version manuscript, Dec. 23, 2002), pp. 5–18: §2.1 (p. 5), Definition 2.1 (p. 5), Definitions 2.5, 2.6 (p. 6), Definitions 3.1, 3.2 (p. 9), Definition 3.3 (p. 10), Lemma 4.1 (G₂, p. 13), Definition 4.3 and Lemma 4.4 (G_m, p. 14), §5.1 (L_p, p. 18); constants: p. 3

import Mathlib

namespace PoAIndep.Topology

open scoped ENNReal

/-- A (simple, nonempty) `u`-`v` path in the directed multigraph with edge set `E`, vertex set
`V`, and edge endpoints `src`, `tgt`: a nonempty list of edges `e₁, …, eₘ` with `src e₁ = u`,
`tgt eⱼ = src eⱼ₊₁`, `tgt eₘ = v`, whose vertex sequence `u, tgt e₁, …, tgt eₘ` has no repeated
vertex. (Paper, §2.1, p. 5: "the set of (simple) sᵢ-tᵢ paths".) -/
def IsSimplePath {V E : Type} (src tgt : E → V) (p : List E) (u v : V) : Prop :=
  p ≠ [] ∧ List.IsChain (fun e e' => tgt e = src e') p ∧ p.head?.map src = some u ∧
    p.getLast?.map tgt = some v ∧ (u :: p.map tgt).Nodup

/-- A latency function (§2.1, p. 5): nonnegative, differentiable and nondecreasing on `[0, ∞)`.
Values on `(-∞, 0)` are irrelevant. -/
def IsLatency (ℓ : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ x → 0 ≤ ℓ x) ∧ DifferentiableOn ℝ ℓ (Set.Ici 0) ∧ MonotoneOn ℓ (Set.Ici 0)

/-- Definition 2.5 (p. 6): `ℓ` is standard if `x · ℓ(x)` is convex on `[0, ∞)`. -/
def IsStandard (ℓ : ℝ → ℝ) : Prop :=
  IsLatency ℓ ∧ ConvexOn ℝ (Set.Ici 0) (fun x => x * ℓ x)

/-- Definition 2.6 (p. 6): the marginal cost function `ℓ* = d/dx (x · ℓ(x))`, taken within
`[0, ∞)` (one-sided at `0`). -/
noncomputable def marginalCost (ℓ : ℝ → ℝ) (x : ℝ) : ℝ :=
  derivWithin (fun y => y * ℓ y) (Set.Ici 0) x

/-- An instance `(G, r, ℓ)` (§2.1, p. 5): a finite directed multigraph `G` (parallel edges
allowed), `k` commodities with source `s i`, sink `t i` and rate `r i > 0`, at least one simple
`s i`-`t i` path per commodity, and a latency function on each edge. -/
structure Instance (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] where
  src : E → V
  tgt : E → V
  k : ℕ
  s : Fin k → V
  t : Fin k → V
  r : Fin k → ℝ
  ℓ : E → ℝ → ℝ
  r_pos : ∀ i, 0 < r i
  paths_nonempty : ∀ i, ∃ p, IsSimplePath src tgt p (s i) (t i)
  latency : ∀ e, IsLatency (ℓ e)

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- A flow assigns to each commodity `i` a finitely supported function on paths
(`f i P` is the flow of commodity `i` on path `P`). -/
abbrev Flow (I : Instance V E) : Type := Fin I.k → (List E →₀ ℝ)

/-- `f` is a flow (§2.1): nonnegative, and commodity `i` uses only simple `s i`-`t i` paths. -/
def IsFlow (I : Instance V E) (f : Flow I) : Prop :=
  ∀ i, (∀ P, 0 ≤ f i P) ∧ ∀ P ∈ (f i).support, IsSimplePath I.src I.tgt P (I.s i) (I.t i)

/-- Feasibility (§2.1): commodity `i` routes exactly `r i` units. -/
def IsFeasible (I : Instance V E) (f : Flow I) : Prop :=
  ∀ i, (f i).sum (fun _ x => x) = I.r i

/-- The edge flow `f_e = Σ_{P ∋ e} f_P`, summed over all commodities. -/
noncomputable def edgeFlow (I : Instance V E) (f : Flow I) (e : E) : ℝ :=
  ∑ i, (f i).sum (fun P x => if e ∈ P then x else 0)

/-- The path latency `ℓ_P(f) = Σ_{e ∈ P} ℓ_e(f_e)`. -/
noncomputable def pathLatency (I : Instance V E) (f : Flow I) (P : List E) : ℝ :=
  (P.map fun e => I.ℓ e (edgeFlow I f e)).sum

/-- The cost `C(f) = Σ_P ℓ_P(f) f_P` (path form, §2.1). -/
noncomputable def cost (I : Instance V E) (f : Flow I) : ℝ :=
  ∑ i, (f i).sum (fun P x => pathLatency I f P * x)

/-- Definition 2.1 (p. 5): `f` is at Nash equilibrium if for every commodity `i`, simple
`s i`-`t i` paths `P₁, P₂` with `f_{P₁} > 0`, and `δ ∈ (0, f_{P₁}]`, moving `δ` units of
commodity `i` from `P₁` to `P₂` gives a flow `f̃` with `ℓ_{P₁}(f) ≤ ℓ_{P₂}(f̃)`. -/
def IsNashFlow (I : Instance V E) (f : Flow I) : Prop :=
  ∀ (i : Fin I.k) (P₁ P₂ : List E),
    IsSimplePath I.src I.tgt P₁ (I.s i) (I.t i) →
    IsSimplePath I.src I.tgt P₂ (I.s i) (I.t i) →
    0 < f i P₁ → ∀ δ ∈ Set.Ioc 0 (f i P₁),
      pathLatency I f P₁ ≤
        pathLatency I (Function.update f i (f i - Finsupp.single P₁ δ + Finsupp.single P₂ δ)) P₂

/-- Definition 3.1 (p. 9): a standard class contains a function that is nonzero somewhere on
`[0, ∞)`, and all its functions are standard. -/
def IsStandardClass (L : Set (ℝ → ℝ)) : Prop :=
  (∃ ℓ ∈ L, ∃ x, 0 ≤ x ∧ ℓ x ≠ 0) ∧ ∀ ℓ ∈ L, IsStandard ℓ

/-- The class contains every constant function `ℓ(x) = c` with `c > 0` (p. 3). -/
def ContainsConstants (L : Set (ℝ → ℝ)) : Prop :=
  ∀ c : ℝ, 0 < c → (fun _ => c) ∈ L

/-- Definition 4.3 (p. 14): for every `c > 0` the class has a function with `ℓ(0) = c`. -/
def IsDiverse (L : Set (ℝ → ℝ)) : Prop :=
  ∀ c : ℝ, 0 < c → ∃ ℓ ∈ L, ℓ 0 = c

/-- Definition 3.2 (p. 9): the anarchy value
`α(ℓ) = sup_{r > 0 : ℓ(r) > 0} [λμ + (1 − λ)]⁻¹`, `λ ∈ [0,1]` with `ℓ*(λr) = ℓ(r)`,
`μ = ℓ(λr)/ℓ(r)`; the supremum is taken in `ℝ≥0∞` over all admissible pairs `(r, λ)`. -/
noncomputable def anarchyValueFn (ℓ : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r) (_ : 0 < ℓ r) (lam : ℝ) (_ : lam ∈ Set.Icc (0 : ℝ) 1)
    (_ : marginalCost ℓ (lam * r) = ℓ r),
    ENNReal.ofReal (lam * (ℓ (lam * r) / ℓ r) + (1 - lam))⁻¹

/-- Definition 3.3 (p. 10): `α(𝓛) = sup_{0 ≠ ℓ ∈ 𝓛} α(ℓ)`, in `ℝ≥0∞`. -/
noncomputable def anarchyValue (L : Set (ℝ → ℝ)) : ℝ≥0∞ :=
  ⨆ ℓ ∈ L, anarchyValueFn ℓ

/-- All latency functions of the instance lie in the class `L`. -/
def InClass (I : Instance V E) (L : Set (ℝ → ℝ)) : Prop :=
  ∀ e, I.ℓ e ∈ L

/-- The one-edge list `[e]` from `0` to `1` in a network all of whose edges go from `0` to `1`. -/
theorem isSimplePath_singleton {E : Type} (e : E) :
    IsSimplePath (fun _ : E => (0 : Fin 2)) (fun _ => 1) [e] 0 1 := by
  exact ⟨by simp, List.isChain_singleton _, by simp, by simp, by simp⟩

/-- `G_m` (p. 14): `m ≥ 1` parallel edges from vertex `0` to vertex `1`, one commodity
from `0` to `1` with rate `r`, latency `ℓ e` on edge `e`. -/
def parallelLinks (m : ℕ) (hm : 0 < m) (r : ℝ) (hr : 0 < r) (ℓ : Fin m → ℝ → ℝ)
    (hℓ : ∀ e, IsLatency (ℓ e)) : Instance (Fin 2) (Fin m) where
  src := fun _ => 0
  tgt := fun _ => 1
  k := 1
  s := fun _ => 0
  t := fun _ => 1
  r := fun _ => r
  ℓ := ℓ
  r_pos := fun _ => hr
  paths_nonempty := fun _ => ⟨[⟨0, hm⟩], isSimplePath_singleton _⟩
  latency := hℓ

/-- `G₂` (p. 13): two parallel edges from vertex `0` to vertex `1`, one commodity from `0`
to `1` with rate `r`. -/
def twoLink (r : ℝ) (hr : 0 < r) (ℓ : Fin 2 → ℝ → ℝ) (hℓ : ∀ e, IsLatency (ℓ e)) :
    Instance (Fin 2) (Fin 2) :=
  parallelLinks 2 (by norm_num) r hr ℓ hℓ

/-- `𝓛_p` (§5.1, p. 18): polynomials with nonnegative coefficients and degree at most `p`. -/
def polyClass (p : ℕ) : Set (ℝ → ℝ) :=
  {ℓ | ∃ a : Fin (p + 1) → ℝ, (∀ i, 0 ≤ a i) ∧ ℓ = fun x => ∑ i, a i * x ^ (i : ℕ)}

end PoAIndep.Topology


