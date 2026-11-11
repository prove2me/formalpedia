-- Prove2me | Definitions.Def_NodeStableProj_Main_Projection
-- name    : NodeStableProj_Main_Projection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:57:57.849185+00:00
-- url     : https://prove2.me/theorems/3ddb4c7e-be77-47e2-8eb4-53fdf7f33330
-- title:
--   The SVT threshold detector (Algorithm 2), the projection P_{D,D̂,ε̃} (Algorithm 1), P̃, Good_{v*}, the SVT accuracy property and the stability parameter
-- statement:
--   **SVT detector** (Algorithm 2). With threshold $\tau$ and parameter $\tilde\varepsilon>0$, a detector keeps a true counter (initially $0$) and a flag (initially $\bot$), and draws $\hat\tau=\tau+\eta$ with $\eta\sim\mathrm{Lap}(2/\tilde\varepsilon)$. On $\mathrm{increment}(b)$, $b\in[0,1]$: if the flag is $\bot$, then $\mathrm{count}\leftarrow\mathrm{count}+b$, $\hat c=\mathrm{count}+\xi$ with a fresh $\xi\sim\mathrm{Lap}(4/\tilde\varepsilon)$, and the flag becomes $\top$ if $\hat c>\hat\tau$. $\mathrm{Lap}(b)$ has density $e^{-|x|/b}/(2b)$.
--
--   **Algorithm 1** ($\mathcal P_{D,\hat D,\tilde\varepsilon}$, integers $0<D<\hat D$). Put $\tau=(D+\hat D)/2$; create one detector $t(u)$ per vertex and $H=(V,\emptyset)$. For the unordered pairs $\{u,v\}$ of $V$ ($u<v$) in lexicographic order: if $\{u,v\}\in E$ and both flags are $\bot$, add $\{u,v\}$ to $H$ and set $a=1$, else $a=0$; then $t(u).\mathrm{increment}(a)$, $t(v).\mathrm{increment}(a)$. **Final check:** if some detector raised its flag at an increment after which its true count is below $D$, or some detector has true count at least $\hat D$ with flag $\bot$ after an increment, return a maximal $\hat D$-bounded subgraph of $G$ chosen by a **fallback rule** $F$; else return $H$. $\tilde{\mathcal P}_{D,\hat D,\tilde\varepsilon}$ always returns $H$.
--
--   The noises are presampled: $\nu_u(0)=\eta_u$ and $\nu_u(\ell)=\xi_{u,\ell}$ is used by the $\ell$-th call to increment on $t(u)$. On a graph with vertex set $V$ the **noise law** makes all $\eta_u\sim\mathrm{Lap}(2/\tilde\varepsilon)$, $\xi_{u,\ell}\sim\mathrm{Lap}(4/\tilde\varepsilon)$ ($u\in V$, $1\le\ell\le|V|-1$) independent; the output law of Algorithm 1 is the pushforward of the noise law.
--
--   **$\mathrm{Good}_{v^*}$** (Eq. (2)) for the noise $\omega$ of $t(v^*)$ on an $n$-node graph: $|\omega(0)|<k/2$ and $|\omega(\ell)|<k/2$ for $\ell\in[n-1]$. **$P^b_\omega$** is the law of $\tilde{\mathcal P}(G)_{-v^*}$ when $t(v^*)$'s noise is fixed to $\omega$ and the other noises are drawn.
--
--   **SVT accuracy for $c_1$** (the conclusion of Lemma 3.6): for all $n$, all $G$ with $|V|\le n$, all $\beta\in(0,1/2)$ and all parameters of Algorithm 1, with probability at least $1-\beta$, putting $k=c_1\log(n/\beta)/\tilde\varepsilon$: all $|\eta_u|,|\xi_{u,\ell}|<k/2$ ($u\in V$, $1\le\ell\le|V|-1$), and at every time step of the main loop every detector with $\mathrm{count}<\tau-k$ has flag $\bot$ and every detector with $\mathrm{count}\ge\tau+k$ has flag $\top$.
--
--   The **stability parameter** of Lemma 3.3 is
--   $$\varepsilon(\hat D,\tilde\varepsilon,\delta)=\tilde\varepsilon\sqrt{2\hat D\ln(3/\delta)}+\hat D\,\tilde\varepsilon\,\frac{e^{\tilde\varepsilon}-1}{e^{\tilde\varepsilon}+1}.$$
--
--   **Formalization Note.** `Lap(b)` is the published `PrivLearn.Generic.laplace b`. Flags are `Bool` (`true` = $\top$), counters real. A call made after the flag is raised draws nothing, so indexing noises by call number changes no law. The final check is accumulated step by step (`bad`). The returned $H$ is `G.withEdges H`, i.e. on $V(G)$ with edge set intersected with $E(G)$, a no-op since only edges of $G$ are inserted. Time step $t$ of the main loop is the state after the first $t$ pairs (`alg1States`, entry $0$ is the initial state). Logarithms are natural (`Real.log`).
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), p. 11 Algorithm 1; p. 13 Algorithm 2 and Lemma 3.6; p. 14 §3.3, P̃ and Eq. (2); pp. 11–12 Lemma 3.3

import Mathlib
import Definitions.Def_PFRelease_Indist
import Definitions.Def_NodeStableProj_Main_Graph

open MeasureTheory

namespace NodeStableProj.Main

/-!
# The SVT threshold detector (Algorithm 2) and the projection `P_{D,D̂,ε̃}` (Algorithm 1)

Aden-Ali, Sealfon, Smith, Steinke, Ullman, *Node Differential Privacy via Node-Stable Graph
Projections*, STOC 2027 submission (manuscript sha256 42f18565…), p. 11 Algorithm 1, p. 13
Algorithm 2 and Lemma 3.6, p. 14 §3.3 (`P̃`, Eq. (2)), pp. 11–12 Lemma 3.3 (the constant `ε`).

**Formalization Note.**
* `Lap(b)` is the published `PrivLearn.Generic.laplace b`, density `e^{−|x|/b}/(2b)`.
* The randomness of the detector `t(u)` is presampled, as in the proof (p. 14): a vector
  `ν u : ℕ → ℝ` with `ν u 0 = η_u ∼ Lap(2/ε̃)` (threshold noise) and `ν u ℓ = ξ_{u,ℓ} ∼ Lap(4/ε̃)`
  the query noise of the `ℓ`-th call to `increment` (`ℓ ≥ 1`); a call made after the flag is
  raised draws nothing, so using call numbers changes no law. All noises are independent. On a
  graph with vertex set `V` each detector receives `|V| − 1` calls, so the noise law is the finite
  product over `u ∈ V`, `j < |V|` (`noiseLaw`), extended by `0` elsewhere (`extendNoise`).
* `flag = true` is `⊤`, `flag = false` is `⊥`. Counters are real (`increment(b)` takes
  `b ∈ [0, 1]`); Algorithm 1 only increments by `0` or `1`.
* Unordered pairs `{u, v}` (`u < v`) of `V` are scanned in lexicographic order of `(u, v)`.
* The final check of line 13 is accumulated step by step (`bad`): after an increment of a
  detector, it fires if the flag was raised at that increment while the (new) true count is below
  `D`, or if the true count is at least `D̂` and the flag is `⊥`.
* "Return any maximal `D̂`-bounded subgraph of `G`" is a parameter `F : Graph → Graph`, a
  *fallback rule*; the theorems quantify over every rule with `IsFallbackRule D̂ F`.
* The graph `H` is returned on the vertex set `V(G)` (`Graph.withEdges`); its edge set is
  intersected with `E(G)`, which is a no-op (only edges of `G` are inserted) that makes the graph
  axioms structural.
-/

/-- The state of an SVT detector (Algorithm 2): the true counter, the flag (`true` = `⊤`) and the
number of `increment` calls received so far. -/
structure Detector where
  count : ℝ
  flag : Bool
  calls : ℕ

/-- `SVT-initialize`: `count ← 0`, `flag ← ⊥`. (The threshold noise is `noise 0`.) -/
def Detector.init : Detector := ⟨0, false, 0⟩

/-- `increment(b)` of Algorithm 2 with threshold `τ` and presampled noise `noise`
(`τ̂ = τ + noise 0`; the `ℓ`-th call uses `ξ = noise ℓ`): if `flag = ⊥` then
`count ← count + b`, `ĉ ← count + ξ`, and `flag ← ⊤` if `ĉ > τ̂`. -/
noncomputable def Detector.increment (τ : ℝ) (noise : ℕ → ℝ) (b : ℝ) (d : Detector) :
    Detector :=
  if d.flag then { d with calls := d.calls + 1 }
  else
    { count := d.count + b
      flag := decide (τ + noise 0 < d.count + b + noise (d.calls + 1))
      calls := d.calls + 1 }

/-- The final check of Algorithm 1 (line 13), for one detector operation taking `old` to `new`:
the flag was raised while the true value is below `D`, or the true value has reached `D̂` and the
flag is not raised. -/
noncomputable def badStep (D Dhat : ℝ) (old new : Detector) : Bool :=
  decide ((old.flag = false ∧ new.flag = true ∧ new.count < D) ∨
    (Dhat ≤ new.count ∧ new.flag = false))

/-- The unordered pairs `{u, v}` of `V`, written `(u, v)` with `u < v`, in lexicographic order. -/
def lexPairs (V : Finset ℕ) : List (ℕ × ℕ) :=
  (V.sort (· ≤ ·)).flatMap fun u => ((V.sort (· ≤ ·)).filter fun v => u < v).map fun v => (u, v)

/-- The state of the main loop of Algorithm 1: all detectors, the edges added to `H`, and whether
the final check has fired. -/
structure Alg1State where
  det : ℕ → Detector
  H : Finset (Sym2 ℕ)
  bad : Bool

/-- The state before the main loop: every detector initialized, `H = ∅`. -/
def Alg1State.init : Alg1State := ⟨fun _ => Detector.init, ∅, false⟩

/-- One iteration of the main loop of Algorithm 1 (lines 6–12) on the pair `(u, v)`, with
`τ = (D + D̂)/2`: if `{u, v} ∈ E` and both flags are `⊥`, add `{u, v}` to `H` and set `a = 1`, else
`a = 0`; then `t(u).increment(a)`, `t(v).increment(a)`. -/
noncomputable def alg1Step (D Dhat : ℕ) (G : Graph) (ν : ℕ → ℕ → ℝ) (st : Alg1State)
    (p : ℕ × ℕ) : Alg1State :=
  let u := p.1
  let v := p.2
  let τ : ℝ := ((D : ℝ) + Dhat) / 2
  let add : Bool := decide (s(u, v) ∈ G.E) && !(st.det u).flag && !(st.det v).flag
  let a : ℝ := if add then 1 else 0
  let du := (st.det u).increment τ (ν u) a
  let dv := (st.det v).increment τ (ν v) a
  { det := Function.update (Function.update st.det u du) v dv
    H := if add then insert s(u, v) st.H else st.H
    bad := st.bad || badStep D Dhat (st.det u) du || badStep D Dhat (st.det v) dv }

/-- The states of the main loop at every time step: entry `t` is the state after the first `t`
pairs (entry `0` is the initial state). -/
noncomputable def alg1States (D Dhat : ℕ) (G : Graph) (ν : ℕ → ℕ → ℝ) : List Alg1State :=
  (lexPairs G.V).scanl (alg1Step D Dhat G ν) Alg1State.init

/-- The state after the main loop. -/
noncomputable def alg1Final (D Dhat : ℕ) (G : Graph) (ν : ℕ → ℕ → ℝ) : Alg1State :=
  (lexPairs G.V).foldl (alg1Step D Dhat G ν) Alg1State.init

/-- `P̃_{D,D̂,ε̃}(G)` (p. 14): the graph `H` built by the main loop, without the fallback. -/
noncomputable def projTilde (D Dhat : ℕ) (G : Graph) (ν : ℕ → ℕ → ℝ) : Graph :=
  G.withEdges (alg1Final D Dhat G ν).H

/-- A fallback rule for line 14: a choice, for every graph `G`, of a maximal `D̂`-bounded
subgraph of `G`. -/
def IsFallbackRule (Dhat : ℝ) (F : Graph → Graph) : Prop :=
  ∀ G : Graph, G.IsMaximalBoundedSubgraph Dhat (F G)

/-- The output of Algorithm 1 on `G` with presampled noise `ν` and fallback rule `F`. -/
noncomputable def alg1Out (D Dhat : ℕ) (F : Graph → Graph) (G : Graph) (ν : ℕ → ℕ → ℝ) :
    Graph :=
  if (alg1Final D Dhat G ν).bad then F G else projTilde D Dhat G ν

/-- The law of the presampled noise on a graph with vertex set `V`: independent
`ν u 0 ∼ Lap(2/ε̃)` and `ν u j ∼ Lap(4/ε̃)` (`1 ≤ j < |V|`), `u ∈ V`. -/
noncomputable def noiseLaw (εt : ℝ) (V : Finset ℕ) : Measure (↥V → Fin V.card → ℝ) :=
  Measure.pi fun _ : ↥V =>
    Measure.pi fun j : Fin V.card =>
      PrivLearn.Generic.laplace (if (j : ℕ) = 0 then 2 / εt else 4 / εt)

/-- A noise vector on `V` read as a function of (vertex label, index), `0` outside. -/
def extendNoise {V : Finset ℕ} (ν : ↥V → Fin V.card → ℝ) : ℕ → ℕ → ℝ :=
  fun u j => if h : u ∈ V then (if hj : j < V.card then ν ⟨u, h⟩ ⟨j, hj⟩ else 0) else 0

/-- The output law of `P_{D,D̂,ε̃}(G)` (Algorithm 1) with fallback rule `F`. -/
noncomputable def alg1Law (D Dhat : ℕ) (εt : ℝ) (F : Graph → Graph) (G : Graph) :
    Measure Graph :=
  (noiseLaw εt G.V).map fun ν => alg1Out D Dhat F G (extendNoise ν)

/-- The output law of `P̃_{D,D̂,ε̃}(G)`. -/
noncomputable def projTildeLaw (D Dhat : ℕ) (εt : ℝ) (G : Graph) : Measure Graph :=
  (noiseLaw εt G.V).map fun ν => projTilde D Dhat G (extendNoise ν)

/-- `Good_{v*}` (Eq. (2), p. 14) for the presampled noise `ω` of `t(v*)` on an `n`-node graph:
`|η_{v*}| < k/2` and `|ξ_{v*,ℓ}| < k/2` for all `ℓ ∈ [n − 1]`. -/
def Good (k : ℝ) (n : ℕ) (ω : ℕ → ℝ) : Prop :=
  |ω 0| < k / 2 ∧ ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ n - 1 → |ω ℓ| < k / 2

/-- `P^b_ω` (p. 15): the law of `P̃_{D,D̂,ε̃}(G)_{−v*}` when the randomness of `t(v*)` is fixed to
`ω` and the other detectors' noises are drawn as in `noiseLaw`. (`P^0_ω` is this on `G`, `P^1_ω`
on `G'`.) -/
noncomputable def projTildeLawFixing (D Dhat : ℕ) (εt : ℝ) (G : Graph) (vstar : ℕ)
    (ω : ℕ → ℝ) : Measure Graph :=
  (noiseLaw εt G.V).map fun ν =>
    (projTilde D Dhat G (Function.update (extendNoise ν) vstar ω)).deleteVertex vstar

/-- The conclusion of Lemma 3.6 for the constant `c1`: for all `n`, all `G` with `|V| ≤ n`, all
`β ∈ (0, 1/2)`, all parameters `0 < D < D̂`, `ε̃ > 0` of Algorithm 1, with probability at least
`1 − β` over the noise, with `k = c1 log(n/β)/ε̃`:
(1) `|η_u| < k/2` and `|ξ_{u,ℓ}| < k/2` for every `u ∈ V` and every call `ℓ ∈ [|V| − 1]`;
(2) at every time step of the main loop, every detector with `count < τ − k` has flag `⊥`;
(3) at every time step, every detector with `count ≥ τ + k` has flag `⊤`. -/
def SVTAccuracy (c1 : ℝ) : Prop :=
  ∀ (n : ℕ) (G : Graph) (β : ℝ) (D Dhat : ℕ) (εt : ℝ),
    G.V.card ≤ n → 0 < β → β < 1 / 2 → 0 < D → D < Dhat → 0 < εt →
    ENNReal.ofReal (1 - β) ≤
      noiseLaw εt G.V {ν |
        (∀ u ∈ G.V, |extendNoise ν u 0| < c1 * Real.log (n / β) / εt / 2 ∧
          ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ G.V.card - 1 →
            |extendNoise ν u ℓ| < c1 * Real.log (n / β) / εt / 2) ∧
        (∀ st ∈ alg1States D Dhat G (extendNoise ν), ∀ u ∈ G.V,
          ((st.det u).count < ((D : ℝ) + Dhat) / 2 - c1 * Real.log (n / β) / εt →
              (st.det u).flag = false) ∧
          (((D : ℝ) + Dhat) / 2 + c1 * Real.log (n / β) / εt ≤ (st.det u).count →
              (st.det u).flag = true))}

/-- The stability parameter of Lemma 3.3, item 3:
`ε = ε̃ √(2 D̂ ln(3/δ)) + D̂ ε̃ (e^{ε̃} − 1)/(e^{ε̃} + 1)`. -/
noncomputable def stabEps (Dhat : ℕ) (εt δ : ℝ) : ℝ :=
  εt * Real.sqrt (2 * Dhat * Real.log (3 / δ)) +
    Dhat * εt * (Real.exp εt - 1) / (Real.exp εt + 1)

end NodeStableProj.Main


