-- Prove2me | Definitions.Def_PDynTreeEmbed_Main_Static
-- name    : PDynTreeEmbed_Main_Static
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:31:08.104474+00:00
-- url     : https://prove2.me/theorems/2bed9c3a-ff72-4619-ac91-ae1cac9f0199
-- title:
--   Blur (Algorithm 3), blurry exponential CKR (Algorithm 2) and its law, touching and covering, the ball-growth profile, F_ℓ(v), and the tree of §4.4
-- statement:
--   Fix a weighted graph $G$ on $V=\{0,\dots,n-1\}$, $n\ge2$, and put $\alpha=1/(2\log_2 n)$.
--
--   **Blur (Algorithm 3).** For $\sigma>0$ let $K=\max(0,\lfloor\log\sigma/\log(1/\alpha)\rfloor+1)$. A **valid execution** of $\mathrm{Blur}(G,\sigma,X_0)$ draws radii $r_1,r_2,\dots$ and chooses sets with $X_0$ given and, for $k=1,\dots,K$,
--   $$B_G\big(X_{k-1},\tfrac{r_k}{1+\alpha^2}\big)\subseteq X_k\subseteq B_G(X_{k-1},r_k),$$
--   where $X_k$ depends only on $r_1,\dots,r_k$; the output is $U=X_K$. The **law** of the radii: independent, $r_k\sim\mathrm{Unif}[0,\alpha^{k-1}\sigma]$.
--
--   **Algorithm 2 with parameter $D$.** The randomness is a permutation $\pi$ (position $i$ holds the center $\pi(i)$), one radius $R_w$ per vertex, and for each center $w$ its own blur radii $r_{w,1},r_{w,2},\dots$; under the law, $\pi$ is uniform, $R_w\sim\mathrm{Exp}(1/D)$ (mean $D$), $r_{w,k}\sim\mathrm{Unif}[0,\alpha^{k-1}D/20]$, all independent. A **valid execution** chooses for each center $w$ a set $X_w$, depending on $\pi$ and the radii only, with
--   $$B_G\big(w,\max\{0,R_w-D/100\}\big)\subseteq X_w\subseteq B_G(w,R_w),$$
--   and a valid execution of $\mathrm{Blur}(G,D/20,X_w)$ driven by $w$'s blur radii, with output $U_w$. The **center** of $v$ is $\mathrm{Center}(v)=\pi(i)$ for the least position $i$ with $v\in U_{\pi(i)}$, and the clusters are the classes of $\mathrm{Center}$ (cluster $C_i=U_i\setminus\bigcup_{j<i}C_j$). We write $u\prec_\pi w$ when $u$ precedes $w$ in $\pi$. An outcome is **in the support** if every $R_w\ge0$ and every $r_{w,k}\in[0,\alpha^{k-1}D/20]$.
--
--   **Touching and covering (Definition 4.1).** For a nonempty $Z$, $w$ **touches** $Z$ if $R_w\ge\mathrm{dist}_G(w,Z)-D$ and **covers** $Z$ if $R_w\ge\mathrm{dist}_G(w,Z)+D$.
--
--   **Scales.** $L=\lceil\log_2(nW)\rceil$; level $\ell$ uses $D_\ell=2^\ell$.
--
--   **Ball-growth profile (7)–(8).** $r_0(v)=1$ and for $\ell\ge1$
--   $$\Delta_\ell(v)=\max\Big\{\xi\in\mathbb Z_{\ge0}:\big|B_G\big(v,(\tfrac{r_{\ell-1}(v)}2+\xi+2)2^\ell\big)\big|\ge e^{\xi/2}\big|B_G(v,r_{\ell-1}(v)2^{\ell-1})\big|\Big\},\qquad r_\ell(v)=\tfrac{r_{\ell-1}(v)}2+\Delta_\ell(v)+2.$$
--
--   **$F_\ell(v)$ (Lemma 4.5).** With $Q_w=E_{touch}(w,v)\cap\bigcap_{u\prec_\pi w}E_{cover}(u,v)^c$, $F_\ell(v)=\max\{\mathrm{dist}_G(v,w):Q_w\text{ occurs}\}$.
--
--   **The tree of §4.4.** Given centers $\mathrm{Center}_\ell$ for $0\le\ell\le L$ ($\mathrm{Center}_0(v)=v$, $\mathrm{Center}_L\equiv c^\star$, and for $0<\ell<L$ the centers of a run of Algorithm 2 with $D_\ell=2^\ell$), $\mathcal C_{\ge\ell}(x)$ is the set of vertices sharing $x$'s center at every level $\ell\le k\le L$. The tree has a node $(\ell,\mathcal C_{\ge\ell}(x))$ for every $\ell\le L$ and $x$, and for $\ell<L$ an edge from $(\ell,\mathcal C_{\ge\ell}(x))$ to $(\ell+1,\mathcal C_{\ge\ell+1}(x))$ of weight $\mathrm{dist}_G(\mathrm{Center}_\ell(x),\mathrm{Center}_{\ell+1}(x))$. The leaf $(0,\{v\})$ is identified with $v$.
--
--   **Formalization Note.** `Outcome n = Perm (Fin n) × (Fin n → ℝ) × (Fin n → ℕ → ℝ)`; blur radius `r w k` (0-based) is the paper's $r_{w,k+1}$ with law $\mathrm{Unif}[0,\alpha^k\sigma]$. Selectors are typed so that $X_w$ sees only $(\pi,R)$ and $w$'s blur stages see only $(\pi,R)$ and $w$'s own radii; `IsBlurRun.adapted` makes stage $k$ depend only on the first $k$ of them. `IsMeasurableExec` (measurable membership events) is a separate predicate, assumed where an expectation of the output appears. `Center` falls back to `v` when no blurred set contains `v`, which never happens for a valid execution ($v\in X_v$). $\Delta_\ell$ is `Nat.findGreatest` with search bound $2n$: every feasible $\xi$ satisfies $e^{\xi/2}\le n$. `farCenter` is `0` when no $Q_w$ occurs. Edge weights of the tree are natural numbers (distances between centers).
-- source:
--   Dorkofikis, Probst Gutenberg, Tight Low-Diameter Decompositions and Tree Embeddings in Partially Dynamic Graphs, STOC 2027 submission (manuscript sha256 bf7ba5b2…), Algorithm 2 (p. 8), Algorithm 3 (p. 10), §4 (pp. 13–18): scales (p. 13), Conventions and (5)–(6) (p. 14), Definition 4.1 (p. 14), (7)–(8) (p. 15), Lemma 4.5 (p. 16), §4.4 (p. 18)

import Mathlib
import Definitions.Def_PDynTreeEmbed_Main_Graphs

namespace PDynTreeEmbed.Main

/-! # Blurry ball growing, blurry exponential CKR, touching and covering, the ball-growth profile,
and the tree of §4.4

Dorkofikis, Probst Gutenberg, *Tight Low-Diameter Decompositions and Tree Embeddings in Partially
Dynamic Graphs*, STOC 2027 submission (manuscript sha256 bf7ba5b2…): Algorithm 2 (p. 8),
Algorithm 3 (p. 10), §4 (pp. 13–18): scales, conventions (5)–(6), Definition 4.1, (7)–(8), Lemma
4.5's `F_ℓ(v)`, the tree of §4.4.

**Formalization Note.**
* `α = 1/(2 log₂ n)`, `K = max(0, ⌊log σ / log(1/α)⌋ + 1)` (for `σ < 1` no blur stage is run, p. 24).
* The randomness of one run of Algorithm 2 with parameter `D` on `Fin n` is an `Outcome n`: a
  permutation `π` (position `i`, 0-based, holds the center `π i`), one radius `R_w` per vertex
  (§4.1 Conventions), and one sequence of blur radii `r_w(0), r_w(1), …` per vertex, where `r_w(k)`
  is the radius of blur stage `k + 1` of the iteration whose center is `w`. Its law (`IsAlg2Law`):
  `π` uniform; `R_w ∼ Exp(1/D)` (rate `1/D`, mean `D`); `r_w(k) ∼ Unif[0, α^k σ]` with
  `σ = D/20`; all of these independent.
* "Compute `X` such that …" is a nondeterministic choice. A valid execution is a pair of selectors:
  `X π R w` (the initial set of center `w`, a function of `π` and the radii only) and
  `Y π R w r k` (blur stage `k` of center `w`, a function of `π`, the radii and center `w`'s own
  blur radii `r`), satisfying Algorithm 2's containment and Algorithm 3's containments, with stage
  `k` depending only on `r(0), …, r(k-1)`. The blurred set is `U_w = Y … K`.
* `Center(v) = π(i)` for the least position `i` with `v ∈ U_{π(i)}`; clusters are the classes of
  `Center`. -/

open MeasureTheory ProbabilityTheory

/-- `α = 1/(2 log₂ n)` (Algorithm 3, Theorem 2.2). -/
noncomputable def blurAlpha (n : ℕ) : ℝ := 1 / (2 * log2 n)

/-- `K = ⌊log σ / log(1/α)⌋ + 1`, read as `0` when this is negative (Algorithm 3, p. 24). -/
noncomputable def blurK (n : ℕ) (σ : ℝ) : ℕ :=
  (⌊Real.log σ / Real.log (1 / blurAlpha n)⌋ + 1).toNat

/-- The uniform law on `[0, b]`. -/
noncomputable def unifLaw (b : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Icc 0 b)

/-- A valid execution of `Blur(G, σ, X₀)` (Algorithm 3): stage `k` is a set `Y r k` chosen from the
blur radii `r`; `Y r 0 = X₀`; for each stage `k < K`,
`B_G(Y_k, r(k)/(1+α²)) ⊆ Y_{k+1} ⊆ B_G(Y_k, r(k))`; and `Y r k` depends only on
`r(0), …, r(k-1)`. The output is `Y r K`. -/
structure IsBlurRun {n : ℕ} (G : WGraph (Fin n)) (σ : ℝ) (X₀ : Finset (Fin n))
    (Y : (ℕ → ℝ) → ℕ → Finset (Fin n)) : Prop where
  start : ∀ r, Y r 0 = X₀
  inner : ∀ r k, k < blurK n σ →
    G.ballSet (Y r k) (r k / (1 + blurAlpha n ^ 2)) ⊆ Y r (k + 1)
  outer : ∀ r k, k < blurK n σ → Y r (k + 1) ⊆ G.ballSet (Y r k) (r k)
  adapted : ∀ r r' k, (∀ j < k, r j = r' j) → Y r k = Y r' k

/-- The law of Blur's radii: independent, `r(k) ∼ Unif[0, α^k σ]`. -/
structure IsBlurLaw {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ) (σ : ℝ)
    (r : Ω → ℕ → ℝ) : Prop where
  prob : IsProbabilityMeasure P
  indep : iIndepFun (fun k ω => r ω k) P
  law : ∀ k, P.map (fun ω => r ω k) = unifLaw (blurAlpha n ^ k * σ)

/-- The randomness of one run of Algorithm 2 on `Fin n`: permutation, radii, blur radii. -/
abbrev Outcome (n : ℕ) := Equiv.Perm (Fin n) × (Fin n → ℝ) × (Fin n → ℕ → ℝ)

/-- The law of the randomness of Algorithm 2 with parameter `D`: `π` uniform, `R_w ∼ Exp(1/D)`,
`r_w(k) ∼ Unif[0, α^k D/20]`, all independent. -/
structure IsAlg2Law {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ) (D : ℝ)
    (ζ : Ω → Outcome n) : Prop where
  prob : IsProbabilityMeasure P
  meas : Measurable ζ
  perm_law : P.map (fun ω => (ζ ω).1) = (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure
  radius_law : ∀ w, P.map (fun ω => (ζ ω).2.1 w) = expMeasure (1 / D)
  blur_law : ∀ w k, P.map (fun ω => (ζ ω).2.2 w k) = unifLaw (blurAlpha n ^ k * (D / 20))
  indep_reals : iIndepFun (fun (i : Fin n ⊕ (Fin n × ℕ)) ω =>
    match i with
    | Sum.inl w => (ζ ω).2.1 w
    | Sum.inr p => (ζ ω).2.2 p.1 p.2) P
  indep_perm : IndepFun (fun ω => (ζ ω).1) (fun ω => (ζ ω).2) P

/-- An outcome in the support of the law: radii are nonnegative and every blur radius
`r_w(k)` lies in `[0, α^k D/20]` ("every outcome of the blur randomness"). -/
def IsOutcome {n : ℕ} (D : ℝ) (ζ : Outcome n) : Prop :=
  (∀ w, 0 ≤ ζ.2.1 w) ∧ ∀ w k, 0 ≤ ζ.2.2 w k ∧ ζ.2.2 w k ≤ blurAlpha n ^ k * (D / 20)

/-- A valid execution of Algorithm 2 (`BlurryExponentialCKR(G, D)`) given by its selectors: for every
`π`, radii `R` and center `w`, `B_G(w, max{0, R_w − D/100}) ⊆ X_w ⊆ B_G(w, R_w)`, and the blur of
center `w` is a valid execution of `Blur(G, D/20, X_w)`. -/
structure IsAlg2Exec {n : ℕ} (G : WGraph (Fin n)) (D : ℝ)
    (X : Equiv.Perm (Fin n) → (Fin n → ℝ) → Fin n → Finset (Fin n))
    (Y : Equiv.Perm (Fin n) → (Fin n → ℝ) → Fin n → (ℕ → ℝ) → ℕ → Finset (Fin n)) : Prop where
  inner : ∀ π R w, G.ball w (max 0 (R w - D / 100)) ⊆ X π R w
  outer : ∀ π R w, X π R w ⊆ G.ball w (R w)
  blur : ∀ π R w, IsBlurRun G (D / 20) (X π R w) (Y π R w)

/-- The blur selectors are measurable: each membership event of each stage is measurable in the
randomness. -/
def IsMeasurableExec {n : ℕ}
    (Y : Equiv.Perm (Fin n) → (Fin n → ℝ) → Fin n → (ℕ → ℝ) → ℕ → Finset (Fin n)) : Prop :=
  ∀ w k v, MeasurableSet {ζ : Outcome n | v ∈ Y ζ.1 ζ.2.1 w (ζ.2.2 w) k}

/-- The blurred set `U_w` of center `w` on the outcome `ζ` (parameter `D`). -/
noncomputable def blurred {n : ℕ}
    (Y : Equiv.Perm (Fin n) → (Fin n → ℝ) → Fin n → (ℕ → ℝ) → ℕ → Finset (Fin n))
    (D : ℝ) (ζ : Outcome n) (w : Fin n) : Finset (Fin n) :=
  Y ζ.1 ζ.2.1 w (ζ.2.2 w) (blurK n (D / 20))

open Classical in
/-- `Center(v) = π(i)` for the least position `i` with `v ∈ U_{π(i)}` (§4.1; `v` itself if there is
none, which never happens for a valid execution). The cluster of `v` is the set of vertices with the
same center. -/
noncomputable def center {n : ℕ}
    (Y : Equiv.Perm (Fin n) → (Fin n → ℝ) → Fin n → (ℕ → ℝ) → ℕ → Finset (Fin n))
    (D : ℝ) (ζ : Outcome n) (v : Fin n) : Fin n :=
  let S := Finset.univ.filter fun i : Fin n => v ∈ blurred Y D ζ (ζ.1 i)
  if h : S.Nonempty then ζ.1 (S.min' h) else v

/-- Definition 4.1: `w` **touches** `Z` if `R_w ≥ dist_G(w, Z) − D`. -/
def Touches {n : ℕ} (G : WGraph (Fin n)) (D : ℝ) (R : Fin n → ℝ) (w : Fin n)
    (Z : Finset (Fin n)) : Prop :=
  ((G.distTo w Z).toNat : ℝ) - D ≤ R w

/-- Definition 4.1: `w` **covers** `Z` if `R_w ≥ dist_G(w, Z) + D`. -/
def Covers {n : ℕ} (G : WGraph (Fin n)) (D : ℝ) (R : Fin n → ℝ) (w : Fin n)
    (Z : Finset (Fin n)) : Prop :=
  ((G.distTo w Z).toNat : ℝ) + D ≤ R w

/-- `L = ⌈log₂(nW)⌉`, the number of scales (§4, p. 13). -/
def levels (n W : ℕ) : ℕ := Nat.clog 2 (n * W)

open Classical in
/-- `Δ_ℓ(v)` of (7), given `r_{ℓ−1}(v) = rPrev`: the largest integer `ξ ≥ 0` with
`|B_G(v, (r_{ℓ−1}/2 + ξ + 2) 2^ℓ)| ≥ e^{ξ/2} |B_G(v, r_{ℓ−1} 2^{ℓ−1})|`. Every feasible `ξ` is at
most `2 ln n < 2n`, so the search bound `2n` loses nothing. -/
noncomputable def growthStep {n : ℕ} (G : WGraph (Fin n)) (v : Fin n) (ℓ : ℕ) (rPrev : ℝ) : ℕ :=
  Nat.findGreatest (fun ξ : ℕ =>
    Real.exp ((ξ : ℝ) / 2) * ((G.ball v (rPrev * 2 ^ (ℓ - 1))).card : ℝ) ≤
      ((G.ball v ((rPrev / 2 + ξ + 2) * 2 ^ ℓ)).card : ℝ)) (2 * n)

/-- The ball-growth profile (7)–(8): `r_0(v) = 1`, `r_ℓ(v) = r_{ℓ−1}(v)/2 + Δ_ℓ(v) + 2`. -/
noncomputable def profile {n : ℕ} (G : WGraph (Fin n)) (v : Fin n) : ℕ → ℝ
  | 0 => 1
  | ℓ + 1 => profile G v ℓ / 2 + growthStep G v (ℓ + 1) (profile G v ℓ) + 2

open Classical in
/-- `F_ℓ(v)` of Lemma 4.5 (scale `D`): the largest `dist_G(v, w)` over the centers `w` for which
`Q_w = E_touch(w, v) ∩ ⋂_{u ≺_π w} E_cover(u, v)^c` occurs (`0` if there is none). It is a function
of the permutation and the radii only. -/
noncomputable def farCenter {n : ℕ} (G : WGraph (Fin n)) (D : ℝ) (π : Equiv.Perm (Fin n))
    (R : Fin n → ℝ) (v : Fin n) : ℕ :=
  (Finset.univ.filter fun w => Touches G D R w {v} ∧
      ∀ u, π.symm u < π.symm w → ¬ Covers G D R u {v}).sup fun w => (G.dist v w).toNat

/-- The centers `Center_ℓ` at every level of the hierarchy (§4, p. 13): `Center_0(v) = v`,
`Center_ℓ(v) = c⋆` for `ℓ ≥ L`, and for `0 < ℓ < L` the center of the level-`ℓ` run of Algorithm 2
with `D_ℓ = 2^ℓ`, outcome `ζ ℓ` and blur selector `Ys ℓ`. -/
noncomputable def levelCenters {n : ℕ} (L : ℕ) (cstar : Fin n)
    (Ys : ℕ → Equiv.Perm (Fin n) → (Fin n → ℝ) → Fin n → (ℕ → ℝ) → ℕ → Finset (Fin n))
    (ζ : ℕ → Outcome n) (ℓ : ℕ) (v : Fin n) : Fin n :=
  if ℓ = 0 then v else if L ≤ ℓ then cstar else center (Ys ℓ) (2 ^ ℓ) (ζ ℓ) v

open Classical in
/-- `C_{≥ℓ}(x)`: the cluster of `x` in the coarsest common refinement of `C_ℓ, …, C_L`, i.e. the
vertices that share `x`'s center at every level `ℓ ≤ k ≤ L`. -/
noncomputable def refinedCluster {n : ℕ} (L : ℕ) (cen : ℕ → Fin n → Fin n) (ℓ : ℕ) (x : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun y => ∀ k, ℓ ≤ k → k ≤ L → cen k y = cen k x

/-- The nodes of the tree `T` of §4.4: one node `(ℓ, C)` for every level `ℓ ≤ L` and every
cluster `C ∈ C_{≥ℓ}`. The leaf `(0, C_{≥0}(v)) = (0, {v})` is identified with `v`. -/
def treeNodes {n : ℕ} (L : ℕ) (cen : ℕ → Fin n → Fin n) : Set (ℕ × Finset (Fin n)) :=
  {p | ∃ ℓ ≤ L, ∃ x, p = (ℓ, refinedCluster L cen ℓ x)}

open Classical in
/-- The weight of the edge from the child node `(ℓ, C)`: `dist_G(Center_ℓ(x), Center_{ℓ+1}(x))`
for an `x ∈ C` (the same for all `x ∈ C`). -/
noncomputable def childWeight {n : ℕ} (G : WGraph (Fin n)) (cen : ℕ → Fin n → Fin n)
    (p : ℕ × Finset (Fin n)) : ℕ :=
  if h : p.2.Nonempty then (G.dist (cen p.1 h.choose) (cen (p.1 + 1) h.choose)).toNat else 0

/-- The tree `T` of §4.4 for the centers `cen` (with `L` levels): for `ℓ < L`, the node
`(ℓ, C_{≥ℓ}(x))` is joined to its parent `(ℓ+1, C_{≥ℓ+1}(x))` by an edge of weight
`dist_G(Center_ℓ(x), Center_{ℓ+1}(x))`. -/
noncomputable def hierTree {n : ℕ} (G : WGraph (Fin n)) (L : ℕ) (cen : ℕ → Fin n → Fin n) :
    WGraph (ℕ × Finset (Fin n)) where
  adj := SimpleGraph.fromRel fun p q =>
    ∃ ℓ < L, ∃ x, p = (ℓ, refinedCluster L cen ℓ x) ∧ q = (ℓ + 1, refinedCluster L cen (ℓ + 1) x)
  wt := Sym2.lift ⟨fun p q =>
      (if p.1 + 1 = q.1 then childWeight G cen p else 0) +
        (if q.1 + 1 = p.1 then childWeight G cen q else 0),
    fun _ _ => add_comm _ _⟩

/-- The leaf of `T` identified with the vertex `v`: the node `(0, C_{≥0}(v))`. -/
noncomputable def leaf {n : ℕ} (L : ℕ) (cen : ℕ → Fin n → Fin n) (v : Fin n) :
    ℕ × Finset (Fin n) :=
  (0, refinedCluster L cen 0 v)

end PDynTreeEmbed.Main


