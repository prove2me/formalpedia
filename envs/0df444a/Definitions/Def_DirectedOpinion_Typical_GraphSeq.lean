-- Prove2me | Definitions.Def_DirectedOpinion_Typical_GraphSeq
-- name    : DirectedOpinion_Typical_GraphSeq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:44.393303+00:00
-- url     : https://prove2.me/theorems/f5e8afb0-69bc-48ac-973c-1b27a1534d1f
-- title:
--   pp. 6–8, 23 — random directed graph sequence with signals, in-components, the coupling event (4), strong coupling (Definition 4), d₁ and the Lipschitz kernel condition
-- statement:
--   **In-components and limit graphs.** For a directed graph $G$ and a vertex $v$, the **in-component of depth $k$** of $v$ (Definition 3) is the set of vertices $u$ with a directed path from $u$ to $v$ of length at most $k$, an edge going from $\ell(w,r)$ to $w$. A **rooted marked limit graph** $\mathcal G(\boldsymbol{\mathcal X})$ has vertex set $\mathbb N$ with root $\emptyset=0$, ordered inbound-neighbour lists $\mathcal L(x,r)$ and full marks $\boldsymbol{\mathcal X}_x$; the in-degree $\mathcal N_x$ and the weights $\mathcal C(x,r)$ of a vertex are read from its mark.
--
--   **The coupling event (4).** Given a graph $G$ with full marks $(\mathbf X_i)$, a vertex $v$, a limit graph $\mathcal G$, a depth $k$ and a tolerance $\epsilon$, the event $\mathcal E_v^{(k,\epsilon)}$ holds if there is a bijection $\theta$ from the depth-$k$ in-component $\mathcal G_\emptyset^{(k)}$ of the root onto the depth-$k$ in-component $G_v^{(k)}$ of $v$ with
--   1. $\theta(\emptyset)=v$;
--   2. for every vertex $x$ at depth $<k$: $x$ and $\theta(x)$ have the same in-degree and $\theta(\mathcal L(x,r))=\ell(\theta(x),r)$ for every $r$;
--   3. $\rho(\mathbf X_{\theta(x)},\boldsymbol{\mathcal X}_x)\le\epsilon$ for every $x\in\mathcal G_\emptyset^{(k)}$.
--
--   **The random graph sequence.** For each $n\ge1$ the graph $G(V_n,E_n;\mathscr A_n)$ has vertex set $V_n=\{1,\dots,n\}$, attributes $\mathbf Y_i=(\mathbf A_i,Q_i,S_i)$ with $Q_i\in[-1,1]$, $S_i\in\{0,1\}$, and weights in $[0,1]$ summing to $c$ at every vertex with $D_i^->0$; $\mathbf X_i$ is the full mark of $i$, and $\mathscr F_n=\sigma(\mathscr A_n)$ is the σ-algebra of the attributes only. Two vertices $I_n,J_n$ are chosen uniformly, independently of each other and of the graph. Given the graph, the external signals are independent with $W_i^{(k)}=\zeta(\mathbf X_i,U_i^{(k)})$, i.i.d. in $k$ with law $\nu(\mathbf X_i)$, and $|W_i^{(k)}|\le d+c-\sum_rC(i,r)$; the initial opinions are $R_i^{(0)}=\varphi(\mathbf X_i,V_i)\in[-1,1]$, conditionally independent of the signals. Here all $U_i^{(k)},V_i$ are i.i.d. uniform on $[0,1]$ and independent of the graph and of everything coupled to it.
--
--   **Strong coupling (Definition 4).** The sequence admits a strong coupling with $\mathcal G(\boldsymbol{\mathcal X})$, of law $\mu$, if for every $k\ge1$ and $\epsilon>0$ there are two independent limit graphs $\mathcal G_\emptyset$, $\hat{\mathcal G}_{\hat\emptyset}$, each of law $\mu$, and events $E_n\subseteq\mathcal E_{I_n}^{(k,\epsilon)}$, $\hat E_n\subseteq\mathcal E_{J_n}^{(k,\epsilon)}$ (built from $\mathcal G_\emptyset$ and $\hat{\mathcal G}_{\hat\emptyset}$ respectively), such that on $E_n\cap\hat E_n$ the depth-$k$ in-components of $I_n$ and $J_n$ are disjoint, with
--   $$P\bigl(E_n\cap\hat E_n\mid\mathscr A_n\bigr)\xrightarrow{P}1,\qquad n\to\infty .$$
--
--   **Lipschitz kernels.** The Wasserstein distance is $d_1(\mu,\nu)=\inf\{E|X-Y|:\mathrm{law}(X)=\mu,\ \mathrm{law}(Y)=\nu\}$; a kernel $\mathbf x\mapsto\nu(\mathbf x)$ is **$K$-Lipschitz** if $d_1(\nu(\mathbf x),\nu(\tilde{\mathbf x}))\le K\rho(\mathbf x,\tilde{\mathbf x})$ for all $\mathbf x,\tilde{\mathbf x}\in\mathcal S$. The file also defines the conditional law given $\mathscr A_n$ of the trajectory $(R^{(0)}_{I_n},\dots,R^{(k)}_{I_n})$ and of the stationary opinion $R_{I_n}$, and the empirical average $\frac1n\sum_{i=1}^nf(x_i)$.
--
--   These are the hypotheses and the objects of Theorem 2.
--
--   **Formalization Note**
--   1. All graphs, couplings and signals live on one probability space; the $m$-th graph has the $m+1$ vertices `Fin (m+1)` (the paper's $G_{m+1}$), so a uniform vertex exists for every index.
--   2. "Conditionally i.i.d. given the marks, with law $\nu(\mathbf x)$" is encoded by the quantile representation $W=\zeta(\mathbf X,U)$ with $U$ uniform and independent of the graph, so $\nu(\mathbf x)$ is the law of $\zeta(\mathbf x,U)$; this loses nothing, since every conclusion is about laws. The same representation $\varphi(\mathbf X,V)$ is used for the initial opinions.
--   3. The coupled limit graphs and the events are measurable with respect to a σ-algebra $\mathscr G_n$ of "the graph and everything coupled to it", which contains the graph, its attributes and $I_n,J_n$ and is independent of the uniforms. The events $E_n\subseteq\mathcal E^{(k,\epsilon)}$ are required to be measurable, since the event "there exists a bijection $\theta$" need not be.
--   4. The bijection $\theta$ preserves the order of inbound neighbours, which the proof of Theorem 2 uses (p. 26) and which Definition 2's isomorphism does not record. It is required to match the edges into vertices of depth $<k$ only; the marks, which contain the in-degree, are compared at every depth.
--   5. Only the second bullet of Definition 4 is stated: the first follows from it.
--   6. The paper's requirement that the weight vectors be conditionally independent given $\mathscr A_n$ is not imposed (it is not used by the proof); this is a generalization.
--   7. **Disjoint in-components (added; a gap of the page).** The strong coupling also requires the depth-$k$ in-components of $I_n$ and $J_n$ to be disjoint on $E_n\cap\hat E_n$. The proof of Theorem 7 (p. 25) gives the vertices of the two in-components their own optimally coupled signals and makes the signals of the two limit copies independent, which is consistent only for disjoint in-components. Definition 4 as printed admits a graph in which every vertex has the same single inbound neighbour (a hub, with a self-loop): its depth-$k$ in-components converge to a fixed limit, but the hub's signals are shared by every vertex, so $\frac1n\sum_if(R_i^{(k)})$ keeps a random shift and does not converge to a constant. In the sparse models the paper lists, two uniform vertices have disjoint in-components with high probability.
-- source:
--   Fraiman, Lin and Olvera-Cravioto, Opinion dynamics on directed complex networks, arXiv:2209.00969v2, p. 3–4 (signals), p. 6 (graph sequence, X_i, R^(0)), p. 7 (Definitions 2–4, (4)), p. 8 (Definition 4 second bullet, ρ, d₁, the Lipschitz condition of Theorem 2), p. 23 (ℱ_n = σ(𝒜_n)), p. 25 (quantile coupling)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_DirectedOpinion_Typical_Model
import Definitions.Def_DirectedOpinion_Typical_Marks

namespace DirectedOpinion.Typical

open MeasureTheory ProbabilityTheory Set Filter

/-! ### Directed in-balls and the limit graph -/

/-- The vertex set of the in-component of depth `k` of `v` (Definition 3, p. 7): the vertices `u`
with a directed path from `u` to `v` of length at most `k`. An edge goes from the inbound
neighbour `G.nbr w r` (`r < G.deg w`) to `w`. -/
def inBall {V : Type*} (G : WDigraph V) (v : V) : ℕ → Set V
  | 0 => {v}
  | k + 1 => inBall G v k ∪ {u | ∃ w ∈ inBall G v k, ∃ r < G.deg w, G.nbr w r = u}

/-- A rooted, marked, directed graph on the vertex set `ℕ` with root `0` (the paper's `𝒢(𝓧)`,
pp. 7, 24): the ordered inbound-neighbour lists `H.1 x r` (0-based; meaningful for
`r < (H.2 x).deg`) and the full marks `H.2 x = 𝓧_x`. The in-degree and the weights of a vertex are
read from its mark. A locally finite graph seen from its root has countably many vertices, so the
vertex set `ℕ` is no restriction; vertices not reachable from the root are never used. -/
abbrev LimGraph (A : Type*) := (ℕ → ℕ → ℕ) × (ℕ → Mark A)

/-- The weighted digraph underlying a limit graph: in-degree `𝓝_x` and weights `𝓒(x, r+1)` from
the mark, inbound neighbours `𝓛(x, r+1)` from the neighbour lists. -/
def LimGraph.toWDigraph {A : Type*} (H : LimGraph A) : WDigraph ℕ where
  deg x := (H.2 x).deg
  nbr := H.1
  wt x r := (H.2 x).wt r

/-- The full mark of vertex `i` of a graph with attribute vector `y = (a, q, s)` (p. 6):
`X_i = (A_i, Q_i, S_i, D_i⁻, C(i,1) 1(D_i⁻ ≥ 1), C(i,2) 1(D_i⁻ ≥ 2), …)` (0-based weights). -/
def fullMark {V A : Type*} (G : WDigraph V) (y : A × ℝ × ℝ) (i : V) : Mark A :=
  (y.1, y.2.1, y.2.2, G.deg i, fun j => if j < G.deg i then G.wt i j else 0)

/-- The coupling event (4) of Definition 4 (p. 7) at depth `k` and tolerance `ε`, for a graph `G`
with full marks `X`, a vertex `v` and a limit graph `H` rooted at `0`: there is a bijection `θ`
from the depth-`k` in-ball of the root of `H` onto the depth-`k` in-ball of `v` in `G` with
`θ(∅) = v`, which is an isomorphism of ordered in-neighbourhoods at every vertex of depth `< k`
(equal in-degrees, and the `r`-th inbound neighbour is sent to the `r`-th inbound neighbour), and
such that `ρ(X_{θ(x)}, 𝓧_x) ≤ ε` for every vertex `x` of the ball. -/
def CoupledAt {V A : Type*} [PseudoMetricSpace A] (G : WDigraph V) (X : V → Mark A) (v : V)
    (H : LimGraph A) (k : ℕ) (ε : ℝ) : Prop :=
  ∃ θ : inBall H.toWDigraph 0 k ≃ inBall G v k,
    (∀ x : inBall H.toWDigraph 0 k, (x : ℕ) = 0 → (θ x : V) = v) ∧
    (∀ x : inBall H.toWDigraph 0 k, (∃ j < k, (x : ℕ) ∈ inBall H.toWDigraph 0 j) →
      G.deg (θ x) = (H.2 x).deg ∧
        ∀ r < (H.2 x).deg, ∀ y : inBall H.toWDigraph 0 k, (y : ℕ) = H.1 x r →
          G.nbr (θ x) r = (θ y : V)) ∧
    (∀ x : inBall H.toWDigraph 0 k, ρ (X (θ x)) (H.2 x) ≤ ε)

/-! ### Wasserstein distance and Lipschitz kernels -/

/-- The Wasserstein distance `d₁(μ, ν) = inf {E|X − Y| : law(X) = μ, law(Y) = ν}` on `ℝ` (p. 8),
as the optimal transport cost for the cost `|u − w|`. -/
noncomputable def W1 (μ ν : Measure ℝ) : ENNReal :=
  RWPI.SqrtLasso.transportCost (fun u w : ℝ => ENNReal.ofReal |u - w|) μ ν

/-- The law `ν(x)` of `ψ(x, U)` for `U` uniform on `[0, 1]`: the quantile representation of a
mark-indexed family of laws on `ℝ`. -/
noncomputable def kernelLaw {A : Type*} [MeasurableSpace A] (ψ : Mark A → ℝ → ℝ) (x : Mark A) :
    Measure ℝ :=
  (volume.restrict (Icc (0 : ℝ) 1)).map (ψ x)

/-- The Lipschitz condition of Theorem 2 (p. 8): `d₁(ν(x), ν(x̃)) ≤ K ρ(x, x̃)` for all
`x, x̃ ∈ 𝒮`, for the kernel `ν(x) = law ψ(x, U)`. -/
def KernelLipschitz {A : Type*} [PseudoMetricSpace A] [MeasurableSpace A]
    (ψ : Mark A → ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ x ∈ markSpace A, ∀ y ∈ markSpace A,
    W1 (kernelLaw ψ x) (kernelLaw ψ y) ≤ ENNReal.ofReal (K * ρ x y)

/-! ### The random graph sequence -/

/-- The data of a sequence of vertex-weighted directed random (multi)graphs with signals (pp. 6–8),
all on one probability space `Ω`. The `m`-th graph has the `m + 1` vertices `Fin (m + 1)` (the
paper's `G(V_{m+1}, E_{m+1}; 𝒜_{m+1})`; `Fin 0` would admit no uniform vertex):
* `G m ω` — the graph (in-degrees `D_i⁻`, ordered inbound neighbours `L(i, r+1)`, weights
  `C(i, r+1)`);
* `Y m i ω = (A_i, Q_i, S_i)` — the attribute vector of vertex `i`;
* `I m`, `J m` — two uniformly chosen vertices;
* `U m k i` — the uniform variable driving the external signal `W_i^(k)`;
* `V m i` — the uniform variable driving the initial opinion `R_i^(0)`. -/
structure GraphSeq (Ω A : Type*) where
  G : (m : ℕ) → Ω → WDigraph (Fin (m + 1))
  Y : (m : ℕ) → Fin (m + 1) → Ω → A × ℝ × ℝ
  I : (m : ℕ) → Ω → Fin (m + 1)
  J : (m : ℕ) → Ω → Fin (m + 1)
  U : (m : ℕ) → ℕ → Fin (m + 1) → Ω → ℝ
  V : (m : ℕ) → Fin (m + 1) → Ω → ℝ

namespace GraphSeq

variable {Ω A : Type*}

/-- The graph and its attributes as one random element: in-degrees, neighbour lists, weights and
the attribute vectors `𝒜_m = {Y_i}`. -/
def graphData (S : GraphSeq Ω A) (m : ℕ) (ω : Ω) :
    (Fin (m + 1) → ℕ) × (Fin (m + 1) → ℕ → Fin (m + 1)) × (Fin (m + 1) → ℕ → ℝ) ×
      (Fin (m + 1) → A × ℝ × ℝ) :=
  ((S.G m ω).deg, (S.G m ω).nbr, (S.G m ω).wt, fun i => S.Y m i ω)

/-- The attribute vector `𝒜_m = (Y_i)_{i}` of the `m`-th graph. -/
def attrs (S : GraphSeq Ω A) (m : ℕ) (ω : Ω) : Fin (m + 1) → A × ℝ × ℝ := fun i => S.Y m i ω

/-- The σ-algebra `ℱ_m = σ(𝒜_m)` generated by the vertex attributes only (p. 23); it does not
contain the edges or the weights. -/
abbrev 𝓐 [MeasurableSpace A] (S : GraphSeq Ω A) (m : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (S.attrs m) inferInstance

/-- The full mark `X_i` of vertex `i` of the `m`-th graph (p. 6). -/
def mark (S : GraphSeq Ω A) (m : ℕ) (i : Fin (m + 1)) (ω : Ω) : Mark A :=
  fullMark (S.G m ω) (S.Y m i ω) i

/-- All the uniform variables of the `m`-th model in one family: `none` indexes the initial
opinions and `some k` the signals at time `k`. -/
def unif (S : GraphSeq Ω A) (m : ℕ) : Option ℕ × Fin (m + 1) → Ω → ℝ
  | (none, i) => S.V m i
  | (some k, i) => S.U m k i

/-- The external signal `W_i^(k) = ζ(X_i, U_i^(k))`. -/
def W (S : GraphSeq Ω A) (ζ : Mark A → ℝ → ℝ) (m k : ℕ) (i : Fin (m + 1)) (ω : Ω) : ℝ :=
  ζ (S.mark m i ω) (S.U m k i ω)

/-- The initial opinion `R_i^(0) = φ(X_i, V_i)`. -/
def R0 (S : GraphSeq Ω A) (φ : Mark A → ℝ → ℝ) (m : ℕ) (ω : Ω) (i : Fin (m + 1)) : ℝ :=
  φ (S.mark m i ω) (S.V m i ω)

/-- The opinion vector `R^(k)` of recursion (1) on the `m`-th graph. -/
def R (S : GraphSeq Ω A) (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ) (m k : ℕ) (ω : Ω) :
    Fin (m + 1) → ℝ :=
  opinion (S.G m ω) c d (S.R0 φ m ω) (fun t i => S.W ζ m t i ω) k

/-- The stationary vector `R = Σ_{r ≥ 0} Δ̄^r W^(r)` on the `m`-th graph (p. 27). -/
noncomputable def Rstat (S : GraphSeq Ω A) (ζ : Mark A → ℝ → ℝ) (c d : ℝ) (m : ℕ) (ω : Ω) :
    Fin (m + 1) → ℝ :=
  stationary (S.G m ω) c d (fun t i => S.W ζ m t i ω)

end GraphSeq

/-- The standing assumptions on a random graph sequence with signals (pp. 3–4, 6, 8, 23), relative
to a family `𝓖 m` of sub-σ-algebras ("the graph and everything coupled to it"):
1. the parameters: `c ∈ [0, 1)`, `d ∈ (0, 1]`, `c + d ≤ 1`;
2. every graph has weights in `[0, 1]` summing to `c` at each vertex with `D_i⁻ > 0`;
3. attributes: `Q_i ∈ [−1, 1]`, `S_i ∈ {0, 1}`;
4. the graph, the attributes and `I m`, `J m` are `𝓖 m`-measurable; `I m`, `J m` are uniform on
   the vertices and `I m`, `J m`, the graph with its attributes are mutually independent;
5. the uniforms `U m k i`, `V m i` are measurable, uniform on `[0, 1]`, mutually independent and
   independent of `𝓖 m`: so, given the graph, the signals `W_i^(k) = ζ(X_i, U_i^(k))` are
   independent, and i.i.d. in `k` with law `ν(X_i)`; the initial opinions
   `R_i^(0) = φ(X_i, V_i)` are conditionally independent of the signals;
6. `ζ`, `φ` are measurable, `φ` takes values in `[−1, 1]`, and the signals satisfy
   `|W_i^(k)| ≤ d + c − Σ_r C(i, r)` (p. 4). -/
structure GraphSeqModel {Ω A : Type*} [MeasurableSpace Ω] [PseudoMetricSpace A]
    [MeasurableSpace A] (P : Measure Ω) (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω)
    (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ) : Prop where
  c_nonneg : 0 ≤ c
  c_lt_one : c < 1
  d_pos : 0 < d
  d_le_one : d ≤ 1
  cd_le_one : c + d ≤ 1
  valid : ∀ m ω, (S.G m ω).Valid c
  q_mem : ∀ m i ω, (S.Y m i ω).2.1 ∈ Icc (-1 : ℝ) 1
  s_mem : ∀ m i ω, (S.Y m i ω).2.2 = 0 ∨ (S.Y m i ω).2.2 = 1
  le : ∀ m, 𝓖 m ≤ ‹MeasurableSpace Ω›
  measurable_graph : ∀ m, Measurable[𝓖 m] (S.graphData m)
  measurable_I : ∀ m, Measurable[𝓖 m] (S.I m)
  measurable_J : ∀ m, Measurable[𝓖 m] (S.J m)
  I_unif : ∀ m, HasLaw (S.I m) (PMF.uniformOfFintype (Fin (m + 1))).toMeasure P
  J_unif : ∀ m, HasLaw (S.J m) (PMF.uniformOfFintype (Fin (m + 1))).toMeasure P
  indep_I : ∀ m, IndepFun (S.I m) (fun ω => (S.J m ω, S.graphData m ω)) P
  indep_J : ∀ m, IndepFun (S.J m) (S.graphData m) P
  measurable_unif : ∀ m p, Measurable (S.unif m p)
  unif_law : ∀ m p, HasLaw (S.unif m p) (volume.restrict (Icc (0 : ℝ) 1)) P
  unif_iIndep : ∀ m, iIndepFun (S.unif m) P
  unif_indep_struct : ∀ m,
    Indep (MeasurableSpace.comap (fun ω p => S.unif m p ω) inferInstance) (𝓖 m) P
  measurable_ζ : Measurable (Function.uncurry ζ)
  measurable_φ : Measurable (Function.uncurry φ)
  φ_mem : ∀ x v, φ x v ∈ Icc (-1 : ℝ) 1
  signal_bound : ∀ m k i ω, |S.W ζ m k i ω| ≤ (S.G m ω).budget c d i

/-- **Strong coupling** (Definition 4, pp. 7–8), second bullet, stated on the given space: for
every `k ≥ 1` and `ε > 0` there are two random limit graphs `H m`, `H' m` (`𝓖 m`-measurable), each
with law `μlim` (the law of `𝒢(𝓧)`) and independent of each other, and `𝓖 m`-measurable events
`E m`, `E' m` contained in the coupling events `ℰ_{I}^{(k,ε)}` (for `I m`, `H m`) and
`ℰ_{J}^{(k,ε)}` (for `J m`, `H' m`), such that `P(E m ∩ E' m | 𝒜_m) → 1` in probability. The first
bullet of Definition 4 follows from the second, since `E m ∩ E' m ⊆ E m`.

**Added (gap of the page):** on `E m ∩ E' m` the depth-`k` in-components of `I m` and `J m` are
disjoint. The proof of Theorem 7 (p. 25) gives the graph vertices of the two in-components their
own optimally coupled signals and makes the two limit copies' signals independent, which is
consistent only when the in-components are disjoint. Without this clause Definition 4 admits a
graph in which every vertex has the same single inbound neighbour (a hub): the hub's signals are
shared by every vertex and `(1/n) Σ_i f(R_i^(k))` does not converge to a constant. -/
def StrongCoupling {Ω A : Type*} [MeasurableSpace Ω] [PseudoMetricSpace A] [MeasurableSpace A]
    (P : Measure Ω) (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (μlim : Measure (LimGraph A)) :
    Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε →
    ∃ (H H' : ℕ → Ω → LimGraph A) (E E' : ℕ → Set Ω),
      (∀ m, Measurable[𝓖 m] (H m)) ∧ (∀ m, Measurable[𝓖 m] (H' m)) ∧
      (∀ m, HasLaw (H m) μlim P) ∧ (∀ m, HasLaw (H' m) μlim P) ∧
      (∀ m, IndepFun (H m) (H' m) P) ∧
      (∀ m, MeasurableSet[𝓖 m] (E m)) ∧ (∀ m, MeasurableSet[𝓖 m] (E' m)) ∧
      (∀ m, E m ⊆ {ω | CoupledAt (S.G m ω) (fun i => S.mark m i ω) (S.I m ω) (H m ω) k ε}) ∧
      (∀ m, E' m ⊆ {ω | CoupledAt (S.G m ω) (fun i => S.mark m i ω) (S.J m ω) (H' m ω) k ε}) ∧
      (∀ m, E m ∩ E' m ⊆
        {ω | Disjoint (inBall (S.G m ω) (S.I m ω) k) (inBall (S.G m ω) (S.J m ω) k)}) ∧
      TendstoInMeasure P
        (fun m => P[(E m ∩ E' m).indicator (fun _ => (1 : ℝ)) | S.𝓐 m]) atTop (fun _ => 1)

/-! ### Conditional laws given the attributes and empirical averages -/

/-- The Wasserstein distance `d₁` on `ℝ^{k+1}` for the sup distance
`max_{0 ≤ r ≤ k} |x_r − y_r|` (the `edist` of the product space `Fin (k+1) → ℝ`). -/
noncomputable def W1vec {k : ℕ} (μ ν : Measure (Fin (k + 1) → ℝ)) : ENNReal :=
  RWPI.SqrtLasso.transportCost (fun x y : Fin (k + 1) → ℝ => edist x y) μ ν

/-- The conditional law, given `𝒜_m`, of the trajectory `(R_{I_m}^(0), …, R_{I_m}^(k))` of the
uniformly chosen vertex `I_m`, evaluated at the attribute vector `𝒜_m(ω)` (a regular conditional
distribution; it is determined for `P`-almost every `ω`). -/
noncomputable def trajCondLaw {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsFiniteMeasure P] (S : GraphSeq Ω A) (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ)
    (m k : ℕ) (ω : Ω) : Measure (Fin (k + 1) → ℝ) :=
  condDistrib (fun ω' (r : Fin (k + 1)) => S.R ζ φ c d m r ω' (S.I m ω')) (S.attrs m) P
    (S.attrs m ω)

/-- The conditional law, given `𝒜_m`, of the stationary opinion `R_{I_m}` of the uniformly chosen
vertex, evaluated at `𝒜_m(ω)`. -/
noncomputable def statCondLaw {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsFiniteMeasure P] (S : GraphSeq Ω A) (ζ : Mark A → ℝ → ℝ) (c d : ℝ)
    (m : ℕ) (ω : Ω) : Measure ℝ :=
  condDistrib (fun ω' => S.Rstat ζ c d m ω' (S.I m ω')) (S.attrs m) P (S.attrs m ω)

/-- The empirical average `(1/n) Σ_{i=1}^{n} f(x_i)` over the `n = m + 1` vertices. -/
noncomputable def empAvg {m : ℕ} (f : ℝ → ℝ) (x : Fin (m + 1) → ℝ) : ℝ :=
  (1 / ((m : ℝ) + 1)) * ∑ i, f (x i)

end DirectedOpinion.Typical


