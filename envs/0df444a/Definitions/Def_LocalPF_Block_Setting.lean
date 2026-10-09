-- Prove2me | Definitions.Def_LocalPF_Block_Setting
-- name    : LocalPF_Block_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:20:32.624973+00:00
-- url     : https://prove2.me/theorems/77756a12-01bb-4224-957c-f5bcd1d765b8
-- title:
--   §1.1 and §2.1–2.2, pp. 5–6, 13–16 — local graph model, operators P, C, B, the filter, block filter and block particle filter, local norms
-- statement:
--   This file sets up the high-dimensional hidden Markov model of Rebeschini and van Handel and the three filters compared in the paper.
--
--   **Graph quantities.** Let $G=(V,E)$ be a finite graph with graph distance $d$ (the length of a shortest path; $d=+\infty$ between different components), and fix a neighbourhood size $r\in\mathbb N$. The $r$-neighbourhood of a vertex is $N(v)=\{v'\in V: d(v,v')\le r\}$, and the $r$-inner boundary of $J\subseteq V$ is $\partial J=\{v\in J: N(v)\not\subseteq J\}$. For $J,J'\subseteq V$, $d(J,J')=\min_{v\in J}\min_{v'\in J'}d(v,v')$, which is $+\infty$ if one of the sets is empty or no path joins them. A partition $\mathcal K$ of $V$ into blocks is given by a block label map $V\to\iota$, the block $K$ with label $k$ being the set of vertices labelled $k$. The local quantities are
--   $$|\mathcal K|_\infty=\max_{K\in\mathcal K}\operatorname{card}K,\qquad \Delta=\max_{v\in V}\operatorname{card}N(v),\qquad \Delta_{\mathcal K}=\max_{K\in\mathcal K}\operatorname{card}\{K'\in\mathcal K: d(K,K')\le r\}.$$
--   For $\beta\in\mathbb R$ and $d\in\mathbb N\cup\{+\infty\}$, the weight $e^{-\beta d}$ is taken to be $0$ when $d=+\infty$; likewise $q^d$ is $0$ when $d=+\infty$.
--
--   **The model.** Each vertex carries a Polish state space $\mathbb X^v$ with a reference measure $\psi^v$ and a Polish observation space $\mathbb Y^v$; $\mathbb X=\prod_v\mathbb X^v$ and $\psi=\bigotimes_v\psi^v$. The local model consists of transition densities $p^v:\mathbb X\times\mathbb X^v\to\mathbb R_+$, jointly measurable, with $\int p^v(x,z^v)\,\psi^v(dz^v)=1$ for every $x$, and *local*: $p^v(x,z^v)=p^v(\tilde x,z^v)$ whenever $x^{N(v)}=\tilde x^{N(v)}$; and observation densities $g^v:\mathbb X^v\times\mathbb Y^v\to\mathbb R_+$, jointly measurable. The full densities are $p(x,z)=\prod_v p^v(x,z^v)$ and $g(x,y)=\prod_v g^v(x^v,y^v)$.
--
--   **Operators.** For a measure $\rho$ on $\mathbb X$ and an observation $y\in\mathbb Y$:
--   $$(\mathsf P\rho)(f)=\int f(x')\,p(x,x')\,\psi(dx')\,\rho(dx),\qquad (\mathsf C\rho)(f)=\frac{\int f(x)\,g(x,y)\,\rho(dx)}{\int g(x,y)\,\rho(dx)},$$
--   and $\mathsf C_n$ is $\mathsf C$ with the $n$-th observation $Y_n$. The blocking operator is $\mathsf B\rho=\bigotimes_{K\in\mathcal K}\mathsf B^K\rho$, where $\mathsf B^K\rho$ is the marginal of $\rho$ on $\prod_{v\in K}\mathbb X^v$; more generally $\bigotimes_K\mu^K$ denotes the product of measures $\mu^K$ on the block spaces, viewed as a measure on $\mathbb X$. The empirical measure of a particle array $(x(1),\dots,x(N))$ is $\frac1N\sum_{i=1}^N\delta_{x(i)}$. The reweighted measure $\mu_\Lambda(A)=\int 1_A\Lambda\,d\mu/\int\Lambda\,d\mu$ is also defined here.
--
--   **Filters.** Fix an observation sequence $(Y_n)_{n\ge1}$ and an initial state $x\in\mathbb X$.
--   1. The filter: $\pi^x_0=\delta_x$, $\pi^x_n=\mathsf F_n\pi^x_{n-1}$ with $\mathsf F_n=\mathsf C_n\mathsf P$; more generally $\mathsf F_{s+m}\cdots\mathsf F_{s+1}\mu$ started at time $s$ from $\mu$.
--   2. The block filter: $\tilde\pi^x_0=\delta_x$, $\tilde\pi^x_n=\tilde{\mathsf F}_n\tilde\pi^x_{n-1}$ with $\tilde{\mathsf F}_n=\mathsf C_n\mathsf B\mathsf P$; more generally $\tilde{\mathsf F}_{s+m}\cdots\tilde{\mathsf F}_{s+1}\mu$.
--   3. The block particle filter with $N$ particles, $\hat\pi^x_n=\hat{\mathsf F}_n\hat\pi^x_{n-1}$ with $\hat{\mathsf F}_n=\mathsf C_n\mathsf B\mathsf S^N\mathsf P$: given the past, the $N$ particles drawn at step $n$ are i.i.d. with law $\mathsf P\hat\pi^x_{n-1}$, and $\hat\pi^x_n=\mathsf C_n\mathsf B(\frac1N\sum_i\delta_{x_n(i)})$. It is represented by the map from the step-$n$ particle array to $\hat\pi^x_n$ (with $\hat\pi^x_0=\delta_x$), together with the law of that array (at step $0$ the array is the constant array $x$).
--
--   **Norms.** For measures $\rho,\rho'$ on a measurable space, $\|\rho-\rho'\|=\sup_{|f|\le1}|\rho(f)-\rho'(f)|$, the supremum over measurable $f$ (twice the usual total variation distance). For $J\subseteq V$, $\mathbb X^J$ is the class of measurable $f:\mathbb X\to\mathbb R$ with $f(x)=f(\tilde x)$ whenever $x^J=\tilde x^J$, and $\|\rho-\rho'\|_J=\sup_{f\in\mathbb X^J,|f|\le1}|\rho(f)-\rho'(f)|$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The graph distance is `SimpleGraph.edist` with values in $\mathbb N\cup\{\infty\}$. The partition is a block label map `blk : V → ι` (surjectivity, i.e. nonempty blocks, is a hypothesis of the theorems). The observation $Y_n$ is `y n`, $n\ge1$. The norms are suprema in $[0,\infty]$, never real suprema. $\mathsf C$ divides by $\int g\,d\rho$ in $[0,\infty]$; the theorems carry hypotheses under which this normaliser is positive and finite. The reference measures of the observations and the normalisation of $g^v$ do not enter any statement and are omitted.
-- source:
--   Rebeschini & van Handel, Can Local Particle Filters Beat the Curse of Dimensionality?, arXiv:1301.6585v2 (reprint of Ann. Appl. Probab. 25(5), 2015), pp. 4–6, 13–16, 25, 27, §1.1, §2.1–2.2, §3.1–3.2, Algorithm 2

import Mathlib

namespace LocalPF.Block

open MeasureTheory
open scoped ENNReal

noncomputable section

/-! ### Graph quantities (§2.1, p. 13; §2.2, p. 16) -/

section Graph

variable {V : Type*} [Fintype V]

/-- The `r`-neighbourhood `N(v) = {v' ∈ V : d(v, v') ≤ r}` of a vertex, for the graph distance
`d = G.edist` (valued in `ℕ∞`, `⊤` between vertices in different components). -/
def nbhd (G : SimpleGraph V) (r : ℕ) (v : V) : Finset V :=
  open Classical in Finset.univ.filter (fun v' => G.edist v v' ≤ (r : ℕ∞))

/-- The `r`-inner boundary `∂J = {v ∈ J : N(v) ⊈ J}` of a set of vertices `J`. -/
def innerBdry (G : SimpleGraph V) (r : ℕ) (J : Finset V) : Finset V :=
  open Classical in J.filter (fun v => ¬ nbhd G r v ⊆ J)

/-- The distance `d(J, J') = min_{v ∈ J} min_{v' ∈ J'} d(v, v')` between two sets of vertices,
valued in `ℕ∞`; it is `⊤` when one of the sets is empty or no path joins them. -/
def setDist (G : SimpleGraph V) (J J' : Finset V) : ℕ∞ :=
  ⨅ v ∈ J, ⨅ v' ∈ J', G.edist v v'

/-- `decayPow q d = q ^ d` for a finite distance `d`, and `0` for `d = ⊤`. -/
def decayPow (q : ℝ) (d : ℕ∞) : ℝ :=
  if d = ⊤ then 0 else q ^ d.toNat

/-- `decay β d = e^{-β d}`, with `e^{-β·∞} = 0`. -/
def decay (β : ℝ) (d : ℕ∞) : ℝ :=
  decayPow (Real.exp (-β)) d

/-- The block `K = {v : blk v = k}` of the partition `𝒦` given by the block label map `blk`. -/
def block {ι : Type*} (blk : V → ι) (k : ι) : Finset V :=
  open Classical in Finset.univ.filter (fun v => blk v = k)

/-- `|𝒦|_∞ = max_{K ∈ 𝒦} card K`. -/
def maxBlock {ι : Type*} [Fintype ι] (blk : V → ι) : ℕ :=
  Finset.univ.sup (fun k => (block blk k).card)

/-- `Δ = max_{v ∈ V} card {v' ∈ V : d(v, v') ≤ r}`. -/
def maxNbhd (G : SimpleGraph V) (r : ℕ) : ℕ :=
  Finset.univ.sup (fun v => (nbhd G r v).card)

/-- `Δ_𝒦 = max_{K ∈ 𝒦} card {K' ∈ 𝒦 : d(K, K') ≤ r}`. -/
def maxBlockNbhd {ι : Type*} [Fintype ι] (G : SimpleGraph V) (r : ℕ) (blk : V → ι) : ℕ :=
  open Classical in
  Finset.univ.sup (fun k =>
    (Finset.univ.filter (fun k' => setDist G (block blk k) (block blk k') ≤ (r : ℕ∞))).card)

end Graph

/-! ### The model (§1.1, pp. 4–5; §2.1, p. 13) -/

section Model

variable {V : Type*} [Fintype V] {Xs : V → Type*} [∀ v, MeasurableSpace (Xs v)]
  {Ys : V → Type*} [∀ v, MeasurableSpace (Ys v)]

/-- The standing assumptions on the local model (§2.1, p. 13): `p^v : 𝕏 × 𝕏^v → ℝ₊` is a
jointly measurable transition density with respect to `ψ^v` that depends on `x` only through
`x^{N(v)}`, and `g^v : 𝕏^v × 𝕐^v → ℝ₊` is jointly measurable. -/
structure IsLocalModel (G : SimpleGraph V) (r : ℕ) (ψ : ∀ v, Measure (Xs v))
    (p : ∀ v, (∀ w, Xs w) → Xs v → ℝ) (g : ∀ v, Xs v → Ys v → ℝ) : Prop where
  p_measurable : ∀ v, Measurable (fun xz : (∀ w, Xs w) × Xs v => p v xz.1 xz.2)
  p_nonneg : ∀ v x z, 0 ≤ p v x z
  p_density : ∀ v x, ∫⁻ z, ENNReal.ofReal (p v x z) ∂(ψ v) = 1
  p_local : ∀ v (x x' : ∀ w, Xs w) (z : Xs v),
    (∀ w ∈ nbhd G r v, x w = x' w) → p v x z = p v x' z
  g_measurable : ∀ v, Measurable (fun ξη : Xs v × Ys v => g v ξη.1 ξη.2)
  g_nonneg : ∀ v ξ η, 0 ≤ g v ξ η

/-- The prediction operator `(𝖯ρ)(f) = ∫ f(x') p(x, x') ψ(dx') ρ(dx)`, with
`p(x, z) = ∏_v p^v(x, z^v)` and `ψ = ⊗_v ψ^v`. -/
def predict (ψ : ∀ v, Measure (Xs v)) (p : ∀ v, (∀ w, Xs w) → Xs v → ℝ)
    (ρ : Measure (∀ v, Xs v)) : Measure (∀ v, Xs v) :=
  ρ.bind (fun x => (Measure.pi ψ).withDensity (fun z => ENNReal.ofReal (∏ v, p v x (z v))))

/-- The observation likelihood `x ↦ g(x, y) = ∏_v g^v(x^v, y^v)`. -/
def obsLik (g : ∀ v, Xs v → Ys v → ℝ) (y : ∀ v, Ys v) (x : ∀ v, Xs v) : ℝ≥0∞ :=
  ENNReal.ofReal (∏ v, g v (x v) (y v))

/-- The correction operator `(𝖢ρ)(f) = ∫ f(x) g(x, y) ρ(dx) / ∫ g(x, y) ρ(dx)` for the
observation `y` (`𝖢_n` is `correct g Y_n`). -/
def correct (g : ∀ v, Xs v → Ys v → ℝ) (y : ∀ v, Ys v)
    (ρ : Measure (∀ v, Xs v)) : Measure (∀ v, Xs v) :=
  (∫⁻ x, obsLik g y x ∂ρ)⁻¹ • ρ.withDensity (obsLik g y)

/-- The product `⊗_{K ∈ 𝒦} μ^K` of measures on the block spaces `∏_{v ∈ K} 𝕏^v`,
reassembled as a measure on `𝕏 = ∏_{v ∈ V} 𝕏^v`. -/
def blockProd {ι : Type*} [Fintype ι] (blk : V → ι)
    (μK : ∀ k, Measure (∀ v : {v // blk v = k}, Xs v.1)) : Measure (∀ v, Xs v) :=
  (Measure.pi μK).map (fun z v => z (blk v) ⟨v, rfl⟩)

/-- The block marginal `𝖡^K ρ` of `ρ` on `∏_{v ∈ K} 𝕏^v`. -/
def blockMarginal {ι : Type*} (blk : V → ι) (ρ : Measure (∀ v, Xs v)) (k : ι) :
    Measure (∀ v : {v // blk v = k}, Xs v.1) :=
  ρ.map (fun x v => x v.1)

/-- The blocking operator `𝖡ρ = ⊗_{K ∈ 𝒦} 𝖡^K ρ`. -/
def blocking {ι : Type*} [Fintype ι] (blk : V → ι) (ρ : Measure (∀ v, Xs v)) :
    Measure (∀ v, Xs v) :=
  blockProd blk (blockMarginal blk ρ)

/-- The empirical measure `(1/N) Σ_{i=1}^N δ_{a(i)}` of a particle array `a`. -/
def empirical {S : Type*} [MeasurableSpace S] {N : ℕ} (a : Fin N → S) : Measure S :=
  (N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (a i)

/-- The filter recursion started at time `s` from `μ`: `filtFrom … s μ m = 𝖥_{s+m} ⋯ 𝖥_{s+1} μ`
with `𝖥_n = 𝖢_n 𝖯` and observation `Y_n = y n`. -/
def filtFrom (ψ : ∀ v, Measure (Xs v)) (p : ∀ v, (∀ w, Xs w) → Xs v → ℝ)
    (g : ∀ v, Xs v → Ys v → ℝ) (y : ℕ → ∀ v, Ys v) (s : ℕ) (μ : Measure (∀ v, Xs v)) :
    ℕ → Measure (∀ v, Xs v)
  | 0 => μ
  | m + 1 => correct g (y (s + m + 1)) (predict ψ p (filtFrom ψ p g y s μ m))

/-- The nonlinear filter `π^x_n` started at `δ_x` (`π^x_0 = δ_x`, `π^x_n = 𝖢_n 𝖯 π^x_{n-1}`). -/
def filt (ψ : ∀ v, Measure (Xs v)) (p : ∀ v, (∀ w, Xs w) → Xs v → ℝ)
    (g : ∀ v, Xs v → Ys v → ℝ) (y : ℕ → ∀ v, Ys v) (x : ∀ v, Xs v) (n : ℕ) :
    Measure (∀ v, Xs v) :=
  filtFrom ψ p g y 0 (Measure.dirac x) n

/-- The block filter recursion started at time `s` from `μ`:
`blockFiltFrom … s μ m = 𝖥̃_{s+m} ⋯ 𝖥̃_{s+1} μ` with `𝖥̃_n = 𝖢_n 𝖡 𝖯`. -/
def blockFiltFrom {ι : Type*} [Fintype ι] (ψ : ∀ v, Measure (Xs v))
    (p : ∀ v, (∀ w, Xs w) → Xs v → ℝ) (g : ∀ v, Xs v → Ys v → ℝ) (blk : V → ι)
    (y : ℕ → ∀ v, Ys v) (s : ℕ) (μ : Measure (∀ v, Xs v)) : ℕ → Measure (∀ v, Xs v)
  | 0 => μ
  | m + 1 =>
      correct g (y (s + m + 1)) (blocking blk (predict ψ p (blockFiltFrom ψ p g blk y s μ m)))

/-- The block filter `π̃^x_n` started at `δ_x`. -/
def blockFilt {ι : Type*} [Fintype ι] (ψ : ∀ v, Measure (Xs v))
    (p : ∀ v, (∀ w, Xs w) → Xs v → ℝ) (g : ∀ v, Xs v → Ys v → ℝ) (blk : V → ι)
    (y : ℕ → ∀ v, Ys v) (x : ∀ v, Xs v) (n : ℕ) : Measure (∀ v, Xs v) :=
  blockFiltFrom ψ p g blk y 0 (Measure.dirac x) n

/-- The block particle filter `π̂^x_n` (Algorithm 2, p. 15) as a function of the particle array
`a` drawn at step `n`: `π̂^x_0 = δ_x`, and `π̂^x_{n+1} = 𝖢_{n+1} 𝖡 (1/N Σ_i δ_{a(i)})`. -/
def bpf {ι : Type*} [Fintype ι] (g : ∀ v, Xs v → Ys v → ℝ) (blk : V → ι)
    (y : ℕ → ∀ v, Ys v) (x : ∀ v, Xs v) (N : ℕ) : ℕ → (Fin N → ∀ v, Xs v) → Measure (∀ v, Xs v)
  | 0, _ => Measure.dirac x
  | n + 1, a => correct g (y (n + 1)) (blocking blk (empirical a))

/-- The law of the particle array of the block particle filter at step `n`: given the past, the
`N` particles drawn at step `n + 1` are i.i.d. with law `𝖯 π̂^x_n` (so that
`π̂^x_{n+1} = 𝖢_{n+1} 𝖡 𝖲^N 𝖯 π̂^x_n`). At step `0` the array is the constant array `x`. -/
def bpfLaw {ι : Type*} [Fintype ι] (ψ : ∀ v, Measure (Xs v))
    (p : ∀ v, (∀ w, Xs w) → Xs v → ℝ) (g : ∀ v, Xs v → Ys v → ℝ) (blk : V → ι)
    (y : ℕ → ∀ v, Ys v) (x : ∀ v, Xs v) (N : ℕ) : ℕ → Measure (Fin N → ∀ v, Xs v)
  | 0 => Measure.dirac (fun _ => x)
  | n + 1 => (bpfLaw ψ p g blk y x N n).bind
      (fun a => Measure.pi (fun _ : Fin N => predict ψ p (bpf g blk y x N n a)))

end Model

/-! ### Norms (§1.1, p. 6; §2.2, p. 16; §3.2, p. 27) -/

section Norms

/-- The total variation norm `‖ρ − ρ'‖ = sup_{|f| ≤ 1} |ρ(f) − ρ'(f)|` (sup over measurable `f`),
valued in `ℝ≥0∞`. -/
def tv {S : Type*} [MeasurableSpace S] (ρ ρ' : Measure S) : ℝ≥0∞ :=
  ⨆ (f : S → ℝ) (_ : Measurable f ∧ ∀ s, |f s| ≤ 1),
    ENNReal.ofReal |∫ s, f s ∂ρ - ∫ s, f s ∂ρ'|

/-- The reweighted measure `µ_Λ(A) = ∫ 1_A Λ dµ / ∫ Λ dµ` (Lemma 4.2, p. 32). -/
def reweight {S : Type*} [MeasurableSpace S] (Λ : S → ℝ) (μ : Measure S) : Measure S :=
  (∫⁻ s, ENNReal.ofReal (Λ s) ∂μ)⁻¹ • μ.withDensity (fun s => ENNReal.ofReal (Λ s))

variable {V : Type*} {Xs : V → Type*} [∀ v, MeasurableSpace (Xs v)]

/-- `f ∈ 𝕏^J` with `|f| ≤ 1`: `f` is measurable, depends only on the coordinates in `J`, and is
bounded by `1`. -/
def IsTest (J : Set V) (f : (∀ v, Xs v) → ℝ) : Prop :=
  Measurable f ∧ (∀ x x' : ∀ v, Xs v, (∀ v ∈ J, x v = x' v) → f x = f x') ∧ ∀ x, |f x| ≤ 1

/-- The local total variation distance `‖ρ − ρ'‖_J = sup_{f ∈ 𝕏^J, |f| ≤ 1} |ρ(f) − ρ'(f)|`. -/
def locTV (J : Set V) (ρ ρ' : Measure (∀ v, Xs v)) : ℝ≥0∞ :=
  ⨆ (f : (∀ v, Xs v) → ℝ) (_ : IsTest J f), ENNReal.ofReal |∫ x, f x ∂ρ - ∫ x, f x ∂ρ'|

end Norms

end

end LocalPF.Block


