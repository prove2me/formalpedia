-- Prove2me | Definitions.Def_PDSEquiv_Laws
-- name    : PDSEquiv_Laws
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:00:50.661691+00:00
-- url     : https://prove2.me/theorems/270716f1-7a5e-4f4c-8ba7-2b2861b6d649
-- title:
--   Graphs on $[N]$, $\mathrm{ER}(N,q)$, $\mathrm{PDS}(N,k,p,q)$, $\widetilde{\mathrm{PDS}}(N,k,p,q)$, the advantage and the benchmark $\Lambda_N(k)$
-- statement:
--   A graph on $[N]$ is an element of $\mathcal G_N=\{0,1\}^{\binom{[N]}{2}}$: one bit $G_e$ per pair $e=\{i,j\}$, $i<j$. For densities $q,p$:
--
--   1. $\mathrm{ER}(N,q)$ makes each pair an edge independently with probability $q$; its mass is $\prod_e q^{G_e}(1-q)^{1-G_e}$.
--   2. For a set $C\subseteq[N]$, the planted mass $\prod_e \mathrm{Ber}(r_e)(G_e)$ uses $r_e=p$ when both ends of $e$ lie in $C$ and $r_e=q$ otherwise.
--   3. The **fixed-$k$ model** $\mathrm{PDS}(N,k,p,q)$ draws $C$ uniformly among the $k$-subsets of $[N]$ and then $G$ from the planted mass; the joint law of $(G,C)$ is the planted mass divided by $\binom Nk$ on sets of size $k$.
--   4. The **binomial-$k$ model** $\widetilde{\mathrm{PDS}}(N,x,p,q)$, for real $x\in[0,N]$, draws $C\sim\mathrm{Bin}([N],x/N)$ instead; the joint mass is $(x/N)^{|C|}(1-x/N)^{N-|C|}$ times the planted mass.
--   5. For a distinguisher with acceptance probabilities $a(G)$ (so its $\pm1$ output has mean $2a(G)-1$), the advantage between laws $D_1,D_2$ is
--   $$\mathrm{adv}(D_1,D_2)=\bigl|\mathbb E_{D_1}[2a-1]-\mathbb E_{D_2}[2a-1]\bigr|=2\,\bigl|\Pr_{D_1}[\text{accept}]-\Pr_{D_2}[\text{accept}]\bigr|,$$
--   and for a $[-1,1]$-valued $f$ the same absolute difference of expectations is $\mathrm{adv}_f$.
--   6. The edge-counting benchmark (4) is
--   $$\Lambda_N(k)=\frac{(p-q)\,k(k-1)}{\sqrt{\pi\,q(1-q)\,N(N-1)}}.$$
--
--   Also defined: the pull-back of a graph along an injection of vertex sets and permutation invariance (a value unchanged by relabeling the vertices). These are the laws and quantities in which all of the paper's assertions are stated.
--
--   **Formalization Note** A graph is a Boolean function on the pairs $i<j$ of `Fin N`. $\mathrm{ER}(N,q)$ is the published $q$-biased product weight `OAI.Problem313.BiasedFourier.weight` on this cube. The laws are real-valued finite mass functions. In the binomial mass $x/N=0$ at $N=0$ and $0^0=1$. $\Lambda_N(k)=0$ at $N\le1$, where the square root vanishes; every statement using it is for large $N$.
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), §4, p.12 (graphs, ER, PDS, binomial PDS), §4.2, p.13 (advantage, eq. (4)), §4.3, p.14 (permutation invariance)

import Mathlib
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis

set_option autoImplicit false

open scoped BigOperators

namespace PDSEquiv

noncomputable section

/-!
# Graphs, the three laws, the benchmark and the advantage

S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), §4, pp.12–13.

**Formalization Note.** A graph on `[N]` is a Boolean function on the pairs `i < j` of `Fin N`, the
page's identification of `G_N` with `{0,1}^([N] choose 2)`. `ER(N, q)` is the published `q`-biased
product weight `OAI.Problem313.BiasedFourier.weight` on the cube `{0,1}^Pair N`, reused. The laws are real-valued finite mass
functions, so these definitions and the milestones written with them need no measure theory. In
`pdsbJoint`, `x / N` is `0` at `N = 0` and Lean's `0 ^ 0 = 1`; the law is a probability law for
`0 ≤ x ≤ N`. In `Lam`, the square root vanishes at `N ≤ 1` and the benchmark is then `0`; every
statement using it is for large `N` or for `2 ≤ k ≤ N`.
-/

/-- The pairs `{i, j}` with `i < j` of `[N]`. -/
abbrev Pair (N : ℕ) := {e : Fin N × Fin N // e.1 < e.2}

/-- The graphs on `[N]`: `G_N = {0,1}^([N] choose 2)`, §4, p.12. -/
abbrev Graph (N : ℕ) := Pair N → Bool

/-- The adjacency of two vertices in a graph; `false` on `u = v`. -/
def gAdj {N : ℕ} (G : Graph N) (u v : Fin N) : Bool :=
  if h : u < v then G ⟨(u, v), h⟩ else if h' : v < u then G ⟨(v, u), h'⟩ else false

/-- The graph `H` on `[n]` with `H_{ij} = G_{φ(i)φ(j)}`, the pull-back of `G` along an injection. -/
def comap {n N : ℕ} (φ : Fin n ↪ Fin N) (G : Graph N) : Graph n :=
  fun e => gAdj G (φ e.1.1) (φ e.1.2)

/-- A function on graphs is permutation-invariant if its value is unchanged by relabeling the
vertices, §4.3, p.14. -/
def PermInvariant {n : ℕ} (w : Graph n → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (G : Graph n), w (comap σ.toEmbedding G) = w G

/-- The mass of `b` under `Ber(θ)`. -/
def ber (θ : ℝ) (b : Bool) : ℝ := if b then θ else 1 - θ

/-- The mass of `G` when each pair inside `C` is `Ber(p)` and each other pair is `Ber(q)`, all
independent. -/
def pairMass {N : ℕ} (C : Finset (Fin N)) (p q : ℝ) (G : Graph N) : ℝ :=
  ∏ e : Pair N, if e.1.1 ∈ C ∧ e.1.2 ∈ C then ber p (G e) else ber q (G e)

/-- `ER(N, q)`, §4.1, p.12: every pair an edge independently with probability `q`, i.e. the published
`q`-biased product weight `∏ e, q^{G_e} (1 − q)^{1 − G_e}` on `{0,1}^Pair N`. -/
def erMass (N : ℕ) (q : ℝ) (G : Graph N) : ℝ := OAI.Problem313.BiasedFourier.weight q G

/-- The joint law of `(G, C) ∼ PDS(N, k, p, q)`: `C` uniform among the `k`-subsets, §4.1, p.12. -/
def pdsJoint (N k : ℕ) (p q : ℝ) (G : Graph N) (C : Finset (Fin N)) : ℝ :=
  if C.card = k then pairMass C p q G / (N.choose k : ℝ) else 0

/-- `PDS(N, k, p, q)`, the fixed-k model, §4.1, p.12. -/
def pdsMass (N k : ℕ) (p q : ℝ) (G : Graph N) : ℝ := ∑ C, pdsJoint N k p q G C

/-- The joint law of `(G, C) ∼ P̃DS(N, x, p, q)`: `C ∼ Bin([N], x/N)`, §4.1, p.12. -/
def pdsbJoint (N : ℕ) (x p q : ℝ) (G : Graph N) (C : Finset (Fin N)) : ℝ :=
  (x / N) ^ C.card * (1 - x / N) ^ (N - C.card) * pairMass C p q G

/-- `P̃DS(N, x, p, q)`, the binomial-k model with mean `x`, §4.1, p.12. -/
def pdsbMass (N : ℕ) (x p q : ℝ) (G : Graph N) : ℝ := ∑ C, pdsbJoint N x p q G C

/-- The expectation of `f` under the mass function `μ`. -/
def expect {N : ℕ} (μ : Graph N → ℝ) (f : Graph N → ℝ) : ℝ := ∑ G, μ G * f G

open Classical in
/-- The probability of the event `E` under the mass function `μ`. -/
def prob {N : ℕ} (μ : Graph N → ℝ) (E : Graph N → Prop) : ℝ := ∑ G, if E G then μ G else 0

/-- `adv_f(D₁, D₂) = |E_{D₁} f − E_{D₂} f|` for a `[−1, 1]`-valued `f`, §4.2, p.13. -/
def advF {N : ℕ} (μ₁ μ₂ : Graph N → ℝ) (f : Graph N → ℝ) : ℝ := |expect μ₁ f - expect μ₂ f|

/-- The advantage of a distinguisher with acceptance probabilities `acc`:
`adv_A(D₁, D₂) = 2 |Pr_{D₁}[A = 1] − Pr_{D₂}[A = 1]|`, §4.2, p.13. -/
def adv {N : ℕ} (μ₁ μ₂ : Graph N → ℝ) (acc : Graph N → ℝ) : ℝ :=
  2 * |expect μ₁ acc - expect μ₂ acc|

/-- The edge-counting benchmark, display (4), p.13:
`Λ_N(k) = (p − q) k (k − 1) / √(π q (1 − q) N (N − 1))`. -/
def Lam (p q : ℝ) (N k : ℕ) : ℝ :=
  (p - q) * k * ((k : ℝ) - 1) / Real.sqrt (Real.pi * q * (1 - q) * N * ((N : ℝ) - 1))

/-- The ±1-valued mean `f(G) = E[A(G)] = 2 Pr[A(G) = 1] − 1` of a distinguisher with acceptance
probabilities `acc`, §4.2, p.13. -/
def signedMean {N : ℕ} (acc : Graph N → ℝ) (G : Graph N) : ℝ := 2 * acc G - 1

end

end PDSEquiv


