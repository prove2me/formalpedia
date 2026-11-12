-- Prove2me | Definitions.Def_FourWayStream_ARHM_Information
-- name    : FourWayStream_ARHM_Information
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:41:58.913523+00:00
-- url     : https://prove2.me/theorems/6c331b81-b8ad-44d8-99d3-39baa6b1f1fe
-- title:
--   §4, Definitions 6.3–6.4 — entropy and mutual information in bits, forest size, balanced matching distributions
-- statement:
--   **Finite probability.** Random variables live on a finite sample space $\Omega$ with weights $p$. For a random variable $f$, its law is $P[f=b]=\sum_{\omega:\,f(\omega)=b}p(\omega)$; $E[f]=\sum_\omega p(\omega)f(\omega)$; $P[A\mid B]=P[A\wedge B]/P[B]$.
--
--   **Entropy in bits.** $H(f)=-\sum_b P[f=b]\log_2 P[f=b]$ (with $0\log 0=0$), $H(f\mid g)=H(f,g)-H(g)$, and
--   $$I(f:g\mid h)=H(f\mid h)-H(f\mid g,h).$$
--
--   **Forest size (Definition 6.4).** For a set $F$ of edges on $[N]$, let $V(F)$ be the set of endpoints and $c(F)$ the number of connected components of the graph $(V(F),F)$. The forest size is
--   $$\mathrm{fs}(F)=|V(F)|-c(F),$$
--   the number of edges of a spanning forest; repeated edges count once.
--
--   **Matching distributions (Definition 6.3).** Requests $q$ range over a finite set $Q$ and request $q$ names the edge set $\mu(q)$. A distribution $D$ on $Q$ is a matching distribution if it is supported on requests naming perfect matchings of $[N]$, and it is **balanced** if in addition
--   $$P_{q\sim D}[e\in\mu(q)]=\frac{1}{N-1}\quad\text{for every pair } e=\{u,v\},\ u\ne v.$$
--   With $Q$ the perfect matchings and $\mu=\mathrm{id}$ this is the paper's notion; the **uniform factor** $U(F)$ of a one-factorization is the uniform distribution on the indices $k\in[N-1]$ with $\mu=F$.
--
--   These are the information-theoretic quantities of the consumability bounds of §6.
--
--   **Formalization Note** Entropies are Shannon entropies of push-forward laws, computed with `Real.logb 2` (`Real.logb 2 0 = 0` gives $0\log 0=0$). The number of components is the number of connected components of `SimpleGraph.fromEdgeSet F` met by $V(F)$.
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §4 notation, p.15; Definition 6.3, p.28; Definition 6.4, p.29

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream

set_option autoImplicit false

/-!
# Finite probability, entropy in bits, forest size, balanced matching distributions

Nadezhda Voronova, *Four Ways to Stream*, STOC 2027 submission #1371 (October 2026): notation of §4
(p.15: "Entropy H(·), binary entropy h₂(·) and mutual information I(· : ·) are in bits"),
Definition 6.3 (p.28), Definition 6.4 (p.29).

Random variables live on a finite sample space `Ω` with a weight function `p : Ω → ℝ` (a probability
vector in every use). A random variable is a function on `Ω`; its law is the push-forward of `p`.
Entropies are Shannon entropies in bits (`Real.logb 2`, with `0 · log 0 = 0` since
`Real.logb 2 0 = 0`); conditional entropy and conditional mutual information are defined by the
chain rule from joint entropies.
-/

noncomputable section
open Classical

namespace FourWayStream.ARHM

variable {Ω : Type*} [Fintype Ω]

/-- The law of the random variable `f` under the weights `p`: `P[f = b]`. -/
def lawOf (p : Ω → ℝ) {β : Type*} (f : Ω → β) (b : β) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω => f ω = b), p ω

/-- `P[A]`. -/
def probOf (p : Ω → ℝ) (A : Ω → Prop) : ℝ :=
  ∑ ω ∈ Finset.univ.filter A, p ω

/-- `P[A | B] = P[A ∧ B] / P[B]` (used only for events with `P[B] > 0`). -/
def condProbOf (p : Ω → ℝ) (A B : Ω → Prop) : ℝ :=
  probOf p (fun ω => A ω ∧ B ω) / probOf p B

/-- `E[f]`. -/
def expect (p : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, p ω * f ω

/-- Shannon entropy in bits of a probability vector on a finite type. -/
def shannonH {β : Type*} [Fintype β] (q : β → ℝ) : ℝ := -∑ b, q b * Real.logb 2 (q b)

/-- `H(f)`, the entropy in bits of the random variable `f`. -/
def entropyOf (p : Ω → ℝ) {β : Type*} [Fintype β] (f : Ω → β) : ℝ := shannonH (lawOf p f)

/-- `H(f | g) = H(f, g) − H(g)`. -/
def condEntropyOf (p : Ω → ℝ) {β γ : Type*} [Fintype β] [Fintype γ] (f : Ω → β) (g : Ω → γ) :
    ℝ :=
  entropyOf p (fun ω => (f ω, g ω)) - entropyOf p g

/-- `I(f : g | h) = H(f | h) − H(f | g, h)`. -/
def condMutualInfoOf (p : Ω → ℝ) {β γ δ : Type*} [Fintype β] [Fintype γ] [Fintype δ]
    (f : Ω → β) (g : Ω → γ) (h : Ω → δ) : ℝ :=
  condEntropyOf p f h - condEntropyOf p f (fun ω => (g ω, h ω))

/-! ### Forest size (Definition 6.4) -/

/-- `V(F)`: the endpoints of the edges of `F`. -/
def edgeVerts {N : ℕ} (F : Finset (Sym2 (Fin N))) : Finset (Fin N) :=
  Finset.univ.filter (fun v => ∃ e ∈ F, v ∈ e)

/-- `c(F)`: the number of connected components of the graph `(V(F), F)`. -/
def numComponents {N : ℕ} (F : Finset (Sym2 (Fin N))) : ℕ :=
  ((edgeVerts F).image
    (fun v => (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin N)))).connectedComponentMk v)).card

/-- Definition 6.4 (p.29): the forest size `fs(F) = |V(F)| − c(F)`, the number of edges of a
spanning forest of `(V(F), F)`. Repeated edges count once (`F` is a set). -/
def forestSize {N : ℕ} (F : Finset (Sym2 (Fin N))) : ℕ :=
  (edgeVerts F).card - numComponents F

/-! ### Matching distributions (Definition 6.3) -/

/-- A distribution `D` on requests `q ∈ Q`, each naming the edge set `μ q`, supported on perfect
matchings of `[N]` (§6.2, p.28: "each matching is drawn independently from some distribution D over
perfect matchings"). With `Q` the perfect matchings and `μ = id` this is a distribution on perfect
matchings; with `Q = [N − 1]` and `μ = F` it is a distribution on factor indices. -/
def IsMatchingDist {N : ℕ} {Q : Type*} [Fintype Q] (μ : Q → Finset (Sym2 (Fin N))) (D : Q → ℝ) :
    Prop :=
  (∀ q, 0 ≤ D q) ∧ ∑ q, D q = 1 ∧ ∀ q, D q ≠ 0 → IsPerfectMatching (μ q)

/-- Definition 6.3 (p.28): `D` is balanced if `P_{q∼D}[e ∈ μ q] = 1/(N − 1)` for every pair
`e = {u, v}`, `u ≠ v`. -/
def IsBalanced {N : ℕ} {Q : Type*} [Fintype Q] (μ : Q → Finset (Sym2 (Fin N))) (D : Q → ℝ) :
    Prop :=
  IsMatchingDist μ D ∧
    ∀ u v : Fin N, u ≠ v → ∑ q ∈ Finset.univ.filter (fun q => s(u, v) ∈ μ q), D q = 1 / ((N : ℝ) - 1)

/-- Definition 6.3 (p.28): the uniform factor `U(F)` of a one-factorization, as the uniform
distribution on the factor indices `k ∈ [N − 1]` (request `k` names `F_k`). -/
def uniformFactor (N : ℕ) : Fin (N - 1) → ℝ := fun _ => 1 / ((N - 1 : ℕ) : ℝ)

end FourWayStream.ARHM


