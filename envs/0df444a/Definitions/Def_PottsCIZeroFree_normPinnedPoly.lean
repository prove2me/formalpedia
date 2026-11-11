-- Prove2me | Definitions.Def_PottsCIZeroFree_normPinnedPoly
-- name    : PottsCIZeroFree_normPinnedPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:26:16.615298+00:00
-- url     : https://prove2.me/theorems/dc4329b9-d757-4260-9818-c1beb4060a01
-- title:
--   Potts partition functions $Z_G$, $Z^\tau_G$, $\widehat Z^\tau_G$, pinnings, boundary counts and hard lists
-- statement:
--   Let $G=(V,E)$ be a finite simple graph and $q$ a positive integer. A **configuration** is a map $\sigma:V\to[q]$, and $m_G(\sigma)=|\{uv\in E:\sigma_u=\sigma_v\}|$ is its number of monochromatic edges. The **Potts partition function** is
--   $$Z_G(q;z)=\sum_{\sigma:V\to[q]} z^{m_G(\sigma)},$$
--   with $0^0=1$. A **pinning** is a map $\tau:\Lambda\to[q]$ on a set $\Lambda\subseteq V$; $m_G(\tau)$ is the number of monochromatic edges of $G[\Lambda]$ and $V^\tau=V\setminus\Lambda$ is the set of free vertices. For a coloring $\varphi:V^\tau\to[q]$, $\tau\cup\varphi$ is the coloring of $V$ that agrees with $\tau$ on $\Lambda$ and with $\varphi$ on $V^\tau$. The **normalized pinned partition function** and the usual pinned partition function are
--   $$\widehat Z^\tau_G(q;z)=\sum_{\varphi:V^\tau\to[q]} z^{m_G(\tau\cup\varphi)-m_G(\tau)},\qquad Z^\tau_G(q;z)=\sum_{\varphi:V^\tau\to[q]} z^{m_G(\tau\cup\varphi)}=z^{m_G(\tau)}\widehat Z^\tau_G(q;z).$$
--   For $r\in V^\tau$ and $a\in[q]$ the **child pinning** $\tau^{r=a}=\tau\cup\{r\mapsto a\}$ lives on $\Lambda\cup\{r\}$. For $\varepsilon>0$ and $I\subseteq\mathbb R$, $\mathcal U_\varepsilon(I)=\{z\in\mathbb C:\operatorname{dist}(z,I)<\varepsilon\}$. The graph has **maximum degree at most $\Delta$** if every vertex has at most $\Delta$ neighbors. The **boundary count** of a free vertex $u$ and a color $c$ is $b^\tau_u(c)=|\{p\in\Lambda:up\in E,\ \tau_p=c\}|$, the **hard effective list** is $L^\tau(u)=\{c\in[q]:b^\tau_u(c)=0\}$, and $\deg_{G^\tau}(u)$ is the degree of $u$ in the free graph $G^\tau=G[V^\tau]$.
--
--   These are the objects of every statement of the mission: the zero-freeness theorems are about $\widehat Z^\tau_G$ and $Z^\tau_G$, and the hard-coloring estimates at $z=0$ use $b^\tau_u$ and $L^\tau(u)$.
--
--   **Formalization Note** Colors are `Fin q`. A pinning is a set `Λ` together with `τ : V → Fin q`, of which only the values on `Λ` are read. $\widehat Z^\tau_G$, $Z^\tau_G$ and $Z_G$ are polynomials in `Polynomial ℂ`, so that zeros and their multiplicities can be stated; `normPinnedAt` is the real value at a real activity. The exponent $m_G(\tau\cup\varphi)-m_G(\tau)$ is a natural-number difference, which is exact. $\mathcal U_\varepsilon(I)$ is the metric thickening of $I\subseteq\mathbb C$.
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), pp.1–2, displays (1)–(3); p.3; §2.1–2.2, pp.7–8, display (6) and the hard list

import Mathlib

open Classical

namespace PottsCIZeroFree

noncomputable section

variable {V : Type*} [Fintype V]

/-- The number `m_G(σ)` of monochromatic edges of a coloring `σ : V → [q]`, display (1) of
Shao, Shi, *Coupling Independence Implies Zero-Freeness*, arXiv:2610.12456 (PDF sha256
831a1633…), p.1: `m_G(σ) = |{uv ∈ E : σ_u = σ_v}|`.

**Formalization Note.** Colors are `Fin q`, i.e. `[q] = {1,…,q}` relabeled as `{0,…,q−1}`.
An edge is a `Sym2 V` in `G.edgeSet`; it is monochromatic when its image under `σ` is a
diagonal pair. -/
def monoCount (G : SimpleGraph V) {q : ℕ} (σ : V → Fin q) : ℕ :=
  Set.ncard {e : Sym2 V | e ∈ G.edgeSet ∧ (e.map σ).IsDiag}

/-- `m_G(τ)` of a pinning `τ : Λ → [q]`, p.2: the number of monochromatic edges of the induced
subgraph `G[Λ]`.

**Formalization Note.** A pinning is encoded as a set `Λ ⊆ V` together with `τ : V → Fin q`,
of which only the values on `Λ` are read; every definition of this mission ignores `τ` off
`Λ`. -/
def pinnedMono (G : SimpleGraph V) (Λ : Set V) {q : ℕ} (τ : V → Fin q) : ℕ :=
  Set.ncard {e : Sym2 V | e ∈ G.edgeSet ∧ (∀ v ∈ e, v ∈ Λ) ∧ (e.map τ).IsDiag}

/-- The coloring `τ ∪ φ : V → [q]` obtained from a pinning `τ` on `Λ` and a coloring
`φ : V^τ → [q]` of the free vertices `V^τ = V \ Λ` (p.3). -/
def extend (Λ : Set V) {q : ℕ} (τ : V → Fin q) (φ : {v // v ∉ Λ} → Fin q) : V → Fin q :=
  fun v => if h : v ∈ Λ then τ v else φ ⟨v, h⟩

/-- The exponent `m_G(τ ∪ φ) − m_G(τ)` of (2) and (4), p.2–3. The natural-number subtraction is
exact, since every monochromatic edge of `G[Λ]` under `τ` is monochromatic under `τ ∪ φ`. -/
def pinExp (G : SimpleGraph V) (Λ : Set V) {q : ℕ} (τ : V → Fin q)
    (φ : {v // v ∉ Λ} → Fin q) : ℕ :=
  monoCount G (extend Λ τ φ) - pinnedMono G Λ τ

/-- The normalized pinned partition function (2), p.2, as a polynomial in the edge activity:
`Ẑ^τ_G(q; z) = Σ_{σ : V → [q], σ|Λ = τ} z^{m_G(σ) − m_G(τ)}`.

**Formalization Note.** The sum runs over the colorings `φ` of the free vertices, which are in
bijection with the colorings `σ` with `σ|Λ = τ` via `σ = τ ∪ φ` (this is the form (7), p.7).
Using `Polynomial ℂ` makes the zeros and their multiplicities of Theorem 1.1 stateable. -/
def normPinnedPoly (G : SimpleGraph V) (Λ : Set V) {q : ℕ} (τ : V → Fin q) : Polynomial ℂ :=
  ∑ φ : {v // v ∉ Λ} → Fin q, Polynomial.X ^ pinExp G Λ τ φ

/-- The value `Ẑ^τ_G(q; x)` of (2) at a real activity `x`, p.2. It equals the evaluation of
`normPinnedPoly` at `(x : ℂ)`; the convention `0^0 = 1` of p.1 is Lean's `pow`. -/
def normPinnedAt (G : SimpleGraph V) (Λ : Set V) {q : ℕ} (τ : V → Fin q) (x : ℝ) : ℝ :=
  ∑ φ : {v // v ∉ Λ} → Fin q, x ^ pinExp G Λ τ φ

/-- The usual pinned partition function `Z^τ_G(q; z) = Σ_{σ|Λ = τ} z^{m_G(σ)}` of p.2, which
satisfies (3): `Z^τ_G = z^{m_G(τ)} Ẑ^τ_G`. -/
def pinnedPoly (G : SimpleGraph V) (Λ : Set V) {q : ℕ} (τ : V → Fin q) : Polynomial ℂ :=
  ∑ φ : {v // v ∉ Λ} → Fin q, Polynomial.X ^ monoCount G (extend Λ τ φ)

/-- The Potts partition function (1), p.1: `Z_G(q; z) = Σ_{σ : V → [q]} z^{m_G(σ)}`. -/
def partitionPoly (G : SimpleGraph V) (q : ℕ) : Polynomial ℂ :=
  ∑ σ : V → Fin q, Polynomial.X ^ monoCount G σ

/-- The pinned set `Λ ∪ {r}` of a child pinning `τ^{r=a}` (p.3, p.8). -/
def childSet (Λ : Set V) (r : V) : Set V := insert r Λ

/-- The child pinning `τ^{r=a} = τ ∪ {r ↦ a}` of p.3, as a map read on `Λ ∪ {r}`. -/
def childPin {q : ℕ} (τ : V → Fin q) (r : V) (a : Fin q) : V → Fin q :=
  Function.update τ r a

/-- `U_ε(I) = {z ∈ ℂ : dist(z, I) < ε}` for `I ⊆ ℝ ⊆ ℂ`, p.2: the open `ε`-thickening. -/
def nbhd (ε : ℝ) (I : Set ℝ) : Set ℂ :=
  Metric.thickening ε ((fun x : ℝ => (x : ℂ)) '' I)

/-- Maximum degree at most `Δ`, §2.1, p.7: `Δ(G) = max_v deg_G(v) ≤ Δ`. -/
def MaxDegLE (G : SimpleGraph V) (Δ : ℕ) : Prop :=
  ∀ v, (G.neighborSet v).ncard ≤ Δ

/-- The boundary count (6), p.7: `b^τ_u(c) = |{p ∈ Λ : up ∈ E, τ_p = c}|`. -/
def boundaryCount (G : SimpleGraph V) (Λ : Set V) {q : ℕ} (τ : V → Fin q) (u : V) (c : Fin q) :
    ℕ :=
  Set.ncard {p : V | p ∈ Λ ∧ G.Adj u p ∧ τ p = c}

/-- The hard effective list of §2.2, p.8: `L^τ(u) = {c ∈ [q] : b^τ_u(c) = 0}`. -/
def hardList (G : SimpleGraph V) (Λ : Set V) {q : ℕ} (τ : V → Fin q) (u : V) : Set (Fin q) :=
  {c | boundaryCount G Λ τ u c = 0}

/-- The degree `deg_{G^τ}(u)` of a vertex in the free graph `G^τ = G[V \ Λ]`, §2.1, p.7. -/
def freeDegree (G : SimpleGraph V) (Λ : Set V) (u : V) : ℕ :=
  Set.ncard {w : V | w ∉ Λ ∧ G.Adj u w}

end

end PottsCIZeroFree


