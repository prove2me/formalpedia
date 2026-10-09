-- Prove2me | Definitions.Def_HighOrderWalks_OneSided_Setting
-- name    : HighOrderWalks_OneSided_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T01:41:31.257001+00:00
-- url     : https://prove2.me/theorems/b3a114b8-ffe7-4028-82aa-b15c1bf8d9cb
-- title:
--   §2–§4, pp. 2, 6–13 — weighted pure complex, cochains, M⁺, M⁻, (M′)⁺, d, d*, links, one-sided local spectral expanders
-- statement:
--   This file fixes the objects of Kaufman–Oppenheim, *High Order Random Walks: Beyond Spectral Gap*, §2–§4.
--
--   **Complex.** A finite simplicial complex $X$ on a vertex type $V$ is a finite family of finite vertex sets, closed under taking subsets. A $k$-simplex ($k$-face) has $k+1$ vertices; $X(k)$ is the set of $k$-simplices and $X(-1)=\{\emptyset\}$. $X$ is **pure $n$-dimensional** if every face has at most $n+1$ vertices, every face is contained in a face with $n+1$ vertices, and $X$ is nonempty.
--
--   **Weight.** A weight function is $m : \bigcup_{-1\le k\le n} X(k)\to(0,\infty)$ such that for every $-1\le k\le n-1$ and $\tau\in X(k)$,
--   $$m(\tau)=\sum_{\sigma\in X(k+1),\ \tau\subseteq\sigma} m(\sigma).$$
--
--   **Cochains.** A $k$-cochain is a function $\phi : X(k)\to\mathbb R$, with the inner product $\langle\phi,\psi\rangle=\sum_{\sigma\in X(k)} m(\sigma)\phi(\sigma)\psi(\sigma)$ and the induced norm $\|\cdot\|$.
--
--   **Operators** (on $k$-cochains, $\tau\in X(k)$):
--   1. the signless differential $d\phi(\sigma)=\sum_{\tau\subset\sigma,\ \tau\in X(k)}\phi(\tau)$ for $\sigma\in X(k+1)$;
--   2. its adjoint, by the formula $d^*\psi(\tau)=\sum_{\sigma\in X(k+1),\ \tau\subset\sigma}\frac{m(\sigma)}{m(\tau)}\psi(\sigma)$;
--   3. the upper random walk $M^+_k\phi(\tau)=\frac{1}{k+2}\phi(\tau)+\sum_{\tau'\in X(k),\ \tau\cup\tau'\in X(k+1)}\frac{m(\tau\cup\tau')}{(k+2)m(\tau)}\phi(\tau')$;
--   4. the lower random walk $M^-_k\phi(\tau)=\Big(\sum_{\eta\in X(k-1),\ \eta\subset\tau}\frac{m(\tau)}{(k+1)m(\eta)}\Big)\phi(\tau)+\sum_{\tau'\ne\tau,\ \tau\cap\tau'\in X(k-1)}\frac{m(\tau')}{(k+1)m(\tau\cap\tau')}\phi(\tau')$;
--   5. the non-lazy upper walk $(M')^+_k=\frac{k+2}{k+1}M^+_k-\frac{1}{k+1}I$.
--
--   **Links.** For $\tau\in X$, the link is $X_\tau=\{\eta\in X:\ \eta\cap\tau=\emptyset,\ \tau\cup\eta\in X\}$, with weight $m_\tau(\eta)=m(\tau\cup\eta)$; the localization of a cochain is $\phi_\tau(\eta)=\phi(\tau\cup\eta)$. All the operators above are applied to $(X_\tau,m_\tau)$ unchanged. For $\tau\in X(k-1)$ the **link term** is
--   $$\sum_{\tau\in X(k-1)}\big\langle (M')^+_{\tau,0}(I-M^-_{\tau,0})\phi_\tau,\ \psi_\tau\big\rangle,$$
--   the inner products being those of $0$-cochains of $X_\tau$.
--
--   **Local spectral expansion.** Let $\mu_\tau$ be the second largest eigenvalue of $(M')^+_{\tau,0}$ and $\mu_k=\max_{\tau\in X(k-1)}\mu_\tau$. The predicate "$\mu_k\le b$" says that for every $\tau\in X(k-1)$ and every $0$-cochain $g$ of $X_\tau$ with $\sum_v m_\tau(v)g(v)=0$,
--   $$\langle (M')^+_{\tau,0}g,g\rangle\le b\,\|g\|^2 .$$
--   $X$ is a **one-sided $\lambda$-local spectral expander** if $\mu_k\le\lambda$ for every $0\le k\le n-1$, i.e. for the links of all faces of dimension $-1,\dots,n-2$, including the empty face (whose link is $X$ itself).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Faces are finite sets `Finset V`, and $X(k)$ is `cells X (k + 1)`: faces are indexed by their number of vertices, so $X(-1)$ is `cells X 0`. Cochains are functions `Finset V → ℝ`; only their values on the relevant faces are read, and every operator is $0$ off $X$. The weight's codomain $\mathbb R^+$ is read as $(0,\infty)$ because $m$ appears in denominators. $d^*$ is defined by the formula of Lemma 3.6; that it is the adjoint of $d$ is the theorem `lemma_3_6`. The diagonal of $M^-_k$ is summed over $\eta\subset\tau$, which Definition 3.2 omits but the computation of $dd^*$ on p. 9 uses. The eigenvalue condition $\mu_k\le b$ is stated in its Rayleigh-quotient form on the $m_\tau$-orthogonal complement of the constants; by Courant–Fischer it is equivalent to the eigenvalue form, since $(M')^+_{\tau,0}$ is $m_\tau$-self-adjoint with the constants as an eigenvector of eigenvalue $1$, its largest eigenvalue.
-- source:
--   Kaufman–Oppenheim, High Order Random Walks: Beyond Spectral Gap, arXiv:1707.02799v3, pp. 2, 6–13, Definition 1.1, §2 (pp. 6–7), Definitions 3.1–3.4 (pp. 7–8), Lemma 3.6 (p. 8), §4 (pp. 10–11), Definition 4.4 (p. 13)

import Mathlib

namespace HighOrderWalks.OneSided

/-- §1.1, p. 2 and §2, p. 7: `X` is a pure `n`-dimensional finite simplicial complex, encoded as a
finite family of finite vertex sets. A `k`-face has `k + 1` vertices, `X(-1) = {∅}`. The conjuncts:
downward closed, every face has at most `n + 1` vertices, every face lies in an `n`-face (pure),
and `X` is nonempty (so `X(n) ≠ ∅` and `∅ ∈ X`). -/
def IsPureComplex {V : Type*} (X : Finset (Finset V)) (n : ℕ) : Prop :=
  (∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) ∧ (∀ σ ∈ X, σ.card ≤ n + 1) ∧
    (∀ σ ∈ X, ∃ ρ ∈ X, σ ⊆ ρ ∧ ρ.card = n + 1) ∧ X.Nonempty

/-- The faces of `X` with exactly `c` vertices: `cells X (k + 1) = X(k)`. -/
def cells {V : Type*} (X : Finset (Finset V)) (c : ℕ) : Finset (Finset V) :=
  X.filter (fun σ => σ.card = c)

/-- §2, p. 6: a weight function `m : ⋃ X(k) → ℝ⁺` with `m(τ) = Σ_{σ ∈ X(k+1), τ ⊆ σ} m(σ)` for
`-1 ≤ k ≤ n - 1` (i.e. `τ.card ≤ n`). `ℝ⁺` is read as `(0, ∞)`. Values off `X` are not constrained. -/
def IsWeight {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ) (m : Finset V → ℝ) :
    Prop :=
  (∀ σ ∈ X, 0 < m σ) ∧
    ∀ τ ∈ X, τ.card ≤ n →
      m τ = ∑ σ ∈ X.filter (fun σ => σ.card = τ.card + 1 ∧ τ ⊆ σ), m σ

/-- §2, p. 7: the weighted inner product `⟨φ, ψ⟩ = Σ_{σ ∈ X(k)} m(σ) φ(σ) ψ(σ)` on cochains of
faces with `c = k + 1` vertices. Cochains are functions `Finset V → ℝ`; only their values on
`cells X c` are read. -/
def ip {V : Type*} (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (φ ψ : Finset V → ℝ) : ℝ :=
  ∑ σ ∈ cells X c, m σ * φ σ * ψ σ

/-- §2, p. 7: the norm induced by `ip`. -/
noncomputable def nrm {V : Type*} (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (φ : Finset V → ℝ) : ℝ :=
  Real.sqrt (ip X m c φ φ)

/-- Definition 3.4, p. 8: the signless differential, `dφ(σ) = Σ_{τ ⊂ σ, τ ∈ X(k)} φ(τ)` for
`σ ∈ X(k+1)`; the degree is read from `σ`. Zero off `X`. -/
def dS {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (φ : Finset V → ℝ) :
    Finset V → ℝ :=
  fun σ => if σ ∈ X then ∑ τ ∈ X.filter (fun τ => τ ⊆ σ ∧ τ.card + 1 = σ.card), φ τ else 0

/-- The adjoint `d*` of the signless differential, defined by the formula of Lemma 3.6, p. 8:
`d*ψ(τ) = Σ_{σ ∈ X(k+1), τ ⊂ σ} (m(σ)/m(τ)) ψ(σ)`. (The page defines `d*` as the adjoint of `d`;
that this formula is the adjoint is the theorem `lemma_3_6`.) Zero off `X`. -/
noncomputable def dStar {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (m : Finset V → ℝ)
    (ψ : Finset V → ℝ) : Finset V → ℝ :=
  fun τ => if τ ∈ X then
    ∑ σ ∈ X.filter (fun σ => τ ⊆ σ ∧ σ.card = τ.card + 1), m σ / m τ * ψ σ else 0

/-- Definition 3.1, p. 7: the upper random walk `M⁺_k` as an averaging operator, with
`c = τ.card = k + 1`: `M⁺(τ, τ) = 1/(k+2)`, `M⁺(τ, τ') = m(τ ∪ τ')/((k+2) m(τ))` when
`τ ∪ τ' ∈ X(k+1)`, `0` otherwise. Zero off `X`. -/
noncomputable def upperWalk {V : Type*} [DecidableEq V] (X : Finset (Finset V))
    (m : Finset V → ℝ) (φ : Finset V → ℝ) : Finset V → ℝ :=
  fun τ => if τ ∈ X then
    φ τ / ((τ.card : ℝ) + 1) +
      ∑ τ' ∈ X.filter (fun τ' => τ'.card = τ.card ∧ τ' ≠ τ ∧ τ ∪ τ' ∈ X ∧
          (τ ∪ τ').card = τ.card + 1),
        m (τ ∪ τ') / (((τ.card : ℝ) + 1) * m τ) * φ τ'
  else 0

/-- Definition 3.2, p. 7: the lower random walk `M⁻_k`, with `c = τ.card = k + 1`:
`M⁻(τ, τ) = Σ_{η ∈ X(k-1), η ⊂ τ} m(τ)/((k+1) m(η))`, `M⁻(τ, τ') = m(τ')/((k+1) m(τ ∩ τ'))` when
`τ ∩ τ' ∈ X(k-1)`, `0` otherwise. The page's diagonal sum omits `η ⊂ τ`; the computation of
`dd*` on p. 9 shows it is meant. Zero off `X`. -/
noncomputable def lowerWalk {V : Type*} [DecidableEq V] (X : Finset (Finset V))
    (m : Finset V → ℝ) (φ : Finset V → ℝ) : Finset V → ℝ :=
  fun τ => if τ ∈ X then
    (∑ η ∈ X.filter (fun η => η ⊆ τ ∧ η.card + 1 = τ.card),
        m τ / ((τ.card : ℝ) * m η)) * φ τ +
      ∑ τ' ∈ X.filter (fun τ' => τ'.card = τ.card ∧ τ' ≠ τ ∧ τ ∩ τ' ∈ X ∧
          (τ ∩ τ').card + 1 = τ.card),
        m τ' / ((τ.card : ℝ) * m (τ ∩ τ')) * φ τ'
  else 0

/-- Definition 3.3, p. 8: the non-lazy upper random walk
`(M')⁺_k = ((k+2)/(k+1)) M⁺_k - (1/(k+1)) I`, with `c = τ.card = k + 1`. Zero off `X`. -/
noncomputable def nonLazyWalk {V : Type*} [DecidableEq V] (X : Finset (Finset V))
    (m : Finset V → ℝ) (φ : Finset V → ℝ) : Finset V → ℝ :=
  fun τ => if τ ∈ X then
    ((τ.card : ℝ) + 1) / (τ.card : ℝ) * upperWalk X m φ τ - φ τ / (τ.card : ℝ)
  else 0

/-- §4, p. 10: the link `X_τ = {η ∈ X : τ ∩ η = ∅, τ ∪ η ∈ X}`; `η ∈ X_τ(l) ⇔ η ∈ X(l)` and
`τ ∪ η ∈ X(k + l + 1)`. -/
def link {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (τ : Finset V) :
    Finset (Finset V) :=
  X.filter (fun η => Disjoint τ η ∧ τ ∪ η ∈ X)

/-- §4, p. 10: the induced weight on the link, `m_τ(η) = m(τ ∪ η)`. -/
def linkWeight {V : Type*} [DecidableEq V] (m : Finset V → ℝ) (τ : Finset V) :
    Finset V → ℝ :=
  fun η => m (τ ∪ η)

/-- §4, p. 10: the localization `φ_τ(η) = φ(τ ∪ η)` of a cochain on the link of `τ`. -/
def loc {V : Type*} [DecidableEq V] (φ : Finset V → ℝ) (τ : Finset V) : Finset V → ℝ :=
  fun η => φ (τ ∪ η)

/-- The summand `⟨(M')⁺_{τ,0}(I - M⁻_{τ,0}) φ_τ, ψ_τ⟩` of Proposition 4.2, p. 11, computed in the
link `X_τ` with weight `m_τ` on its vertices (faces with one vertex). -/
noncomputable def linkSummand {V : Type*} [DecidableEq V] (X : Finset (Finset V))
    (m : Finset V → ℝ) (τ : Finset V) (φ ψ : Finset V → ℝ) : ℝ :=
  ip (link X τ) (linkWeight m τ) 1
    (nonLazyWalk (link X τ) (linkWeight m τ)
      (fun η => loc φ τ η - lowerWalk (link X τ) (linkWeight m τ) (loc φ τ) η))
    (loc ψ τ)

/-- Proposition 4.2, p. 11: `Σ_{τ ∈ X(k-1)} ⟨(M')⁺_{τ,0}(I - M⁻_{τ,0}) φ_τ, ψ_τ⟩`; here
`X(k-1) = cells X k`. -/
noncomputable def linkTerm {V : Type*} [DecidableEq V] (X : Finset (Finset V))
    (m : Finset V → ℝ) (k : ℕ) (φ ψ : Finset V → ℝ) : ℝ :=
  ∑ τ ∈ cells X k, linkSummand X m τ φ ψ

/-- p. 11 and Definition 4.4, p. 13: `μ_c ≤ b`, where `μ_c = max_{τ ∈ X(c-1)} μ_τ` and `μ_τ` is
the second largest eigenvalue of `(M')⁺_{τ,0}`. Stated in Rayleigh form: for every face `τ` with
`c` vertices and every `g` on the vertices of the link that is `m_τ`-orthogonal to the
constants, `⟨(M')⁺_{τ,0} g, g⟩ ≤ b ‖g‖²`. -/
def LinkUpper {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (b : ℝ) : Prop :=
  ∀ τ ∈ cells X c, ∀ g : Finset V → ℝ,
    ip (link X τ) (linkWeight m τ) 1 g (fun _ => 1) = 0 →
      ip (link X τ) (linkWeight m τ) 1 (nonLazyWalk (link X τ) (linkWeight m τ) g) g ≤
        b * ip (link X τ) (linkWeight m τ) 1 g g

/-- Definition 1.1, p. 2 / Definition 4.4, p. 13: `X` is a one-sided `λ`-local spectral expander
if `μ_k ≤ λ` for every `0 ≤ k ≤ n - 1`, i.e. for the links of all faces `τ ∈ X(i)`,
`-1 ≤ i ≤ n - 2` (including `τ = ∅`). -/
def OneSidedLSE {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (m : Finset V → ℝ) (n : ℕ)
    (lam : ℝ) : Prop :=
  ∀ c : ℕ, c + 1 ≤ n → LinkUpper X m c lam

end HighOrderWalks.OneSided


