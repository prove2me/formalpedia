-- Prove2me | Definitions.Def_PottsCIZeroFree_Supplement_fieldNormPinned
-- name    : PottsCIZeroFree_Supplement_fieldNormPinned
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:35:32.516784+00:00
-- url     : https://prove2.me/theorems/90a98fb0-bc3b-4a8b-9915-33d9cad09ba5
-- title:
--   Potts color-field polynomials $\widehat Z^\tau_G(\lambda)$, $Z^\tau_G(\lambda)$ and the Lee–Yang polydisc conclusion
-- statement:
--   Let $G=(V,E)$ be a finite simple graph, $q$ a positive integer, and $\tau:\Lambda\to[q]$ a pinning on a set $\Lambda\subseteq V$ (proper or not), with free set $V^\tau=V\setminus\Lambda$. For a coloring $\varphi:V^\tau\to[q]$ let $\tau\cup\varphi$ be the coloring of $V$ that agrees with $\tau$ on $\Lambda$ and with $\varphi$ on $V^\tau$. For **field variables** $\lambda=(\lambda_{u,c})_{(u,c)\in V\times[q]}\in\mathbb C^{V\times[q]}$, the **normalized pinned field polynomial** is
--   $$\widehat Z^\tau_G(\lambda)=\sum_{\varphi:V^\tau\to[q]}\ \prod_{u\in V^\tau}\lambda_{u,\varphi_u}\prod_{\substack{uv\in E\\ \{u,v\}\not\subseteq\Lambda}}\mathbf 1\big[(\tau\cup\varphi)_u\neq(\tau\cup\varphi)_v\big],$$
--   so a coloring of the free vertices contributes exactly when no edge with a free endpoint is monochromatic; edges inside $G[\Lambda]$ are ignored. The **pinned field polynomial** is
--   $$Z^\tau_G(\lambda)=\sum_{\substack{\sigma:V\to[q]\ \text{proper}\\ \sigma|_\Lambda=\tau}}\ \prod_{v\in V}\lambda_{v,\sigma_v}.$$
--
--   For a class $\mathcal G$ of finite simple graphs and a radius $\theta$, the **polydisc conclusion** $\mathrm{PolydiscZeroFree}(q,\mathcal G,\theta)$ says: for every $G\in\mathcal G$ and every pinning $\tau$,
--   1. $\widehat Z^\tau_G(\lambda)\neq0$ whenever $|\lambda_{u,c}-1|<\theta$ for all $u\in V^\tau$, $c\in[q]$;
--   2. if $\tau$ is proper on $G[\Lambda]$, then $Z^\tau_G(\lambda)\neq0$ whenever $|\lambda_{u,c}-1|<\theta$ for all $u\in V^\tau$, $c\in[q]$ and $\lambda_{v,\tau_v}\neq0$ for every $v\in\Lambda$;
--   3. if $\tau$ is proper on $G[\Lambda]$, then $Z^\tau_G(\lambda)\neq0$ whenever $|\lambda_{u,c}-1|<\theta$ for every $u\in V$ and $c\in[q]$.
--
--   These are the objects of the Lee–Yang polydisc theorem (Theorem 5.2): at $\lambda=\mathbf 1$ the field polynomial $\widehat Z^\tau_G(\mathbf 1)$ is the hard-coloring value $\widehat Z^\tau_G(0)$ of the edge-activity polynomial.
--
--   **Formalization Note** $\lambda$ is a function `lam : V → Fin q → ℂ`; colors are `Fin q`; a pinning is a set `Λ` with `τ : V → Fin q` read only on `Λ`, and $\tau\cup\varphi$ is the published `PottsCIZeroFree.extend`. The indicator product is written as an `if` on the predicate `FreeProper`. "$\tau$ proper on $G[\Lambda]$" is `pinnedMono G Λ τ = 0` (the published $m_G(\tau)=0$). A class of graphs is a predicate on simple graphs over finite types.
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), §5.1.1, p.25 (PDF p.27), display (38) and the pinned field polynomial; Theorem 5.2, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_PottsCIZeroFree_normPinnedPoly

open Classical

namespace PottsCIZeroFree.Supplement

open PottsCIZeroFree

noncomputable section

/-- `τ ∪ φ` is proper on every edge with a free endpoint: for every edge `uv ∈ E` with
`{u, v} ⊄ Λ`, `(τ ∪ φ)_u ≠ (τ ∪ φ)_v`. This is the condition under which the indicator product
`∏_{uv ∈ E, {u,v} ⊄ Λ} 1[(τ∪φ)_u ≠ (τ∪φ)_v]` of display (38) of Shao, Shi, *Coupling Independence
Implies Zero-Freeness*, arXiv:2610.12456 (PDF sha256 831a1633…), printed p.25 (PDF p.27), equals
`1` (it is `0` otherwise). Edges inside `G[Λ]` are not checked. -/
def FreeProper {V : Type*} [Fintype V] (G : SimpleGraph V) (Λ : Set V) {q : ℕ} (τ : V → Fin q)
    (φ : {v // v ∉ Λ} → Fin q) : Prop :=
  ∀ u v, G.Adj u v → (u ∉ Λ ∨ v ∉ Λ) → extend Λ τ φ u ≠ extend Λ τ φ v

/-- The normalized pinned field polynomial (38), printed p.25 (PDF p.27):
`Ẑ^τ_G(λ) = Σ_{φ : V^τ → [q]} ∏_{u ∈ V^τ} λ_{u,φ_u} ∏_{uv ∈ E, {u,v} ⊄ Λ} 1[(τ∪φ)_u ≠ (τ∪φ)_v]`,
for field variables `λ = (λ_{u,c})_{(u,c) ∈ V × [q]} ∈ ℂ^{V × [q]}`.

**Formalization Note.** `λ` is a function `lam : V → Fin q → ℂ`; only its values on free
vertices `u ∉ Λ` enter. The indicator product is `1` exactly when `FreeProper` holds and `0`
otherwise. Colors are `Fin q`; a pinning is `Λ : Set V` with `τ : V → Fin q` read only on `Λ`
(the base encoding of `PottsCIZeroFree.normPinnedPoly`). -/
def fieldNormPinned {V : Type*} [Fintype V] (G : SimpleGraph V) (Λ : Set V) {q : ℕ}
    (τ : V → Fin q) (lam : V → Fin q → ℂ) : ℂ :=
  ∑ φ : {v // v ∉ Λ} → Fin q,
    if FreeProper G Λ τ φ then ∏ u : {v // v ∉ Λ}, lam u (φ u) else 0

/-- The pinned field polynomial of printed p.25 (PDF p.27):
`Z^τ_G(λ) = Σ_{σ : V → [q] proper, σ|_Λ = τ} ∏_{v ∈ V} λ_{v,σ_v}`, where `σ` is proper when
`σ_u ≠ σ_v` for every edge `uv ∈ E`. -/
def fieldPinned {V : Type*} [Fintype V] (G : SimpleGraph V) (Λ : Set V) {q : ℕ}
    (τ : V → Fin q) (lam : V → Fin q → ℂ) : ℂ :=
  ∑ σ ∈ Finset.univ.filter (fun σ : V → Fin q =>
      (∀ u v, G.Adj u v → σ u ≠ σ v) ∧ ∀ v ∈ Λ, σ v = τ v),
    ∏ v, lam v (σ v)

/-- The conclusion of Theorem 5.2, printed p.27 (PDF p.29), for a graph class `𝒢` (given as a
predicate on finite simple graphs) and a radius `θ`: for every `G ∈ 𝒢` and every pinning `τ`,
1. `Ẑ^τ_G(λ) ≠ 0` whenever `|λ_{u,c} − 1| < θ` for all `u ∈ V^τ`, `c ∈ [q]`;
2. if `τ` is proper on `G[Λ]` (`m_G(τ) = 0`), then `Z^τ_G(λ) ≠ 0` whenever
   `|λ_{u,c} − 1| < θ` for all `u ∈ V^τ`, `c ∈ [q]` and `λ_{v,τ_v} ≠ 0` for every `v ∈ Λ`;
3. if `τ` is proper on `G[Λ]`, then `Z^τ_G(λ) ≠ 0` whenever `|λ_{u,c} − 1| < θ` for every
   vertex `u ∈ V` and color `c ∈ [q]`.

**Formalization Note.** Every pinning is allowed in clause 1, improper ones included. The class
is a predicate on simple graphs over finite types in `Type`. -/
def PolydiscZeroFree (q : ℕ) (𝒢 : ∀ {V : Type} [Fintype V], SimpleGraph V → Prop) (θ : ℝ) :
    Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V), 𝒢 G →
    ∀ (Λ : Set V) (τ : V → Fin q) (lam : V → Fin q → ℂ),
      ((∀ u, u ∉ Λ → ∀ c, ‖lam u c - 1‖ < θ) → fieldNormPinned G Λ τ lam ≠ 0) ∧
      (pinnedMono G Λ τ = 0 → (∀ u, u ∉ Λ → ∀ c, ‖lam u c - 1‖ < θ) →
        (∀ v ∈ Λ, lam v (τ v) ≠ 0) → fieldPinned G Λ τ lam ≠ 0) ∧
      (pinnedMono G Λ τ = 0 → (∀ u c, ‖lam u c - 1‖ < θ) → fieldPinned G Λ τ lam ≠ 0)

end

end PottsCIZeroFree.Supplement


