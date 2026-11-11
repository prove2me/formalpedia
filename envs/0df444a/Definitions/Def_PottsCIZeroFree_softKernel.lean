-- Prove2me | Definitions.Def_PottsCIZeroFree_softKernel
-- name    : PottsCIZeroFree_softKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:27:47.841693+00:00
-- url     : https://prove2.me/theorems/1ca1e5ee-04b3-4be2-be4d-29affb25f9df
-- title:
--   Flip profiles, the hard list-flip kernel (Def. 4.5), the soft flip kernel (Def. 4.6) and Vigoda's profile (25)
-- statement:
--   A **hard list instance** $F=(W,E,L)$ is a finite vertex set $W$, a graph $E$ on $W$ and lists $L_u\subseteq[q]$; $\Omega_F$ is the set of proper colorings of $(W,E)$ with $X_u\in L_u$ for every $u$. A **flip profile** is a sequence $\rho=(\rho_s)_{s\ge1}$ with $0\le\rho_s\le1$.
--
--   **Definition 4.5 (Hard list-flip transition).** From $X\in\Omega_F$, choose $(u,c)$ uniformly in $W\times[q]$. If $c=X_u$, hold. Otherwise let $S_X(u,c)$ be the component containing $u$ of the subgraph of $(W,E)$ induced by the vertices colored $X_u$ or $c$, and swap its two colors with probability $\rho_{|S_X(u,c)|}/|S_X(u,c)|$, provided the swap respects every list; otherwise hold. This kernel is $\Phi^\rho_F$; it is the identity when $W=\emptyset$.
--
--   A **pinned system** is a free vertex set $W$, a free graph $E$ on $W$, and a finite family of individually labeled free–pinned constraints $(u,c)$, each forbidding color $c$ at $u$. Given a coloring $\sigma$, each satisfied inequality (a free edge with different endpoint colors, or a constraint $(u,c)$ with $\sigma_u\ne c$) is activated independently with probability $1-x$. For the active set $A$, $E_A$ is the set of active free edges, $L_{A,u}=[q]\setminus\{c:(u,c)\in A\}$ and $F_A=(W,E_A,L_A)$.
--
--   **Definition 4.6 (Soft flip kernel).** The kernel $K_{x,\rho}$ samples $A$ conditional on the current coloring, applies $\Phi^\rho_{F_A}$ and returns the updated coloring.
--
--   For a graph $G$ and a pinning $\tau$ the pinned system has $W=V^\tau$, the free graph $G^\tau$, and one constraint $(u,\tau_p)$ for every edge $up$ with $u$ free and $p$ pinned, even when several pinned neighbors share a color; its soft kernel is $K^{G,\tau}_{x,\rho}$. **Vigoda's profile** is
--   $$p_1=1,\ p_2=\tfrac{13}{42},\ p_3=\tfrac16,\ p_4=\tfrac2{21},\ p_5=\tfrac1{21},\ p_6=\tfrac1{84},\ p_s=0\ (s\ge7),$$
--   and $K^{G,\tau}_x=K^{G,\tau}_{x,p}$.
--
--   These kernels carry the coupling argument of Section 4: their stationary law is the pinned Gibbs law, and their contraction gives coupling independence above $11\Delta/6$.
--
--   **Formalization Note** Kernels are real matrices indexed by all colorings $W\to[q]$; the hard kernel is given by the same formula at every coloring, and only its rows at feasible colorings are used. The profile is a function `ℕ → ℝ` whose value at `0` is never read. The active set is a pair (a finite set of free edges, a finite set of constraint labels), with probability $(1-x)^{|A|}x^{\#\mathrm{satisfied}-|A|}$ if it consists of satisfied constraints and $0$ otherwise.
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), §4.2, pp.17–18, Definitions 4.5–4.6 and display (22); p.19, display (25)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_PottsCIZeroFree_normPinnedPoly

open Classical

namespace PottsCIZeroFree

noncomputable section

variable {W : Type*} [Fintype W] {q : ℕ}

/-- A flip profile, p.18 of Shao, Shi, *Coupling Independence Implies Zero-Freeness*,
arXiv:2610.12456 (PDF sha256 831a1633…): a sequence `ρ = (ρ_s)_{s ≥ 1}` with `0 ≤ ρ_s ≤ 1`.

**Formalization Note.** `ρ : ℕ → ℝ`; the value at `0` is never read. -/
def IsProfile (ρ : ℕ → ℝ) : Prop :=
  ∀ s, 1 ≤ s → 0 ≤ ρ s ∧ ρ s ≤ 1

/-- Vigoda's profile (25), p.19: `p_1 = 1, p_2 = 13/42, p_3 = 1/6, p_4 = 2/21, p_5 = 1/21,
p_6 = 1/84, p_s = 0 (s ≥ 7)` (and `0` at the unused index `0`). -/
def vigodaProfile : ℕ → ℝ
  | 1 => 1
  | 2 => 13 / 42
  | 3 => 1 / 6
  | 4 => 2 / 21
  | 5 => 1 / 21
  | 6 => 1 / 84
  | _ => 0

/-- `Ω_F`, p.17: a coloring `X : W → [q]` is a proper coloring of the hard list instance
`F = (W, E, L)` respecting every list. -/
def IsFeasible (E : SimpleGraph W) (L : W → Set (Fin q)) (X : W → Fin q) : Prop :=
  (∀ u v, E.Adj u v → X u ≠ X v) ∧ ∀ u, X u ∈ L u

/-- The subgraph of `(W, E)` induced by the vertices colored `X_u` or `c` (Definition 4.5,
p.18). -/
def kempeGraph (E : SimpleGraph W) (X : W → Fin q) (u : W) (c : Fin q) : SimpleGraph W :=
  E ⊓ SimpleGraph.fromRel (fun a b => (X a = X u ∨ X a = c) ∧ (X b = X u ∨ X b = c))

/-- `S_X(u, c)`, the `{X_u, c}`-component of `u` (Definition 4.5, p.18): the component
containing `u` of the subgraph of `(W, E)` induced by the vertices colored `X_u` or `c`. -/
def kempeComp (E : SimpleGraph W) (X : W → Fin q) (u : W) (c : Fin q) : Set W :=
  {w | (kempeGraph E X u c).Reachable u w}

/-- The coloring obtained from `X` by swapping the two colors `X_u` and `c` on `S_X(u, c)`. -/
def kempeSwap (E : SimpleGraph W) (X : W → Fin q) (u : W) (c : Fin q) : W → Fin q :=
  fun w => if w ∈ kempeComp E X u c then (if X w = X u then c else X u) else X w

/-- The probability that the proposal `(u, c)` of Definition 4.5 is accepted: `0` if
`c = X_u`; otherwise `ρ_{|S_X(u,c)|} / |S_X(u,c)|` if the swap respects every list, and `0`
(hold) if it does not. -/
def acceptProb (ρ : ℕ → ℝ) (E : SimpleGraph W) (L : W → Set (Fin q)) (X : W → Fin q) (u : W)
    (c : Fin q) : ℝ :=
  if c = X u then 0
  else if ∀ w, kempeSwap E X u c w ∈ L w then
    ρ (kempeComp E X u c).ncard / ((kempeComp E X u c).ncard : ℝ)
  else 0

/-- Definition 4.5 (Hard list-flip transition), p.18: the kernel `Φ^ρ_F` of the hard list
instance `F = (W, E, L)`. From `X`, choose `(u, c)` uniformly in `W × [q]`; if `c = X_u`
hold; otherwise swap the colors `X_u, c` on `S_X(u, c)` with probability
`ρ_{|S_X(u,c)|}/|S_X(u,c)|` provided the swap respects every list, and hold otherwise. It is
the identity kernel when `W = ∅`.

**Formalization Note.** The paper defines the kernel from states `X ∈ Ω_F`; the matrix is
written for every `X : W → [q]` by the same formula, and only its rows at feasible states are
used (the soft kernel reaches only such rows, and Lemma 4.9's hard clause restricts to them). -/
def flipKernel (ρ : ℕ → ℝ) (E : SimpleGraph W) (L : W → Set (Fin q)) :
    Matrix (W → Fin q) (W → Fin q) ℝ :=
  fun X Y =>
    if Fintype.card W = 0 then (if Y = X then 1 else 0)
    else (1 / ((Fintype.card W : ℝ) * q)) *
      ∑ u : W, ∑ c : Fin q,
        (acceptProb ρ E L X u c * (if Y = kempeSwap E X u c then 1 else 0) +
          (1 - acceptProb ρ E L X u c) * (if Y = X then 1 else 0))

section Soft

/-! A pinned system (§4.2–4.3, pp.17–19): a free vertex set `W`, a free graph `E` on `W`, and a
finite family of individually labeled free–pinned constraints `lab i = (u, c)`, each
forbidding the color `c` at the free vertex `u` (the pinned neighbor of `u` has color `c`). -/

variable {ι : Type*} [Fintype ι]

/-- The free edges whose inequality is satisfied by `X` (endpoint colors differ). -/
def satEdges (E : SimpleGraph W) (X : W → Fin q) : Finset (Sym2 W) :=
  E.edgeFinset.filter (fun e => ¬ (e.map X).IsDiag)

/-- The labeled free–pinned constraints satisfied by `X`: `lab i = (u, c)` with `X_u ≠ c`. -/
def satLabels (lab : ι → W × Fin q) (X : W → Fin q) : Finset ι :=
  Finset.univ.filter (fun i => X (lab i).1 ≠ (lab i).2)

/-- The activation law of p.17: given the coloring `X`, each satisfied inequality (free edge or
labeled free–pinned edge) is activated independently with probability `1 − x`. The probability
of the active set `A = (A_E, A_L)` is
`(1 − x)^{|A|} x^{#satisfied − |A|}` if `A` consists of satisfied constraints, and `0`
otherwise. -/
def actProb (E : SimpleGraph W) (lab : ι → W × Fin q) (x : ℝ) (X : W → Fin q)
    (A : Finset (Sym2 W) × Finset ι) : ℝ :=
  if A.1 ⊆ satEdges E X ∧ A.2 ⊆ satLabels lab X then
    (1 - x) ^ (A.1.card + A.2.card) *
      x ^ (((satEdges E X).card - A.1.card) + ((satLabels lab X).card - A.2.card))
  else 0

/-- `E_A`, p.17: the active free edges. -/
def activeGraph (E : SimpleGraph W) (AE : Finset (Sym2 W)) : SimpleGraph W :=
  E ⊓ SimpleGraph.fromEdgeSet (AE : Set (Sym2 W))

/-- `L_{A,u} = [q] \ {τ_p : up ∈ A free–pinned}`, p.17. -/
def activeList (lab : ι → W × Fin q) (AL : Finset ι) (u : W) : Set (Fin q) :=
  {c | ∀ i ∈ AL, lab i ≠ (u, c)}

/-- Definition 4.6 (Soft flip kernel), p.18: `K_{x,ρ}` samples the active set `A` conditional
on the current coloring, applies `Φ^ρ_{F_A}` (Definition 4.5) with `F_A = (W, E_A, L_A)`, and
returns the updated coloring. -/
def softKernel (ρ : ℕ → ℝ) (x : ℝ) (E : SimpleGraph W) (lab : ι → W × Fin q) :
    Matrix (W → Fin q) (W → Fin q) ℝ :=
  fun X Y => ∑ A : Finset (Sym2 W) × Finset ι,
    actProb E lab x X A * flipKernel ρ (activeGraph E A.1) (activeList lab A.2) X Y

end Soft

section OfPinning

variable {V : Type*} [Fintype V]

/-- The free graph `G^τ = G[V^τ]` of §2.1, p.7, on the free vertices `V^τ = V \ Λ`. -/
def freeGraph (G : SimpleGraph V) (Λ : Set V) : SimpleGraph {v // v ∉ Λ} :=
  G.comap Subtype.val

/-- The individually labeled free–pinned edges of `(G, τ)`, p.17: the pairs `(u, p)` with `u`
free, `p ∈ Λ` and `up ∈ E`. Pinned neighbors are kept separately even when several have the
same color (p.7). -/
abbrev FPEdge (G : SimpleGraph V) (Λ : Set V) : Type _ :=
  {pr : V × V // pr.1 ∉ Λ ∧ pr.2 ∈ Λ ∧ G.Adj pr.1 pr.2}

/-- The label `(u, τ_p)` of the free–pinned edge `up`: it forbids the color `τ_p` at `u`. -/
def fpLabel (G : SimpleGraph V) (Λ : Set V) (τ : V → Fin q) (e : FPEdge G Λ) :
    {v // v ∉ Λ} × Fin q :=
  (⟨e.1.1, e.2.1⟩, τ e.1.2)

/-- `K^{G,τ}_{x,ρ}`, Definition 4.6, p.18: the soft flip kernel of the pinned system of
`(G, τ)`, on the colorings `[q]^{V^τ}` of the free vertices, keeping `τ` fixed. With Vigoda's
profile (25) it is `K^{G,τ}_x` (p.19). -/
def pinnedSoftKernel (ρ : ℕ → ℝ) (x : ℝ) (G : SimpleGraph V) (Λ : Set V) (τ : V → Fin q) :
    Matrix ({v // v ∉ Λ} → Fin q) ({v // v ∉ Λ} → Fin q) ℝ :=
  softKernel ρ x (freeGraph G Λ) (fpLabel G Λ τ)

end OfPinning

end

end PottsCIZeroFree


