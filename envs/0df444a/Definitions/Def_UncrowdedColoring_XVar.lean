-- Prove2me | Definitions.Def_UncrowdedColoring_XVar
-- name    : UncrowdedColoring_XVar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:17:03.52089+00:00
-- url     : https://prove2.me/theorems/bd2d4ddc-f4da-40ec-9520-ea62d7a11dc1
-- title:
--   The counting variables $X_{\ell,j}$, $X_\ell$, $Y^{(1)}_{\ell,j}$, $Y^{(2)}_{\ell,j}$, $Z^{(1)}_{\ell,j}$ and the deviations $\tau_j$
-- statement:
--   Fix $v\in U$, $c\in L(v)$ and $2\le\ell\le j\le k$. $X_{\ell,j}(v,c)$ counts pairs $(e,f)$ with $e\in E(F_c,j,v)$, $f\in\binom{e-v}{\ell-1}$ such that every $u\in f$ lies in $\tilde U$ with $c\in L'(u)$ and $\psi(w)=c$ for every $w\in e\setminus(f\cup\{v\})$, and $X_\ell=\sum_{j=\ell}^kX_{\ell,j}$. $D^*(u)$ is the set of colors discarded at $u$ via an edge not containing $v$; $L^*(u)=\{c^*\in L(u):c^*\notin D^*(u),\ \mathrm{eq}(u,c^*)=1\}$ and $U^*=\{u\in U:u\notin A\text{ or }c_u\notin L^*(u)\}$. With these,
--   $$Y^{(1)}_{\ell,j}=\sum_{e}\sum_{f}\prod_{u\in f}\mathbb 1[u\in U^*]\prod_{w\in e\setminus(f\cup\{v\})}\mathbb 1[w\in A,c_w=c],$$
--   $$Y^{(2)}_{\ell,j}=\sum_{e}\sum_{f}\prod_{x\in e-v}\mathbb 1[x\in A,c_x=c_v]\prod_{w\in e\setminus(f\cup\{v\})}\mathbb 1[c_w=c],$$
--   $$Z^{(1)}_{\ell,j}=\sum_{e}\sum_{f}\prod_{u\in f}\mathbb 1[u\in U^*]\prod_{w\in e\setminus(f\cup\{v\})}\mathbb 1[w\in A,c_w=c]\Big(1-\prod_{x\in e-v}\mathbb 1[c\in L^*(x)]\Big),$$
--   and $\tau_j=\delta^2\binom{k-1}{\ell-1}\binom{k-\ell}{j-\ell}(\alpha/q_i)^{k-\ell}\beta_i^{j-1}\gamma_i^{k-j}t_i$.
--
--   These variables control the color degrees after one nibble step.
--
--   **Formalization Note** Each is a bounded function on a discrete space; the sanity file proves integrability of $Y^{(1)},Y^{(2)},Z^{(1)}$ and the containments $L'(u)\subseteq L^*(u)$, $U^*\subseteq\tilde U$ stated on p.31.
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), pp.27–28, eqs. (35)–(38), (40), (43), pp.31–32

import Mathlib
import Definitions.Def_UncrowdedColoring_IsRestrictionFamily
import Definitions.Def_UncrowdedColoring_nibblePsi

open scoped Classical

namespace UncrowdedColoring

variable {V : Type*} {U : Finset V} {L : V → Finset ℕ}

/-- `X_{ℓ,j}(v, c)` (p.27): the sum over `e ∈ E(F_c, j, v)` and `f ∈ binom(e − v, ℓ − 1)` of
`1[(∀u ∈ f, u ∈ Ũ and c ∈ L′(u)) ∧ (∀w ∈ e \ (f ∪ {v}), ψ(w) = c)]`. (Dhawan, Methuku, Vo, manuscript
sha256 2e7243ce…, p.27.) -/
noncomputable def XVarJ (F : ℕ → Finset (Finset V)) (T : TrialSpace U L) (ℓ j : ℕ) (v : V) (c : ℕ) :
    ℝ :=
  ∑ e ∈ edgesOfSizeAt (F c) j v, ∑ f ∈ (e.erase v).powersetCard (ℓ - 1),
    if (∀ u ∈ f, u ∈ uTilde F T ∧ c ∈ keptColours F T u) ∧
        ∀ w ∈ e \ (f ∪ {v}), nibblePsi F T w = some c
    then 1 else 0

/-- `X_ℓ(v, c) := ∑_{j=ℓ}^k X_{ℓ,j}(v, c)` (p.28). -/
noncomputable def XVar (k : ℕ) (F : ℕ → Finset (Finset V)) (T : TrialSpace U L) (ℓ : ℕ) (v : V)
    (c : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc ℓ k, XVarJ F T ℓ j v c

/-- `D∗(u)` relative to `v` (p.31): `c∗` was discarded at `u` via an edge not containing `v`, i.e.
"there exists an edge e′ ∈ E(F_{c∗}, u) \ E(F_{c∗}, v) such that every vertex x ∈ e′ − u satisfies
x ∈ A and c_x = c∗." -/
def IsDiscardedStar (F : ℕ → Finset (Finset V)) (A : Set V) (col : V → ℕ) (v u : V) (c : ℕ) : Prop :=
  ∃ e ∈ F c, u ∈ e ∧ v ∉ e ∧ ∀ x ∈ e.erase u, x ∈ A ∧ col x = c

/-- `L∗(u) := {c∗ ∈ L(u) : c∗ ∉ D∗(u), eq(u, c∗) = 1}` relative to `v` (eq. (35), p.31). -/
noncomputable def LStar (F : ℕ → Finset (Finset V)) (T : TrialSpace U L) (v u : V) : Finset ℕ :=
  (L u).filter fun c =>
    ¬ IsDiscardedStar F (activeSet T.1.1) (colourRead T.1.2) v u c ∧ eqRead T.2 u c

/-- `U∗ := {u ∈ U : u ∉ A or c_u ∉ L∗(u)}` relative to `v` (eq. (36), p.31). -/
noncomputable def UStar (F : ℕ → Finset (Finset V)) (T : TrialSpace U L) (v : V) : Finset V :=
  U.filter fun u => u ∉ activeSet T.1.1 ∨ colourRead T.1.2 u ∉ LStar F T v u

/-- `Y^{(1)}_{ℓ,j}` (eq. (37), p.31). -/
noncomputable def Y1 (F : ℕ → Finset (Finset V)) (T : TrialSpace U L) (ℓ j : ℕ) (v : V) (c : ℕ) :
    ℝ :=
  ∑ e ∈ edgesOfSizeAt (F c) j v, ∑ f ∈ (e.erase v).powersetCard (ℓ - 1),
    (∏ u ∈ f, if u ∈ UStar F T v then (1 : ℝ) else 0) *
      ∏ w ∈ e \ (f ∪ {v}), if w ∈ activeSet T.1.1 ∧ colourRead T.1.2 w = c then (1 : ℝ) else 0

/-- `Y^{(2)}_{ℓ,j}` (eq. (38), p.31). -/
noncomputable def Y2 (F : ℕ → Finset (Finset V)) (T : TrialSpace U L) (ℓ j : ℕ) (v : V) (c : ℕ) :
    ℝ :=
  ∑ e ∈ edgesOfSizeAt (F c) j v, ∑ f ∈ (e.erase v).powersetCard (ℓ - 1),
    (∏ x ∈ e.erase v,
        if x ∈ activeSet T.1.1 ∧ colourRead T.1.2 x = colourRead T.1.2 v then (1 : ℝ) else 0) *
      ∏ w ∈ e \ (f ∪ {v}), if colourRead T.1.2 w = c then (1 : ℝ) else 0

/-- `Z^{(1)}_{ℓ,j}` (eq. (40), p.32). -/
noncomputable def Z1 (F : ℕ → Finset (Finset V)) (T : TrialSpace U L) (ℓ j : ℕ) (v : V) (c : ℕ) :
    ℝ :=
  ∑ e ∈ edgesOfSizeAt (F c) j v, ∑ f ∈ (e.erase v).powersetCard (ℓ - 1),
    (∏ u ∈ f, if u ∈ UStar F T v then (1 : ℝ) else 0) *
      (∏ w ∈ e \ (f ∪ {v}),
        if w ∈ activeSet T.1.1 ∧ colourRead T.1.2 w = c then (1 : ℝ) else 0) *
      (1 - ∏ x ∈ e.erase v, if c ∈ LStar F T v x then (1 : ℝ) else 0)

/-- `τ_j := δ² binom(k−1, ℓ−1) binom(k−ℓ, j−ℓ) (α/q_i)^{k−ℓ} β_i^{j−1} γ_i^{k−j} t_i`
(eq. (43), p.32). -/
noncomputable def tauJ (k : ℕ) (ε d : ℝ) (i ℓ j : ℕ) : ℝ :=
  delta k ε d ^ 2 * ((k - 1).choose (ℓ - 1) : ℝ) * ((k - ℓ).choose (j - ℓ) : ℝ) *
    (alpha ε d / qSeq k ε d i) ^ (k - ℓ) * betaSeq k ε d i ^ (j - 1) *
    gammaSeq k ε d i ^ (k - j) * tSeq k ε d i

end UncrowdedColoring


