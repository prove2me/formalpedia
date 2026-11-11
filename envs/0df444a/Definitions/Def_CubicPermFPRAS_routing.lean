-- Prove2me | Definitions.Def_CubicPermFPRAS_routing
-- name    : CubicPermFPRAS_routing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:56:54.829552+00:00
-- url     : https://prove2.me/theorems/da5f1760-d8d4-49fb-9f60-9e52bc6a90a5
-- title:
--   Routings, routing energy, weighted routing families and the coupling $\kappa_{u,v}$
-- statement:
--   For a chain $P$ on a finite set, a **transition** is a pair $\{x,y\}$ with $x\ne y$ and $P(x,y)>0$, and $\mathrm{Paths}(I,F)$ are the sequences of distinct states from $I$ to $F$ along transitions.
--
--   1. A **routing** from $I$ to $F$ (Definition 20) is a probability distribution $\theta$ on $\mathrm{Paths}(I,F)$.
--   2. Its **energy** (Definition 22) is $\mathrm{En}(\theta)=\sum_e\Pr_{\gamma\sim\theta}[e\in\gamma]^2$.
--   3. A **weighted routing family** for a demand $\kappa$ with labels $L$ (Definition 27) consists of weights $\hat\kappa(I,a,J)\ge0$ with $\sum_a\hat\kappa(I,a,J)=\kappa(I,J)$ (Eq. (21)) and a routing $\theta_{I,a,J}$ from $I$ to $J$ for each triple of positive weight.
--   4. The **coupling** $\kappa_{u,v}$ of Lemma 26: draw $I\sim\mu_{u,v}$ (the $\lambda$-weighted law on $\mathcal N(u,v)$) and $F\sim\mu_\emptyset$ (on $\mathcal P$) independently, and set $J=I\oplus A(I,F)$, where $A(I,F)$ is the augmenting path of $I\oplus F$ between the holes; $J$ gives the left vertices on $A(I,F)$ their $F$-partners and keeps the $I$-partners elsewhere.
--
--   **Formalization Note** A routing is a finitely supported nonnegative function on lists of states. The augmenting path is the connected component of the hole $u$ in the graph of $I\oplus F$.
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), Definitions 20, 22, 27, pp.19–25 (PDF 21–27); Lemma 26, p.24 (PDF 26)

import Mathlib
import Definitions.Def_CubicPermFPRAS_matchWeight

set_option autoImplicit false

namespace CubicPermFPRAS

noncomputable section

open Classical

section General

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- `{x, y}` is a transition of the chain `P`: `x ≠ y` and `P(x,y) > 0` (§6.1, p.19 (PDF 21);
arXiv:2609.20717, held version sha256 9e14f335…). -/
def IsTransition (P : Matrix Ω Ω ℝ) (x y : Ω) : Prop := x ≠ y ∧ 0 < P x y

/-- `γ ∈ Paths(I,F)`: a sequence `I = x₀, x₁, …, x_k = F` of distinct states with
`{x_{j−1}, x_j}` a transition for every `j` (§6.1, p.19). The empty path `[I]` is allowed
when `I = F`. -/
def IsPathFrom (P : Matrix Ω Ω ℝ) (I F : Ω) (γ : List Ω) : Prop :=
  γ.Nodup ∧ γ.head? = some I ∧ γ.getLast? = some F ∧
    ∀ k (h : k + 1 < γ.length), IsTransition P (γ[k]'(by omega)) (γ[k + 1])

/-- The transitions `{x_{j−1}, x_j}` used by a path, as unordered pairs. -/
def pathEdges (γ : List Ω) : List (Sym2 Ω) :=
  (γ.zip γ.tail).map fun p => s(p.1, p.2)

/-- A **routing** from `I` to `F` (Definition 20, p.19): a probability distribution `θ` on
`Paths(I,F)`, given as a finitely supported nonnegative function on lists of states with total
mass `1` whose support consists of paths from `I` to `F`. -/
def IsRouting (P : Matrix Ω Ω ℝ) (I F : Ω) (θ : List Ω →₀ ℝ) : Prop :=
  (∀ γ, 0 ≤ θ γ) ∧ (∀ γ ∈ θ.support, IsPathFrom P I F γ) ∧ θ.sum (fun _ x => x) = 1

/-- `Pr_{γ∼θ}[e ∈ γ]`, the probability that the routing uses the transition `e` (§6.2, p.21). -/
def usage (θ : List Ω →₀ ℝ) (e : Sym2 Ω) : ℝ :=
  ∑ γ ∈ θ.support, θ γ * (if e ∈ pathEdges γ then 1 else 0)

/-- The **energy** `En(θ) = ∑_{e ∈ T} Pr_{γ∼θ}[e ∈ γ]²` of a routing (Definition 22, p.21).
Unordered pairs that are not transitions have usage `0` for a routing, so the sum may run over
all unordered pairs. -/
def energy (θ : List Ω →₀ ℝ) : ℝ := ∑ e : Sym2 Ω, usage θ e ^ 2

/-- A **weighted routing family** for an endpoint demand `κ : Ω × Ω → ℝ≥0` with auxiliary
labels `L` (Definition 27, p.25 (PDF 27)): weights `κ̂(I,a,J) ≥ 0` with
`∑_a κ̂(I,a,J) = κ(I,J)` (Eq. (21)), and a routing `θ_{I,a,J}` from `I` to `J` for every triple
with positive weight. -/
structure WeightedRoutingFamily (P : Matrix Ω Ω ℝ) (κ : Ω → Ω → ℝ) (L : Type*) [Fintype L] where
  /-- The occurrence weights `κ̂(I,a,J)`. -/
  khat : Ω → L → Ω → ℝ
  khat_nonneg : ∀ I a J, 0 ≤ khat I a J
  khat_sum : ∀ I J, ∑ a, khat I a J = κ I J
  /-- The routing `θ_{I,a,J}` of each occurrence. -/
  route : Ω → L → Ω → (List Ω →₀ ℝ)
  route_valid : ∀ I a J, 0 < khat I a J → IsRouting P I J (route I a J)

end General

variable {n : ℕ}

/-- The graph on `V₁ ⊔ V₂` whose edges are those of the symmetric difference `I ⊕ F` of two
assignments viewed as edge sets. -/
def symmDiffGraph (I F : Asg n) : SimpleGraph (Fin n ⊕ Fin n) :=
  SimpleGraph.fromRel fun p q =>
    ∃ x y, p = Sum.inl x ∧ q = Sum.inr y ∧ Xor (I x = some y) (F x = some y)

/-- `J = I ⊕ A(I,F)` (§6.3, p.24 (PDF 26)): for `I ∈ N(u,v)` and `F ∈ P`, the component of the
hole `u` in `I ⊕ F` is the augmenting path `A(I,F)`; switching it gives each left vertex on it
its `F`-partner, while every other left vertex keeps its `I`-partner. -/
def switchAug (I F : Asg n) (u : Fin n) : Asg n :=
  fun u' => if (symmDiffGraph I F).Reachable (Sum.inl u) (Sum.inl u') then F u' else I u'

/-- `µ_{u,v}(I) = λ(I)/λ(N(u,v))` for `I ∈ N(u,v)`, `0` otherwise (p.23 (PDF 25)). -/
def muNear (lam : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n) (σ : Asg n) : ℝ :=
  if IsNear u v σ then matchWeight lam σ / familyWeight lam (NSet u v) else 0

/-- The coupling `κ_{u,v}` of Lemma 26 (p.24): draw `I ∼ µ_{u,v}` and `F ∼ µ_∅` independently
and set `J = I ⊕ A(I,F)`; `κ_{u,v}(I,J)` is the probability of the pair `(I,J)`. -/
def kappa (lam : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n) (I J : Omega n) : ℝ :=
  ∑ F ∈ PSet n, if J.1 = switchAug I.1 F u then muNear lam u v I.1 * muPM lam F else 0

end

end CubicPermFPRAS


