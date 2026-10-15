-- Prove2me | Definitions.Def_SuperstarExcl_Complementors_Market
-- name    : SuperstarExcl_Complementors_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:22.361396+00:00
-- url     : https://prove2.me/theorems/893d4e1d-f5b8-49f5-83da-7acec7a09e52
-- title:
--   Indifferent consumer (1), fulfilled-expectations demand (4), price equilibrium, homing decisions and complementors' surplus
-- statement:
--   Fix a model (see the definition of the model) and let $\phi\in\mathbb R$ be the value of the Superstar to consumers. Let $g_i\in\{0,1\}$ indicate the Superstar's presence on platform $i$, and let $p_1,p_2$ be the consumer prices. The file defines the following objects.
--
--   1. **Indifferent consumer (1).** For expected complementor masses $N_1,N_2$,
--   $$
--   \tilde m(p_1,p_2,N_1,N_2,g_1,g_2)=\phi(g_1-g_2)-(p_1-p_2)+\theta(N_1-N_2).
--   $$
--   Consumers with $m\le\tilde m$ join platform $1$.
--   2. **Fulfilled-expectations demand (4).** A number $D$ is a fulfilled-expectations consumer share of platform $1$ at prices $(p_1,p_2)$ if
--   $$
--   D=F\bigl(\phi(g_1-g_2)-(p_1-p_2)+\theta[\Lambda(\gamma D)-\Lambda(\gamma(1-D))]\bigr).
--   $$
--   Platform $2$'s share is $1-D$, and the complementor mass on platform $i$ is $\Lambda(\gamma D_i)$.
--   3. **Price equilibrium.** A triple $(p_1,p_2,D)$ is an equilibrium for $(g_1,g_2)$ if $D$ is a fulfilled-expectations share at $(p_1,p_2)$ and no platform gains from a unilateral price change. For every price $p$ and every fulfilled-expectations share $D'$ at $(p,p_2)$, $pD'\le p_1D$. Symmetrically, for every $p$ and every share $D'$ at $(p_1,p)$, $p(1-D')\le p_2(1-D)$.
--   4. **Equilibrium indifferent consumer** $m^\star=\tilde m(p_1,p_2,\Lambda(\gamma D),\Lambda(\gamma(1-D)),g_1,g_2)$.
--   5. **Selected exclusivity outcome.** For exclusivity on platform $1$ ($g=(1,0)$) and $\phi$ given, consider continuous functions $t\mapsto(p_1(t),p_2(t),D(t))$ on $[0,\phi]$. For every $t\in[0,\phi]$, the triple $(p_1(t),p_2(t),D(t))$ is an equilibrium of the game in which the Superstar is worth $t$, with $0<D(t)<1$. At $t=0$ the prices are equal, $p_1(0)=p_2(0)$. The outcome at value $\phi$ is $(p_1(\phi),p_2(\phi),D(\phi))$.
--   6. **Homing decisions.** A type-$k$ complementor joins a platform with consumer share $D_i$ if and only if $k\le\gamma D_i$. It multihomes if it joins both platforms, singlehomes on platform $1$ if it joins $1$ but not $2$, and zerohomes if it joins neither.
--   7. **Complementors' total surplus.** When the shares are $D_1,D_2$, a type-$k$ complementor earns $\gamma D_i-k$ on each platform it joins, so
--   $$
--   FS(D_1,D_2)=\int_0^{\gamma D_1}(\gamma D_1-k)\lambda(k)\,dk+\int_0^{\gamma D_2}(\gamma D_2-k)\lambda(k)\,dk .
--   $$
--   At $D_1=D_2=\tfrac12$ this is the paper's $FS^\star(1,1)=\int_0^{\gamma/2}(\gamma-2k)\lambda(k)\,dk$. The file proves this equality as a lemma.
--
--   These objects carry the paper's third and second stages: the coordination of consumers and complementors under fulfilled expectations, and price competition between the platforms.
--
--   **Formalization Note** Fulfilled-expectations demand is a relation, not a chosen function: at a given price profile the fixed-point equation may have several solutions. The best-response condition quantifies over every solution reachable by a deviation, which is the conservative reading. The paper selects equilibria verbally (p. 11). The symmetric equal-price outcome under non-exclusivity is imposed in the theorems as a hypothesis $p_1=p_2$. The exclusive outcome is the end point of the continuous path of item 5, which starts from the symmetric outcome at $t=0$; this is the object the paper's proof of Lemma 3 differentiates in $\phi$. Platform $2$'s demand is always written $1-D$. The paper's $D^\star_2(0,1)$ is $1-D(\phi)$.
-- source:
--   Carroni, Madio & Shekhar, Superstar Exclusivity in Two-Sided Markets, accepted manuscript (hdl:11585/922035), p. 8, Eq. (1) and joining rule; p. 11, Eq. (4) and equilibrium selection; p. 40, App. A.4 (FS⋆)

import Mathlib
import Definitions.Def_SuperstarExcl_Complementors_Model

namespace SuperstarExcl.Complementors

open Set

/-- Eq. (1): the indifferent consumer `m̃(p₁, p₂, N₁ᵉ, N₂ᵉ, g₁, g₂) = ϕ(g₁ - g₂) - (p₁ - p₂) + θ(N₁ᵉ - N₂ᵉ)`;
types `m ≤ m̃` join platform 1. -/
def mtilde (M : Model) (ϕ g₁ g₂ p₁ p₂ N₁ N₂ : ℝ) : ℝ :=
  ϕ * (g₁ - g₂) - (p₁ - p₂) + M.θ * (N₁ - N₂)

/-- Fulfilled-expectations demand (system (4)), as a relation: `D` is a consumer share of
platform 1 at prices `(p₁, p₂)` if `D = F(m̃)` when the complementor masses are the ones the
shares `D` and `1 - D` attract, `Nᵢ = Λ(γ Dᵢ)`. -/
def IsFEDemand (M : Model) (ϕ g₁ g₂ p₁ p₂ D : ℝ) : Prop :=
  D = M.F (mtilde M ϕ g₁ g₂ p₁ p₂ (M.Λ (M.γ * D)) (M.Λ (M.γ * (1 - D))))

/-- Price equilibrium of the second stage for exclusivity decisions `(g₁, g₂)`: `D` is a
fulfilled-expectations demand at `(p₁, p₂)`, and no platform can raise its gross profit
`pᵢ Dᵢ` by a unilateral price change, whatever fulfilled-expectations demand the deviation
induces. Platform 2's demand is `1 - D`. -/
def IsEquilibrium (M : Model) (ϕ g₁ g₂ p₁ p₂ D : ℝ) : Prop :=
  IsFEDemand M ϕ g₁ g₂ p₁ p₂ D ∧
  (∀ p D', IsFEDemand M ϕ g₁ g₂ p p₂ D' → p * D' ≤ p₁ * D) ∧
  (∀ p D', IsFEDemand M ϕ g₁ g₂ p₁ p D' → p * (1 - D') ≤ p₂ * (1 - D))

/-- The indifferent consumer at a price profile and a fulfilled-expectations share `D`
(the paper's `m⋆` at an equilibrium). -/
def mstar (M : Model) (ϕ g₁ g₂ p₁ p₂ D : ℝ) : ℝ :=
  mtilde M ϕ g₁ g₂ p₁ p₂ (M.Λ (M.γ * D)) (M.Λ (M.γ * (1 - D)))

/-- The selected exclusivity outcome (exclusivity on platform 1, `g = (1, 0)`): a continuous
path `t ↦ (p₁ t, p₂ t, D t)`, `t ∈ [0, ϕ]`, of interior price equilibria of the game in which the
Superstar is worth `t`, starting from equal prices at `t = 0`. The outcome at value `ϕ` is
`(p₁ ϕ, p₂ ϕ, D ϕ)`. -/
def IsExclusivePath (M : Model) (ϕ : ℝ) (p₁ p₂ D : ℝ → ℝ) : Prop :=
  ContinuousOn p₁ (Icc 0 ϕ) ∧ ContinuousOn p₂ (Icc 0 ϕ) ∧ ContinuousOn D (Icc 0 ϕ) ∧
  (∀ t ∈ Icc 0 ϕ, IsEquilibrium M t 1 0 (p₁ t) (p₂ t) (D t) ∧ 0 < D t ∧ D t < 1) ∧
  p₁ 0 = p₂ 0

/-- A type-`k` complementor joins a platform with consumer share `D` iff `k ≤ γ D`. -/
def Joins (M : Model) (D k : ℝ) : Prop := k ≤ M.γ * D

/-- Type `k` joins both platforms (shares `D₁`, `D₂`). -/
def Multihomes (M : Model) (D₁ D₂ k : ℝ) : Prop := Joins M D₁ k ∧ Joins M D₂ k

/-- Type `k` joins platform 1 only. -/
def SinglehomesOn1 (M : Model) (D₁ D₂ k : ℝ) : Prop := Joins M D₁ k ∧ ¬ Joins M D₂ k

/-- Type `k` joins no platform. -/
def Zerohomes (M : Model) (D₁ D₂ k : ℝ) : Prop := ¬ Joins M D₁ k ∧ ¬ Joins M D₂ k

/-- Complementors' total surplus when the platforms' consumer shares are `D₁` and `D₂`: a type-`k`
complementor earns `γ Dᵢ - k` on each platform it joins, so
`FS = ∫₀^{γD₁} (γD₁ - k) λ(k) dk + ∫₀^{γD₂} (γD₂ - k) λ(k) dk` (App. A.4). -/
noncomputable def FS (M : Model) (D₁ D₂ : ℝ) : ℝ :=
  (∫ k in (0)..(M.γ * D₁), (M.γ * D₁ - k) * M.lam k) +
    ∫ k in (0)..(M.γ * D₂), (M.γ * D₂ - k) * M.lam k

/-- At the equal split, `FS` is the paper's `FS⋆(1, 1) = ∫₀^{γ/2} (γ - 2k) λ(k) dk`. -/
theorem FS_half (M : Model) :
    FS M (1 / 2) (1 / 2) = ∫ k in (0)..(M.γ / 2), (M.γ - 2 * k) * M.lam k := by
  have h : ∀ k : ℝ, (M.γ - 2 * k) * M.lam k = 2 * ((M.γ * (1 / 2) - k) * M.lam k) := by
    intro k; ring
  simp_rw [h, intervalIntegral.integral_const_mul]
  unfold FS
  have : M.γ * (1 / 2) = M.γ / 2 := by ring
  rw [this]
  ring

end SuperstarExcl.Complementors


