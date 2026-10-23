-- Prove2me | Definitions.Def_SurelyBetter_CLB_Model
-- name    : SurelyBetter_CLB_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:32.215731+00:00
-- url     : https://prove2.me/theorems/fb706643-9c48-41d7-98c4-b58a62b53fb0
-- title:
--   §§3–5 and (6)–(7), pp. 7624–7627 — utility profiles, capacities, MBA and c-linearly biseparable preferences, optimal mixtures, monotonicity in optimal mixtures
-- statement:
--   This file fixes the Anscombe–Aumann setting of Ghili and Klibanoff in **utility space**.
--
--   Let $S$ be a finite set of states; events are subsets $E\subseteq S$ and $E^c$ is the complement. In the paper, acts are maps $f:S\to X$ into the simple lotteries $X$, mixed statewise, and every preference is in the MBA class: it is represented by $V\big((u(f(s)))_{s\in S}\big)$ as in (6), with $u:X\to\mathbb R$ nonconstant and affine and $V:u(X)^S\to\mathbb R$ normalized, monotonic and sup-norm continuous. Two acts with the same utility profile are therefore indifferent, $u$ turns statewise mixtures of acts into mixtures of profiles, and $f'(s)\succsim f(s)$ means $u(f'(s))\ge u(f(s))$. So an act is represented by its profile $v=u\circ f:S\to U$, where $U=u(X)$; and $U$ is a convex subset of $\mathbb R$ with two distinct points, every such set arising this way. The definitions are:
--
--   1. **Binary profiles.** For an event $E$ and $a,b\in\mathbb R$, $\mathrm{binProf}(E,a,b)$ is the profile equal to $a$ on $E$ and to $b$ off $E$: the profile of the act $xEy$ with $u(x)=a$, $u(y)=b$.
--   2. **Capacity** (§3). $\rho:2^S\to\mathbb R$ with $\rho(\emptyset)=0$, $\rho(S)=1$ and $\rho(E)\le\rho(F)$ whenever $E\subseteq F$.
--   3. **MBA** (§4, (6)). $V$ is normalized ($V(c,\dots,c)=c$ for $c\in U$), monotone on $U^S$ (statewise $v\le w$ implies $V(v)\le V(w)$) and continuous on $U^S$.
--   4. **c-linearly biseparable** (§6.1, (7)). $V$ is MBA, $\rho$ is a capacity, and for all events $E,E'$ and all $a\ge b$, $a'\ge b'$ in $U$,
--   $$V(\mathrm{binProf}(E,a,b))\le V(\mathrm{binProf}(E',a',b'))\iff W(E,a,b)\le W(E',a',b'),\qquad W(E,a,b)=a\,\rho(E)+b\,(1-\rho(E)).$$
--   5. **Mixtures and optimal mixtures.** $\mathrm{mix}(\alpha,f,g)=\alpha f+(1-\alpha)g$, and $\alpha^*_{f,g}$ is the set of all $\alpha\in[0,1]$ with $V(\mathrm{mix}(\beta,f,g))\le V(\mathrm{mix}(\alpha,f,g))$ for every $\beta\in[0,1]$.
--   6. **Monotonicity in optimal mixtures restricted to $\mathcal G$** (Definition 2 and §5). For all $f,f',g\in\mathcal G$ with $f\le f'$ statewise, $\alpha^*_{f,g}\le_s\alpha^*_{f',g}$ in the set order of Definition 1: $a\in\alpha^*_{f,g}$ and $b\in\alpha^*_{f',g}$ imply $\min\{a,b\}\in\alpha^*_{f,g}$ and $\max\{a,b\}\in\alpha^*_{f',g}$.
--   7. **$\{E,E^c\}$-measurable profiles**: all $\mathrm{binProf}(E,a,b)$ with $a,b\in U$.
--   8. **Axiom 2** (state-by-state monotonicity) and **Axiom 1** (independence: $f\succsim g$ iff $\alpha f+(1-\alpha)h\succsim\alpha g+(1-\alpha)h$ for $\alpha\in(0,1]$), each restricted to a set of profiles $\mathcal G$.
--
--   These objects carry Theorem 2 of the paper, its proof steps, and the §5 link between independence and monotonicity in optimal mixtures.
--
--   **Formalization Note** "Normalized" is read in the sense of Cerreia-Vioglio et al. (2011), $V$ equal to the identity on constant profiles. On a finite $S$ the product topology on `S → ℝ` is the sup-norm topology, so continuity is `ContinuousOn V (Profiles U)`. The c-linearly biseparable class is used through its representation (7), as the paper does; the Ghirardato–Marinacci axioms (1)–(5) are not encoded. A binary act with the better prize off $E$ is the profile $\mathrm{binProf}(E^c,b,a)$, so (7) for the event $E^c$ covers it. The set order is the published `Supermodularity.Lattices.InducedSetOrder` on $\mathbb R$, where $\sqcap=\min$ and $\sqcup=\max$.
-- source:
--   Ghili & Klibanoff, If It Is Surely Better, Do It More? Implications for Preferences Under Ambiguity, Management Science 67(12) (2021), pp. 7624–7627, §§3–5, Definitions 1–2, Axioms 1–2, (6), (7)

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder

namespace SurelyBetter.CLB
open Supermodularity.Lattices

variable {S : Type*}

open Classical in
/-- The utility profile of the binary act `xEy` with `u(x) = a` and `u(y) = b`:
it takes the value `a` on the event `E` and `b` off `E`. -/
noncomputable def binProf (E : Set S) (a b : ℝ) : S → ℝ := fun s => if s ∈ E then a else b

/-- §3, p. 7624: `ρ : 2^S → ℝ` is a capacity if `ρ(∅) = 0`, `ρ(S) = 1`, and `ρ` is monotone
with respect to inclusion. -/
def IsCapacity (ρ : Set S → ℝ) : Prop :=
  ρ ∅ = 0 ∧ ρ Set.univ = 1 ∧ ∀ E F : Set S, E ⊆ F → ρ E ≤ ρ F

/-- The utility profiles `u ∘ f` of acts `f`, where `U` stands for `u(X)`: all maps `S → U`. -/
def Profiles (U : Set ℝ) : Set (S → ℝ) := {v | ∀ s, v s ∈ U}

/-- §4, (6), p. 7624: `V : u(X)^S → ℝ` is normalized (`V(c,…,c) = c` on constants), monotonic
and sup-norm continuous. Only the values of `V` on `Profiles U` matter. For finite `S` the
product topology on `S → ℝ` is the sup-norm topology. -/
structure IsMBA (U : Set ℝ) (V : (S → ℝ) → ℝ) : Prop where
  normalized : ∀ c ∈ U, V (fun _ => c) = c
  monotone : ∀ v ∈ Profiles U, ∀ w ∈ Profiles U, (∀ s, v s ≤ w s) → V v ≤ V w
  continuous : ContinuousOn V (Profiles U)

/-- (7), p. 7627: `W(xEy) = u(x) ρ(E) + u(y) (1 − ρ(E))`, written for `u(x) = a`, `u(y) = b`. -/
def W7 (ρ : Set S → ℝ) (E : Set S) (a b : ℝ) : ℝ := a * ρ E + b * (1 - ρ E)

/-- §6.1, p. 7627: a c-linearly biseparable preference (within the standing MBA class of §4),
used through its representation (7): `ρ` is a capacity and `W` of (7) represents the
preference `V` over all binary acts `xEy` with `x ≿ y`, for all events `E`. -/
structure IsCLinBisep (U : Set ℝ) (V : (S → ℝ) → ℝ) (ρ : Set S → ℝ) : Prop
    extends IsMBA U V where
  capacity : IsCapacity ρ
  rep7 : ∀ E E' : Set S, ∀ a ∈ U, ∀ b ∈ U, ∀ a' ∈ U, ∀ b' ∈ U, b ≤ a → b' ≤ a' →
    (V (binProf E a b) ≤ V (binProf E' a' b') ↔ W7 ρ E a b ≤ W7 ρ E' a' b')

/-- The statewise mixture `αf + (1 − α)g` of two utility profiles. -/
def mix (α : ℝ) (f g : S → ℝ) : S → ℝ := α • f + (1 - α) • g

/-- The set of all `α ∈ [0,1]` such that `αf + (1 − α)g` is optimal in
`{βf + (1 − β)g : β ∈ [0,1]}`. -/
def optMix (V : (S → ℝ) → ℝ) (f g : S → ℝ) : Set ℝ :=
  {α | α ∈ Set.Icc (0:ℝ) 1 ∧ ∀ β ∈ Set.Icc (0:ℝ) 1, V (mix β f g) ≤ V (mix α f g)}

/-- Definition 2 (monotonicity in optimal mixtures), p. 7624, restricted to the set of
profiles `G` (§5, p. 7625): for all `f, f', g ∈ G` with `f ≤ f'` statewise, the optimal
mixtures of `(f, g)` are smaller in the set order (Definition 1) than those of `(f', g)`. -/
def MOMOn (V : (S → ℝ) → ℝ) (G : Set (S → ℝ)) : Prop :=
  ∀ f ∈ G, ∀ f' ∈ G, ∀ g ∈ G, (∀ s, f s ≤ f' s) →
    InducedSetOrder (optMix V f g) (optMix V f' g)

/-- The utility profiles of the acts measurable with respect to `{E, Eᶜ}`. -/
def measE (U : Set ℝ) (E : Set S) : Set (S → ℝ) :=
  {h | ∃ a ∈ U, ∃ b ∈ U, h = binProf E a b}

/-- Axiom 2 (state-by-state monotonicity), p. 7625, on the set of profiles `G`. -/
def StateMonotone (V : (S → ℝ) → ℝ) (G : Set (S → ℝ)) : Prop :=
  ∀ f ∈ G, ∀ f' ∈ G, (∀ s, f s ≤ f' s) → V f ≤ V f'

/-- Axiom 1 (independence), p. 7624, on the set of profiles `G`:
`f ≿ g` iff `αf + (1 − α)h ≿ αg + (1 − α)h`, for `α ∈ (0,1]`. -/
def Independence (V : (S → ℝ) → ℝ) (G : Set (S → ℝ)) : Prop :=
  ∀ f ∈ G, ∀ g ∈ G, ∀ h ∈ G, ∀ α ∈ Set.Ioc (0:ℝ) 1,
    (V g ≤ V f ↔ V (mix α g h) ≤ V (mix α f h))

end SurelyBetter.CLB


