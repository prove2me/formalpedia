-- Prove2me | Definitions.Def_SepCostShare_Protocol
-- name    : SepCostShare_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:24:46.761893+00:00
-- url     : https://prove2.me/theorems/5ef9e6c9-f2cb-4bbf-b03b-31c9725db93b
-- title:
--   Separable cost sharing protocols, pure Nash equilibria and enforceable profiles (Definition 2)
-- statement:
--   Fix a matroid game. A **cost sharing protocol** assigns to every profile $S$, player $i$ and resource $e$ a cost share $\xi_{i,e}(S)$. The **private cost** of player $i$ is
--   $$\xi_i(S)=\sum_{e\in S_i}\bigl(\xi_{i,e}(S)+d_{i,e}\bigr).$$
--   A profile $S$ is a **pure Nash equilibrium** if $\xi_i(S)\le\xi_i(S'_i,S_{-i})$ for every player $i$ and every base $S'_i\in\mathcal B_i$.
--
--   The protocol is **separable** (Definition 2) if, at every profile $S$:
--
--   1. all shares are nonnegative;
--   2. it is *stable*: the induced game has at least one pure Nash equilibrium;
--   3. it is *budget balanced*: $c_e(N_e(S))=\sum_{i\in N_e(S)}\xi_{i,e}(S)$ for every $e$ with $N_e(S)\ne\emptyset$, and $\xi_{i,e}(S)=0$ for $i\notin N_e(S)$;
--   4. it is *separable*: for any two profiles $S,S'$ and every resource $e$, $N_e(S)=N_e(S')$ implies $\xi_{i,e}(S)=\xi_{i,e}(S')$ for all $i\in N_e(S)$.
--
--   A profile $B$ is **enforceable** if some separable protocol makes $B$ a pure Nash equilibrium.
--
--   Lemma 3 characterizes enforceable profiles, and Theorem 5 produces one from any given profile.
--
--   **Formalization Note** The protocol is a share map $\xi(S,i,e)$ for the one game at hand, constrained at profiles only. Budget balance uses the set-function cost $c_e(N_e(S))$ of §3. Item 4 of Definition 2 (polynomial-time computability) is not encoded; no statement of the mission uses it.
-- source:
--   Harks, Hoefer, Huber & Surek, Efficient Black-Box Reductions for Separable Cost Sharing, arXiv:1802.10351v1, §2, p.5 (cost sharing protocol, private cost ξᵢ(S), PNE), Definition 2, pp.5–6 (stable, budget balanced, separable, enforceable)

import Mathlib
import Definitions.Def_SepCostShare_MatroidGame

namespace SepCostShare

variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

/-- The **private cost** of player `i` under cost shares `ξ` at profile `S`, arXiv:1802.10351v1,
§2, p.5: `ξᵢ(S) := Σ_{e∈Sᵢ} (ξᵢ,ₑ(S) + dᵢ,ₑ)`. Cost shares are a map `ξ S i e = ξᵢ,ₑ(S)`. -/
def MatroidGame.privCost (G : MatroidGame N E) (ξ : (N → Finset E) → N → E → ℝ)
    (S : N → Finset E) (i : N) : ℝ :=
  ∑ e ∈ S i, (ξ S i e + G.d i e)

/-- **Pure Nash equilibrium**, arXiv:1802.10351v1, §2, p.5: "A profile is a pure Nash equilibrium
(PNE) if for all i ∈ N it holds ξᵢ(S) ≤ ξᵢ(S′ᵢ, S₋ᵢ) for all S′ᵢ ∈ 𝓢ᵢ." In a matroid game the
strategies of player `i` are the bases of `𝓜ᵢ`. -/
def MatroidGame.IsPNE (G : MatroidGame N E) (ξ : (N → Finset E) → N → E → ℝ)
    (S : N → Finset E) : Prop :=
  G.IsProfile S ∧
    ∀ (i : N) (T : Finset E), (G.M i).IsBase (↑T : Set E) →
      G.privCost ξ S i ≤ G.privCost ξ (Function.update S i T) i

/-- **Separable cost sharing protocol**, Definition 2, arXiv:1802.10351v1, pp.5–6, for the
set-function costs of §3 (budget balance reads `cₑ(Nₑ(S)) = Σ_{i∈Nₑ(S)} ξᵢ,ₑ(S)`). At every
profile `S` of the game:

1. shares are nonnegative (`ξᵢ,ₑ : 𝓢 → ℝ≥0`, p.5);
2. *stable*: the induced game has at least one pure Nash equilibrium;
3. *budget balanced*: for every `e` with `Nₑ(S) ≠ ∅`, `cₑ(Nₑ(S)) = Σ_{i∈Nₑ(S)} ξᵢ,ₑ(S)`, and
   `ξᵢ,ₑ(S) = 0` for all `i ∉ Nₑ(S)`;
4. *separable*: for any two profiles `S, S′` and every `e`, `Nₑ(S) = Nₑ(S′)` implies
   `ξᵢ,ₑ(S) = ξᵢ,ₑ(S′)` for all `i ∈ Nₑ(S)`.

**Formalization Note.** The protocol is a fixed share map for the one game at hand; it is
constrained at profiles only. Item 4 of Definition 2 (polynomial-time computability) is not used
by Lemma 3 or Theorem 5 and is not encoded. -/
structure MatroidGame.IsSeparableProtocol (G : MatroidGame N E)
    (ξ : (N → Finset E) → N → E → ℝ) : Prop where
  nonneg : ∀ S, G.IsProfile S → ∀ (i : N) (e : E), 0 ≤ ξ S i e
  stable : ∃ S, G.IsPNE ξ S
  budget_balance : ∀ S, G.IsProfile S → ∀ e : E, (G.users e S).Nonempty →
    G.c e (G.users e S) = ∑ i ∈ G.users e S, ξ S i e
  zero_of_not_user : ∀ S, G.IsProfile S → ∀ (e : E) (i : N), i ∉ G.users e S → ξ S i e = 0
  separable : ∀ S S', G.IsProfile S → G.IsProfile S' → ∀ e : E,
    G.users e S = G.users e S' → ∀ i ∈ G.users e S, ξ S i e = ξ S' i e

/-- **Enforceable profile**, arXiv:1802.10351v1, p.6: "We say that a strategy profile S is
enforceable, if there is a separable protocol inducing S as a pure Nash equilibrium." -/
def MatroidGame.Enforceable (G : MatroidGame N E) (B : N → Finset E) : Prop :=
  ∃ ξ : (N → Finset E) → N → E → ℝ, G.IsSeparableProtocol ξ ∧ G.IsPNE ξ B

end SepCostShare


