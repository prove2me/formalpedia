-- Prove2me | Definitions.Def_DiscreteSearchGame_Optimal_Model
-- name    : DiscreteSearchGame_Optimal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:29.647335+00:00
-- url     : https://prove2.me/theorems/39724305-3ac1-462c-96a3-b96f59f4319e
-- title:
--   §2, p. 4; Definition 1, p. 6; §3.2, pp. 9–10; p. 15; App. A, pp. 40–44 — the search game, its value, optimal strategies, Gittins sequences with tie-breaking rules, G(ε)
-- statement:
--   This file sets up the two-person zero-sum **search game** $G$ of Clarkson, Lin and Glazebrook, the objects of its Section 4 (Gittins search sequences that break ties by a fixed preference ordering) and the perturbed game $G(\epsilon)$ of Section 3.2 and Appendix A.
--
--   **The game (§2, p. 4).** A hider hides in one of $n$ boxes $1,\dots,n$. A search of box $i$ takes time $t_i>0$ and, if the hider is in box $i$, finds them with probability $q_i\in(0,1)$, independently of all other searches. A pure strategy of the searcher is a **search sequence** $\xi=(\xi_0,\xi_1,\dots)\in\mathcal C=\{1,\dots,n\}^\infty$. Write $N_i(m)$ for the number of searches of box $i$ among the first $m$ searches. If the hider is in box $i$, search $m$ is carried out exactly when the first $N_i(m)$ searches of box $i$ have failed, so the expected time to detection is
--   $$V_i(\xi)=\sum_{m\ge 0} t_{\xi_m}\,(1-q_i)^{N_i(m)}\in[0,\infty],$$
--   which is $\infty$ when $\xi$ searches box $i$ only finitely often. A **hiding strategy** is a probability vector $p$ in the simplex $\mathcal P$; a **mixed search strategy** is a probability mass function $\eta$ on $\mathcal C$ (its support is countable), with $V_i(\eta)=\sum_\xi \eta(\xi)V_i(\xi)$. Against $\xi$ the hider's expected payoff is $\sum_i p_iV_i(\xi)$.
--
--   **Value and optimality (p. 4, (1); p. 5).** The value is the hider's max-inf
--   $$v^*=\sup_{p\in\mathcal P}\ \inf_{\xi\in\mathcal C}\ \sum_{i=1}^n p_iV_i(\xi).$$
--   A hiding strategy $p$ is **optimal** if $\inf_\xi\sum_i p_iV_i(\xi)=v^*$; a search strategy $\eta$ is **optimal** if $V_i(\eta)\le v^*$ for every box $i$.
--
--   **Gittins search sequences (Definition 1, (3), p. 6).** The Gittins index of box $i$ after $m_i$ searches of it is $p_i(1-q_i)^{m_i}q_i/t_i$. A sequence $\xi$ is a Gittins search sequence against $p$, $\xi\in\mathcal C_p$, if every search is of a box with maximal current index (the published `ConformsToSearchIndex` with search cost $t$).
--
--   **Tie-breaking (p. 15; pp. 40–41).** A permutation $\sigma\in S_n$ is a preference ordering listing boxes from most to least preferred ($(2,3,1,4)$ breaks a tie between boxes 1, 2, 4 in the order 2, 1, 4). A tie-breaking rule $r\in\mathcal R$ is a sequence of preference orderings. $\xi(r,p)$ is the Gittins search sequence against $p$ that, at each search, searches the most preferred (under the ordering $r$ assigns to that search) among the boxes of maximal index; $f(r,p)=V(\xi(r,p))$. With a constant rule $\sigma$ this is $\xi_{\sigma,p}$, and
--   $$\widehat{\mathcal C}_p=\{\xi_{\sigma,p}:\sigma\in S_n\},\qquad \mathcal S_p=\{V(\xi):\xi\in\mathcal C_p\},\qquad \widehat{\mathcal S}_p=\{V(\xi):\xi\in\widehat{\mathcal C}_p\}.$$
--   $p$ is a **tie point** if $|\mathcal C_p|>1$. For $\Sigma\subseteq S_n$, (33) defines $\mathcal P(p,\Sigma)=\{x\in\mathcal P: x_{\sigma(i)}/p_{\sigma(i)}\ge x_{\sigma(i+1)}/p_{\sigma(i+1)},\ i=1,\dots,n-1,\ \sigma\in\Sigma\}$, $\sigma(i)$ the box in position $i$ of $\sigma$.
--
--   **The perturbed game (§3.2, (7)–(8); p. 40).** For $\epsilon\in(0,1/n)$ let $\mathcal P(\epsilon)=\{p\in\mathcal P: p_i\ge\epsilon\ \forall i\}$ and $M_i(\epsilon)=\inf\{V_i(\xi):\xi\in\mathcal C_p,\ p\in\mathcal P,\ p_i<\epsilon\}$. In $G(\epsilon)$ the searcher's pure strategies are $\mathcal C(\epsilon)=\{\xi\in\mathcal C_p:p\in\mathcal P(\epsilon)\}\cup\{\zeta_i(\epsilon)\}$, where $\zeta_i(\epsilon)$ pays $M_i(\epsilon)$ if the hider is in box $i$ and $0$ otherwise. Its value and optimal strategies are defined as for $G$. Finally $\bar S(\epsilon)=\{V(\xi):\xi\in\mathcal C_p,\ p\in\mathcal P(\epsilon)\}$.
--
--   These are the objects of the paper's main results: optimal search strategies exist and can be taken to mix at most $n$ sequences of $\widehat{\mathcal C}_{p^*}$.
--
--   **Formalization Note.** Boxes are `Fin n` and searches are 0-indexed (`ξ : ℕ → Fin n`). Payoffs live in `ℝ≥0∞`, so a sequence that neglects a box has payoff `⊤` there rather than a junk value. The value `gameValue` is the hider's max-inf (1), written as a supremum over the whole simplex; searcher optimality is pinned to it, so the existence results contain the minimax equality the paper takes from Ferguson. A permutation `σ : Equiv.Perm (Fin n)` is read as position ↦ box; `tieBreak σ f` is the box `σ j` with least position `j` among the maximizers of `f`. Tie-breaking rules are indexed by search step (`r k` is used at search `k`), where the paper indexes them by encountered tie; both rule spaces generate exactly $\mathcal C_p$ and constant rules give $\xi_{\sigma,p}$ in both. Constructing $\xi(r,p)$ needs `[NeZero n]`. The real vectors of $\mathcal S_p$, $\widehat{\mathcal S}_p$ and $\bar S(\epsilon)$ use `ENNReal.toReal`; they are only used for interior $p$, where every coordinate is finite. $\bar S(\epsilon)$ is written directly as the set of $V(\xi)$, which equals $S(\epsilon)$ minus the $\zeta$ payoff vectors because those have a zero coordinate while every $V_i(\xi)\ge t_{\xi_0}>0$.
-- source:
--   Clarkson, Lin & Glazebrook, A Classical Search Game in Discrete Locations, arXiv:2103.09310v1, pp. 1, 4–6, 9–10, 15, 40–41, 44: §2, (1), Definition 1 and (3), §3.2 (7)–(8), §4 p. 15, Appendix A and (33)

import Mathlib
import Definitions.Def_AllocationIndices_Jobs

namespace DiscreteSearchGame.Optimal

/-!
Clarkson, Lin & Glazebrook, *A Classical Search Game in Discrete Locations*, arXiv:2103.09310v1:
§2 (p. 4), Definition 1 and (3) (p. 6), §3.2 (pp. 9–10), §4 (p. 15) and Appendix A (pp. 40–44).

`n` boxes; a search of box `i` takes time `t i > 0` and finds a hider hidden there with
probability `q i ∈ (0, 1)`. A search sequence is `ξ : ℕ → Fin n` (searches 0-indexed); a hiding
strategy is a point of the standard simplex; a mixed search strategy is a `PMF` on search
sequences. Payoffs are expected times to detection in `ℝ≥0∞`. The published
`AllocationIndices.searchCount`, `searchCost` and `ConformsToSearchIndex` (with search cost
`c := t`) give the counts `N_i(m)`, the hider's expected payoff `∑ᵢ pᵢ Vᵢ(ξ)` and membership in the
set `𝒞_p` of Gittins search sequences against `p`.
-/

open AllocationIndices

noncomputable section

variable {n : ℕ}

/-! ### The search game `G` (§2, p. 4) -/

/-- `V_i(ξ)`: the expected time to detection when the hider is in box `i` and the searcher follows
`ξ`. Search `m` (0-indexed) is made iff the hider was not found before it, which has probability
`(1 - q_i)^{N_i(m)}`, `N_i(m)` the number of searches of box `i` among the first `m`; it takes time
`t_{ξ_m}`. The value is `∞` when `ξ` searches box `i` only finitely often. -/
def V (t q : Fin n → ℝ) (i : Fin n) (ξ : ℕ → Fin n) : ENNReal :=
  ∑' m : ℕ, ENNReal.ofReal (t (ξ m) * (1 - q i) ^ searchCount ξ m i)

/-- `V_i(η) = ∑_ξ η(ξ) V_i(ξ)` for a mixed search strategy `η` (a probability mass function on
search sequences; its support is countable). -/
def Vmix (t q : Fin n → ℝ) (i : Fin n) (η : PMF (ℕ → Fin n)) : ENNReal :=
  ∑' ξ, η ξ * V t q i ξ

/-- What the hiding strategy `p` guarantees: `inf_{ξ ∈ 𝒞} ∑ᵢ pᵢ Vᵢ(ξ)`. -/
def hiderGuarantee (t q p : Fin n → ℝ) : ENNReal :=
  ⨅ ξ : ℕ → Fin n, searchCost p q t ξ

/-- The value `v* = v₁ = max_p inf_ξ ∑ᵢ pᵢ Vᵢ(ξ)` of (1), p. 4, the outer supremum over the whole
simplex of hiding strategies. -/
def gameValue (t q : Fin n → ℝ) : ENNReal :=
  ⨆ p ∈ stdSimplex ℝ (Fin n), hiderGuarantee t q p

/-- An optimal hiding strategy: a hiding strategy that guarantees the value `v*`. -/
def IsOptimalHider (t q p : Fin n → ℝ) : Prop :=
  p ∈ stdSimplex ℝ (Fin n) ∧ hiderGuarantee t q p = gameValue t q

/-- An optimal search strategy: it guarantees an expected time to detection of at most `v*`
wherever the hider hides (p. 5). -/
def IsOptimalSearcher (t q : Fin n → ℝ) (η : PMF (ℕ → Fin n)) : Prop :=
  ∀ i, Vmix t q i η ≤ gameValue t q

/-! ### Gittins search sequences breaking ties by preference orderings (p. 15; pp. 40–41) -/

/-- The Gittins index `pᵢ (1 - qᵢ)^{mᵢ} qᵢ / tᵢ` of (3) of box `i` after `mᵢ = cnt i` searches. -/
def gittinsIndex (t q p : Fin n → ℝ) (cnt : Fin n → ℕ) (i : Fin n) : ℝ :=
  p i * (1 - q i) ^ cnt i * q i / t i

/-- The box chosen among the maximizers of `f` by the preference ordering `σ`. A permutation
`σ` is read as position ↦ box (`σ j` is the box in the `j`-th position of the ordering, so
`(2, 3, 1, 4)` prefers box 2, then 3, then 1, then 4); the chosen box is `σ j` for the least
position `j` whose box maximizes `f`. -/
def tieBreak [NeZero n] (σ : Equiv.Perm (Fin n)) (f : Fin n → ℝ) : Fin n :=
  σ ((Finset.univ.filter fun j : Fin n => ∀ i, f i ≤ f (σ j)).min' (by
    obtain ⟨x, -, hx⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
    exact ⟨σ.symm x, by simpa using fun i => hx i (Finset.mem_univ i)⟩))

/-- A tie-breaking rule `r ∈ ℛ`: a sequence of preference orderings, `r k` used at search `k`. -/
abbrev Rule (n : ℕ) := ℕ → Equiv.Perm (Fin n)

/-- The search counts `(m₁, …, mₙ)` before search `k` of the Gittins search sequence against `p`
that breaks ties by the rule `r`. -/
def ruleCounts [NeZero n] (t q p : Fin n → ℝ) (r : Rule n) : ℕ → Fin n → ℕ
  | 0 => 0
  | k + 1 =>
    ruleCounts t q p r k + Pi.single (tieBreak (r k) (gittinsIndex t q p (ruleCounts t q p r k))) 1

/-- `ξ(r, p)`: the Gittins search sequence against `p` that at search `k` searches the box of
maximal Gittins index (3) preferred by `r k`. -/
def ruleSeq [NeZero n] (t q : Fin n → ℝ) (r : Rule n) (p : Fin n → ℝ) : ℕ → Fin n :=
  fun k => tieBreak (r k) (gittinsIndex t q p (ruleCounts t q p r k))

/-- `ξ_{σ,p}`: the Gittins search sequence against `p` that breaks every tie by `σ` (p. 15). -/
def simpleSeq [NeZero n] (t q : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) :
    ℕ → Fin n :=
  ruleSeq t q (fun _ => σ) p

/-- `𝒞̂_p = {ξ_{σ,p} : σ ∈ Sₙ}` (p. 15). -/
def simpleGittins [NeZero n] (t q p : Fin n → ℝ) : Set (ℕ → Fin n) :=
  Set.range fun σ : Equiv.Perm (Fin n) => simpleSeq t q σ p

/-- The payoff vector `V(ξ) = (V₁(ξ), …, Vₙ(ξ))` as a real vector; used only for Gittins sequences
against interior `p`, where every coordinate is finite. -/
def vecReal (t q : Fin n → ℝ) (ξ : ℕ → Fin n) : Fin n → ℝ :=
  fun i => (V t q i ξ).toReal

/-- `𝒮_p = {V(ξ) : ξ ∈ 𝒞_p}` (p. 15, (29)). -/
def payoffSet (t q p : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {v | ∃ ξ, ConformsToSearchIndex p q t ξ ∧ v = vecReal t q ξ}

/-- `𝒮̂_p = {V(ξ) : ξ ∈ 𝒞̂_p}` (p. 15). -/
def simplePayoffSet [NeZero n] (t q p : Fin n → ℝ) : Set (Fin n → ℝ) :=
  vecReal t q '' simpleGittins t q p

/-- `f(r, x) = V(ξ(r, x))` (p. 41), in `[0, ∞]ⁿ`. -/
def ruleVec [NeZero n] (t q : Fin n → ℝ) (r : Rule n) (x : Fin n → ℝ) : Fin n → ENNReal :=
  fun i => V t q i (ruleSeq t q r x)

/-- `p` is a tie point: `|𝒞_p| > 1` (p. 40). -/
def IsTiePoint (t q p : Fin n → ℝ) : Prop :=
  ∃ ξ ξ', ConformsToSearchIndex p q t ξ ∧ ConformsToSearchIndex p q t ξ' ∧ ξ ≠ ξ'

/-- `𝒫(p, Σ)` of (33), p. 44: hiding strategies `x` with
`x_{σ(i)}/p_{σ(i)} ≥ x_{σ(i+1)}/p_{σ(i+1)}` for `i = 1, …, n − 1` and every `σ ∈ Σ`. -/
def orderCone (p : Fin n → ℝ) (Sig : Set (Equiv.Perm (Fin n))) : Set (Fin n → ℝ) :=
  {x | x ∈ stdSimplex ℝ (Fin n) ∧ ∀ σ ∈ Sig, ∀ i j : Fin n, j.val = i.val + 1 →
    x (σ j) / p (σ j) ≤ x (σ i) / p (σ i)}

/-! ### The perturbed game `G(ε)` (§3.2, pp. 9–10; Appendix A, p. 40) -/

/-- `𝒫(ε) = {p : pᵢ ≥ ε, i = 1, …, n}` (p. 9). -/
def interiorEps (ε : ℝ) : Set (Fin n → ℝ) :=
  {p | p ∈ stdSimplex ℝ (Fin n) ∧ ∀ i, ε ≤ p i}

/-- `Mᵢ(ε) = inf{Vᵢ(ξ) : ξ ∈ 𝒞_p with pᵢ < ε}` of (7), `p` ranging over hiding strategies. -/
def Mbound (t q : Fin n → ℝ) (ε : ℝ) (i : Fin n) : ENNReal :=
  ⨅ (p : Fin n → ℝ) (_ : p ∈ stdSimplex ℝ (Fin n)) (_ : p i < ε) (ξ : ℕ → Fin n)
    (_ : ConformsToSearchIndex p q t ξ), V t q i ξ

/-- Pure search strategies of `G(ε)`: `Sum.inl ξ` is the search sequence `ξ`, `Sum.inr i` is the
pseudo-strategy `ζᵢ(ε)`. -/
abbrev PerturbedStrategy (n : ℕ) := (ℕ → Fin n) ⊕ Fin n

/-- `𝒞(ε) = {ξ ∈ 𝒞_p : p ∈ 𝒫(ε)} ∪ {ζᵢ(ε) : i = 1, …, n}` of (8). -/
def perturbedAllowed (t q : Fin n → ℝ) (ε : ℝ) : Set (PerturbedStrategy n) :=
  {s | Sum.elim (fun ξ => ∃ p ∈ interiorEps ε, ConformsToSearchIndex p q t ξ) (fun _ => True) s}

/-- Payoff vectors in `G(ε)`: `V(ξ)` for a search sequence; `ζᵢ(ε)` pays `Mᵢ(ε)` if the hider is in
box `i` and `0` otherwise. -/
def perturbedVec (t q : Fin n → ℝ) (ε : ℝ) : PerturbedStrategy n → Fin n → ENNReal
  | Sum.inl ξ => fun i => V t q i ξ
  | Sum.inr j => Pi.single j (Mbound t q ε j)

/-- What the hiding strategy `p` guarantees in `G(ε)`. -/
def perturbedGuarantee (t q : Fin n → ℝ) (ε : ℝ) (p : Fin n → ℝ) : ENNReal :=
  ⨅ s ∈ perturbedAllowed t q ε, ∑ i, ENNReal.ofReal (p i) * perturbedVec t q ε s i

/-- The value of `G(ε)`: the hider's max-inf, as (1) with `𝒞(ε)` in place of `𝒞`. -/
def perturbedValue (t q : Fin n → ℝ) (ε : ℝ) : ENNReal :=
  ⨆ p ∈ stdSimplex ℝ (Fin n), perturbedGuarantee t q ε p

/-- An optimal hiding strategy of `G(ε)`. -/
def IsOptimalHiderPert (t q : Fin n → ℝ) (ε : ℝ) (p : Fin n → ℝ) : Prop :=
  p ∈ stdSimplex ℝ (Fin n) ∧ perturbedGuarantee t q ε p = perturbedValue t q ε

/-- An optimal search strategy of `G(ε)`: a mixture of elements of `𝒞(ε)` whose expected payoff
is at most the value of `G(ε)` wherever the hider hides. -/
def IsOptimalSearcherPert (t q : Fin n → ℝ) (ε : ℝ) (μ : PMF (PerturbedStrategy n)) : Prop :=
  (∀ s ∈ μ.support, s ∈ perturbedAllowed t q ε) ∧
    ∀ i, ∑' s, μ s * perturbedVec t q ε s i ≤ perturbedValue t q ε

/-- `S̄(ε) = S(ε) \ {V(ζᵢ(ε))} = {V(ξ) : ξ ∈ 𝒞_p, p ∈ 𝒫(ε)}` (p. 40). -/
def perturbedGittinsSet (t q : Fin n → ℝ) (ε : ℝ) : Set (Fin n → ℝ) :=
  {v | ∃ p ∈ interiorEps ε, ∃ ξ, ConformsToSearchIndex p q t ξ ∧ v = vecReal t q ξ}

end

end DiscreteSearchGame.Optimal


