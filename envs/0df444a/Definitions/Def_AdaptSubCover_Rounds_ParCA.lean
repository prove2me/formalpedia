-- Prove2me | Definitions.Def_AdaptSubCover_Rounds_ParCA
-- name    : AdaptSubCover_Rounds_ParCA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:00.536737+00:00
-- url     : https://prove2.me/theorems/22ae57e4-d611-48db-b152-dbdf99ed534e
-- title:
--   Algorithms 1–2, pp. 7–8 — the score (1), ParCA's greedy list and probing phase NA, and the r-round algorithm SSC
-- statement:
--   Fix an instance of stochastic submodular cover (items $\mathcal X$, costs $c$, monotone submodular $f$, $Q = f(U)$).
--
--   **Partial cover parameter.** For $z \in \mathbb N$ put $\delta = 2^{-z}$ and $\tau = Q(1-\delta)$ (Algorithm 1, line 1; the analysis takes $\delta$ a power of two, p. 10).
--
--   **The score (1).** For a set function $g$ with maximal value $Q'$ and threshold $\tau'$, a set $\mathcal S$ of items already on the list, and an item $\mathcal X_e \notin \mathcal S$,
--   $$\mathrm{score}(\mathcal X_e) = \frac{1}{c_e} \sum_{S \sim \mathcal S :\, g(S) \le \tau'} \Pr(\mathcal S = S)\cdot \mathbb E_{X_e \sim \mathcal X_e}\!\left[\frac{g(S \cup X_e) - g(S)}{Q' - g(S)}\right].$$
--   In round 1 of the algorithm $g = f$, $Q' = Q$, $\tau' = \tau$.
--
--   **ParCA (Algorithm 1).** A list $L$ is a *greedy list* over a set of available items if it lists each available item exactly once and each entry maximizes the score among the available items not yet listed (every tie-break is allowed). The non-adaptive strategy $\mathtt{NA}$ probes the items of $L$ in order while the realized set $R$ satisfies $f(R) \le \tau$, i.e. it stops as soon as $f(R) > \tau$ (or the list is exhausted).
--
--   **SSC (Algorithm 2).** A round-based solution follows $\mathrm{SSC}(r, \mathcal X, f)$ if in every round $k = 1, \dots, r$, from every history with realization $R$ at the start of the round, it runs ParCA on the residual instance: the items not yet probed, the function $g = f$ in round 1 and $g = f_R$, $f_R(T) = f(R \cup T) - f(R)$, afterwards, the maximal value $Q' = Q$ in round 1 and $Q' = Q - f(R)$ afterwards, and the parameter $\delta = Q'^{-1/(r-k+1)}$ rounded down to the power of two $\delta' = 2^{-z}$ with $\delta/2 < \delta' \le \delta$. The round's list is a greedy list for $(g, Q', Q'(1-\delta'))$ and its stopping rule is "$g(\text{everything realized so far}) > Q'(1-\delta')$". If $Q' = 0$ (already covered) the round probes nothing.
--
--   **Formalization Note.** The rounding of $\delta$ to $\delta' = 2^{-\lceil \log_2 Q' / (r-k+1)\rceil}$ is the paper's own (p. 10, "we can use a power-of-two value $\delta'$ where $\delta/2 \le \delta' \le \delta$"); it is built into SSC here. The score sums over all joint realizations $\omega$ the quantity for $S = $ the image of $\mathcal S$ under $\omega$; by independence this equals (1), and in later rounds the items' laws are unchanged. "Select an item that maximizes" is formalized as "every entry maximizes", so all tie-breaks are covered.
-- source:
--   Ghuge, Gupta, Nagarajan, The Power of Adaptivity for Stochastic Submodular Cover, arXiv:2106.16115v1, pp. 7–10, §3, Algorithm 1 (eq. (1)), Algorithm 2, §3.1, §4 (power-of-two δ, p. 10)

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_Model

namespace AdaptSubCover.Rounds

noncomputable section

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

/-- `δ = 2^{-z}`, the power-of-two partial-cover parameter (p. 10). -/
def delta (z : ℕ) : ℝ := (2⁻¹ : ℝ) ^ z

/-- The threshold `τ = Q(1 - δ)` of ParCA for `δ = 2^{-z}` (Algorithm 1, line 1). -/
def Instance.tau (I : Instance U m) (z : ℕ) : ℝ := (I.Q : ℝ) * (1 - delta z)

open Classical in
/-- The score (1) of item `e` after the items `S` are on the list, for a set function `g` with
maximal value `Q'` and threshold `τ'`:
`(1/c_e) · Σ_{S : g(S) ≤ τ'} P(𝒮 = S) · E_{X_e}[(g(S ∪ X_e) − g(S)) / (Q' − g(S))]`. -/
def Instance.scoreG (I : Instance U m) (g : Finset U → ℝ) (Q' τ' : ℝ)
    (S : Finset (Fin m)) (e : Fin m) : ℝ :=
  (1 / (I.c e : ℝ)) * I.E (fun ω =>
    if g (S.image ω) ≤ τ' then
      (g (insert (ω e) (S.image ω)) - g (S.image ω)) / (Q' - g (S.image ω))
    else 0)

/-- `L` is a list ParCA can build (Algorithm 1, lines 2–4) over the items `avail` for the
function `g`, maximal value `Q'` and threshold `τ'`: it lists every item of `avail` once, and
each entry maximizes the score (1) among the items not yet listed (any tie-break). -/
def Instance.IsGreedyList (I : Instance U m) (g : Finset U → ℝ) (Q' τ' : ℝ)
    (avail : Finset (Fin m)) (L : List (Fin m)) : Prop :=
  L.Nodup ∧ L.toFinset = avail ∧
    ∀ k (hk : k < L.length), ∀ e ∈ avail \ (L.take k).toFinset,
      I.scoreG g Q' τ' (L.take k).toFinset e ≤ I.scoreG g Q' τ' (L.take k).toFinset (L[k]'hk)

/-- The probing phase of ParCA (Algorithm 1, lines 5–9) as a round: probe the list `L` in order
while `f(R) ≤ τ`. -/
def Instance.parcaRound (I : Instance U m) (τ : ℝ) (L : List (Fin m)) : Round m U :=
  ⟨L, fun h => decide (τ < (I.f h.realized : ℝ))⟩

/-- The decision path of the non-adaptive strategy `NA` of §3.1 under `ω`. -/
def Instance.NA (I : Instance U m) (τ : ℝ) (L : List (Fin m)) (ω : Fin m → U) : History m U :=
  (I.parcaRound τ L).run ω []

/-- `σ` follows Algorithm 2 `SSC(r, 𝒳, f)` in each round `k < r`, from every history `h` at the
start of the round. With `R` the realization of `h`, round `k` runs ParCA on the residual instance
(items not in `h`, function `g = f` in round 1 and `g = f_R` afterwards, maximal value
`Q' = Q − f(R)`, `Q' = Q` in round 1) with `δ = Q'^{-1/(r-k)}` rounded down to the power of two
`δ' = 2^{-z}`, `δ/2 < δ' ≤ δ` (p. 10). If `Q' = 0` the round probes nothing. -/
def Instance.IsSSC (I : Instance U m) (r : ℕ) (σ : RoundPolicy m U) : Prop :=
  ∀ k < r, ∀ h : History m U,
    let R := h.realized
    let g : Finset U → ℝ :=
      if k = 0 then (fun A => (I.f A : ℝ)) else (fun A => (I.f (R ∪ A) : ℝ) - I.f R)
    let Q' : ℝ := if k = 0 then (I.Q : ℝ) else (I.Q : ℝ) - I.f R
    let z : ℕ := ⌈Real.logb 2 Q' / ((r : ℝ) - k)⌉₊
    let τ' : ℝ := Q' * (1 - delta z)
    (Q' = 0 ∧ (σ k h).order = []) ∨
      (0 < Q' ∧ I.IsGreedyList g Q' τ' (Finset.univ \ h.items) (σ k h).order ∧
        ∀ h' : History m U, (σ k h).stop h' = decide (τ' < g h'.realized))

end

end AdaptSubCover.Rounds


