-- Prove2me | Definitions.Def_MultiPriceOnline_Ranking_Setting
-- name    : MultiPriceOnline_Ranking_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:42:55.576545+00:00
-- url     : https://prove2.me/theorems/0dca1110-ae6e-476e-a337-aef7b2159c3e
-- title:
--   §2, §4, pp. 11–14, 22 — price sets, booking limits (7), the value function Φ_𝒫 (9), and Multi-price Ranking (Algorithm 2)
-- statement:
--   The objects of Ma and Simchi-Levi's analysis of **Multi-price Ranking** in the deterministic case.
--
--   1. **Price set.** A price set with $m\ge1$ prices is $0<r^{(1)}<\dots<r^{(m)}$, with the convention $r^{(0)}:=0$.
--   2. **Booking limits** (Proposition 1). Positive numbers $\alpha^{(1)},\dots,\alpha^{(m)}$ summing to $1$ with
--   $$1-e^{-\alpha^{(1)}}=\frac{1-e^{-\alpha^{(j)}}}{1-r^{(j-1)}/r^{(j)}},\qquad j=2,\dots,m.\quad(7)$$
--   They are unique. $F(\mathcal P)=1-e^{-\alpha^{(1)}}$ (Definition 2).
--   3. **Segments and value function** (Definition 1). $L^{(j)}=\sum_{j'=1}^{j}\alpha^{(j')}$, so $L^{(0)}=0$, $L^{(m)}=1$; $\ell(w)$ is the $j\in[m]$ with $w\in[L^{(j-1)},L^{(j)})$, and $\ell(1)=m$. The value function is
--   $$\Phi_{\mathcal P}(w)=r^{(\ell(w)-1)}+\bigl(r^{(\ell(w))}-r^{(\ell(w)-1)}\bigr)\frac{\exp(w-L^{(\ell(w)-1)})-1}{\exp(\alpha^{(\ell(w))})-1},\quad(9)$$
--   and $\Phi'_{\mathcal P}(w)=\bigl(r^{(\ell)}-r^{(\ell-1)}\bigr)\exp(w-L^{(\ell-1)})/(\exp(\alpha^{(\ell)})-1)$ with $\ell=\ell(w)$.
--   4. **Deterministic case.** Every $p^{(j)}_{t,i}$ is $0$ or $1$, and $j_{t,i}=\max\{j\in[m_i]:p^{(j)}_{t,i}=1\}$, or $0$ if no such $j$ exists.
--   5. **Algorithm 2.** Each item draws a seed $W_i$ uniformly from $[0,1]$, independently. Customer $t$ is offered, at price $j_{t,i}$, an available item $i$ maximizing
--   $$r_i^{(j_{t,i})}-\Phi_{\mathcal P_i}(W_i)\quad(23)$$
--   provided that maximum is strictly positive; the offered item is sold and becomes unavailable. Ties are broken by an arbitrary rule that returns a maximizer.
--   6. **Dual variables** (p. 22). If item $i$ is assigned to customer $t$, then $Z_t=r_i^{(j_{t,i})}-\Phi_{\mathcal P_i}(W_i)$ and $Y_i=\Phi'_{\mathcal P_i}(W_i)$; all others are $0$. The revenue of a run is the sum of $r_i^{(j_{t,i})}$ over assigned pairs.
--   7. **Run without an item.** The same algorithm started with a subset of the items available; with item $i$ removed it is the "run on a modified setup with item $i$ removed" of App. C.
--   8. **No ties.** At every customer, two distinct items never share the same strictly positive value of (23). This fails only on a null set of seeds.
--
--   These are the objects in which Theorem 2, Lemmas 2–3 and the two claims of App. C are stated.
--
--   **Formalization Note** Items `Fin n`, customers `Fin T`, 0-based; prices 1-based, with `pr r 0 = 0` encoding $r^{(0)}=0$. The price convention `pr`, the predicate `IsBookingLimits`, and (as reducible aliases `L` and `F`) the sums $L^{(j)}$ and $F(\mathcal P)$ come from the shared module `MultiPriceOnline.Balance.PriceSet`. This module's own `IsPriceSet` also requires $m\ge1$, the standing assumption $m_i\in\mathbb N$ of p. 11; the shared one omits it, which is harmless because no booking limits exist for $m=0$. The booking limits enter as a predicate (`IsBookingLimits`), which Proposition 1 makes uniquely satisfiable, so theorems quantified over $\alpha$ with it are about the paper's $\alpha$. $\ell(w)$ is computed as $1+\#\{j\in[1,m-1]:L^{(j)}\le w\}$, which equals Definition 1's $\ell$ when every $\alpha^{(j)}>0$. $\Phi'$ is the explicit derivative on the segment $\ell(w)$, which is the right derivative at a segment border (the paper leaves $\Phi'$ undefined there). The algorithm's step at customer $t$ reads only $p_t$, the seeds and the set of available items; the tie-breaking rule may depend on the time, the candidate set and the scores. The seed law is the product of $n$ copies of Lebesgue measure restricted to $[0,1]$.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, pp. 11–14 (model, deterministic case, Proposition 1 (7), Definitions 1–2, (9)); p. 22 (Algorithm 2, (23), dual variables); pp. 45–46 (App. C, run with item i removed)

import Mathlib
import Definitions.Def_MultiPriceOnline_Balance_PriceSet

namespace MultiPriceOnline.Ranking

open MeasureTheory

/-! Price sets, booking limits, the value function `Φ_𝒫` (9), the deterministic case and
Algorithm 2 (Multi-price Ranking) of Ma–Simchi-Levi, arXiv:1905.04770v1, pp. 11–14, 22.

A price set with `m` prices is a function `r : ℕ → ℝ` read at `1, …, m`; `pr r 0 = 0` is the
paper's convention `r^{(0)} := 0`. Items are `Fin n`, customers `Fin T` (0-based). -/

/-- A price set of `m ∈ ℕ` prices `0 < r^{(1)} < … < r^{(m)}`, with `m ≥ 1` (p. 11). -/
def IsPriceSet (m : ℕ) (r : ℕ → ℝ) : Prop :=
  1 ≤ m ∧ 0 < r 1 ∧ ∀ j, 1 ≤ j → j < m → r j < r (j + 1)

/-- `F(𝒫) = 1 - e^{-α^{(1)}}` (Definition 2, p. 14): the shared `MultiPriceOnline.Balance.Fval`. -/
noncomputable abbrev F (α : ℕ → ℝ) : ℝ := MultiPriceOnline.Balance.Fval α

/-- The segment border `L^{(j)} = ∑_{j'=1}^{j} α^{(j')}` (Definition 1, p. 14); `L^{(0)} = 0`:
the shared `MultiPriceOnline.Balance.Lsum`. -/
abbrev L (α : ℕ → ℝ) (j : ℕ) : ℝ := MultiPriceOnline.Balance.Lsum α j

/-- The segment index `ℓ(w)` (Definition 1): `1 + #{j ∈ [1, m-1] : L^{(j)} ≤ w}`. For positive
booking limits this is the unique `j ∈ [m]` with `w ∈ [L^{(j-1)}, L^{(j)})`, and `ℓ(L^{(m)}) = m`. -/
noncomputable def ell (m : ℕ) (α : ℕ → ℝ) (w : ℝ) : ℕ :=
  1 + ((Finset.Icc 1 (m - 1)).filter (fun j => L α j ≤ w)).card

/-- The value function (9), p. 14:
`Φ_𝒫(w) = r^{(ℓ-1)} + (r^{(ℓ)} - r^{(ℓ-1)}) (exp(w - L^{(ℓ-1)}) - 1) / (exp(α^{(ℓ)}) - 1)`,
`ℓ = ℓ(w)`. -/
noncomputable def Phi (m : ℕ) (r : ℕ → ℝ) (α : ℕ → ℝ) (w : ℝ) : ℝ :=
  MultiPriceOnline.Balance.pr r (ell m α w - 1) +
    (r (ell m α w) - MultiPriceOnline.Balance.pr r (ell m α w - 1)) *
      (Real.exp (w - L α (ell m α w - 1)) - 1) / (Real.exp (α (ell m α w)) - 1)

/-- The derivative `Φ'_𝒫(w) = (r^{(ℓ)} - r^{(ℓ-1)}) exp(w - L^{(ℓ-1)}) / (exp(α^{(ℓ)}) - 1)`,
`ℓ = ℓ(w)`: the derivative of (9) inside a segment, and its right derivative at a border. -/
noncomputable def PhiDeriv (m : ℕ) (r : ℕ → ℝ) (α : ℕ → ℝ) (w : ℝ) : ℝ :=
  (r (ell m α w) - MultiPriceOnline.Balance.pr r (ell m α w - 1)) *
    Real.exp (w - L α (ell m α w - 1)) / (Real.exp (α (ell m α w)) - 1)

/-- The deterministic case (p. 12): every `p_{t,i}^{(j)}`, `j ∈ [m_i]`, is `0` or `1`. -/
def IsDeterministic {n T : ℕ} (m : Fin n → ℕ) (p : Fin T → Fin n → ℕ → ℝ) : Prop :=
  ∀ t i j, 1 ≤ j → j ≤ m i → (p t i j = 0 ∨ p t i j = 1)

/-- `j_{t,i} = max{j ∈ [m_i] : p_{t,i}^{(j)} = 1}`, and `0` if that set is empty (p. 12),
computed from the present customer's purchase data `q = p t` only. -/
noncomputable def jt {n : ℕ} (m : Fin n → ℕ) (q : Fin n → ℕ → ℝ) (i : Fin n) : ℕ :=
  (Finset.Icc 1 (m i)).sup fun j => if q i j = 1 then j else 0

/-- The quantity maximized in (23): `r_i^{(j_{t,i})} - Φ_{𝒫_i}(W_i)`, for the present customer's
data `q = p t` and seeds `W`. -/
noncomputable def score {n : ℕ} (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (q : Fin n → ℕ → ℝ)
    (W : Fin n → ℝ) (i : Fin n) : ℝ :=
  MultiPriceOnline.Balance.pr (r i) (jt m q i) - Phi (m i) (r i) (α i) (W i)

/-- A tie-breaking rule: at time `t`, from a nonempty set of candidate items and their scores,
it returns an item. -/
abbrev Selector (n T : ℕ) :=
  Fin T → (C : Finset (Fin n)) → C.Nonempty → (Fin n → ℝ) → Fin n

/-- The rule returns a maximizer of the scores over the candidate set ("offer any item
maximizing (23)"). -/
def IsArgmaxSelector {n T : ℕ} (sel : Selector n T) : Prop :=
  ∀ t (C : Finset (Fin n)) (hC : C.Nonempty) (s : Fin n → ℝ),
    sel t C hC s ∈ C ∧ ∀ i ∈ C, s i ≤ s (sel t C hC s)

/-- Lines 4–6 of Algorithm 2 at customer `t`, given only the present customer's data `q = p t`,
the seeds and the set of available items: if the maximum of (23) over available items is
strictly positive, the selected maximizer is offered (at price `j_{t,i}`); otherwise nothing. -/
noncomputable def offer {n T : ℕ} (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (sel : Selector n T)
    (t : Fin T) (q : Fin n → ℕ → ℝ) (W : Fin n → ℝ) (avail : Finset (Fin n)) : Option (Fin n) :=
  if h : avail.Nonempty then
    if 0 < score m r α q W (sel t avail h (score m r α q W)) then
      some (sel t avail h (score m r α q W))
    else none
  else none

/-- The set of available items before customer `s` (0-based) in a run of Algorithm 2 whose
initially available items are `present` (`Finset.univ` for the algorithm itself; `univ.erase i`
for the run "on a modified setup with item `i` removed", App. C). Line 7 removes an offered
item. The step at customer `s` reads only `p s`. -/
noncomputable def availBefore {n T : ℕ} (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (p : Fin T → Fin n → ℕ → ℝ) (sel : Selector n T) (present : Finset (Fin n))
    (W : Fin n → ℝ) : ℕ → Finset (Fin n)
  | 0 => present
  | s + 1 =>
    if h : s < T then
      match offer m r α sel ⟨s, h⟩ (p ⟨s, h⟩) W (availBefore m r α p sel present W s) with
      | some i => (availBefore m r α p sel present W s).erase i
      | none => availBefore m r α p sel present W s
    else availBefore m r α p sel present W s

/-- The item assigned to customer `t` by Algorithm 2 (from the available items `present`) with
seeds `W`, or `none` if customer `t` is rejected. -/
noncomputable def run2 {n T : ℕ} (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (p : Fin T → Fin n → ℕ → ℝ) (sel : Selector n T) (present : Finset (Fin n))
    (W : Fin n → ℝ) (t : Fin T) : Option (Fin n) :=
  offer m r α sel t (p t) W (availBefore m r α p sel present W t.val)

/-- The revenue of the run: customer `t` assigned item `i` pays `r_i^{(j_{t,i})}`. -/
noncomputable def rev2 {n T : ℕ} (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (p : Fin T → Fin n → ℕ → ℝ) (sel : Selector n T) (present : Finset (Fin n))
    (W : Fin n → ℝ) : ℝ :=
  ∑ t, match run2 m r α p sel present W t with
    | some i => MultiPriceOnline.Balance.pr (r i) (jt m (p t) i)
    | none => 0

/-- The dual variable `Z_t` (p. 22): `r_i^{(j_{t,i})} - Φ_{𝒫_i}(W_i)` if the run assigns item
`i` to customer `t`, and `0` otherwise (the pseudorevenue earned at `t`). -/
noncomputable def Zt {n T : ℕ} (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (p : Fin T → Fin n → ℕ → ℝ) (sel : Selector n T) (present : Finset (Fin n))
    (W : Fin n → ℝ) (t : Fin T) : ℝ :=
  match run2 m r α p sel present W t with
  | some i => score m r α (p t) W i
  | none => 0

/-- The dual variable `Y_i` (p. 22): `Φ'_{𝒫_i}(W_i)` if the run assigns item `i` to some
customer, and `0` otherwise. -/
noncomputable def Yi {n T : ℕ} (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (p : Fin T → Fin n → ℕ → ℝ) (sel : Selector n T) (present : Finset (Fin n))
    (W : Fin n → ℝ) (i : Fin n) : ℝ :=
  if ∃ t, run2 m r α p sel present W t = some i then PhiDeriv (m i) (r i) (α i) (W i) else 0

/-- The law of the seeds (line 1 of Algorithm 2): `W_i` independent and uniform on `[0, 1]`. -/
noncomputable def seedMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)

/-- No ties: at every customer, two distinct items never have the same strictly positive value
of (23). This fails only on a null set of seeds (App. C, "we ignore measure-zero events"). -/
def NoTies {n T : ℕ} (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (W : Fin n → ℝ) : Prop :=
  ∀ t (i i' : Fin n), i ≠ i' → 0 < score m r α (p t) W i →
    score m r α (p t) W i ≠ score m r α (p t) W i'

end MultiPriceOnline.Ranking


