-- Prove2me | Definitions.Def_ValTrackRM_Public_Model
-- name    : ValTrackRM_Public_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:36.30077+00:00
-- url     : https://prove2.me/theorems/c4d5dbbb-0eba-45e6-b449-da15e13a5af3
-- title:
--   §3, pp. 8–9, Algorithm 1 p. 13, Defs. EC.1–EC.2 — price grid, $q^{(j)}$, $q$, $c^*(\mathcal P)$, OPT, valuation tracking levels, law of the sold vector, expected revenue
-- statement:
--   This file sets up the single-leg pricing model of Section 3 (public pricing, deterministic valuations) and Algorithm 1, the **valuation tracking procedure**.
--
--   **Prices and valuations.** Fix integers $m\ge 1$ and $k\ge 1$. A firm holds $k$ units of one item. The price grid is $0<r^{(1)}<\dots<r^{(m)}$, with $r^{(0)}=0$ representing the lack of a customer and $r^{(m+1)}=\infty$ representing shutting off demand. Customers $t=1,\dots,T$ arrive online ($T$ unknown to the seller); customer $t$ has valuation $V_t=r^{(j_t)}$ with $j_t\in\{0,1,\dots,m\}$. A valuation sequence is therefore a finite list of indices $(j_1,\dots,j_T)$.
--
--   **Definition 1.** For $j\in[m]$,
--   $$
--   q^{(j)}=1-\frac{r^{(j-1)}}{r^{(j)}},\qquad q=\sum_{j=1}^m q^{(j)},\qquad c^*(\mathcal P)=\frac1q .
--   $$
--   For a level $\ell<m$ write $q_{\mathrm{tot}}(\ell)=\sum_{j=\ell+1}^m q^{(j)}$.
--
--   **Offline optimum.** $\mathrm{OPT}(V_1,\dots,V_T)$ is the largest total valuation $\sum_{t\in S}V_t$ over sets $S\subseteq[T]$ of at most $k$ customers (each charged her valuation), i.e. the sum of the $\min\{k,T\}$ largest valuations. $M^k(t)$ (Definition EC.2) is the list of the $k$ largest elements of $(V_1,\dots,V_t)$, largest first, padded with zeros when $t<k$.
--
--   **Algorithm 1.** Each unit $i\in[k]$ carries a level $\ell_{i,t}\in\{0,\dots,m\}$ (meaning $\mathtt{level}[i]=r^{(\ell_{i,t})}$, initially $0$) and a flag $\mathtt{sold}[i]$ (initially false). Customer $t$ is assigned to a unit $i_t$ of minimal level (line 4; ties broken by a fixed selector). Let $\ell=\ell_{i_t,t-1}$. If $\mathtt{sold}[i_t]$ is false and $\ell<m$, the price $r^{(p)}$, $\ell<p\le m$, is offered with probability $q^{(p)}/q_{\mathrm{tot}}(\ell)$ (line 8); otherwise the price is $\infty$. The customer buys iff $V_t\ge P_t$, in which case $\mathtt{sold}[i_t]$ becomes true; finally $\ell_{i_t,t}=\max\{\ell,j_t\}$ (line 13), and the other levels are unchanged.
--
--   The levels and assignments are deterministic functions of the valuations (Definition EC.1); only the sold vector $(S_{1,t},\dots,S_{k,t})$ is random. Its law after $t$ steps is an explicit probability mass function on $\{0,1\}^k$, obtained from the point mass at "nothing sold" by applying the transition just described once per customer. From it the file defines $\Pr[S_{i,t}=1]$, the expected revenue $\mathbb E[P_tX_t]$ of step $t$ (computed from the law after $t-1$ steps and $V_t$ only), and
--   $$
--   \mathbb E[\mathsf{ALG}(V_1,\dots,V_T)]=\sum_{t=1}^T\mathbb E[P_tX_t].
--   $$
--
--   These objects are shared by every statement of the mission: Lemmas EC.1–EC.4 and Theorem 1.
--
--   **Formalization Note.** Prices are a function $r:\mathbb N\to\mathbb R$; the standing assumptions $r(0)=0$ and $r(j)<r(j+1)$ for $j<m$ are hypotheses of each theorem. Valuations are indices in $\{0,\dots,m\}$ and the level update of line 13 takes the maximum of indices, which equals the maximum of values because $r$ is strictly increasing. The tie-break of line 4 is a parameter `sel`; the theorems require it to return a unit of minimal level and hold for every such selector. Printed line 8 lists the last offer probability as `ℓt+1/q_tot`; the definition uses $q^{(m)}/q_{\mathrm{tot}}$, which is what the text ("these probabilities sum to 1") and the proofs on pp. ec2–ec3 use. At a unit of level $m$ the step is a rejection; the paper shows (p. 13) that such a unit is always already sold.
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, pp. 8–9, 13, ec1, ec4, Section 3, Equation (1), Definition 1, Algorithm 1, Definition EC.1, Definition EC.2

import Mathlib

namespace ValTrackRM.Public

/-! Ma, Simchi-Levi & Teo, *On Policies for Single-Leg Revenue Management with Limited Demand
Information*, arXiv:1810.10900v2: §3 (p. 8), Definition 1 (pp. 8–9), Algorithm 1 (p. 13),
Definition EC.1 (p. ec1), Definition EC.2 (p. ec4).

Prices are `r : ℕ → ℝ`, with `r 0 = 0` (no customer) and `r 1 < ⋯ < r m` the price grid; a
valuation is an index `j : Fin (m + 1)` (meaning `V_t = r^{(j)}`), a valuation sequence is a
`List (Fin (m + 1))`, and inventory units are `Fin k`. -/

/-- Definition 1: `q^{(j)} = 1 - r^{(j-1)} / r^{(j)}` (used for `1 ≤ j ≤ m`). -/
noncomputable def qj (r : ℕ → ℝ) (j : ℕ) : ℝ := 1 - r (j - 1) / r j

/-- Definition 1: `q = ∑_{j=1}^m q^{(j)}`. -/
noncomputable def qSum (r : ℕ → ℝ) (m : ℕ) : ℝ := ∑ j ∈ Finset.Icc 1 m, qj r j

/-- Definition 1: `c^*(P) = 1 / q`. -/
noncomputable def cStar (r : ℕ → ℝ) (m : ℕ) : ℝ := 1 / qSum r m

/-- Algorithm 1, line 7: `q_tot = ∑_{j=ℓ+1}^m q^{(j)}`. -/
noncomputable def qTot (r : ℕ → ℝ) (m ℓ : ℕ) : ℝ := ∑ p ∈ Finset.Ioc ℓ m, qj r p

/-- Algorithm 1, line 8 (corrected): at level `ℓ < m`, price `r^{(p)}`, `ℓ < p ≤ m`, is offered
with probability `q^{(p)} / q_tot`. -/
noncomputable def offerProb (r : ℕ → ℝ) (m ℓ p : ℕ) : ℝ := qj r p / qTot r m ℓ

variable {m k : ℕ}

/-- Algorithm 1, lines 4 and 13: with the current levels `L` (indices, `level[i] = r^{(L i)}`),
the customer is assigned to the unit `sel L` (a unit of minimal level, line 4), and that unit's
level becomes `max (L (sel L)) j` after a customer of valuation index `j` (line 13). -/
def levelStep (sel : (Fin k → Fin (m + 1)) → Fin k) (L : Fin k → Fin (m + 1)) (j : Fin (m + 1)) :
    Fin k → Fin (m + 1) :=
  Function.update L (sel L) (max (L (sel L)) j)

/-- Definition EC.1: the level vector `(ℓ_{1,t}, …, ℓ_{k,t})` after the valuations `W`
(all levels start at `0`, line 1). Deterministic: it depends only on the valuations. -/
def levels (sel : (Fin k → Fin (m + 1)) → Fin k) (W : List (Fin (m + 1))) : Fin k → Fin (m + 1) :=
  W.foldl (levelStep sel) (fun _ => 0)

/-- Definition EC.1: the inventory unit `i_t = sel (ℓ_{·,t-1})` assigned to customer `t`
(1-based), given the valuation sequence `V`. -/
def assigned (sel : (Fin k → Fin (m + 1)) → Fin k) (V : List (Fin (m + 1))) (t : ℕ) : Fin k :=
  sel (levels sel (V.take (t - 1)))

/-- Definition EC.1: `j_t`, the valuation index of customer `t` (1-based; meaningful for
`1 ≤ t ≤ V.length`). -/
def valIdx (V : List (Fin (m + 1))) (t : ℕ) : Fin (m + 1) := V.getD (t - 1) 0

/-- One step of Algorithm 1 acting on the law `μ` of the `sold` vector, when the levels before the
step are `L` and the customer has valuation index `j`. Let `i = sel L` and `ℓ = L i`.
If `sold[i] = true` or `ℓ = m` the price is `∞` and nothing changes (lines 9–10). Otherwise
(lines 7–8) price `r^{(p)}`, `ℓ < p ≤ m`, is drawn with probability `offerProb r m ℓ p`, and the
customer buys iff `r^{(p)} ≤ r^{(j)}` (`V_t ≥ P_t`), in which case `sold[i]` becomes `true`
(lines 14–15). -/
noncomputable def lawStep (r : ℕ → ℝ) (sel : (Fin k → Fin (m + 1)) → Fin k)
    (L : Fin k → Fin (m + 1)) (j : Fin (m + 1)) (μ : (Fin k → Bool) → ℝ) :
    (Fin k → Bool) → ℝ :=
  fun s' => ∑ s, μ s *
    (if s (sel L) = false ∧ ((L (sel L) : ℕ) < m) then
      ∑ p ∈ Finset.Ioc (L (sel L) : ℕ) m, offerProb r m (L (sel L)) p *
        (if r p ≤ r j then (if s' = Function.update s (sel L) true then 1 else 0)
         else (if s' = s then 1 else 0))
    else (if s' = s then 1 else 0))

/-- Auxiliary: the law of the `sold` vector, by recursion on the reversed valuation list. -/
noncomputable def soldLawRev (r : ℕ → ℝ) (sel : (Fin k → Fin (m + 1)) → Fin k) :
    List (Fin (m + 1)) → (Fin k → Bool) → ℝ
  | [] => fun s => if s = (fun _ => false) then 1 else 0
  | j :: R => lawStep r sel (levels sel R.reverse) j (soldLawRev r sel R)

/-- The law of the `sold` vector `(S_{1,t}, …, S_{k,t})` of Algorithm 1 after the valuations `W`
(a probability mass function on `Fin k → Bool`): the point mass at "nothing sold" for `W = []`,
pushed forward by `lawStep` for each valuation in turn. -/
noncomputable def soldLaw (r : ℕ → ℝ) (sel : (Fin k → Fin (m + 1)) → Fin k)
    (W : List (Fin (m + 1))) : (Fin k → Bool) → ℝ :=
  soldLawRev r sel W.reverse

/-- `Pr[S_{i,t} = 1]` = `E[S_{i,t}]` after the valuations `W`. -/
noncomputable def probSold (r : ℕ → ℝ) (sel : (Fin k → Fin (m + 1)) → Fin k)
    (W : List (Fin (m + 1))) (i : Fin k) : ℝ :=
  ∑ s, soldLaw r sel W s * (if s i = true then 1 else 0)

/-- Expected revenue `E[P_t X_t]` of the step whose past valuations are `W` and whose customer
has valuation index `j`: with `L = levels sel W`, `i = sel L`, `ℓ = L i`, an offer is made only
on the event `sold[i] = false` and only if `ℓ < m`; price `r^{(p)}` is offered with probability
`offerProb r m ℓ p` and earns `r^{(p)}` iff `r^{(p)} ≤ r^{(j)}`. Price `∞` earns `0`. -/
noncomputable def stepRev (r : ℕ → ℝ) (sel : (Fin k → Fin (m + 1)) → Fin k)
    (W : List (Fin (m + 1))) (j : Fin (m + 1)) : ℝ :=
  ∑ s, soldLaw r sel W s *
    (if s (sel (levels sel W)) = false ∧ ((levels sel W (sel (levels sel W)) : ℕ) < m) then
      ∑ p ∈ Finset.Ioc (levels sel W (sel (levels sel W)) : ℕ) m,
        offerProb r m (levels sel W (sel (levels sel W))) p * (if r p ≤ r j then r p else 0)
    else 0)

/-- `E[P_t X_t]` for customer `t` (1-based) of the valuation sequence `V`: it depends only on
`V_1, …, V_{t-1}` (through `V.take (t - 1)`) and on `V_t`. -/
noncomputable def stepRevenue (r : ℕ → ℝ) (sel : (Fin k → Fin (m + 1)) → Fin k)
    (V : List (Fin (m + 1))) (t : ℕ) : ℝ :=
  stepRev r sel (V.take (t - 1)) (valIdx V t)

/-- `E[ALG(V_1, …, V_T)] = ∑_{t=1}^T E[P_t X_t]` with `T = V.length`. -/
noncomputable def expRevenue (r : ℕ → ℝ) (sel : (Fin k → Fin (m + 1)) → Fin k)
    (V : List (Fin (m + 1))) : ℝ :=
  ∑ t ∈ Finset.Icc 1 V.length, stepRevenue r sel V t

/-- `OPT(V_1, …, V_T)`: the offline optimum, the largest total valuation of a set of at most `k`
customers (each charged her valuation). -/
noncomputable def opt (r : ℕ → ℝ) (k : ℕ) (V : List (Fin (m + 1))) : ℝ :=
  (Finset.univ.filter (fun S : Finset (Fin V.length) => S.card ≤ k)).sup'
    ⟨∅, by simp⟩ (fun S => ∑ t ∈ S, r (V.get t))

/-- Definition EC.2: `M^k(t)`, the `k` largest valuations `r^{(j)}` of `W = (V_1, …, V_t)`,
filled with zeros if `t < k` (as a list, largest first). -/
noncomputable def topK (r : ℕ → ℝ) (k : ℕ) (W : List (Fin (m + 1))) : List ℝ :=
  ((W.map (fun j => r j)).mergeSort (fun a b => decide (b ≤ a)) ++ List.replicate k 0).take k

end ValTrackRM.Public


