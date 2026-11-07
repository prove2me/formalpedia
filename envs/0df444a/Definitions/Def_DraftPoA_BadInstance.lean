-- Prove2me | Definitions.Def_DraftPoA_BadInstance
-- name    : DraftPoA_BadInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:16.291212+00:00
-- url     : https://prove2.me/theorems/919a60fe-5ef3-4a78-8fe0-72ab417313fd
-- title:
--   The lower-bound instance: harmonic bidder $A$, sink bidders, threat $Q$, rent block, and its strategy profile
-- statement:
--   For $N\ge4$ sink items let $K=\lceil H_N\rceil$, $L=4N^2K^2$, $\delta_N=1/L$, $\alpha_j=\lfloor L/j\rfloor\delta_N$, $\sigma_j=\lfloor L/(jK)\rfloor\delta_N$, $\varphi_j=\alpha_j-\sigma_j$, $w=1/(2NK)$, $h=(1+1/K)w$, $r=\lceil(\ln K+3)/w\rceil$ and $m(N)=N+r$.
--
--   1. **Items.** Sink items $1,\dots,N$, a rent block $R$ of $r$ items, and $d\ge0$ dummy items nobody values.
--   2. **Bidders.** $A$ (additive: $\alpha_j$ for sink item $j$, $h$ per rent item), $Q$ (values nothing), and for each sink item $j$ two sink bidders $C_j,C'_j$ who value only $j$, at $\sigma_j$. Priority $A\succ Q\succ C_1\succ C'_1\succ C_2\succ\cdots$; cap $\bar M=1$.
--   3. **State.** $S$ unsold sink items, $R'$ unsold rent items, the marker $F=A$ if $A$ has won a round while a sink item was unsold ($F=\emptyset$ otherwise); a state is *damaged* if a rent item is held by a bidder other than $A$. The threat price is $q(S)=\varphi_{t_{\min}}$, $t_{\min}=\min S$.
--   4. **Profile.** Sink bidders bid $\sigma_j$ for $\{j\}$ while $j$ is unsold, $0$ afterwards. $Q$ bids $0$ if $F=\emptyset$; $q(S)$ for $\{t_{\min}\}$ if $F=A$, $S\ne\emptyset$; $w$ for $R'$ if $F=A$, $S=\emptyset$. $A$ copies $Q$ if $F=A$; bids $0$ for $R'$ (and the remaining dummy items) if $F=\emptyset$, $S=\emptyset$; bids $0$ if $F=\emptyset$, $S\ne\emptyset$, except at damaged states, where her action is left free. Once only dummy items remain, everyone bids $0$ and $A$ names them all. A bid of $0$ without a named set is for the first remaining item.
--
--   A **completion** is a profile of legal strategies agreeing with these actions at every legal node at which an item remains, except $A$'s action at damaged states with $F=\emptyset$, $S\ne\emptyset$. The admissible grids are $\delta'=0$ and $\delta'=\delta_N/k$, $k\ge1$ an integer; the values stay rounded to $\delta_N$.
--
--   This is the instance whose subgame-perfect equilibrium attains $\mathrm{OPT}/\mathrm{SW}\ge H_N/(\ln(H_N+1)+6)$.
--
--   **Formalization Note** Items are indexed $0,\dots,m(N)+d-1$ (sink item $j$ is index $j-1$, then the rent block, then the dummy items); bidders are indexed $0,\dots,2N+1$ with $A=0$, $Q=1$, $C_j=2j$, $C'_j=2j+1$, and priority is index order.
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), §4.1–4.2, pp.9–10 (PDF 10–11); App. B "Facts about the instance" and "From N to m", pp.20–21 (PDF 21–22)

import Mathlib
import Definitions.Def_DraftPoA_Auction

namespace DraftPoA

/-!
# The bad instance of the lower bound and its strategy profile

H. T. Truong, N. Thach, H. Chan, M. Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027
submission (manuscript sha256 270ffdaa…), §4.1 "The instance" and §4.2 "The strategies",
pp.9–10 (PDF 10–11); App. B "Facts about the instance" and "From N to m", pp.20–21 (PDF 21–22).

Parameters, for `N ≥ 4` sink items: `K = ⌈H_N⌉`, `L = 4N²K²`, the value-rounding increment
`δ_N = 1/L`, the rounded values `α_j = ⌊L/j⌋ δ_N`, `σ_j = ⌊L/(jK)⌋ δ_N`, `φ_j = α_j − σ_j`, the threat
`w = 1/(2NK)`, A's rent value `h = (1 + 1/K) w`, the rent block size `r = ⌈(ln K + 3)/w⌉` and
`m(N) = N + r`.

**Formalization Note.**
* Items are `Fin (m(N) + d)`: indices `0, …, N − 1` are the sink items `1, …, N` (sink item `j` is
  index `j − 1`), indices `N, …, m(N) − 1` the rent block `R`, and indices `m(N), …` the `d`
  dummy items nobody values (App. B, "From N to m"; `d = 0` is the instance of §4.1).
* Bidders are `Fin (2N + 2)`: `A = 0`, `Q = 1`, and `C_j = 2j`, `C′_j = 2j + 1` for `j = 1, …, N`.
  The priority order is the index order (`Equiv.refl`), i.e. `A ≻ Q ≻ C_1 ≻ C′_1 ≻ C_2 ≻ ⋯`.
  All valuations are additive; `M̄ = 1`.
* The state is read from the node: `S` (unsold sink items), `R′` (unsold rent items), the marker
  `F = A` iff `A` won some round while a sink item was unsold (the set `S` is read before that
  round), and *damaged* iff some rent item is held by a bidder other than `A`.
* "A bid of 0 without a named set" names the first remaining item in index order.
* With dummy items (App. B, p.21): when `A` bids `0` for `R′` she also names all remaining dummy
  items, and once only dummy items remain every bidder bids `0`, `A` naming all of them.
* `badAct` is the explicit profile of §4.2 at every node. At damaged nodes with `F = ∅` and `S ≠ ∅`
  the paper lets `A` best-respond; `IsCompletion` therefore leaves `A`'s action free exactly there
  and fixes every other action at every legal node at which an item remains.
* `IsAdmissibleGrid N δ′`: the game's grid is `δ′ = 0` or `δ′ = δ_N/k` for an integer `k ≥ 1`.
  The values stay rounded to `δ_N` whatever the grid.
-/

/-- `K = ⌈H_N⌉`. -/
noncomputable def Kof (N : ℕ) : ℕ := ⌈(harmonic N : ℝ)⌉₊

/-- `L = 4N²K²`. -/
noncomputable def Lof (N : ℕ) : ℕ := 4 * N ^ 2 * Kof N ^ 2

/-- The bid increment of Theorem 4.1, `δ_N = 1/(4N²⌈H_N⌉²) = 1/L`. -/
noncomputable def deltaOf (N : ℕ) : ℝ := 1 / (Lof N : ℝ)

/-- `α_j = ⌊L/j⌋ δ_N`: `1/j` rounded down to a multiple of `δ_N` (A's value for sink item `j`). -/
noncomputable def alpha (N j : ℕ) : ℝ := ((Lof N / j : ℕ) : ℝ) / (Lof N : ℝ)

/-- `σ_j = ⌊L/(jK)⌋ δ_N`: `1/(jK)` rounded down (the sink bidders' value for sink item `j`). -/
noncomputable def sigma (N j : ℕ) : ℝ := ((Lof N / (j * Kof N) : ℕ) : ℝ) / (Lof N : ℝ)

/-- `φ_j = α_j − σ_j`: the threat price at sink item `j`. -/
noncomputable def phi (N j : ℕ) : ℝ := alpha N j - sigma N j

/-- `w = 1/(2NK)`: Q's threat per rent item. -/
noncomputable def wOf (N : ℕ) : ℝ := 1 / (2 * (N : ℝ) * (Kof N : ℝ))

/-- `h = (1 + 1/K) w`: A's value for a rent item. -/
noncomputable def hOf (N : ℕ) : ℝ := (1 + 1 / (Kof N : ℝ)) * wOf N

/-- `r = ⌈(ln K + 3)/w⌉`: the number of rent items. -/
noncomputable def rOf (N : ℕ) : ℕ := ⌈(Real.log (Kof N) + 3) / wOf N⌉₊

/-- `m(N) = N + r`: the number of items of the instance with `N` sink items. -/
noncomputable def mOf (N : ℕ) : ℕ := N + rOf N

/-- The number of bidders, `2N + 2`. -/
def nBid (N : ℕ) : ℕ := 2 * N + 2

instance (N : ℕ) : NeZero (nBid N) := ⟨by simp [nBid]⟩

/-- Bidder `A`. -/
def bidA (N : ℕ) : Fin (nBid N) := ⟨0, by simp [nBid]⟩

/-- Bidder `Q`. -/
def bidQ (N : ℕ) : Fin (nBid N) := ⟨1, by simp [nBid]⟩

/-- The priority order `A ≻ Q ≻ C_1 ≻ C′_1 ≻ ⋯`: the index order. -/
def prioBad (N : ℕ) : Equiv.Perm (Fin (nBid N)) := Equiv.refl _

/-- Item values: `A` values sink item `j` at `α_j` and each rent item at `h`; `C_j` and `C′_j`
value sink item `j` at `σ_j`; `Q` and the dummy items carry value `0`. -/
noncomputable def itemValue (N d : ℕ) (i : Fin (nBid N)) (x : Fin (mOf N + d)) : ℝ :=
  if i.val = 0 then
    (if x.val < N then alpha N (x.val + 1) else if x.val < mOf N then hOf N else 0)
  else if 2 ≤ i.val ∧ x.val < N ∧ x.val + 1 = i.val / 2 then sigma N (i.val / 2) else 0

/-- The additive valuations of the instance. -/
noncomputable def vBad (N d : ℕ) (i : Fin (nBid N)) (S : Finset (Fin (mOf N + d))) : ℝ :=
  ∑ x ∈ S, itemValue N d i x

/-- The unsold sink items `S` at a node. -/
noncomputable def sinkLeft {N d : ℕ} (ν : Node (nBid N) (mOf N + d)) : Finset (Fin (mOf N + d)) :=
  (remaining ν).filter fun x => x.val < N

/-- The unsold rent items `R′` at a node. -/
noncomputable def rentLeft {N d : ℕ} (ν : Node (nBid N) (mOf N + d)) :
    Finset (Fin (mOf N + d)) :=
  (remaining ν).filter fun x => N ≤ x.val ∧ x.val < mOf N

/-- The marker `F = A`: `A` won some round while a sink item was unsold. -/
def markerA {N d : ℕ} (ν : Node (nBid N) (mOf N + d)) : Prop :=
  ∃ k, ∃ hk : k < ν.length, (ν[k]).1 = bidA N ∧ (sinkLeft (ν.take k)).Nonempty

/-- A damaged state: some rent item is held by a bidder other than `A`. -/
def damaged {N d : ℕ} (ν : Node (nBid N) (mOf N + d)) : Prop :=
  ∃ i, i ≠ bidA N ∧ ∃ x ∈ holdings ν i, N ≤ x.val ∧ x.val < mOf N

open Classical in
/-- The explicit strategy profile of §4.2 (with the dummy-item rule of App. B), as an action at
every node. -/
noncomputable def badAct (N d : ℕ) (i : Fin (nBid N)) (ν : Node (nBid N) (mOf N + d)) :
    ℝ × Finset (Fin (mOf N + d)) :=
  let rem := remaining ν
  let first : Finset (Fin (mOf N + d)) := if h : rem.Nonempty then {rem.min' h} else ∅
  let S := sinkLeft ν
  let R' := rentLeft ν
  if i.val = 0 then
    if markerA ν then
      if hS : S.Nonempty then (phi N ((S.min' hS).val + 1), {S.min' hS})
      else if R'.Nonempty then (wOf N, R') else (0, rem)
    else if S.Nonempty then (0, first) else (0, rem)
  else if i.val = 1 then
    if markerA ν then
      if hS : S.Nonempty then (phi N ((S.min' hS).val + 1), {S.min' hS})
      else if R'.Nonempty then (wOf N, R') else (0, first)
    else (0, first)
  else
    let J := S.filter fun x => x.val + 1 = i.val / 2
    if J.Nonempty then (sigma N (i.val / 2), J) else (0, first)

/-- The grids on which the lower bound is verified: `δ′ = 0` or `δ′ = δ_N/k`, `k ≥ 1` an integer. -/
def IsAdmissibleGrid (N : ℕ) (δ' : ℝ) : Prop :=
  δ' = 0 ∨ ∃ k : ℕ, 1 ≤ k ∧ δ' = deltaOf N / k

/-- A completion of the profile on the grid `(δ′, M̄ = 1)`: every bidder plays `badAct` at every
legal node at which an item remains, except `A` at damaged nodes with `F = ∅` and `S ≠ ∅`, where
her (legal) action is free (§4.2). -/
def IsCompletion (N d : ℕ) {δ' : ℝ}
    (b : Fin (nBid N) → Strategy (nBid N) (mOf N + d) δ' 1) : Prop :=
  ∀ ν : Node (nBid N) (mOf N + d), IsNode δ' 1 ν → (remaining ν).Nonempty →
    ∀ i, ¬ (i = bidA N ∧ damaged ν ∧ ¬ markerA ν ∧ (sinkLeft ν).Nonempty) →
      (b i).act ν = badAct N d i ν

end DraftPoA


