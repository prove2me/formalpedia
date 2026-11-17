-- Prove2me | Definitions.Def_RoundOptVSS_Supplement_WSSProtocol
-- name    : RoundOptVSS_Supplement_WSSProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:11:58.566289+00:00
-- url     : https://prove2.me/theorems/5cebbb99-f451-4f39-bd81-b46f74dc13c4
-- title:
--   The key-uniform WSS of §7.2 (Protocols 4–7 with the packed IC of §5.1) in the execution model, its layout and the error $\varepsilon_{\mathrm{WSS}}$
-- statement:
--   This definition writes the protocol of §7.2 rule by rule as a protocol of the base mission's execution model, for finite fields $\mathbb F\subseteq\mathbb E$ and public constants at each parameter set: packing nodes $\beta_1,\dots,\beta_h\in\mathbb F$, the point $\alpha_0$ and party points $a_1,\dots,a_n\in\mathbb F$. Its **standing assumptions** are those of §5.1 and §7.2: $h\ge1$, distinct packing nodes with $\beta_1=0$ when $h=1$, $\alpha_0\in\mathcal A=\mathbb F\setminus\{0,\beta_1,\dots,\beta_h\}$, and distinct nonzero points $a_i$ for the row holders $i\ne D$.
--
--   1. *Sharing round 1 (Protocol 4).* The dealer samples a uniform symmetric $B(X,Y)$ with $\deg_X B,\deg_Y B\le t$ and $B(0,0)=s$; each row holder $P_i$ samples pads $r_{ij}\leftarrow\mathbb E^h$. For each label of the table ($W_{i,\ell}$, $S_{ij}$, $Q_{ij}$, $R_{ij}$, $i\ne j$ row holders) the sender runs Distribute of the packed IC on the label's message ($\gamma_{i,\ell}$, $B(a_i,a_j)$, $r_{ij}$, $r_{ij}$): uniform $F,G$ of degree $\le\delta=h+t-1$ with $\mathrm{val}(F)=x$, the pair to the holder and a key $(\alpha_w,F(\alpha_w),G(\alpha_w))$, $\alpha_w\leftarrow\mathcal A$, to every party. Row holders compute $g_i$, $\mathrm{inv}_i$, incoming pads and flags $\phi_{ij}$.
--   2. *Sharing round 2 (Protocol 5).* Holders broadcast checkpoints $(d,dF+G)$, $d\leftarrow\mathbb F^\times$ (an invalid one after an invalid pair); row holders broadcast $\mathrm{inv}_i$, $\phi_{ij}$, $a_{ij}$, $b_{ij}$; the dealer broadcasts $a^D_{ij}$, $b^D_{ij}$. Senders compute their finishes and the dealer its repair plan $U_{\mathrm{plan}}$.
--   3. *Sharing round 3 (Protocol 6).* Senders broadcast finishes; the dealer broadcasts $U$ and the rows $u_i=B(a_i,\cdot)$, $i\in U$, and opens $Q_{ij}$ for $i\notin U_{\mathrm{plan}}\ni j$; row holders open $S_{ij}$ when $p_{ij}\vee\hat c_{R_{ij}}\vee\bigvee_k\hat c_{Q_{ik}}$.
--   4. *Reconstruction (Protocol 7).* Every party broadcasts its verification vector $\kappa_w\in\mathbb E^{m_{\mathrm{WS}}}$, $m_{\mathrm{WS}}=6(n-1)(n-2)$ (its stored normalized keys of the $S$ and $Q$ labels in a fixed public order, three entries per key), and its opening: a row holder's LATE candidates ($W_{i,\ell}$, and $R_{ji}$ with $c_{R_{ji}}=0$, $\phi_{ij}=0$), the dealer's fallback. Each party outputs $\mathrm{Out}(\sigma_h,K;\tau)=\mathrm{Dec}_{O,h}(\sigma_h,K;\tau)$, the base mission's decoder.
--
--   The scheme is packaged as a broadcast-then-decode scheme with key length $m_{\mathrm{WS}}$, together with its layout for the cost model, and with the error of (7)
--   $$\varepsilon_{\mathrm{WSS}}=Mn\Big(\frac1{q-1}+\frac{\delta}{|\mathcal A|}\Big),\qquad M=(n-1)(t+1)+3(n-1)(n-2),\ q=|\mathbb F|,\ \delta=h+t-1 .$$
--
--   This is the protocol about which Theorem 7.1 is stated.
--
--   **Formalization Note** A party's state is its view: its input, its coins of each round (a coin drawn uniformly from $\mathbb E$, $\mathbb F^\times$ or $\mathcal A$ is stored as the element drawn) and its inboxes, by sender; every message is computed from the view. Messages are lists of tagged items; a receiver takes the first item with the tag it needs, and a missing or malformed value reads as $\perp$, a missing flag as $1$ (p.20). $F$ is sampled as $F=c+\mathrm{Interp}_\beta(x-\mathrm{val}(c))$ with $c$ uniform of degree $\le\delta$, which is uniform among the polynomials of degree $\le\delta$ with $\mathrm{val}(F)=x$. Every party draws the same fixed pattern of coins in each round, and ignores the ones its role does not use. The public message cap is $1000(n+h+2)^4$, above every honest message.
-- source:
--   Liu-Zhang, Masserova, Round-Optimal Statistical Verifiable Secret Sharing with Polynomial Complexity, manuscript (2026; STOC 2027 submission, sha256 3a45d95d…), §5.1 and Protocol 3 (p.17), label table and M (p.20), notation, verification vectors and (4) (pp.20–21), Protocols 4–6 with (5), (6) (pp.21–22), Protocol 7 (p.23), (7) (p.24)

import Mathlib
import Definitions.Def_RoundOptVSS_Model
import Definitions.Def_RoundOptVSS_PackedIC
import Definitions.Def_RoundOptVSS_WSSDecoder
import Definitions.Def_RoundOptVSS_Supplement_Cost
import Definitions.Def_RoundOptVSS_Supplement_KeyUniform

open scoped Polynomial ENNReal
open Polynomial Classical

namespace RoundOptVSS

namespace Supplement

/-!
# The key-uniform WSS of §7.2 (Protocols 4–7 with the packed IC of §5.1) in the execution model

Liu-Zhang, Masserova, *Round-Optimal Statistical Verifiable Secret Sharing with Polynomial
Complexity*, manuscript (STOC 2027 submission, sha256 3a45d95d…): §5.1 and Protocol 3 (p.17), the
label table and `M` (p.20), the notation and verification-vector paragraphs and (4) (pp.20–21),
Protocols 4–6 and (5), (6) (pp.21–22), Protocol 7 (p.23), Theorem 7.1's error (7) (p.24).

**Formalization Note.**
* Model rounds `0, 1, 2` are the paper's sharing rounds 1, 2, 3 and round `3` is reconstruction.
  The public constants of a parameter set are a `WSSCfg`: packing nodes `β`, the point `α₀` and the
  party points `a_i ∈ 𝔽`; the standing assumptions (`h ≥ 1`, distinct nodes, `β₁ = 0` if `h = 1`,
  `α₀ ∈ A`, distinct nonzero `a_i` for the row holders `i ≠ D`) are `CfgAdm`.
* A party's state is its view (`WView`): its input, its coins of each round (decoded: a coin drawn
  uniformly from `𝔼`, from `𝔽^×` or from `A` is stored as that element) and its inboxes of each
  round, indexed by sender. Every message and every decision of a round is computed from the view by
  the rules of Protocols 4–7 (the state update only records). Messages are lists of tagged items; a
  receiver takes the first item with the tag it needs; a missing or malformed value reads as ⊥
  (`none`) and a missing flag as `1`, as on p.20.
* Sampling. The dealer's symmetric `B` with `B(0,0) = s` takes its coefficients `b_{kl} = b_{lk}`
  (`(k,l) ≠ (0,0)`) as independent uniform elements of `𝔼^h`; the pads `r_ij` are uniform in
  `𝔼^h`; for the packed IC the sender draws `c ∈ 𝔼^{δ+1}` and `G` uniformly and sets
  `F = c + Interp_β(x − val(c))` (a uniform polynomial of degree `≤ δ` with `val(F) = x`), the
  holder's challenge `d` is uniform in `𝔽^×` and each verifier's point `α_w` is uniform in `A`.
  Every party draws the same fixed pattern of coins (unused ones are ignored).
* Labels are the published `Label n t`; the table labels are `W_{i,ℓ}` (`i ≠ D`) and `S_ij, Q_ij,
  R_ij` (`i ≠ j`, both `≠ D`). An honest holder whose Distribute pair is invalid broadcasts the
  invalid checkpoint `(0, 0)` and, when asked to reveal, an invalid candidate.
* The verification vector `κ_w ∈ 𝔼^{mWS}`, `mWS = 6(n − 1)(n − 2)`, lists `P_w`'s stored normalized
  keys of the EARLY labels `S_ij` then `Q_ij`, ordered by `(i, j)` over the row holders (rank of `i`
  in `I`, then rank of `j` in `I \ {i}`), three entries per key. The opening `ω_w` is the rest of
  `P_w`'s reconstruction broadcast (its LATE candidates and, for the dealer, the fallback).
* `Out(σ_h, K; τ)` is the published decoder `Dec` of Protocol 7 on the public sharing data read
  from `σ_h`, `P_h`'s stored keys, the openings `τ` and the assignment `K` (a vector of the wrong
  length, a missing one, or `bad`, reads as `bad`).
-/

/-- The public constants of §5.1 and §7.2 at a parameter set: packing nodes `β₁, …, β_h`, the point
`α₀` used by `Norm`, and the party points `a_1, …, a_n ∈ 𝔽`. -/
structure WSSCfg (𝔽 : Type) (P : Params) where
  β : Fin P.h → 𝔽
  α0 : 𝔽
  pt : Fin P.n → 𝔽

variable {𝔽 𝔼 : Type} [Field 𝔽] [Fintype 𝔽] [Field 𝔼] [Fintype 𝔼] [Algebra 𝔽 𝔼]

/-- The packed-IC parameters of a configuration. -/
abbrev WSSCfg.ic {P : Params} (c : WSSCfg 𝔽 P) : ICParams 𝔽 := ⟨P.h, P.t, c.β, c.α0⟩

/-- The decoder parameters of a configuration. -/
abbrev WSSCfg.wss {P : Params} (c : WSSCfg 𝔽 P) : WSSParams 𝔽 :=
  { toICParams := c.ic, n := P.n, D := P.dealer, pt := c.pt }

/-- The standing assumptions of §5.1 and §7.2 at `P`. -/
def CfgAdm (cfg : (P : Params) → WSSCfg 𝔽 P) (P : Params) : Prop :=
  (cfg P).ic.Standing ∧ (∀ i, i ≠ P.dealer → (cfg P).pt i ≠ 0) ∧
    ∀ i j, i ≠ P.dealer → j ≠ P.dealer → (cfg P).pt i = (cfg P).pt j → i = j

/-- The number of labels `M = (n − 1)(t + 1) + 3(n − 1)(n − 2)` (p.20). -/
def Mlabels (n t : ℕ) : ℕ := (n - 1) * (t + 1) + 3 * (n - 1) * (n - 2)

/-- The key length `mWS = 6(n − 1)(n − 2)` (p.21). -/
def mWS (n : ℕ) : ℕ := 6 * (n - 1) * (n - 2)

/-- The error (7): `εWSS = M n (1/(q − 1) + δ/|A|)`, `q = |𝔽|`, `δ = h + t − 1`. -/
noncomputable def epsWSS (cfg : (P : Params) → WSSCfg 𝔽 P) (P : Params) : ℝ≥0∞ :=
  (Mlabels P.n P.t : ℝ≥0∞) * (P.n : ℝ≥0∞) *
    (((Fintype.card 𝔽 : ℝ≥0∞) - 1)⁻¹ + ((cfg P).ic.δ : ℝ≥0∞) / ((cfg P).ic.A.card : ℝ≥0∞))

/-! ## Messages, coins and views -/

/-- A label code `(kind, i, j)`: kind `0` = `W` (`j = ℓ`), `1` = `S`, `2` = `Q`, `3` = `R`. -/
abbrev LCode := ℕ × ℕ × ℕ

/-- The code of a label. -/
def labelCode {n t : ℕ} : Label n t → LCode
  | .W i l => (0, i, l)
  | .S i j => (1, i, j)
  | .Q i j => (2, i, j)
  | .R i j => (3, i, j)

/-- A message item. `pair L F G`: Distribute pair (coefficient lists); `key L k`: Distribute key;
`cp L d T`: checkpoint; `inv b`, `phi j b`: flags; `a j v`, `b j v`: comparisons `a_ij`, `b_ij`;
`aD i j v`, `bD i j v`: the dealer's versions; `fin L r`: finish (`none` = ok, `some x` =
fail(x)); `U s`, `u i rows`: repair declaration and repaired rows; `cand L x P`, `badCand L`: a
candidate (valid or not); `vk k`: verification vector; `fallback x`: the dealer's fallback. -/
inductive Item (𝔽 𝔼 : Type) where
  | pair (L : LCode) (F G : List 𝔼)
  | key (L : LCode) (k : 𝔼 × 𝔼 × 𝔼)
  | cp (L : LCode) (d : 𝔽) (T : List 𝔼)
  | inv (b : Bool)
  | phi (j : ℕ) (b : Bool)
  | a (j : ℕ) (v : List 𝔼)
  | b (j : ℕ) (v : List 𝔼)
  | aD (i j : ℕ) (v : List 𝔼)
  | bD (i j : ℕ) (v : List 𝔼)
  | fin (L : LCode) (r : Option (List 𝔼))
  | U (s : List ℕ)
  | u (i : ℕ) (rows : List (List 𝔼))
  | cand (L : LCode) (x P : List 𝔼)
  | badCand (L : LCode)
  | vk (k : List 𝔼)
  | fallback (x : List 𝔼)

/-- A message: a list of items. -/
abbrev WMsg (𝔽 𝔼 : Type) := List (Item 𝔽 𝔼)

/-- A drawn coin: an element of `𝔼` or of `𝔽`. -/
inductive WCoin (𝔽 𝔼 : Type) where
  | e (x : 𝔼)
  | f (x : 𝔽)

/-- The domain of a coin: uniform in `𝔼`, in `A`, or in `𝔽^×`. -/
inductive CoinKind where
  | E
  | A
  | U

/-- A party's state: its view (input, decoded coins per round, inboxes per round by sender). -/
structure WView (𝔽 𝔼 : Type) where
  input : Option (List 𝔼)
  coins : List (List (WCoin 𝔽 𝔼))
  priv : List (List (Option (WMsg 𝔽 𝔼)))
  bc : List (List (Option (WMsg 𝔽 𝔼)))

/-- The coins of round `r`. -/
def WView.coinsAt (v : WView 𝔽 𝔼) (r : ℕ) : List (WCoin 𝔽 𝔼) := v.coins.getD r []

/-- The private message received from `j` in round `r`. -/
def WView.privFrom (v : WView 𝔽 𝔼) (r j : ℕ) : Option (WMsg 𝔽 𝔼) := (v.priv.getD r []).getD j none

/-- The broadcast received from `j` in round `r`. -/
def WView.bcFrom (v : WView 𝔽 𝔼) (r j : ℕ) : Option (WMsg 𝔽 𝔼) := (v.bc.getD r []).getD j none

/-- The `k`-th coin of a round as an element of `𝔼` (`0` if absent). -/
def ce (cs : List (WCoin 𝔽 𝔼)) (k : ℕ) : 𝔼 :=
  match cs.getD k (.e 0) with
  | .e x => x
  | .f x => algebraMap 𝔽 𝔼 x

/-- The `k`-th coin of a round as an element of `𝔽` (`0` if absent). -/
def cf (cs : List (WCoin 𝔽 𝔼)) (k : ℕ) : 𝔽 :=
  match cs.getD k (.f 0) with
  | .f x => x
  | .e _ => 0

/-- The modulus requested for a coin of a given domain. -/
noncomputable def modulusOf (I : ICParams 𝔽) : CoinKind → ℕ
  | .E => Fintype.card 𝔼
  | .A => I.A.card
  | .U => Fintype.card 𝔽ˣ

/-- The element drawn: the `v`-th element of the domain in a fixed enumeration. -/
noncomputable def decodeCoin (I : ICParams 𝔽) : CoinKind → ℕ → WCoin 𝔽 𝔼
  | .E, v => .e (if h : v < Fintype.card 𝔼 then (Fintype.equivFin 𝔼).symm ⟨v, h⟩ else 0)
  | .A, v => .f (if h : v < I.A.card then ((I.A.equivFin.symm ⟨v, h⟩ : I.A) : 𝔽) else I.α0)
  | .U, v => .f (if h : v < Fintype.card 𝔽ˣ then (((Fintype.equivFin 𝔽ˣ).symm ⟨v, h⟩ : 𝔽ˣ) : 𝔽)
      else 1)

/-- Every label (all index pairs), in a fixed order. -/
def allLabels (n t : ℕ) : List (Label n t) :=
  ((List.finRange n).flatMap fun i => (List.finRange (t + 1)).map fun l => Label.W i l) ++
    (List.finRange n).flatMap fun i => (List.finRange n).flatMap fun j =>
      [Label.S i j, Label.Q i j, Label.R i j]

/-- The position of a label in `allLabels`. -/
noncomputable def labelIdx {n t : ℕ} (L : Label n t) : ℕ := (allLabels n t).idxOf L

/-- The coin pattern of round `r`: round `0` draws the dealer's coefficients `(t+1)²h`, the pads
`n h`, and for every label `2(δ + 1)` elements of `𝔼` and `n` points of `A`; round `1` draws one
challenge in `𝔽^×` per label; rounds `2, 3` draw nothing. -/
def kindsAt (P : Params) (r : Fin 4) : List CoinKind :=
  if r.val = 0 then
    List.replicate ((P.t + 1) * (P.t + 1) * P.h) CoinKind.E ++ List.replicate (P.n * P.h) CoinKind.E ++
      (allLabels P.n P.t).flatMap fun _ =>
        List.replicate (2 * (P.h + P.t - 1 + 1)) CoinKind.E ++ List.replicate P.n CoinKind.A
  else if r.val = 1 then List.replicate (allLabels P.n P.t).length CoinKind.U
  else []

/-- The coins of round `r` as drawn. -/
noncomputable def decodeCoins (P : Params) (I : ICParams 𝔽) (r : Fin 4) (c : List ℕ) :
    List (WCoin 𝔽 𝔼) :=
  List.zipWith (decodeCoin I) (kindsAt P r) c

/-! ## Parsing -/

/-- A vector of length `k` from a list (`none` if the length is wrong). -/
def vecOfList (k : ℕ) (l : List 𝔼) : Option (Fin k → 𝔼) :=
  if l.length = k then some (fun r => l.getD r 0) else none

/-- The polynomial with coefficient list `l`. -/
noncomputable def polyOfList (l : List 𝔼) : 𝔼[X] :=
  ∑ k ∈ Finset.range l.length, C (l.getD k 0) * X ^ k

/-- The coefficients `0, …, δ` of a polynomial. -/
def coeffList (δ : ℕ) (F : 𝔼[X]) : List 𝔼 := List.ofFn fun k : Fin (δ + 1) => F.coeff k

/-- A repair set from a list of indices (`none` if some index is out of range). -/
def finsetOf (n : ℕ) (s : List ℕ) : Option (Finset (Fin n)) :=
  if ∀ k ∈ s, k < n then some (Finset.univ.filter fun i : Fin n => (i : ℕ) ∈ s) else none

/-- A row `Y ↦ (u^{(1)}(Y), …, u^{(h)}(Y))` from `h` coefficient lists. -/
noncomputable def rowsOf (h : ℕ) (rows : List (List 𝔼)) : Option (Fin h → 𝔼[X]) :=
  if rows.length = h then some (fun r => polyOfList (rows.getD r [])) else none

/-- The first item of a message selected by `f`. -/
def pick {β : Type} (f : Item 𝔽 𝔼 → Option β) (m : Option (WMsg 𝔽 𝔼)) : Option β :=
  m.bind fun l => l.findSome? f

/-! ## Labels of the table -/

section Labels

variable {n t : ℕ}

/-- A label of the table (p.20). -/
def IsTable (D : Fin n) : Label n t → Prop
  | .W i _ => i ≠ D
  | .S i j => i ≠ D ∧ j ≠ D ∧ i ≠ j
  | .Q i j => i ≠ D ∧ j ≠ D ∧ i ≠ j
  | .R i j => i ≠ D ∧ j ≠ D ∧ i ≠ j

/-- The sender of a label. -/
def lsender (D : Fin n) : Label n t → Fin n
  | .W _ _ => D
  | .S _ _ => D
  | .Q i _ => i
  | .R i _ => i

/-- The holder of a label. -/
def lholder (D : Fin n) : Label n t → Fin n
  | .W i _ => i
  | .S i _ => i
  | .Q _ _ => D
  | .R _ j => j

end Labels

/-! ## Derived data of a view -/

section Derived

variable (P : Params) (c : WSSCfg 𝔽 P)

/-- `δ = h + t − 1`. -/
abbrev dlt : ℕ := P.h + P.t - 1

/-- Offset of the pads in the round-`0` coins. -/
def offPad : ℕ := (P.t + 1) * (P.t + 1) * P.h

/-- Offset of the IC block of label `L` in the round-`0` coins. -/
noncomputable def offIC (L : Label P.n P.t) : ℕ :=
  offPad P + P.n * P.h + labelIdx L * (2 * (dlt P + 1) + P.n)

/-- The point `a_i` in `𝔼`. -/
def ptE (i : Fin P.n) : 𝔼 := algebraMap 𝔽 𝔼 (c.pt i)

variable (v : WView 𝔽 𝔼)

/-- The dealer's input `s ∈ 𝔼^h`. -/
def sVec : Fin P.h → 𝔼 := fun r => (v.input.getD []).getD r 0

/-- The dealer's coefficient `b_{kl} = b_{lk}` (`b_{00} = s`) of the bivariate polynomial `B`. -/
def bmat (k l : Fin (P.t + 1)) : Fin P.h → 𝔼 := fun r =>
  if k.val = 0 ∧ l.val = 0 then sVec P v r
  else ce (v.coinsAt 0) (((min k l : ℕ) * (P.t + 1) + (max k l : ℕ)) * P.h + r)

/-- `γ_{i,ℓ}`, the coefficient of `Y^ℓ` in `B(i, Y)`. -/
def gamma (i : Fin P.n) (l : Fin (P.t + 1)) : Fin P.h → 𝔼 := fun r =>
  ∑ k : Fin (P.t + 1), bmat P v k l r * ptE P c i ^ (k : ℕ)

/-- `B(i, j)`. -/
def bval (i j : Fin P.n) : Fin P.h → 𝔼 := fun r =>
  ∑ k : Fin (P.t + 1), ∑ l : Fin (P.t + 1), bmat P v k l r * ptE P c i ^ (k : ℕ) * ptE P c j ^ (l : ℕ)

/-- The party's own pad `r_ij` for neighbour `j`. -/
def pad (j : Fin P.n) : Fin P.h → 𝔼 := fun r => ce (v.coinsAt 0) (offPad P + (j : ℕ) * P.h + r)

/-- The message of label `L` as computed by its sender: `γ_{i,ℓ}`, `B(i, j)`, `r_ij`, `r_ij`. -/
def icMsg : Label P.n P.t → Fin P.h → 𝔼
  | .W i l => gamma P c v i l
  | .S i j => bval P c v i j
  | .Q _ j => pad P v j
  | .R _ j => pad P v j

/-- Lagrange interpolation on the packing nodes. -/
noncomputable def interp (I : ICParams 𝔽) (y : Fin I.h → 𝔼) : 𝔼[X] :=
  ∑ r : Fin I.h, C (y r) * ∏ s ∈ Finset.univ.erase r,
    (C (algebraMap 𝔽 𝔼 (I.β r - I.β s))⁻¹ * (X - C (algebraMap 𝔽 𝔼 (I.β s))))

/-- The sender's IC polynomial `F` of label `L` (uniform of degree `≤ δ` with `val(F) = x_L`). -/
noncomputable def icF (L : Label P.n P.t) : 𝔼[X] :=
  let cF : Fin (dlt P + 1) → 𝔼 := fun k => ce (v.coinsAt 0) (offIC P L + k)
  polyOf cF + interp c.ic (icMsg P c v L - val c.ic (polyOf cF))

/-- The sender's IC polynomial `G` of label `L`. -/
noncomputable def icG (L : Label P.n P.t) : 𝔼[X] :=
  polyOf fun k : Fin (dlt P + 1) => ce (v.coinsAt 0) (offIC P L + (dlt P + 1) + k)

/-- The sender's point `α_w` for verifier `w` in label `L`. -/
noncomputable def icAlpha (L : Label P.n P.t) (w : Fin P.n) : 𝔽 :=
  cf (v.coinsAt 0) (offIC P L + 2 * (dlt P + 1) + w)

/-- The holder's Distribute output for `L`: the received pair `(F, G)` if well formed of degree
`≤ δ`, else `none` (`x_v(L) = ⊥`). -/
noncomputable def heldPair (L : Label P.n P.t) : Option (𝔼[X] × 𝔼[X]) :=
  match pick (fun it => match it with
      | .pair cd F G => if cd = labelCode L then some (F, G) else none
      | _ => none) (v.privFrom 0 (lsender P.dealer L)) with
  | some (F, G) =>
      if (polyOfList F).natDegree ≤ dlt P ∧ (polyOfList G).natDegree ≤ dlt P then
        some (polyOfList F, polyOfList G) else none
  | none => none

/-- `x_v(L) = val(F)` for the holder (`none` = ⊥). -/
noncomputable def xv (L : Label P.n P.t) : Option (Fin P.h → 𝔼) :=
  (heldPair P v L).map fun p => val c.ic p.1

/-- The verifier's stored normalized key `K_{L,w}`. -/
noncomputable def storedKey (L : Label P.n P.t) : ICKey 𝔼 :=
  norm c.ic (pick (fun it => match it with
      | .key cd k => if cd = labelCode L then some k else none
      | _ => none) (v.privFrom 0 (lsender P.dealer L)))

/-- All `x_i(W_{i,ℓ})` are finite. -/
def allW (i : Fin P.n) : Prop := ∀ l, (xv P c v (.W i l)).isSome

/-- The received row `g_i(Y)` (zero if some `x_i(W_{i,ℓ})` is ⊥). -/
noncomputable def gRow (i : Fin P.n) : Fin P.h → 𝔼[X] :=
  if allW P c v i then rowOfCoeffs (fun l => (xv P c v (.W i l)).getD 0) else 0

/-- `inv_i`: some `x_i(W_{i,ℓ})` or `x_i(S_ij)` is ⊥, or some `x_i(S_ij) ≠ g_i(j)`. -/
noncomputable def invFlag (i : Fin P.n) : Bool :=
  decide (¬ allW P c v i ∨ ∃ j : Fin P.n, j ≠ P.dealer ∧ j ≠ i ∧
    (xv P c v (.S i j) = none ∨
      ∃ x, xv P c v (.S i j) = some x ∧ x ≠ rowEval (gRow P c v i) (c.pt j)))

/-- The incoming pad `r^{(i)}_{ji} = x_i(R_ji)`. -/
noncomputable def inPad (i j : Fin P.n) : Option (Fin P.h → 𝔼) := xv P c v (.R j i)

/-- `ϕ_ij = [r^{(i)}_{ji} = ⊥]`. -/
noncomputable def phiFlag (i j : Fin P.n) : Bool := (inPad P c v i j).isNone

/-- The public sharing data `Γ_O` as read from the view (broadcasts of rounds `1`, `2`). -/
noncomputable def transcript : WSSTranscript 𝔽 𝔼 P.n P.t P.h where
  inv i := (pick (fun it => match it with | .inv b => some b | _ => none) (v.bcFrom 1 i)).getD true
  phi i j := (pick (fun it => match it with
      | .phi j' b => if j' = (j : ℕ) then some b else none | _ => none) (v.bcFrom 1 i)).getD true
  a i j := (pick (fun it => match it with
      | .a j' x => if j' = (j : ℕ) then some x else none | _ => none) (v.bcFrom 1 i)).bind
        (vecOfList P.h)
  b i j := (pick (fun it => match it with
      | .b j' x => if j' = (j : ℕ) then some x else none | _ => none) (v.bcFrom 1 i)).bind
        (vecOfList P.h)
  aD i j := (pick (fun it => match it with
      | .aD i' j' x => if i' = (i : ℕ) ∧ j' = (j : ℕ) then some x else none | _ => none)
        (v.bcFrom 1 P.dealer)).bind (vecOfList P.h)
  bD i j := (pick (fun it => match it with
      | .bD i' j' x => if i' = (i : ℕ) ∧ j' = (j : ℕ) then some x else none | _ => none)
        (v.bcFrom 1 P.dealer)).bind (vecOfList P.h)
  cp L := (pick (fun it => match it with
      | .cp cd d T => if cd = labelCode L then some (d, polyOfList T) else none | _ => none)
        (v.bcFrom 1 (lholder P.dealer L)))
  rep L := ((pick (fun it => match it with
      | .fin cd r => if cd = labelCode L then some r else none | _ => none)
        (v.bcFrom 2 (lsender P.dealer L))).bind id).bind (vecOfList P.h)
  U := (pick (fun it => match it with | .U s => some s | _ => none) (v.bcFrom 2 P.dealer)).bind
    (finsetOf P.n)
  u i := (pick (fun it => match it with
      | .u i' rows => if i' = (i : ℕ) then some rows else none | _ => none)
        (v.bcFrom 2 P.dealer)).bind (rowsOf P.h)
  cand L := pick (fun it => match it with
      | .cand cd x Q => if cd = labelCode (L.toLabel : Label P.n P.t) then
          some ((vecOfList P.h x).map fun x' => (x', polyOfList Q)) else none
      | .badCand cd => if cd = labelCode (L.toLabel : Label P.n P.t) then some none else none
      | _ => none) (v.bcFrom 2 (lholder P.dealer (L.toLabel : Label P.n P.t)))

/-- The sender's finish flag `ĉ_L` (fail on a missing, invalid or inconsistent checkpoint). -/
noncomputable def chat (L : Label P.n P.t) : Prop :=
  match (transcript P v).cp L with
  | some cp =>
      (match senderFinish c.ic (icMsg P c v L) (icF P c v L) (icG P v L) cp with
       | .ok => False
       | .fail _ => True)
  | none => True

/-- The dealer's planned repair set `U_plan`. -/
noncomputable def Uplan : Finset (Fin P.n) :=
  Finset.univ.filter fun k => k ≠ P.dealer ∧
    (eta c.wss (transcript P v) k ∨ (∃ j, RowPair c.wss k j ∧ chat P c v (.S k j)) ∨
      ∃ l, chat P c v (.W k l))

/-- A candidate broadcast for a held label: `(x_v(L), ω_v(L))`, or an invalid one if `x_v(L) = ⊥`. -/
noncomputable def candItem (L : Label P.n P.t) : Item 𝔽 𝔼 :=
  match heldPair P v L with
  | some (F, _) => .cand (labelCode L) (List.ofFn (val c.ic F)) (coeffList (dlt P) F)
  | none => .badCand (labelCode L)

/-- The verification vector `κ_w`: the stored keys of the EARLY labels in the fixed public order. -/
noncomputable def vkVec : Fin (mWS P.n) → 𝔼 := fun idx =>
  let p := (idx : ℕ) / 3
  let co := (idx : ℕ) % 3
  let n := P.n
  let D := (P.dealer : ℕ)
  let kind := p / ((n - 1) * (n - 2))
  let rem := p % ((n - 1) * (n - 2))
  let a := rem / (n - 2)
  let b := rem % (n - 2)
  let i := if a < D then a else a + 1
  let lo := min D i
  let hi := max D i
  let j := if b < lo then b else if b + 1 < hi then b + 1 else b + 2
  if hi' : i < n ∧ j < n then
    let k := storedKey P c v (if kind = 0 then Label.S ⟨i, hi'.1⟩ ⟨j, hi'.2⟩
      else Label.Q ⟨i, hi'.1⟩ ⟨j, hi'.2⟩)
    if co = 0 then k.1 else if co = 1 then k.2.1 else k.2.2
  else 0

end Derived

/-- The position of an EARLY label `S_ij` (kind `0`) or `Q_ij` (kind `1`) in the public order. -/
def earlyPos (n D kind i j : ℕ) : ℕ :=
  let ri := if i < D then i else i - 1
  let rj := j - (if D < j then 1 else 0) - (if i < j then 1 else 0)
  (kind * (n - 1) + ri) * (n - 2) + rj

/-- The key slot of an EARLY label in a vector `k ∈ 𝔼^{mWS}`. -/
def slotOf {n : ℕ} (D : Fin n) (k : Fin (mWS n) → 𝔼) : EarlyLabel n → ICKey 𝔼
  | .S i j =>
      let p := earlyPos n D 0 i j
      if h : 3 * p + 2 < mWS n then (k ⟨3 * p, by omega⟩, k ⟨3 * p + 1, by omega⟩, k ⟨3 * p + 2, h⟩)
      else (0, 0, 0)
  | .Q i j =>
      let p := earlyPos n D 1 i j
      if h : 3 * p + 2 < mWS n then (k ⟨3 * p, by omega⟩, k ⟨3 * p + 1, by omega⟩, k ⟨3 * p + 2, h⟩)
      else (0, 0, 0)

section Rounds

variable (P : Params) (c : WSSCfg 𝔽 P) (v : WView 𝔽 𝔼)

/-- Protocol 4, step 2: the private message from party `i` to party `j` (Distribute pairs to the
holder and keys to every verifier, for every table label `i` sends). -/
noncomputable def r0Priv (i j : Fin P.n) : WMsg 𝔽 𝔼 :=
  (allLabels P.n P.t).flatMap fun L =>
    if IsTable P.dealer L ∧ lsender P.dealer L = i then
      (if lholder P.dealer L = j then
          [Item.pair (labelCode L) (coeffList (dlt P) (icF P c v L)) (coeffList (dlt P) (icG P v L))]
        else []) ++
        [Item.key (labelCode L) (senderKey (icAlpha P v L j) (icF P c v L) (icG P v L))]
    else []

/-- Protocol 5, steps 1–2: the broadcast of party `i` (checkpoints of the labels it holds; for a
row holder `inv_i`, `ϕ_ij`, `a_ij`, `b_ij`; for the dealer `a^D_ij`, `b^D_ij`). -/
noncomputable def r1Bc (i : Fin P.n) : WMsg 𝔽 𝔼 :=
  ((allLabels P.n P.t).flatMap fun L =>
    if IsTable P.dealer L ∧ lholder P.dealer L = i then
      (match heldPair P v L with
       | some (F, G) =>
          let d := cf (v.coinsAt 1) (labelIdx L)
          [Item.cp (labelCode L) d (coeffList (dlt P) (C (algebraMap 𝔽 𝔼 d) * F + G))]
       | none => [Item.cp (labelCode L) 0 []])
    else []) ++
  (if i ≠ P.dealer then
    Item.inv (invFlag P c v i) :: (List.finRange P.n).flatMap fun j =>
      if j ≠ P.dealer ∧ j ≠ i then
        [Item.phi j (phiFlag P c v i j),
          Item.a j (List.ofFn (rowEval (gRow P c v i) (c.pt j) + pad P v j))] ++
        (match inPad P c v i j with
         | some r => [Item.b j (List.ofFn (rowEval (gRow P c v i) (c.pt j) + r))]
         | none => [])
      else []
  else
    (List.finRange P.n).flatMap fun i' => (List.finRange P.n).flatMap fun j' =>
      if i' ≠ P.dealer ∧ j' ≠ P.dealer ∧ i' ≠ j' then
        (match xv P c v (.Q i' j') with
         | some r => [Item.aD i' j' (List.ofFn (bval P c v i' j' + r))]
         | none => []) ++
        (match xv P c v (.Q j' i') with
         | some r => [Item.bD i' j' (List.ofFn (bval P c v i' j' + r))]
         | none => [])
      else [])

/-- Protocol 6: the broadcast of party `i` (finishes of the labels it sends; for the dealer `U` and
the rows `u_k = B(k, ·)`, `k ∈ U`, and the reveals of `Q_ij` with `i ∉ U_plan`, `j ∈ U_plan`; for a
row holder the reveals of `S_ij` with `p_ij ∨ ĉ_{R_ij} ∨ ⋁_k ĉ_{Q_ik}`). -/
noncomputable def r2Bc (i : Fin P.n) : WMsg 𝔽 𝔼 :=
  ((allLabels P.n P.t).flatMap fun L =>
    if IsTable P.dealer L ∧ lsender P.dealer L = i then
      [Item.fin (labelCode L) (if chat P c v L then some (List.ofFn (icMsg P c v L)) else none)]
    else []) ++
  (if i = P.dealer then
    Item.U (((List.finRange P.n).filter fun k => k ∈ Uplan P c v).map fun k => (k : ℕ)) ::
      ((List.finRange P.n).flatMap fun k =>
        if k ∈ Uplan P c v then
          [Item.u k (List.ofFn fun r : Fin P.h =>
            coeffList P.t ((rowOfCoeffs (fun l => gamma P c v k l) : Fin P.h → 𝔼[X]) r))]
        else []) ++
      ((List.finRange P.n).flatMap fun i' => (List.finRange P.n).flatMap fun j' =>
        if i' ≠ P.dealer ∧ j' ≠ P.dealer ∧ i' ≠ j' ∧ i' ∉ Uplan P c v ∧ j' ∈ Uplan P c v then
          [candItem P c v (.Q i' j')] else [])
  else
    (List.finRange P.n).flatMap fun j =>
      if j ≠ P.dealer ∧ j ≠ i ∧
          (disp c.wss (transcript P v) i j ∨ chat P c v (.R i j) ∨
            ∃ k, k ≠ P.dealer ∧ k ≠ i ∧ chat P c v (.Q i k)) then
        [candItem P c v (.S i j)] else [])

/-- The opening `ω_w` of Protocol 7: the LATE candidates (`W_{w,ℓ}` and `R_jw` with `c_{R_jw} = 0`
and `ϕ_wj = 0`) of a row holder, and the dealer's fallback. -/
noncomputable def openingOf (w : Fin P.n) : WMsg 𝔽 𝔼 :=
  if w ≠ P.dealer then
    ((List.finRange (P.t + 1)).map fun l => candItem P c v (.W w l)) ++
      (List.finRange P.n).flatMap fun j =>
        if j ≠ P.dealer ∧ j ≠ w ∧ (transcript P v).rep (.R j w) = none ∧
            phiFlag P c v w j = false then
          [candItem P c v (.R j w)] else []
  else [Item.fallback (List.ofFn (sVec P v))]

/-- The messages of party `i` in round `r` from its view (the current round's coins included). -/
noncomputable def sendFrom (i : Fin P.n) (r : Fin 4) : (Fin P.n → WMsg 𝔽 𝔼) × WMsg 𝔽 𝔼 :=
  if r.val = 0 then (fun j => r0Priv P c v i j, [])
  else if r.val = 1 then (fun _ => [], r1Bc P c v i)
  else if r.val = 2 then (fun _ => [], r2Bc P c v i)
  else (fun _ => [], Item.vk (List.ofFn (vkVec P c v)) :: openingOf P c v i)

/-- The opening vector `τ` read as the decoder's LATE candidates and fallback. -/
noncomputable def toOpening (τ : Fin P.n → Option (WMsg 𝔽 𝔼)) : WSSOpening 𝔼 P.n P.t P.h where
  late L := pick (fun it => match it with
    | .cand cd x Q => if cd = labelCode L then
        (vecOfList P.h x).map fun x' => (x', polyOfList Q) else none
    | _ => none) (τ (lholder P.dealer L))
  fallback := (pick (fun it => match it with | .fallback x => some x | _ => none)
    (τ P.dealer)).bind (vecOfList P.h)

/-- `Out(σ_h, K; τ) = Dec_{O,h}(σ_h, K; τ)` (Protocol 7). -/
noncomputable def wssOut (h : Fin P.n) (K : Fin P.n → Option (Fin (mWS P.n) → 𝔼))
    (τ : Fin P.n → Option (WMsg 𝔽 𝔼)) : Option (Fin P.h → 𝔼) :=
  let _ := h
  Dec c.wss (transcript P v) (storedKey P c v) (toOpening P τ)
    (fun w => (K w).map (slotOf P.dealer))

end Rounds

/-- The key vector of a reconstruction broadcast. -/
def parseVK (n : ℕ) (m : WMsg 𝔽 𝔼) : Option (Fin (mWS n) → 𝔼) :=
  (m.findSome? fun it => match it with | .vk k => some k | _ => none).bind (vecOfList (mWS n))

/-- The opening part of a reconstruction broadcast (everything but the key vector). -/
def parseOpening (m : WMsg 𝔽 𝔼) : Option (WMsg 𝔽 𝔼) :=
  some (m.filter fun it => match it with | .vk _ => false | _ => true)

/-! ## Layouts -/

/-- Layout of a label code. -/
def layCode (L : LCode) : MVal 𝔼 := MVal.ofList [layNat L.1, layNat L.2.1, layNat L.2.2]

/-- Layout of a list of field elements. -/
def layFl (l : List 𝔼) : MVal 𝔼 := layList MVal.fld l

/-- Layout of a message item. -/
def layItem : Item 𝔽 𝔼 → MVal 𝔼
  | .pair L F G => MVal.ofList [layNat 0, layCode L, layFl F, layFl G]
  | .key L k => MVal.ofList [layNat 1, layCode L, .fld k.1, .fld k.2.1, .fld k.2.2]
  | .cp L d T => MVal.ofList [layNat 2, layCode L, .fld (algebraMap 𝔽 𝔼 d), layFl T]
  | .inv b => MVal.ofList [layNat 3, layBool b]
  | .phi j b => MVal.ofList [layNat 4, layNat j, layBool b]
  | .a j x => MVal.ofList [layNat 5, layNat j, layFl x]
  | .b j x => MVal.ofList [layNat 6, layNat j, layFl x]
  | .aD i j x => MVal.ofList [layNat 7, layNat i, layNat j, layFl x]
  | .bD i j x => MVal.ofList [layNat 8, layNat i, layNat j, layFl x]
  | .fin L r => MVal.ofList [layNat 9, layCode L, layOpt layFl r]
  | .U s => MVal.ofList [layNat 10, layList layNat s]
  | .u i rows => MVal.ofList [layNat 11, layNat i, layList layFl rows]
  | .cand L x Q => MVal.ofList [layNat 12, layCode L, layFl x, layFl Q]
  | .badCand L => MVal.ofList [layNat 13, layCode L]
  | .vk k => MVal.ofList [layNat 14, layFl k]
  | .fallback x => MVal.ofList [layNat 15, layFl x]

/-- Layout of a message. -/
def layWMsg (m : WMsg 𝔽 𝔼) : MVal 𝔼 := layList layItem m

/-- Layout of a drawn coin. -/
def layCoin : WCoin 𝔽 𝔼 → MVal 𝔼
  | .e x => .fld x
  | .f x => .fld (algebraMap 𝔽 𝔼 x)

/-- Layout of a view. -/
def layView (v : WView 𝔽 𝔼) : MVal 𝔼 :=
  MVal.ofList [layOpt layFl v.input, layList (layList layCoin) v.coins,
    layList (layList (layOpt layWMsg)) v.priv, layList (layList (layOpt layWMsg)) v.bc]

/-! ## The scheme -/

/-- **The protocol of §7.2** (Protocols 4–7 with the packed IC of §5.1) in the execution model. -/
noncomputable def wssProtocol (cfg : (P : Params) → WSSCfg 𝔽 P) :
    Protocol (WMsg 𝔽 𝔼) (WView 𝔽 𝔼) 𝔼 where
  init _ _ x := ⟨x.map List.ofFn, [], [], []⟩
  coins P _ r _ := (kindsAt P r).map (modulusOf (𝔼 := 𝔼) (cfg P).ic)
  send P i r st cs :=
    sendFrom P (cfg P) { st with coins := st.coins ++ [decodeCoins P (cfg P).ic r cs] } i r
  recv P _ r st cs pr bc :=
    { input := st.input, coins := st.coins ++ [decodeCoins P (cfg P).ic r cs],
      priv := st.priv ++ [List.ofFn pr], bc := st.bc ++ [List.ofFn bc] }
  output P i st :=
    wssOut P (cfg P) st i (fun j => (st.bcFrom 3 j).bind (parseVK P.n))
      (fun j => (st.bcFrom 3 j).bind parseOpening)
  msgLen m := valSize (layWMsg m)
  msgCap P := 1000 * (P.n + P.h + 2) ^ 4

/-- **The scheme of §7.2 as a broadcast-then-decode WSS** (Definition 6.1): key length `mWS`,
verification vector `κ_w`, opening `ω_w`, output `Out = Dec_O`. -/
noncomputable def wssScheme (cfg : (P : Params) → WSSCfg 𝔽 P) :
    BTD 𝔼 (WMsg 𝔽 𝔼) (WView 𝔽 𝔼) (WMsg 𝔽 𝔼) where
  prot := wssProtocol cfg
  keyLen n _ _ := mWS n
  vkey P _ σ := vkVec P (cfg P) σ
  vkey1 P _ σ := vkVec P (cfg P) σ
  opening P w σ := openingOf P (cfg P) σ w
  parseKey P m := parseVK P.n m
  parseOpen _ m := parseOpening m
  Out P i σ K τ := wssOut P (cfg P) σ i K τ

/-- **The layout of the §7.2 scheme** for the cost model: the parameters with `β`, `α₀` and the
points `a_i`, views, messages, and the coins as drawn. -/
noncomputable def wssLayout (cfg : (P : Params) → WSSCfg 𝔽 P) :
    Layout 𝔼 (WMsg 𝔽 𝔼) (WView 𝔽 𝔼) where
  par P := MVal.ofList [layParams P, layFin (fun b => MVal.fld (algebraMap 𝔽 𝔼 b)) (cfg P).β,
    MVal.fld (algebraMap 𝔽 𝔼 (cfg P).α0), layFin (fun b => MVal.fld (algebraMap 𝔽 𝔼 b)) (cfg P).pt]
  st := layView
  msg := layWMsg
  coin P _ r _ cs := layList layCoin (decodeCoins (𝔼 := 𝔼) P (cfg P).ic r cs)

end Supplement

end RoundOptVSS


