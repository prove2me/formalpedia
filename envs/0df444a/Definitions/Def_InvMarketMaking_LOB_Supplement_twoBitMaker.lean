-- Prove2me | Definitions.Def_InvMarketMaking_LOB_Supplement_twoBitMaker
-- name    : InvMarketMaking_LOB_Supplement_twoBitMaker
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:30:00.61242+00:00
-- url     : https://prove2.me/theorems/bae5ea33-db0c-4f97-8d1e-5a00e552f57d
-- title:
--   Algorithm 1 (Two-Bit Market Maker) with its subroutines Algorithms 2–3
-- statement:
--   Algorithm 1 is a phased elimination procedure that sees only the two trade bits of each round. With $K=\lfloor T^{1/3}\rfloor$ it works on the grids
--   $$
--   \mathcal B^\circ=\{n/K:n=0,\dots,K-1\},\qquad \mathcal A^\circ=\{n/K:n=1,\dots,K\},
--   $$
--   the cap $L=\lfloor\log_2(T^{2/3})\rfloor$, block lengths $n_\ell=2^{\min\{\ell,L\}}$ and radii $\psi_\ell=\sqrt{\log(4T/\delta)/n_\ell}$. It starts with $\mathcal B_0=\mathcal B^\circ$, $\mathcal A_0=\mathcal A^\circ$, $F^{\mathrm{up}}_0\equiv S^{\mathrm{up}}_0\equiv1$, $F^{\mathrm{low}}_0\equiv S^{\mathrm{low}}_0\equiv0$. With $J^{\mathrm{low}}_\ell(b,a)=(a-b)\min\{F^{\mathrm{low}}_\ell(b),S^{\mathrm{low}}_\ell(a)\}$, $J^{\mathrm{up}}_\ell(b,a)=(a-b)\min\{F^{\mathrm{up}}_\ell(b),S^{\mathrm{up}}_\ell(a)\}$ and $J^{\mathrm{low}*}_\ell$ the maximum of $J^{\mathrm{low}}_\ell$ over the active pairs, the compatibility sets (9) are $\mathcal C_\ell(b)=\{a:J^{\mathrm{up}}_\ell(b,a)\ge J^{\mathrm{low}*}_\ell,\ a>b\}$ and $\mathcal C_\ell(a)=\{b:J^{\mathrm{up}}_\ell(b,a)\ge J^{\mathrm{low}*}_\ell,\ a>b\}$.
--
--   In phase $\ell+1$ the algorithm calls Algorithm 2 on every active bid $b$ and then Algorithm 3 on every active ask $a$, each call lasting $n_{\ell+1}$ consecutive rounds. Algorithm 2 pairs $b$ with $a'\in\arg\max\{S^{\mathrm{up}}_\ell(a):a\in\mathcal C_\ell(b)\}$, sets $u=\min\{F^{\mathrm{up}}_\ell(b),S^{\mathrm{up}}_\ell(a')\}+\psi_{\ell+1}$, posts $(b,a')$, and counts the purchases $X_s$ and sales $Y_s$ at the posted prices. Once $X_s\ge n_{\ell+1}u$ it sets the bid to $0$ and the bounds to $1$ and $\min\{F^{\mathrm{up}}_\ell(b),S^{\mathrm{up}}_\ell(a')\}$; otherwise its bounds are $X_s/s\pm\psi_{\ell+1}$. Once $Y_s\ge n_{\ell+1}u$ it sets the ask to $1$. The call returns the last bounds intersected with the phase-$\ell$ interval. Algorithm 3 is the mirror image. After the phase, $\mathcal C_{\ell+1}$ is computed from the new bounds and the prices without a compatible partner are eliminated. If a call returns an empty interval, or no price remains active, the algorithm posts $(0,1)$ in every later round. The result is the pair $(B_t,A_t)$ posted in each global round $t$.
--
--   **Formalization Note** The algorithm is a deterministic function of $T$, $\delta$, an argmax tie-break rule and the valuation sequences, and it reads only the two trade bits. Three decisions are left open by the page and are fixed here. Calls within a phase run in increasing price order, bids first. Ties in argmax are broken by the rule, a parameter of the definition. If no price remains active, $(0,1)$ is posted from then on. $J^{\mathrm{low}*}$ is taken over all of $\mathcal B_\ell\times\mathcal A_\ell$, including pairs with $a\le b$, as on p. 22, and $\mathcal C_{\ell+1}$ is computed on $\mathcal B_\ell\times\mathcal A_\ell$ (Line 14).
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Sec. 5.1, pp. 21–24 (Algorithms 1–3, Eqs. (8)–(9), footnote 4)

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_IsRoundModel

namespace InvMarketMaking.LOB.Supplement

/-- `K = ⌊T^{1/3}⌋`, the size of the grids of Algorithm 1 (Maran, Restelli, Stradi, No-Regret Revenue
Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Sec. 5.1,
p. 21). -/
noncomputable def tbK (T : ℕ) : ℕ := ⌊(T : ℝ) ^ ((1 : ℝ) / 3)⌋₊

/-- The bid grid `B° = {n/⌊T^{1/3}⌋ : n = 0, 1, …, ⌊T^{1/3}⌋ − 1}` of Algorithm 1 (p. 21). -/
noncomputable def tbBids (T : ℕ) : Finset ℝ :=
  (Finset.range (tbK T)).image (fun n : ℕ => (n : ℝ) / tbK T)

/-- The ask grid `A° = {n/⌊T^{1/3}⌋ : n = 1, 2, …, ⌊T^{1/3}⌋}` of Algorithm 1 (p. 21). -/
noncomputable def tbAsks (T : ℕ) : Finset ℝ :=
  (Finset.Icc 1 (tbK T)).image (fun n : ℕ => (n : ℝ) / tbK T)

/-- `L = ⌊log₂(T^{2/3})⌋`, the cap on the block exponent (p. 21). -/
noncomputable def tbL (T : ℕ) : ℕ := ⌊Real.logb 2 ((T : ℝ) ^ ((2 : ℝ) / 3))⌋₊

/-- The block length `2^{min{ℓ, ⌊log₂(T^{2/3})⌋}}` assigned to each active price in phase `ℓ`
(p. 21; Algorithms 2–3, Line 8). -/
noncomputable def tbBlock (T ℓ : ℕ) : ℕ := 2 ^ min ℓ (tbL T)

/-- The phase-`ℓ` confidence radius `ψ_ℓ = √(log(4T/δ)/2^{min{ℓ, ⌊log₂(T^{2/3})⌋}})` (p. 21;
Algorithms 2–3, Line 1). `log` is the natural logarithm. -/
noncomputable def tbRadius (T : ℕ) (δ : ℝ) (ℓ : ℕ) : ℝ :=
  Real.sqrt (Real.log (4 * T / δ) / tbBlock T ℓ)

/-- The confidence bounds `F^up_ℓ, F^low_ℓ, S^up_ℓ, S^low_ℓ` held after phase `ℓ`. -/
structure TBBounds where
  Fup : ℝ → ℝ
  Flo : ℝ → ℝ
  Sup : ℝ → ℝ
  Slo : ℝ → ℝ

/-- `J^up_ℓ(b, a) = (a − b) min{F^up_ℓ(b), S^up_ℓ(a)}` (Eq. (8), p. 22). -/
noncomputable def TBBounds.Jup (β : TBBounds) (b a : ℝ) : ℝ := (a - b) * min (β.Fup b) (β.Sup a)

/-- `J^low_ℓ(b, a) = (a − b) min{F^low_ℓ(b), S^low_ℓ(a)}` (Eq. (8), p. 22). -/
noncomputable def TBBounds.Jlow (β : TBBounds) (b a : ℝ) : ℝ := (a - b) * min (β.Flo b) (β.Slo a)

/-- `J^{low*} = max_{b ∈ Bs, a ∈ As} J^low(b, a)` (p. 22), over all pairs of `Bs × As` (including
pairs with `a ≤ b`). Its value on an empty product is irrelevant (no compatibility set is then
nonempty) and is set to `0`. -/
noncomputable def Jlowstar (β : TBBounds) (Bs As : Finset ℝ) : ℝ :=
  if h : (Bs ×ˢ As).Nonempty then (Bs ×ˢ As).sup' h (fun p => β.Jlow p.1 p.2) else 0

/-- The compatibility set of a bid, `C(b) = {a ∈ As : J^up(b, a) ≥ J^{low*}, a > b}` (Eq. (9),
p. 22), computed on `Bs × As`. -/
noncomputable def compatB (β : TBBounds) (Bs As : Finset ℝ) (b : ℝ) : Finset ℝ :=
  As.filter (fun a => Jlowstar β Bs As ≤ β.Jup b a ∧ b < a)

/-- The compatibility set of an ask, `C(a) = {b ∈ Bs : J^up(b, a) ≥ J^{low*}, a > b}` (Eq. (9),
p. 22), computed on `Bs × As`. -/
noncomputable def compatA (β : TBBounds) (Bs As : Finset ℝ) (a : ℝ) : Finset ℝ :=
  Bs.filter (fun b => Jlowstar β Bs As ≤ β.Jup b a ∧ b < a)

/-- An argmax selection rule: `sel s f` is a maximizer of `f` on `s` whenever `s` is nonempty. The
paper writes `a′ ← argmax{…}` without a tie-break; Algorithm 1 is parametrized by the rule and the
theorems quantify over every rule. -/
def IsArgmaxRule (sel : Finset ℝ → (ℝ → ℝ) → ℝ) : Prop :=
  ∀ s : Finset ℝ, ∀ f : ℝ → ℝ, s.Nonempty → sel s f ∈ s ∧ ∀ x ∈ s, f x ≤ f (sel s f)

/-- The local state of a call of Algorithm 2 or 3: the pair `(B, A)` to be posted next, the counters
`X, Y`, and the current local bounds (`F^up(b), F^low(b)` for Algorithm 2, `S^up(a), S^low(a)` for
Algorithm 3). -/
structure CallState where
  bid : ℝ
  ask : ℝ
  X : ℝ
  Y : ℝ
  up : ℝ
  low : ℝ

/-- One local round `s` of Algorithm 2 (`isBid = true`) or Algorithm 3 (`isBid = false`), Lines 9–23,
with block length `n`, target `u`, radius `ψ = ψ_{ℓ+1}`, halting lower bound `haltLow =
min{F^up_ℓ(b), S^up_ℓ(a′)}` (resp. `min{F^up_ℓ(b′), S^up_ℓ(a)}`), and the round's valuations `vs`, `vb`.
The current pair `(c.bid, c.ask)` is posted; the counters count trades at these prices; the halting
conditions `X_s ≥ n u`, `Y_s ≥ n u` then update the pair to be posted next and the local bounds. -/
noncomputable def callStep (isBid : Bool) (n : ℕ) (u ψ haltLow : ℝ) (s : ℕ) (vs vb : ℝ)
    (c : CallState) : CallState :=
  let X := c.X + (if vs ≤ c.bid then 1 else 0)
  let Y := c.Y + (if c.ask ≤ vb then 1 else 0)
  if isBid then
    { bid := if (n : ℝ) * u ≤ X then 0 else c.bid
      ask := if (n : ℝ) * u ≤ Y then 1 else c.ask
      X := X
      Y := Y
      up := if (n : ℝ) * u ≤ X then 1 else X / s + ψ
      low := if (n : ℝ) * u ≤ X then haltLow else X / s - ψ }
  else
    { bid := if (n : ℝ) * u ≤ X then 0 else c.bid
      ask := if (n : ℝ) * u ≤ Y then 1 else c.ask
      X := X
      Y := Y
      up := if (n : ℝ) * u ≤ Y then 1 else Y / s + ψ
      low := if (n : ℝ) * u ≤ Y then haltLow else Y / s - ψ }

/-- The state of a call after `s` local rounds, started at the pair `(p, q)` with `X_0 = Y_0 = 0`
(Lines 4–7); `vs s`, `vb s` are the valuations of local round `s ≥ 1`. The initial local bounds are
never read (every call lasts `n ≥ 1` rounds). -/
noncomputable def callRun (isBid : Bool) (n : ℕ) (u ψ haltLow p q : ℝ) (vs vb : ℕ → ℝ) :
    ℕ → CallState
  | 0 => ⟨p, q, 0, 0, 1, 0⟩
  | s + 1 => callStep isBid n u ψ haltLow (s + 1) (vs (s + 1)) (vb (s + 1))
      (callRun isBid n u ψ haltLow p q vs vb s)

/-- The state of Algorithm 1 after phase `ℓ`: the active sets `B_ℓ, A_ℓ`, the bounds of phase `ℓ`,
the compatibility sets `C_ℓ`, the number `clock` of global rounds used so far, the flag `dead`
(the algorithm posts `(0, 1)` in every later round), and the posted pairs `post g` of the global
rounds `g ≤ clock` (`(0, 1)` beyond). -/
structure TBState where
  Bact : Finset ℝ
  Aact : Finset ℝ
  bnd : TBBounds
  CB : ℝ → Finset ℝ
  CA : ℝ → Finset ℝ
  clock : ℕ
  dead : Bool
  post : ℕ → ℝ × ℝ

/-- The initialization of Algorithm 1 (Lines 1–5): `B_0 = B°`, `A_0 = A°`, `F^up_0 ≡ 1`,
`F^low_0 ≡ 0`, `S^up_0 ≡ 1`, `S^low_0 ≡ 0`, and `C_0` from Eq. (9) on `B_0 × A_0`. -/
noncomputable def tbInit (T : ℕ) : TBState :=
  let β : TBBounds := ⟨fun _ => 1, fun _ => 0, fun _ => 1, fun _ => 0⟩
  { Bact := tbBids T
    Aact := tbAsks T
    bnd := β
    CB := compatB β (tbBids T) (tbAsks T)
    CA := compatA β (tbBids T) (tbAsks T)
    clock := 0
    dead := decide (tbBids T = ∅ ∨ tbAsks T = ∅)
    post := fun _ => (0, 1) }

open Classical in
/-- Phase `ℓ + 1` of Algorithm 1 (Lines 7–17), from the state after phase `ℓ`. The calls are made in
the order: Algorithm 2 for each `b ∈ B_ℓ` in increasing order, then Algorithm 3 for each `a ∈ A_ℓ` in
increasing order; call number `j` occupies the global rounds `clock + j n + 1, …, clock + (j + 1) n`
with `n = 2^{min{ℓ+1, L}}`, and uses only phase-`ℓ` quantities. A bid call on `b` pairs it with
`a′ = sel(C_ℓ(b), S^up_ℓ)` and uses `u = min{F^up_ℓ(b), S^up_ℓ(a′)} + ψ_{ℓ+1}`; an ask call on `a` pairs
it with `b′ = sel(C_ℓ(a), F^up_ℓ)` and `u = min{F^up_ℓ(b′), S^up_ℓ(a)} + ψ_{ℓ+1}`. A call returns
`min{up, F^up_ℓ(b)}`, `max{low, F^low_ℓ(b)}` (Line 25; mirrored for asks) from its last local round.
If a returned interval is empty (upper < lower), the algorithm posts `(0, 1)` in every later round
(footnote 4, p. 22). Otherwise `C_{ℓ+1}` is computed from the new bounds on `B_ℓ × A_ℓ` (Line 14),
`B_{ℓ+1} = {b ∈ B_ℓ : C_{ℓ+1}(b) ≠ ∅}`, `A_{ℓ+1} = {a ∈ A_ℓ : C_{ℓ+1}(a) ≠ ∅}` (Lines 15–16), and if
no price remains active the algorithm posts `(0, 1)` from then on. -/
noncomputable def phaseStep (T : ℕ) (δ : ℝ) (sel : Finset ℝ → (ℝ → ℝ) → ℝ) (vs vb : ℕ → ℝ)
    (ℓ : ℕ) (st : TBState) : TBState :=
  if st.dead then st else
  let n := tbBlock T (ℓ + 1)
  let ψ := tbRadius T δ (ℓ + 1)
  let calls : List (Bool × ℝ) :=
    (st.Bact.sort (· ≤ ·)).map (fun b => (true, b)) ++ (st.Aact.sort (· ≤ ·)).map (fun a => (false, a))
  let partner : Bool × ℝ → ℝ := fun c =>
    if c.1 then sel (st.CB c.2) st.bnd.Sup else sel (st.CA c.2) st.bnd.Fup
  let hl : Bool × ℝ → ℝ := fun c =>
    if c.1 then min (st.bnd.Fup c.2) (st.bnd.Sup (partner c))
    else min (st.bnd.Fup (partner c)) (st.bnd.Sup c.2)
  let off : Bool × ℝ → ℕ := fun c => st.clock + calls.idxOf c * n
  let run : Bool × ℝ → ℕ → CallState := fun c =>
    callRun c.1 n (hl c + ψ) ψ (hl c) (if c.1 then c.2 else partner c)
      (if c.1 then partner c else c.2) (fun s => vs (off c + s)) (fun s => vb (off c + s))
  let newUp : Bool × ℝ → ℝ := fun c =>
    min (run c n).up (if c.1 then st.bnd.Fup c.2 else st.bnd.Sup c.2)
  let newLow : Bool × ℝ → ℝ := fun c =>
    max (run c n).low (if c.1 then st.bnd.Flo c.2 else st.bnd.Slo c.2)
  let bad : ℕ → Prop := fun j => ∃ c, calls[j]? = some c ∧ newUp c < newLow c
  let phasePost : ℕ → ℝ × ℝ := fun g =>
    let j := (g - st.clock - 1) / n
    let s := (g - st.clock - 1) % n + 1
    let c := calls.getD j (true, 0)
    if ∃ j' < j, bad j' then (0, 1) else ((run c (s - 1)).bid, (run c (s - 1)).ask)
  let len := calls.length * n
  let bnd' : TBBounds :=
    { Fup := fun x => if x ∈ st.Bact then newUp (true, x) else st.bnd.Fup x
      Flo := fun x => if x ∈ st.Bact then newLow (true, x) else st.bnd.Flo x
      Sup := fun x => if x ∈ st.Aact then newUp (false, x) else st.bnd.Sup x
      Slo := fun x => if x ∈ st.Aact then newLow (false, x) else st.bnd.Slo x }
  let CB' := compatB bnd' st.Bact st.Aact
  let CA' := compatA bnd' st.Bact st.Aact
  let B' := st.Bact.filter (fun b => (CB' b).Nonempty)
  let A' := st.Aact.filter (fun a => (CA' a).Nonempty)
  { Bact := B'
    Aact := A'
    bnd := bnd'
    CB := CB'
    CA := CA'
    clock := st.clock + len
    dead := decide ((∃ j < calls.length, bad j) ∨ B' = ∅ ∨ A' = ∅)
    post := fun g => if st.clock < g ∧ g ≤ st.clock + len then phasePost g else st.post g }

/-- The state of Algorithm 1 after `ℓ` phases. -/
noncomputable def tbRun (T : ℕ) (δ : ℝ) (sel : Finset ℝ → (ℝ → ℝ) → ℝ) (vs vb : ℕ → ℝ) :
    ℕ → TBState
  | 0 => tbInit T
  | ℓ + 1 => phaseStep T δ sel vs vb ℓ (tbRun T δ sel vs vb ℓ)

/-- **Algorithm 1** (Two-Bit Market Maker, with the subroutines Algorithms 2–3; Maran, Restelli,
Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints,
arXiv:2610.24562v1, pp. 21–24, Eqs. (8)–(9), footnote 4), run on horizon `T`, confidence `δ`, the
argmax rule `sel`, and the valuation sequences `vs`, `vb` (round `g ≥ 1` uses `vs g`, `vb g`): the
pair `(B_g, A_g)` posted in global round `g ≥ 1`.

**Formalization Note** (i) Each phase makes at least two calls of at least one round each unless the
algorithm has stopped, so after `g` phases either round `g` has been played or the algorithm posts
`(0, 1)` from then on; `tbRun … g` therefore fixes round `g`. (ii) The algorithm only reads the
two trade bits `I(V^sell ≤ B)`, `I(V^buy ≥ A)` of the posted pairs. (iii) Decisions the page leaves
open: calls within a phase in increasing price order, bids first (the order of Lines 7–13);
`argmax` ties broken by the rule `sel`; if no price remains active, `(0, 1)` is posted from then on.
(iv) The horizon only truncates: the theorems read `(B_g, A_g)` for `g ≤ T`. -/
noncomputable def twoBitMaker (T : ℕ) (δ : ℝ) (sel : Finset ℝ → (ℝ → ℝ) → ℝ) (vs vb : ℕ → ℝ)
    (g : ℕ) : ℝ × ℝ :=
  (tbRun T δ sel vs vb g).post g

/-- The bid process `B_t(ω)` of Algorithm 1 on the market `M`. -/
noncomputable def twoBitBid {Ω : Type*} (T : ℕ) (δ : ℝ) (sel : Finset ℝ → (ℝ → ℝ) → ℝ)
    (M : Market Ω) (t : ℕ) (ω : Ω) : ℝ :=
  (twoBitMaker T δ sel (fun s => M.Vs s ω) (fun s => M.Vb s ω) t).1

/-- The ask process `A_t(ω)` of Algorithm 1 on the market `M`. -/
noncomputable def twoBitAsk {Ω : Type*} (T : ℕ) (δ : ℝ) (sel : Finset ℝ → (ℝ → ℝ) → ℝ)
    (M : Market Ω) (t : ℕ) (ω : Ω) : ℝ :=
  (twoBitMaker T δ sel (fun s => M.Vs s ω) (fun s => M.Vb s ω) t).2

end InvMarketMaking.LOB.Supplement


