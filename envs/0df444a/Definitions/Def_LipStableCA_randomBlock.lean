-- Prove2me | Definitions.Def_LipStableCA_randomBlock
-- name    : LipStableCA_randomBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:50:38.882403+00:00
-- url     : https://prove2.me/theorems/d231262e-5b7e-4938-8ab9-c5d686845b70
-- title:
--   Mechanism 3: the random block auction
-- statement:
--   Let $L=\lfloor\log_2m\rfloor$. Draw $\ell\in\{0,\dots,L\}$ with $\Pr[\ell]=2^{-\ell-1}$ for $\ell\ge 1$ and $\Pr[0]=\frac12+2^{-L-1}$, and let $k=2^\ell$. Put each item in a uniformly random block $M_b$, $b\in[k]$, and offer each bidder $i$ a uniformly random block $Y_i$. On each nonempty block, run Mechanism 1 with $\epsilon=\frac12$ on the bidders offered it, with reported values $v_i(M_b)$ and desired bundles $Q_i=M_b$. The module also defines $\phi_m=\mathbb E[k^{-1}]=\frac23+2^{-L-1}-\frac{4^{-L}}6$, the largest value $V_b$ in block $b$, and the count $Y_t$ of blocks with $V_b\ge t$.
--
--   **Formalization Note.** Blocks are labels in $\{0,\dots,2^L-1\}$ read modulo $2^\ell$, which is uniform on $[2^\ell]$ and independent across items and bidders. The weights are indexed by bidders, as on p.26. One order serves every run.
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Mechanism 3, p.25; pp.26–27

import Definitions.Def_LipStableCA_Mechanism
import Definitions.Def_LipStableCA_weightedVCG

open MeasureTheory

namespace LipStableCA

variable {n m : ℕ}

/-- `L = ⌊log₂ m⌋`, Mechanism 3, line 1, p.25. -/
def blockLevel (m : ℕ) : ℕ := Nat.log 2 m

/-- The seed of Mechanism 3: the level `ℓ ∈ {0, …, L}`; a label in `{0, …, 2^L − 1}` per item and per
bidder; and the weight `Zᵢ` per bidder. **Formalization Note.** A block is a label read modulo `2^ℓ`, which
is uniform on `[2^ℓ]` and independent across items and bidders, as lines 5 and 7 require. The paper itself
indexes the weights by the bidders (p.26). -/
abbrev BlockSeed (n m : ℕ) :=
  Fin (blockLevel m + 1) ×
    ((Fin m → Fin (2 ^ blockLevel m)) × (Fin n → Fin (2 ^ blockLevel m))) × (Fin n → ℝ)

/-- `Pr[ℓ]`, Mechanism 3, line 2, p.25: `2^{−ℓ−1}` for `1 ≤ ℓ ≤ L`, and `1/2 + 2^{−L−1}` for `ℓ = 0`. -/
noncomputable def levelProb (L l : ℕ) : ℝ :=
  if l = 0 then 1 / 2 + (2 : ℝ) ^ (-((L : ℤ) + 1)) else (2 : ℝ) ^ (-((l : ℤ) + 1))

/-- The law of `ℓ`. -/
noncomputable def levelLaw (m : ℕ) : Measure (Fin (blockLevel m + 1)) :=
  ∑ l : Fin (blockLevel m + 1), ENNReal.ofReal (levelProb (blockLevel m) l.val) • Measure.dirac l

/-- The seed law of Mechanism 3: `ℓ`, the uniform labels, and the weights are independent. -/
noncomputable def blockMeasure (n m : ℕ) : Measure (BlockSeed n m) :=
  (levelLaw m).prod ((ProbabilityTheory.uniformOn Set.univ).prod (weightMeasure n))

/-- The number of blocks `k = 2^ℓ`, Mechanism 3, line 3, p.25. -/
def blockCount (ω : BlockSeed n m) : ℕ := 2 ^ ω.1.val

open Classical in
/-- The block `M_b`, Mechanism 3, line 5, p.25. Here `b` is a block number in `{0, …, k − 1}`. -/
noncomputable def itemBlock (ω : BlockSeed n m) (b : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun j => (ω.2.1.1 j).val % blockCount ω = b

/-- The block number assigned to bidder `i`, Mechanism 3, line 7, p.25. -/
def bidderBlock (ω : BlockSeed n m) (i : Fin n) : ℕ := (ω.2.1.2 i).val % blockCount ω

/-- The offer `Yᵢ = M_b`, Mechanism 3, line 7, p.25. -/
noncomputable def blockOffer (ω : BlockSeed n m) (i : Fin n) : Finset (Fin m) :=
  itemBlock ω (bidderBlock ω i)

open Classical in
/-- The participants of the run for bidder `i`'s block, Mechanism 3, line 10, p.25: the bidders assigned to
the same block. When the block is nonempty, this is the set of bidders `h` with `Yₕ = Yᵢ`. -/
noncomputable def blockParticipants (ω : BlockSeed n m) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun h => bidderBlock ω h = bidderBlock ω i

/-- `S*ᵢ` of the run on bidder `i`'s block: Mechanism 1 with `ϵ = 1/2`, the block's participants, reported
values `v_h(Yᵢ)`, and desired bundles `Q_h = Yᵢ`. -/
noncomputable def blockWinners (ord : LinearOrder (Finset (Fin n))) (v : Profile n m)
    (ω : BlockSeed n m) (i : Fin n) : Finset (Fin n) :=
  winnerSet ord (fun _ => blockOffer ω i) (blockParticipants ω i) (tauOf (1 / 2)) ω.2.2
    (fun h => v h (blockOffer ω i))

open Classical in
/-- **Mechanism 3 (Random block auction)**, p.25, for a fixed order `ord` of the runs of Mechanism 1. Only
nonempty blocks are sold (line 9), so a bidder offered an empty block gets `∅` and pays `0`. **Formalization
Note.** One order `ord` serves every run; the paper fixes an order for Mechanism 1 and does not distinguish
runs. Every statement about this mechanism is for every order. -/
noncomputable def randomBlock (ord : LinearOrder (Finset (Fin n))) :
    Mechanism n m (BlockSeed n m) where
  alloc v ω := toAlloc fun i =>
    if (blockOffer ω i).Nonempty ∧ i ∈ blockWinners ord v ω i then blockOffer ω i else ∅
  pay v ω i :=
    if (blockOffer ω i).Nonempty then
      scalarPay ord (fun _ => blockOffer ω i) (blockParticipants ω i) (tauOf (1 / 2)) ω.2.2
        (fun h => v h (blockOffer ω i)) i
    else 0

/-- `ϕ_m = E[k⁻¹] = 2/3 + 2^{−L−1} − 4^{−L}/6`, p.26. -/
noncomputable def phiM (m : ℕ) : ℝ :=
  2 / 3 + (2 : ℝ) ^ (-((blockLevel m : ℤ) + 1)) - (4 : ℝ) ^ (-(blockLevel m : ℤ)) / 6

open Classical in
/-- `V_b`, p.27: the largest value `vᵢ(M_b)` of a bidder `i` with `Yᵢ = M_b`, with `V_b = 0` if `M_b = ∅` or
there is no such bidder. -/
noncomputable def blockValue (v : Profile n m) (ω : BlockSeed n m) (b : ℕ) : ℝ :=
  if h : (itemBlock ω b).Nonempty ∧ (Finset.univ.filter fun i => bidderBlock ω i = b).Nonempty then
    (Finset.univ.filter fun i => bidderBlock ω i = b).sup' h.2 fun i => v i (itemBlock ω b)
  else 0

open Classical in
/-- `Y_t`, p.27: the number of `b ∈ [k]` with `V_b ≥ t`. -/
noncomputable def blockCountAbove (v : Profile n m) (ω : BlockSeed n m) (t : ℝ) : ℕ :=
  ((Finset.range (blockCount ω)).filter fun b => t ≤ blockValue v ω b).card

end LipStableCA


