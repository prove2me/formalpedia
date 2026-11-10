-- Prove2me | Definitions.Def_TurnstileRank_TightBounds_Blocks
-- name    : TurnstileRank_TightBounds_Blocks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:08:51.697193+00:00
-- url     : https://prove2.me/theorems/eb2eb44d-b866-4e03-9436-08c5e0be94f5
-- title:
--   Blocks, weights, independent inputs, and the packed input (§5)
-- statement:
--   §5: a block is a set of consecutive coordinates $[o,o+\ell)\subseteq[U]$; a hard instance placed on a block of $k^d$ coordinates is identified with $[k]^d$ in lexicographic order and has weight $w$ when each item is inserted with weight $w$.
--
--   * `placeVec U pos w` inserts weight $w$ at coordinate `pos i` for every item $i$; `hardVec U o w h` places the hard instance $h$ on $[o,o+k^d)$ with weight $w$.
--   * `totalMass z` $=\sum_uz_u$ and `massIn z lo hi` $=\sum_{lo\le u<hi}z_u$ for an input $z\in\mathbb N^U$.
--   * `blockInfo L base ζ Y vec` $=I(Y;A_\rho(\mathrm{vec}+Z)\mid\rho)$ when the seed $\rho$ (law of $L$), the sample $a\sim$ `base` (which determines $Y$ and the inserted vector) and the input $Z\sim\zeta$ are independent: "the state $M$ on $V+Z$" with "$Z$ an input independent of $V$ and $\rho$".
--   * Packed input (p. 26): $\theta=2^{1-h}$ if $h<q$ and $\theta=0$ if $h=q$ (`theta h q`); the layer weight $w_j=2^{q-1-j}$ (`layerWeight q j`).
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, §5, printed pp. 23–27 (PDF 24–28)

import Mathlib
import Definitions.Def_TurnstileRank_TightBounds_LinearSketch
import Definitions.Def_TurnstileRank_TightBounds_HardInstance

/-!
# Blocks, weights, independent inputs and the packed input (§5)

Hu, Jiang, Liu, Yu (2026), held STOC 2027 submission (SHA-256 4be42600…), §5, printed pp. 23–27
(PDF 24–28).

* p. 24: "define a block as a set of consecutive coordinates in the universe (`k^d` of them for a
  hard instance) … A hard instance placed on a block is identified with `[k]^d` in lexicographic
  order, and has weight `w` if each of its items is inserted with weight `w`."
* Lemma 5.1, Remark 5.3, Theorem 5.4, Lemma 5.5: the state `M` of a linear sketch on `V + Z`, where
  `Z` is "an input independent of `V` and `ρ`" with bounds on its mass, on its mass inside the
  block, and (in Remark 5.3, Theorem 5.4, Lemma 5.5) "a fixed mass before that block".
* Packed input (p. 26): "Fix integers `q ≥ 1`, `1 ≤ h ≤ q` and `r, t, b ≥ 1`. Take `h` disjoint groups
  `P_0 < ⋯ < P_{h−1}` of consecutive coordinates of `[U]`, each consisting of `r` consecutive blocks of
  `b` coordinates, its positions `1, …, r` … cell `(j, a)` is a tuple `V_{j,a}` of `t` items in position
  `a` of `P_{j mod h}`, each with weight `w_j = 2^{q−1−j}` … `θ = 2^{1−h}` if `h < q`, and `θ = 0` if
  `h = q`."

**Formalization Note.**
* An input is a nonnegative integer vector `z : Fin U → ℕ`; a random input is a discrete law
  `ζ : PMF (Fin U → ℕ)`, and a bound "of mass at most `m`" holds for every `z` in its support.
* A block is `[o, o + ℓ)` with `o + ℓ ≤ U`; `placeVec U pos w` inserts weight `w` at coordinate
  `pos i` for every item `i` (all items lie in the block in every use).
* `blockInfo L base ζ Y vec` is `I(Y ; A_ρ(vec + Z) | ρ)` when the seed `ρ ∼ L.law`, the sample
  `a ∼ base` (which determines `Y = Y a` and the inserted vector `vec a`) and `Z ∼ ζ` are
  independent.
* Positions `1, …, r` of a group are `0, …, r − 1` here; position `a` of the group starting at
  `off g` is `[off g + a b, off g + (a + 1) b)`.
-/

noncomputable section

open scoped BigOperators Classical

namespace TurnstileRank.TightBounds

/-- The vector that inserts weight `w` at coordinate `pos i` for every item `i`. -/
def placeVec (U : ℕ) {ι : Type} [Fintype ι] (pos : ι → ℕ) (w : ℕ) : Fin U → ℕ :=
  fun u => w * (Finset.univ.filter fun i => pos i = u.val).card

/-- The total mass `Σ_u z_u` of an input. -/
def totalMass {U : ℕ} (z : Fin U → ℕ) : ℕ := ∑ u, z u

/-- The mass of an input on the coordinates `[lo, hi)`. -/
def massIn {U : ℕ} (z : Fin U → ℕ) (lo hi : ℕ) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u : Fin U => lo ≤ u.val ∧ u.val < hi), z u

/-- A hard instance (Definition 4.2) placed on the block `[o, o + k^d)` with weight `w`. -/
def hardVec (U o w : ℕ) {d k : ℕ} (h : HardSample d k) : Fin U → ℕ :=
  placeVec U (fun i : Fin d => o + strVal (h.V i)) w

/-- `I(Y ; A_ρ(vec + Z) | ρ)` for independent `ρ ∼ L.law`, `a ∼ base` and `Z ∼ ζ`, with `Y = Y a`
and the inserted vector `vec a`. -/
def blockInfo {U : ℕ} {Ρ G Q O α β : Type} [AddCommGroup G] [Fintype β]
    (L : LinearSketch U Ρ G Q O) (base : PMF α) (ζ : PMF (Fin U → ℕ)) (Y : α → β)
    (vec : α → Fin U → ℕ) : ENNReal :=
  condMI (indepProd L.law (indepProd base ζ)) (fun ω => Y ω.2.1)
    (fun ω => L.state ω.1 (toZ (vec ω.2.1 + ω.2.2))) (fun ω => ω.1)

/-- `θ = 2^{1−h}` if `h < q`, and `θ = 0` if `h = q`. -/
def theta (h q : ℕ) : ℝ := if h < q then (2 : ℝ) ^ ((1 : ℤ) - h) else 0

/-- The layer weight `w_j = 2^{q−1−j}` (for `0 ≤ j < q`). -/
def layerWeight (q j : ℕ) : ℕ := 2 ^ (q - 1 - j)

end TurnstileRank.TightBounds


