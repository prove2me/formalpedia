-- Prove2me | Definitions.Def_NecklacePPAD_Main_Rigid
-- name    : NecklacePPAD_Main_Rigid
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:06:25.602615+00:00
-- url     : https://prove2.me/theorems/dada4650-eec3-4fd0-8bd0-035368406747
-- title:
--   Rigid necklaces, home and sensor beads, orientation, segments and j(c) (Definition 4.1, §4.1)
-- statement:
--   A family of **blocks** gives each colour $c$ an interval $B(c)=[\mathrm{lo}(c),\mathrm{hi}(c)]$ of (0-based) positions. A necklace is **rigid** with blocks $B$ (Definition 4.1) if each $B(c)$ is a nonempty interval of positions of the necklace, the blocks are pairwise disjoint, and $B(c)$ contains more than $b_c$ of the $2b_c$ positions of colour $c$ (written $\#\{q:a_q=c\}<2m_c$). The positions of colour $c$ in $B(c)$ are its **home beads** ($m_c$ of them), the other positions of colour $c$ its **sensor beads** ($s_c$ of them); $S_c$ is the number of sensor beads of $c$ with label 1. A cut $q$ is **inside** $B(c)$ if $q,q+1\in B(c)$. The **orientation** $\tau(c)$ is the number of blocks lying to the left of $B(c)$, mod 2. The home beads from left to right are $h^c_1<\dots<h^c_{m_c}$ (1-based index, as on the page), and **segment $i$** of $c$, $i\in[1,m_c-1]$, is the set of positions strictly between $h^c_i$ and $h^c_{i+1}$. $j(c)$ is the number of home beads of $c$ to the left of the cut inside $B(c)$ (home beads at positions $p\le q$ for a cut $q$ inside $B(c)$; in the situation of Lemma 4.2 that cut is unique).
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Necklace Splitting with Ten Beads per Colour is PPAD-Hard (STOC 2027 submission, sha256 d5b5449c…41ac), Definition 4.1, p. 5 (PDF 7); Lemmas 4.2–4.3 and the segment definition, p. 6 (PDF 8)

import Mathlib
import Definitions.Def_NecklacePPAD_Main_Necklace

set_option autoImplicit false

namespace NecklacePPAD.Main

/-- A family of **blocks** `(B(c))_{c ∈ Fin n}` (Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission,
sha256 d5b5449c…, Definition 4.1, p. 5 (PDF 7)): the block of colour `c` is the set of
consecutive (0-based) positions `[lo c, hi c]`. -/
structure Blocks (n : ℕ) where
  lo : Fin n → ℕ
  hi : Fin n → ℕ

namespace Blocks

/-- Position `q` lies in the block `B(c)`. -/
abbrev InBlock {n : ℕ} (B : Blocks n) (c : Fin n) (q : ℕ) : Prop := B.lo c ≤ q ∧ q ≤ B.hi c

/-- `q` is a **home bead** of `c`: a position of colour `c` in `B(c)` (Definition 4.1). -/
abbrev IsHome (a : Necklace) (B : Blocks a.n) (c : Fin a.n) (q : ℕ) : Prop :=
  B.InBlock c q ∧ a.beads[q]? = some c

/-- `q` is a **sensor bead** of `c`: a position of colour `c` outside `B(c)` (Definition 4.1). -/
abbrev IsSensor (a : Necklace) (B : Blocks a.n) (c : Fin a.n) (q : ℕ) : Prop :=
  ¬ B.InBlock c q ∧ a.beads[q]? = some c

/-- The number `m_c` of home beads of `c`. -/
def homeCount (a : Necklace) (B : Blocks a.n) (c : Fin a.n) : ℕ :=
  ((Finset.range a.N).filter (fun q => IsHome a B c q)).card

/-- The number `s_c` of sensor beads of `c`. -/
def sensorCount (a : Necklace) (B : Blocks a.n) (c : Fin a.n) : ℕ :=
  ((Finset.range a.N).filter (fun q => IsSensor a B c q)).card

/-- The number `S_c` of sensor beads of `c` with label 1 under `ℓ` (Lemma 4.3). -/
def sensorOnes (a : Necklace) (B : Blocks a.n) (ℓ : Fin a.N → Bool) (c : Fin a.n) : ℕ :=
  ((Finset.range a.N).filter (fun q => IsSensor a B c q ∧ a.lab ℓ q = true)).card

/-- The cut `q` (between positions `q` and `q + 1`) is **inside** `B(c)`: `q, q + 1 ∈ B(c)`. -/
abbrev Inside {n : ℕ} (B : Blocks n) (c : Fin n) (q : ℕ) : Prop := B.InBlock c q ∧ B.InBlock c (q + 1)

/-- The number of blocks lying entirely to the left of position `q`. -/
def blocksLeftOf {n : ℕ} (B : Blocks n) (q : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun d => B.hi d < q)).card

/-- The **orientation** `τ(c)` (Lemma 4.2, p. 6): the number of blocks lying to the left of `B(c)`,
modulo 2. -/
def tau {n : ℕ} (B : Blocks n) (c : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun d => B.hi d < B.lo c)).card % 2

/-- A necklace is **rigid** with blocks `B` (Definition 4.1): each `B(c)` is a nonempty interval of
positions of the necklace, the blocks are pairwise disjoint, and `B(c)` contains more than `b_c` of
the `2b_c` positions of colour `c` (written `2 m_c > #{q : a_q = c}`). -/
def _root_.NecklacePPAD.Main.Necklace.IsRigid (a : Necklace) (B : Blocks a.n) : Prop :=
  (∀ c, B.lo c ≤ B.hi c ∧ B.hi c < a.N) ∧
  (∀ c d, c ≠ d → B.hi c < B.lo d ∨ B.hi d < B.lo c) ∧
  (∀ c, a.beads.count c < 2 * homeCount a B c)

/-- The home beads `h^c_1 < ⋯ < h^c_{m_c}` of `c`, from left to right, as a list. -/
def homeList (a : Necklace) (B : Blocks a.n) (c : Fin a.n) : List ℕ :=
  (List.range a.N).filter (fun q => decide (IsHome a B c q))

/-- The home bead `h^c_i` (1-based index `i`, as on p. 6). -/
def home (a : Necklace) (B : Blocks a.n) (c : Fin a.n) (i : ℕ) : ℕ :=
  (homeList a B c).getD (i - 1) 0

/-- **Segment `i` of `c`** (p. 6), for `i ∈ [1, m_c − 1]`: the positions strictly between `h^c_i`
and `h^c_{i+1}`. -/
def InSegment (a : Necklace) (B : Blocks a.n) (c : Fin a.n) (i q : ℕ) : Prop :=
  1 ≤ i ∧ i + 1 ≤ homeCount a B c ∧ home a B c i < q ∧ q < home a B c (i + 1)

/-- `j(c)` (Lemma 4.3, p. 6): the number of home beads of `c` to the left of the cut inside `B(c)`
under `ℓ`, i.e. the home beads at positions `p ≤ q` for a cut `q` of `ℓ` inside `B(c)`.

**Formalization Note** In the situation of Lemma 4.2 there is exactly one cut inside `B(c)`, and
this is the paper's `j(c)`. -/
def jCut (a : Necklace) (B : Blocks a.n) (ℓ : Fin a.N → Bool) (c : Fin a.n) : ℕ :=
  ((Finset.range a.N).filter
    (fun p => IsHome a B c p ∧ ∃ q ∈ a.cuts ℓ, B.Inside c q ∧ p ≤ q)).card

end Blocks

end NecklacePPAD.Main


