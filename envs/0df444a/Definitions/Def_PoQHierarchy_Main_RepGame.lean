-- Prove2me | Definitions.Def_PoQHierarchy_Main_RepGame
-- name    : PoQHierarchy_Main_RepGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:23.637865+00:00
-- url     : https://prove2.me/theorems/7c6c4d3d-7051-4fbe-8d94-e73d4a53bb8d
-- title:
--   The game $G^L$ with $nL+1$ players (p.36) and the player set $I'$ of Lemma 5.10
-- statement:
--   Let $G$ be an $n$-player nonlocal game and $L\ge1$. The game **$G^L$** (p.36) has $nL+1$ players. Players $(l-1)n+1,\dots,ln$ form group $l\in[L]$, and player $i$ of group $l$ is player $(l-1)n+i$. Every group receives an independent instance of $G$: the question distribution is
--   $$\mu^L(x)=\prod_{l=1}^L\mu\bigl(x^{(l)}\bigr).$$
--   The additional player $P_{\mathrm{last}}$ always receives the fixed question $\perp$ and answers an index $j\in[L]$. The players win iff group $j$ wins its instance, $V(a^{(j)},x^{(j)})=1$.
--
--   For $I\subseteq[n]$, the set of Lemma 5.10 is
--   $$I'=\bigcup_{l=1}^L\bigl((l-1)n+I\bigr)\subseteq[nL+1].$$
--
--   The compiled game $G_{L\text{-comp}}$ of p.37 is the KLVY compilation of $G^L$, so the paper's identity $G_{L\text{-comp}}=G^L_{\mathrm{comp}}$ holds by definition.
--
--   **Formalization Note** Player $i\in\{0,\dots,n-1\}$ of group $l\in\{0,\dots,L-1\}$ is player $l\cdot n+i$, and $P_{\mathrm{last}}$ is player $nL$. The question $\perp$ is the single element of `Fin 1`, and $[L]$ is `Fin L`.
-- source:
--   Kaniuar Bacho, Dominik Leichtle, Atul Singh Arora, Alexandru Cojocaru, STOC 2027 submission #1666 (October 2026), §5.4 (p.36), Lemma 5.10 (p.36), p.37 (G_{L-comp}); canonical PDF sha256 3009a0afeb95e5789f4e029db39d01935081f03d75e7fa263cb4b408aed40fb1

import Mathlib
import Definitions.Def_PoQHierarchy_Main_NonlocalGame

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PoQHierarchy.Main

/-!
Bacho, Leichtle, Arora, Cojocaru, STOC 2027 submission #1666, §5.4 (p.36): the game `G^L` with
`nL + 1` players. Players `(l-1)n + 1, …, ln` form group `l` (here: player `l·n + i` is player `i` of
group `l`, for `l : Fin L`, `i : Fin n`); every group plays an independent copy of `G`; the last
player `P_last` receives the fixed question `⊥` (the single element of `Fin 1`) and answers an index
`j ∈ [L]` (an element of `Fin L`); the players win iff group `j` wins its copy of `G`.

The compiled game `G_{L-comp}` of p.37 is the KLVY compilation of `G^L`, i.e. `winComp Sch (G.rep L)`;
the identity `G_{L-comp} = G^L_comp` holds by this definition.
-/

namespace NonlocalGame

variable {n : ℕ} (G : NonlocalGame n) (L : ℕ)

/-- Player `i` of group `l`, as a player of `G^L`. -/
def repIdx (l : Fin L) (i : Fin n) : Fin (n * L + 1) :=
  ⟨l.val * n + i.val, by
    have h1 : l.val * n + i.val < (l.val + 1) * n := by rw [Nat.succ_mul]; omega
    have h2 : (l.val + 1) * n ≤ L * n := Nat.mul_le_mul_right n l.isLt
    rw [Nat.mul_comm n L]; omega⟩

/-- A player index below `nL` has its position `p mod n` in `Fin n`. -/
def repPos (p : Fin (n * L + 1)) (h : p.val < n * L) : Fin n :=
  ⟨p.val % n, Nat.mod_lt _ (Nat.pos_of_ne_zero fun hn => by simp [hn] at h)⟩

/-- Question set sizes of `G^L`: those of `G` for the groups, one question `⊥` for `P_last`. -/
def repQ (p : Fin (n * L + 1)) : ℕ :=
  if h : p.val < n * L then G.q (repPos L p h) else 1

/-- Answer set sizes of `G^L`: those of `G` for the groups, `L` indices for `P_last`. -/
def repO (p : Fin (n * L + 1)) : ℕ :=
  if h : p.val < n * L then G.o (repPos L p h) else L

theorem repIdx_lt (l : Fin L) (i : Fin n) : (repIdx L l i).val < n * L := by
  have h1 : l.val * n + i.val < (l.val + 1) * n := by rw [Nat.succ_mul]; omega
  have h2 : (l.val + 1) * n ≤ L * n := Nat.mul_le_mul_right n l.isLt
  show l.val * n + i.val < n * L
  rw [Nat.mul_comm n L]; omega

theorem repPos_repIdx (l : Fin L) (i : Fin n) :
    repPos L (repIdx L l i) (repIdx_lt L l i) = i := by
  apply Fin.ext
  show (l.val * n + i.val) % n = i.val
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]

theorem repQ_repIdx (l : Fin L) (i : Fin n) : G.repQ L (repIdx L l i) = G.q i := by
  unfold repQ; rw [dif_pos (repIdx_lt L l i), repPos_repIdx]

theorem repO_repIdx (l : Fin L) (i : Fin n) : G.repO L (repIdx L l i) = G.o i := by
  unfold repO; rw [dif_pos (repIdx_lt L l i), repPos_repIdx]

theorem repO_last : G.repO L (Fin.last (n * L)) = L := by
  unfold repO; rw [dif_neg (by simp)]

/-- The questions of group `l`. -/
def repGroupQ (x : (p : Fin (n * L + 1)) → Fin (G.repQ L p)) (l : Fin L) :
    (i : Fin n) → Fin (G.q i) :=
  fun i => Fin.cast (G.repQ_repIdx L l i) (x (repIdx L l i))

/-- The answers of group `l`. -/
def repGroupA (a : (p : Fin (n * L + 1)) → Fin (G.repO L p)) (l : Fin L) :
    (i : Fin n) → Fin (G.o i) :=
  fun i => Fin.cast (G.repO_repIdx L l i) (a (repIdx L l i))

/-- **The game `G^L`** (p.36): independent questions `∏_l μ(x^{(l)})` for the `L` groups and the
fixed question `⊥` for `P_last`; the players win iff group `j` wins `G`, where `j` is the answer of
`P_last`. -/
def rep : NonlocalGame (n * L + 1) where
  q := G.repQ L
  o := G.repO L
  μ := fun x => ∏ l : Fin L, G.μ (G.repGroupQ L x l)
  V := fun a x =>
    let j : Fin L := Fin.cast (G.repO_last L) (a (Fin.last (n * L)))
    G.V (G.repGroupA L a j) (G.repGroupQ L x j)

/-- The set `I' = ⋃_{l=1}^{L} ((l-1)n + I) ⊆ [nL + 1]` of Lemma 5.10. -/
def repSet (I : Finset (Fin n)) : Finset (Fin (n * L + 1)) :=
  Finset.univ.biUnion fun l : Fin L => I.image fun i => repIdx L l i

end NonlocalGame

end PoQHierarchy.Main


