-- Prove2me | Definitions.Def_ShortestPlanarDisjoint_Main_DiskState
-- name    : ShortestPlanarDisjoint_Main_DiskState
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:02.486398+00:00
-- url     : https://prove2.me/theorems/2138e5fc-58ee-44f9-84c0-5758fc77ec53
-- title:
--   Cut-disk layouts, states and stack codes
-- statement:
--   A fixed disk layout orders $f$ terminal blocks and two labelled sides for each of
--   $r$ seams. Every terminal occurs exactly once in the ordered block lists. Choose
--   counts $q_s\ge0$ with $\sum_s q_s\le b$. There is one endpoint at every terminal
--   and $q_s$ ordered endpoints on each copy of seam $s$.
--
--   A state is a fixed-point-free involution of the endpoints, representing a perfect
--   matching, such that no two matched pairs alternate in boundary order and no pair
--   lies wholly on one seam side. These are exactly the noncrossing and no-return
--   conditions. Counts and matching constitute state identity; no curve shape or
--   component orientation is stored. States need not be realized by the graph.
--
--   $$\operatorname{code}(D)=
--    ((q_s)_s,(o_{s,a},o_{s,b})_s,(\text{opening bit at terminal }i)_i).$$
--
--   An endpoint opens when it precedes its mate. Each $o_{s,e}$ counts opening endpoints
--   on that side. Injectivity of this code is a theorem, not part of the definition.
--   The layout permits all disk-side orders, including the planar and surface orders.
--   Gluing sides and extracting components remain separate work.
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Section 5.1 (states and stack code), p. 16 (PDF p. 18)

import Mathlib

set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main

/-- Original boundary blocks and the two sides of each seam. -/
abbrev DiskSide (f r : ℕ) := Fin f ⊕ (Fin r × Bool)

/-- The fixed boundary order of a cut disk. Terminal lists include each terminal
exactly once. The order of the sides may be arbitrary, as on a surface cut.
No state enumeration, signature separation or disk-cut existence is assumed. -/
structure DiskLayout (k f r : ℕ) where
  sideOrder : List (DiskSide f r)
  sides_nodup : sideOrder.Nodup
  sides_complete : ∀ s, s ∈ sideOrder
  block : Fin f → List (Fin (2 * k))
  terminals_nodup : ((List.ofFn block).flatten).Nodup
  terminals_complete : ∀ i, i ∈ (List.ofFn block).flatten

abbrev DiskEndpoint (k r : ℕ) (q : Fin r → ℕ) :=
  Fin (2 * k) ⊕ ((s : Fin r) × (Bool × Fin (q s)))

/-- Every terminal once, and q_s ordered endpoints on each copy of seam s. -/
def DiskLayout.endpoints {k f r : ℕ} (L : DiskLayout k f r) (q : Fin r → ℕ) :
    List (DiskEndpoint k r q) :=
  L.sideOrder.flatMap fun side => match side with
    | .inl j => (L.block j).map Sum.inl
    | .inr (s, e) => (List.finRange (q s)).map fun i => .inr ⟨s, e, i⟩

/-- The rank in the boundary traversal, with its fixed starting point. -/
def DiskLayout.rank {k f r : ℕ} (L : DiskLayout k f r) {q : Fin r → ℕ}
    (p : DiskEndpoint k r q) : ℕ := (L.endpoints q).idxOf p

/-- A state contains just counts and a return-free noncrossing perfect matching.
No geometry or chosen component orientation is included in state identity. -/
structure DiskState {k f r : ℕ} (L : DiskLayout k f r) (b : ℕ) where
  q : Fin r → ℕ
  budget : ∑ s, q s ≤ b
  mate : Equiv.Perm (DiskEndpoint k r q)
  involutive : Function.Involutive mate
  no_fixed : ∀ p, mate p ≠ p
  noncrossing : ∀ p u,
    L.rank p < L.rank (mate p) → L.rank u < L.rank (mate u) →
    ¬ (L.rank p < L.rank u ∧ L.rank u < L.rank (mate p) ∧
       L.rank (mate p) < L.rank (mate u))
  no_return : ∀ s e (i j : Fin (q s)),
    mate (.inr ⟨s, e, i⟩) ≠ .inr ⟨s, e, j⟩

namespace DiskState

variable {k f r b : ℕ} {L : DiskLayout k f r}

def Opens (D : DiskState L b) (p : DiskEndpoint k r D.q) : Prop :=
  L.rank p < L.rank (D.mate p)

instance (D : DiskState L b) (p : DiskEndpoint k r D.q) : Decidable (D.Opens p) :=
  inferInstanceAs (Decidable (L.rank p < L.rank (D.mate p)))

def sideOpenCount (D : DiskState L b) (s : Fin r) (e : Bool) : ℕ :=
  ((List.finRange (D.q s)).filter fun j => decide (D.Opens (.inr ⟨s, e, j⟩))).length

/-- Counts, then side-opening counts, then terminal bits. This is an encoding,
not a definition of equality of states; injectivity is the content of Lemma 5.2. -/
def stackCode (D : DiskState L b) : List ℕ :=
  List.ofFn D.q ++
  (List.ofFn fun s : Fin r => [D.sideOpenCount s false, D.sideOpenCount s true]).flatten ++
  List.ofFn (fun i : Fin (2 * k) => if D.Opens (.inl i) then 1 else 0)

/-- All closings precede all openings on each side. -/
def ClosingsBeforeOpenings (D : DiskState L b) : Prop :=
  ∀ s e (i j : Fin (D.q s)), i < j →
    D.Opens (.inr ⟨s, e, i⟩) → D.Opens (.inr ⟨s, e, j⟩)

end DiskState
end ShortestPlanarDisjoint.Main


