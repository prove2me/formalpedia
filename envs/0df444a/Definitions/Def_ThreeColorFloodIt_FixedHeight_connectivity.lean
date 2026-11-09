-- Prove2me | Definitions.Def_ThreeColorFloodIt_FixedHeight_connectivity
-- name    : ThreeColorFloodIt_FixedHeight_connectivity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:33.585812+00:00
-- url     : https://prove2.me/theorems/e631aae5-d7b4-42e1-9b0c-e8b596da18f7
-- title:
--   True prefix partitions and explicit two-column connectivity unions
-- statement:
--   For a region $S_x$ and column $B_j$, the frontier domain is $D_x=S_x\cap B_j$. Its true partition connects rows precisely when the processed region $S_x\cap V_{\le j}$ connects them. No-lost-component means every processed component has a frontier representative.
--
--   The two-column update starts with old partition blocks and new singleton vertices, then takes Boolean transitive closure along new-column vertical edges and cross-column edges. It uses an explicit Floyd–Warshall loop on $2k$ slots. The acceptance test is
--   $$\text{every block reaches the new column, or a retiring region has exactly one block}.$$
--   Thus updated connectivity is computed independently of the actual extended region used to audit it. This representation keeps all partitions for general height, including disconnected local domains.
-- source:
--   Zhou, Three-Color Free-Flood-It on Fixed-Height Grids Is Polynomial-Time Solvable, STOC 2027 submission #31, supplied 2026 preprint, SHA-256 222ec38f7c30952eda9e86f87b16e8d7dfc93aa0b6b9705ac931e1b56017d280, printed p. 11 (PDF 12), §4.3–§4.4 and Lemma 17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/31.pdf Additional locations: printed pp. 12–14 (PDF 13–15), §4.4 and Lemma 17.

import Definitions.Def_ThreeColorFloodIt_FixedHeight_trees

set_option autoImplicit false

namespace ThreeColorFloodIt.FixedHeight

def Frontier {k n : ℕ} (T : TreeData (Cell k n) (Fin 3))
    (j : Fin n) (x : Fin T.tree.size) : Set (Fin k) :=
  {r | (r, j) ∈ Region T x}

def PrefixRegion {k n : ℕ} (T : TreeData (Cell k n) (Fin 3))
    (j : Fin n) (x : Fin T.tree.size) : Set (Cell k n) :=
  Region T x ∩ Prefix j

def PrefixPartition {k n : ℕ} (T : TreeData (Cell k n) (Fin 3))
    (j : Fin n) (x : Fin T.tree.size) (r s : Fin k) : Prop :=
  Within (Grid k n) (PrefixRegion T j x) (r, j) (s, j)

def NoLost {k n : ℕ} (R : Set (Cell k n)) (j : Fin n) : Prop :=
  ∀ v ∈ R, ∃ r : Fin k, Within (Grid k n) R v (r, j)

def Refines {V : Type} (p q : V → V → Prop) : Prop := ∀ u v, p u v → q u v

/-- Floyd--Warshall is an explicit finite sequence of Boolean unions. -/
def close (s : ℕ) (E : Fin s → Fin s → Bool) : Fin s → Fin s → Bool :=
  (List.finRange s).foldl (fun R p => fun u v => R u v || (R u p && R p v)) E

/-- Two-column slots: old rows 0..k-1, new rows k..2k-1. -/
def oldSlot {k : ℕ} (r : Fin k) : Fin (2 * k) := ⟨r.val, by omega⟩
def newSlot {k : ℕ} (r : Fin k) : Fin (2 * k) := ⟨k + r.val, by omega⟩

def slotRow {k : ℕ} (v : Fin (2 * k)) : ℕ := if v.val < k then v.val else v.val - k
def slotOld {k : ℕ} (v : Fin (2 * k)) : Bool := decide (v.val < k)
def slotAdjacent {k : ℕ} (u v : Fin (2 * k)) : Bool :=
  if slotOld u = slotOld v then
    decide (slotRow u + 1 = slotRow v ∨ slotRow v + 1 = slotRow u)
  else decide (slotRow u = slotRow v)

/-- The old equivalence relation is input data. All new relations are computed
by unions along new vertical and cross-column edges. -/
def updateConnectivity {k : ℕ} (oldDomain newDomain : Fin k → Bool)
    (oldEq : Fin k → Fin k → Bool) : Fin (2 * k) → Fin (2 * k) → Bool :=
  let active := fun v : Fin (2 * k) =>
    if h : v.val < k then oldDomain ⟨v.val, h⟩
    else newDomain ⟨v.val - k, by omega⟩
  close (2 * k) (fun u v =>
    if hu : u.val < k then
      if hv : v.val < k then oldEq ⟨u.val, hu⟩ ⟨v.val, hv⟩
      else active u && active v && slotAdjacent u v
    else if v.val < k then active u && active v && slotAdjacent u v
    else active u && active v && (decide (u = v) || slotAdjacent u v))

def updatePasses {k : ℕ} (oldDomain newDomain : Fin k → Bool)
    (oldEq : Fin k → Fin k → Bool) : Prop :=
  let U := updateConnectivity oldDomain newDomain oldEq
  if ∃ r, newDomain r = true then
    ∀ r, oldDomain r = true → ∃ s, newDomain s = true ∧ U (oldSlot r) (newSlot s) = true
  else
    (∃ r, oldDomain r = true) ∧
      ∀ r s, oldDomain r = true → oldDomain s = true → U (oldSlot r) (oldSlot s) = true

noncomputable def domainAt {k n : ℕ} (R : Set (Cell k n)) (j : Fin n) : Fin k → Bool := by
  classical
  exact fun r => decide ((r, j) ∈ R)

noncomputable def relationAt {k n : ℕ} (R : Set (Cell k n)) (j : Fin n) :
    Fin k → Fin k → Bool := by
  classical
  exact fun r s => decide (Within (Grid k n) R (r, j) (s, j))

def slotCell {k n : ℕ} (j l : Fin n) (u : Fin (2 * k)) : Cell k n :=
  if h : u.val < k then (⟨u.val, h⟩, j) else (⟨u.val - k, by omega⟩, l)

end ThreeColorFloodIt.FixedHeight


