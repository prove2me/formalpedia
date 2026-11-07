-- Prove2me | Definitions.Def_SymCircMM_dk
-- name    : SymCircMM_dk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:54.707253+00:00
-- url     : https://prove2.me/theorems/ee7a4c18-c857-4fd1-8a59-060c7eecf4ce
-- title:
--   The divide-and-conquer circuit $D_k$ for $\mathrm{MM}_{2^k}$
-- statement:
--   Let $n=2^k$ and index rows, inner index and columns by the leaves $\{0,1\}^k$ of $T_k$. The circuit $D_k$ has an input gate for each variable $A_{ij}$ and $B_{j\ell}$, and a gate $g^v_{i\ell}$ for all $i,\ell\in\{0,1\}^k$ and all nodes $v\in\{0,1\}^{\le k}$:
--
--   1. for a leaf $v=j\in\{0,1\}^k$, $g^j_{i\ell}$ is a $\times$-gate with children $A_{ij}$ and $B_{j\ell}$;
--   2. for an internal node $v\in\{0,1\}^{<k}$, $g^v_{i\ell}$ is a $+$-gate with children $g^{v0}_{i\ell}$ and $g^{v1}_{i\ell}$.
--
--   All edges have multiplicity one, and the output gates are the gates $g^{\varepsilon}_{i\ell}$ at the root $\varepsilon$. The gate $g^v_{i\ell}$ computes $\sum_{j\in L(v)}A_{ij}B_{j\ell}$, where $L(v)$ is the set of leaves below $v$, so $g^\varepsilon_{i\ell}$ computes $(AB)_{i\ell}$.
--
--   $D_k$ is the unfolded recursive four-block algorithm; Theorem 2.14 shows that its symmetry group is exactly $G_k$, and it gives the upper bound of the goal.
--
--   **Formalization Note** A node is a pair (depth $d\le k$, string `Fin d → Bool`); the children $v0$, $v1$ append `false`, `true`. The gate type is the variables plus the triples $(i,\ell,v)$.
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), Definition 2.13, pp.6–7 (PDF pp.7–8)

import Mathlib
import Definitions.Def_SymCircMM_Circuit
import Definitions.Def_SymCircMM_MMVar
import Definitions.Def_SymCircMM_treeAut

set_option autoImplicit false

namespace SymCircMM

/-- The nodes `v ∈ {0,1}^{≤k}` of the complete binary tree `T_k` (Dahan, Dawar, Kush, Pago, *Symmetric
Circuits for Matrix Multiplication*, manuscript (sha256 999a7eba…), §2.4, p.6 (PDF p.7)): a depth
`d ≤ k` and a string of length `d`. The root is `ε` (depth `0`), the leaves are the strings of depth
`k`, and the children of an internal node `v` are `v0` and `v1`. -/
abbrev Node (k : ℕ) : Type := Σ d : Fin (k + 1), (Fin d → Bool)

instance (k : ℕ) : DecidableEq (Node k) := inferInstance

/-- The gates of the divide-and-conquer circuit `D_k`: an input gate for each variable `A_{ij}`,
`B_{jℓ}`, and a gate `g^v_{iℓ}` for all leaves `i, ℓ` and nodes `v`. -/
abbrev DkGate (k : ℕ) : Type := MMVar (Leaf k) ⊕ (Leaf k × Leaf k × Node k)

instance (k : ℕ) : DecidableEq (DkGate k) := instDecidableEqSum

/-- The input gate `A_{ij}` of `D_k`. -/
def dkA {k : ℕ} (i j : Leaf k) : DkGate k := Sum.inl (Sum.inl (i, j))

/-- The input gate `B_{jℓ}` of `D_k`. -/
def dkB {k : ℕ} (j l : Leaf k) : DkGate k := Sum.inl (Sum.inr (j, l))

/-- The gate `g^v_{iℓ}` of `D_k` at the node `v = ⟨d, w⟩` of depth `d`. -/
def dkG {k : ℕ} (i l : Leaf k) (v : Node k) : DkGate k := Sum.inr (i, l, v)

/-- The children `v0` (`b = false`) and `v1` (`b = true`) of an internal node `v` of depth `d < k`. -/
def Node.child {k : ℕ} (d : Fin (k + 1)) (w : Fin d → Bool) (h : d.val ≠ k) (b : Bool) : Node k :=
  ⟨⟨d.val + 1, by omega⟩, Fin.snoc (α := fun _ => Bool) w b⟩

/-- The children of a gate of `D_k` (Definition 2.13, pp.6–7 (PDF pp.7–8)): for a leaf `v = j`,
`g^j_{iℓ}` has the children `A_{ij}` and `B_{jℓ}`; for an internal node `v`, `g^v_{iℓ}` has the
children `g^{v0}_{iℓ}` and `g^{v1}_{iℓ}`; input gates have none. -/
def dkChildren (k : ℕ) : DkGate k → Finset (DkGate k)
  | Sum.inl _ => ∅
  | Sum.inr (i, l, ⟨d, w⟩) =>
    if h : d.val = k then
      {dkA i (fun t => w (Fin.cast h.symm t)), dkB (fun t => w (Fin.cast h.symm t)) l}
    else
      {dkG i l (Node.child d w h false), dkG i l (Node.child d w h true)}

/-- The label of a gate of `D_k`: `A_{ij}`, `B_{jℓ}` for the input gates, `×` for `g^j_{iℓ}` at a leaf
`j`, and `+` for `g^v_{iℓ}` at an internal node `v`. -/
def dkLabel (F : Type) (k : ℕ) : DkGate k → GateLabel (MMVar (Leaf k)) F
  | Sum.inl x => .input x
  | Sum.inr (_, _, ⟨d, _⟩) => if d.val = k then .mul else .add

/-- The **divide-and-conquer circuit** `D_k` (Definition 2.13, pp.6–7 (PDF pp.7–8)), `n = 2^k`, with
the leaves `{0,1}^k` as the index set `[n]`: input gates `A_{ij}`, `B_{jℓ}`, and gates `g^v_{iℓ}`
(`i, ℓ ∈ [n]`, `v ∈ {0,1}^{≤k}`), where `g^j_{iℓ}` is a `×`-gate with children `A_{ij}`, `B_{jℓ}` for a
leaf `j`, and `g^v_{iℓ}` is a `+`-gate with children `g^{v0}_{iℓ}`, `g^{v1}_{iℓ}` for an internal node
`v`. Every edge has multiplicity one. -/
def dk (F : Type) [Field F] (k : ℕ) : Circuit F (MMVar (Leaf k)) (DkGate k) where
  label := dkLabel F k
  wire g c := if c ∈ dkChildren k g then 1 else 0
  acyclic := by
    refine ⟨fun g => match g with
      | Sum.inl _ => 0
      | Sum.inr (_, _, ⟨d, _⟩) => k + 1 - d.val, ?_⟩
    intro g c h
    have hc : c ∈ dkChildren k g := by
      by_contra hc
      exact h (if_neg hc)
    rcases g with x | ⟨i, l, d, w⟩
    · simp [dkChildren] at hc
    · have hd := d.isLt
      by_cases hk : d.val = k
      · simp only [dkChildren, hk, dite_true, Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl <;> simp only [dkA, dkB] <;> omega
      · simp only [dkChildren, hk, dite_false, Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl <;> simp only [dkG, Node.child] <;> omega
  leaf_no_child := by
    intro g hg c
    rcases g with x | ⟨i, l, d, w⟩
    · simp [dkChildren]
    · by_cases hk : d.val = k <;> simp [dkLabel, hk, GateLabel.isLeaf] at hg
  internal_has_child := by
    intro g hg
    rcases g with x | ⟨i, l, d, w⟩
    · simp [dkLabel, GateLabel.isLeaf] at hg
    · by_cases hk : d.val = k
      · exact ⟨dkA i (fun t => w (Fin.cast hk.symm t)), by simp [dkChildren, hk]⟩
      · exact ⟨dkG i l (Node.child d w hk false), by simp [dkChildren, hk]⟩

/-- The output gates `g^ε_{iℓ}` of `D_k` (Definition 2.13, p.7 (PDF p.8)), at the root `ε`. -/
def dkOut (k : ℕ) : Leaf k × Leaf k → DkGate k
  | (i, l) => dkG i l ⟨⟨0, Nat.succ_pos k⟩, Fin.elim0⟩

end SymCircMM


