-- Prove2me | Definitions.Def_SymCircMM_treeAut
-- name    : SymCircMM_treeAut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:29:37.623948+00:00
-- url     : https://prove2.me/theorems/564f4fe4-12f3-4b39-8b3f-d145df8e6830
-- title:
--   The leaves $\{0,1\}^k$ of $T_k$ and the group $G_k=\mathrm{Aut}(T_k)$
-- statement:
--   The **complete binary tree** $T_k$ of height $k$ is a single leaf for $k=0$ and, for $k\ge1$, a root whose two children are roots of two copies of $T_{k-1}$; it has $n=2^k$ leaves. Its nodes are the binary strings of length at most $k$, the leaves are the strings $b=b_1\cdots b_k\in\{0,1\}^k$, and $[n]$ is identified with $\{0,1\}^k$.
--
--   The group $G_k=\mathrm{Aut}(T_k)$ acts faithfully on the leaves. As a group of permutations of $\{0,1\}^k$ it consists of the permutations $\sigma$ such that for every depth $0\le i\le k$ and all leaves $b,b'$:
--
--   $$b \text{ and } b' \text{ agree on their first } i \text{ bits} \iff \sigma(b) \text{ and } \sigma(b') \text{ agree on their first } i \text{ bits}.$$
--
--   $G_k$ is the symmetry group of the divide-and-conquer circuit for $\mathrm{MM}_n$, and the group of the mission's goal.
--
--   **Formalization Note** A leaf is `Fin k → Bool`, the bit $b_{t+1}$ being `b t`. A tree automorphism fixes the root, preserves depths and maps the leaf set $L(v)$ below each node $v$ onto $L(\sigma(v))$, so its leaf permutation preserves each relation "below the same node of depth $i$"; conversely, a leaf permutation preserving these relations permutes the sets $L(v)$ of each depth compatibly with inclusion and comes from a unique automorphism. Equivalently these are the permutations $(\tau\cdot b)_i=b_i\oplus\tau(b_1\cdots b_{i-1})$ given by the swap functions of display (1).
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), Definitions 2.7, 2.8, pp.4–5 (PDF pp.5–6); display (1), p.5 (PDF p.6); §2.4, p.6 (PDF p.7)

import Mathlib

set_option autoImplicit false

namespace SymCircMM

/-- The leaves of the complete binary tree `T_k` of height `k` (Dahan, Dawar, Kush, Pago, *Symmetric
Circuits for Matrix Multiplication*, manuscript (sha256 999a7eba…), Definition 2.7, p.4 (PDF p.5) and
§2.2, p.5 (PDF p.6)): binary strings `b = b₁b₂⋯b_k ∈ {0,1}^k`, which are identified with `[n]`, `n = 2^k`.

**Formalization Note.** `b : Fin k → Bool` with `b t` the bit `b_{t+1}`; the prefix of length `i` is
the restriction to the coordinates `t < i`. -/
abbrev Leaf (k : ℕ) : Type := Fin k → Bool

/-- Two leaves `b, b'` agree on their first `i` bits, i.e. lie below the same node of depth `i`. -/
def AgreeUpTo {k : ℕ} (i : ℕ) (b b' : Leaf k) : Prop := ∀ t : Fin k, t.val < i → b t = b' t

instance {k : ℕ} (i : ℕ) (b b' : Leaf k) : Decidable (AgreeUpTo i b b') := by
  unfold AgreeUpTo; infer_instance

/-- The group `G_k = Aut(T_k)` acting on the leaves (Definition 2.8, p.5 (PDF p.6)): the permutations
`σ` of `{0,1}^k` such that, for every depth `i ≤ k`, two leaves lie below a common node of depth `i`
if and only if their images do.

**Formalization Note.** An automorphism of `T_k` fixes the root, preserves depths and the parent–child
relation, and satisfies `σ(L(v)) = L(σ(v))` for the leaf sets `L(v)` (§2.4, p.6 (PDF p.7)); hence its
leaf permutation preserves each relation "same node of depth `i`". Conversely a leaf permutation
preserving these relations permutes the sets `L(v)` of each depth, compatibly with inclusion, and so
comes from a unique automorphism of `T_k` (the action of `G_k` on leaves is faithful). Equivalently,
these are the permutations given by the swap functions of display (1), p.5 (PDF p.6). -/
def treeAut (k : ℕ) : Subgroup (Equiv.Perm (Leaf k)) where
  carrier := {σ | ∀ (i : Fin (k + 1)) (b b' : Leaf k), AgreeUpTo i b b' ↔ AgreeUpTo i (σ b) (σ b')}
  one_mem' := fun _ _ _ => Iff.rfl
  mul_mem' := fun {σ τ} hσ hτ i b b' => (hτ i b b').trans (hσ i (τ b) (τ b'))
  inv_mem' := fun {σ} hσ i b b' => by
    have h := hσ i (σ⁻¹ b) (σ⁻¹ b')
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at h
    exact h.symm

theorem mem_treeAut {k : ℕ} (σ : Equiv.Perm (Leaf k)) :
    σ ∈ treeAut k ↔
      ∀ (i : Fin (k + 1)) (b b' : Leaf k), AgreeUpTo i b b' ↔ AgreeUpTo i (σ b) (σ b') :=
  Iff.rfl

end SymCircMM


