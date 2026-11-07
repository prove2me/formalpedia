-- Prove2me | Definitions.Def_DoublingMST_EncodesHierarchy
-- name    : DoublingMST_EncodesHierarchy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:38:18.993112+00:00
-- url     : https://prove2.me/theorems/dd940613-ce7c-4802-bad0-219d8b8b5a76
-- title:
--   A net hierarchy laid out in integer memory
-- statement:
--   The memory layout of the input of Lemma 3.3's algorithm. Integer memory holds the labels in cells $0,\dots,n-1$, and each element $(u,\ell)$ of the net hierarchy has a record at some address $\ge n$: the label of $u$, the level $\ell$, one spare field holding $0$, the number $c$ of children, and the $c$ addresses of the children's records, each once and in any order. Records do not overlap and negative addresses hold $0$; $a_0$ is the address of the root's record.
--
--   The record holds what the paper's data structure stores (p.13: each net point maintains pointers to its children), plus the spare field that lets the algorithm attach marks to an element.
--
--   **Formalization Note** The paper fixes no layout, so this one is a convention of this formalization.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), §2.1, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_DoublingMST_children
open scoped Classical

namespace DoublingMST

/-- **A net hierarchy in integer memory (the input of Lemma 3.3's algorithm).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), §2.1, p.13 (PDF p.15): "In the net hierarchy data structure N, each net point u ∈ N_ℓ
maintains a set of pointers to all its children C(u) ⊆ N_{ℓ−1}".

`EncodesHierarchy H ι a₀ mem`: the integer memory `mem` holds the labels in cells `0, …, n − 1`, and
each element `a = (u, ℓ)` of `H` has a record at an address `addr a ≥ n`:
* `mem (addr a) = ι u`, `mem (addr a + 1) = ℓ`;
* `mem (addr a + 2) = 0`, a spare field for the algorithm's use;
* `mem (addr a + 3) = c`, the number of children of `a`;
* `mem (addr a + 4 + i)`, `i < c`: the addresses of the children, each once, in any order.
Records do not overlap, negative addresses hold `0`, and `a₀` is the address of the root record.

**Formalization Note.** The page fixes no memory layout, so this one is a convention. It carries
exactly the page's data (labels, levels, child pointers) plus one spare field; a record of a RAM
data structure can always have such a field, and without one the algorithm could not attach its
marks to an element in constant time. Nothing in the record reveals distances. -/
def EncodesHierarchy {n : ℕ} {d : Fin n → Fin n → ℝ} (H : NetHierarchy d) (ι : Fin n → ℤ)
    (a₀ : ℤ) (mem : ℤ → ℤ) : Prop :=
  (∀ i : Fin n, mem (i : ℕ) = ι i) ∧ (∀ i : ℤ, i < 0 → mem i = 0) ∧
  ∃ (addr : Fin n × ℕ → ℤ) (kids : Fin n × ℕ → List (Fin n × ℕ)),
    (∃ r ∈ H.N (topLevel d), a₀ = addr (r, topLevel d)) ∧
    (∀ a : Fin n × ℕ, a.2 ≤ topLevel d → a.1 ∈ H.N a.2 →
      (n : ℤ) ≤ addr a ∧ (kids a).Nodup ∧ (kids a).toFinset = children H a ∧
      mem (addr a) = ι a.1 ∧ mem (addr a + 1) = a.2 ∧ mem (addr a + 2) = 0 ∧
      mem (addr a + 3) = (kids a).length ∧
      ∀ i (hi : i < (kids a).length), mem (addr a + 4 + i) = addr ((kids a)[i])) ∧
    (∀ a b : Fin n × ℕ, a.2 ≤ topLevel d → a.1 ∈ H.N a.2 → b.2 ≤ topLevel d → b.1 ∈ H.N b.2 →
      a ≠ b → addr a + 4 + (kids a).length ≤ addr b ∨ addr b + 4 + (kids b).length ≤ addr a)

end DoublingMST


