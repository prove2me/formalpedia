-- Prove2me | Definitions.Def_MonDepMW_decodeSet
-- name    : MonDepMW_decodeSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:50:45.760674+00:00
-- url     : https://prove2.me/theorems/8c567cac-0bfa-46d1-aa8d-d0246d5dba63
-- title:
--   Output decoders
-- statement:
--   Fixed functions of the output cells and $n$ that read a result: a vertex set (a vertex belongs iff its cell is $1$); a graph ($n^2$ cells, read symmetrically and without loops); a partition (equal labels mean the same part); a relation on the parts of a partition; a sequence $B_0,\dots,B_m$ ($m$ then $m+1$ blocks of $n$ cells); and a merge sequence ($m$, then $m$ blocks of labels giving $\mathcal P_i$, then $n^2$ cells $E[u][v]$, with $uv\in R_i$ iff $u\neq v$ and $\min(E[u][v],E[v][u])\leqslant i$).
--
--   Because a decoder sees neither the input graph nor the paper's objects, the program cannot leave any of the work to it.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), App. C, p.43

import Mathlib
import Definitions.Def_MonDepMW_MergeSeq

set_option autoImplicit false

namespace MonDepMW

/-- A vertex set from `n` output cells from position `base`: `v` belongs iff its cell is `1`. Like every decoder of this
mission it is a fixed function of the output cells and `n`. -/
def decodeSet (n : ℕ) (out : ℕ → ℤ) (base : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => out (base + (v : ℕ)) = 1

/-- A graph from `n²` adjacency cells from position `base`, read symmetrically and without loops. -/
def decodeGraph (n : ℕ) (out : ℕ → ℤ) (base : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (out (base + (u : ℕ) * n + v) = 1 ∨ out (base + (v : ℕ) * n + u) = 1)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A partition from `n` label cells from position `base`: `u, v` lie in one part iff their labels are equal. -/
def decodePartition (n : ℕ) (out : ℕ → ℤ) (base : ℕ) : Setoid (Fin n) where
  r u v := out (base + (u : ℕ)) = out (base + (v : ℕ))
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩

/-- `σ` is the relation on the parts of `Q` written in the `n × n` output cells from position `base`, entry `(u, v)` being
`1` iff the part of `u` is related to the part of `v`. -/
def EncodesRel {n : ℕ} (out : ℕ → ℤ) (base : ℕ) (Q : Setoid (Fin n))
    (σ : Quotient Q → Quotient Q → Prop) : Prop :=
  ∀ u v : Fin n, out (base + (u : ℕ) * n + v) = 1 ↔ σ (Quotient.mk Q u) (Quotient.mk Q v)

/-- A sequence `B_0, …, B_m` of vertex sets: `m` in cell `0`, then `m + 1` blocks of `n` cells. -/
def decodeSetSeq (n : ℕ) (out : ℕ → ℤ) : ℕ × (ℕ → Finset (Fin n)) :=
  ((out 0).toNat, fun i => decodeSet n out (1 + i * n))

/-- A merge sequence: `m` in cell `0`, then `m` blocks of `n` labels (block `i` gives `𝒫_i`), then `n²` cells `E[u][v]`
with `uv ∈ R_i` iff `u ≠ v` and `min(E[u][v], E[v][u]) ≤ i`. -/
def decodeMergeSeq (n : ℕ) (out : ℕ → ℤ) : MergeSeq n where
  m := (out 0).toNat
  P := fun i => decodePartition n out (1 + (i - 1) * n)
  R := fun i =>
    { Adj := fun u v => u ≠ v ∧
        min (out (1 + (out 0).toNat * n + (u : ℕ) * n + v)) (out (1 + (out 0).toNat * n + (v : ℕ) * n + u)) ≤ (i : ℤ)
      symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [min_comm]; exact h.2⟩⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }

end MonDepMW


