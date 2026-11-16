-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_DeltaCClose
-- name    : DoublyEffIP_Supplement_DeltaCClose
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:34:17.710614+00:00
-- url     : https://prove2.me/theorems/11790b3e-2bac-4a83-92a9-a0408bed9c62
-- title:
--   $\Delta_c$-$d$-closeness of matrices
-- statement:
--   For $k\times L$ matrices $A,B$ over $\mathbb F$, the **$\Delta_c$-distance** is the largest Hamming distance between corresponding columns,
--
--   $$
--   \Delta_c(A,B)=\max_{j\in[L]}\#\{i : A_{ij}\ne B_{ij}\},
--   $$
--
--   and $A,B$ are **$\Delta_c$-$d$-close** if $\Delta_c(A,B)\le d$. The $\Delta_c$-$d$-ball of $A$ is $B_{d,\mathbb F}(A)=\{A' : \Delta_c(A,A')\le d\}$, and $M$ is $d$-$\Delta_c$-far from a set $L_\Phi$ if $B_{d,\mathbb F}(M)\cap L_\Phi=\emptyset$.
--
--   This is the distance under which the IPP with row reduction is sound.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.1, p.8, Definition 2

import Mathlib

set_option autoImplicit false

namespace DoublyEffIP.Supplement

/-- **`Δc`-`d`-closeness of matrices** — Definition 2 (`Δc`-distance) of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), Section 3.1, p.8:
"`Δc(A, B) = max_{i∈[L]} Δ(a_i, b_i)`. If `Δc(A, B) ≤ d`, we say A and B are Δc-d-close", where
`Δ` is the Hamming distance of the columns.

`DeltaCClose d A B`: in every column `j` of the `k × L` matrices `A`, `B`, at most `d` rows differ.
Then `B_{d,F}(A) = {A' | DeltaCClose d A A'}` is the `Δc`-`d`-ball, and `M` is `d`-`Δc`-far from
a set `L_Φ` if no matrix of its ball lies in `L_Φ`.

**Formalization Note.** "max over columns ≤ d" is "every column ≤ d" (for `L = 0` both hold). -/
def DeltaCClose {F : Type*} {k L : ℕ} (d : ℕ) (A B : Fin k → Fin L → F) : Prop :=
  ∀ j : Fin L, Nat.card {i : Fin k // A i j ≠ B i j} ≤ d

end DoublyEffIP.Supplement


