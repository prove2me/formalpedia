-- Prove2me | Definitions.Def_MinrankTW_relOfPartial
-- name    : MinrankTW_relOfPartial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:52.961686+00:00
-- url     : https://prove2.me/theorems/f529b030-4868-4396-a03a-8abad2c16d47
-- title:
--   Linear relation $R(M_t)$ of a partial matrix at a bag
-- statement:
--   Let $M_t$ be a partial matrix whose interior consists of the rows $I_r$ and columns $I_c$ and whose bag consists of the rows $B_r$ and columns $B_c$. With $a$ bag columns and $c$ bag rows, its linear relation is
--   $$
--   R(M_t)=\Bigl\{(x,y)\in\mathbb F^a\oplus\mathbb F^c : \exists u,\ M_t[V_t,V_t]\begin{pmatrix}u\\x\end{pmatrix}=\begin{pmatrix}0\\y\end{pmatrix}\Bigr\},
--   $$
--   where $u$ has one coordinate per interior column and $V_t$ is the interior together with the bag.
--
--   **Formalization Note** Ambient coordinates: $x$ and $u$ are vectors in $\mathbb F^n$ (all columns), $y$ a vector in $\mathbb F^m$ (all rows); $x$ is supported on the bag columns, $u$ on the interior columns and $y$ on the bag rows, and the equation says that $M_t(u+x)$ vanishes on the interior rows and equals $y$ on the bag rows. This is (13) with the bag coordinates embedded; it agrees with (13) when interior and bag are disjoint, which the theorems assume.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 3.2, p.10, Eq. (13)

import Mathlib

namespace MinrankTW

open Matrix

/-- The linear relation of a partial matrix at a bag (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §3.2, p.10, Eq. (13)): for a
partial matrix `M_t` whose interior consists of the row set `I_r` and the column set `I_c`
and whose bag consists of the row set `B_r` and the column set `B_c`,
`R(M_t) = {(x, y) : ∃ u, M_t[V_t, V_t] (u; x) = (0; y)}`, where `u` has one coordinate per
interior column, `x` one per bag column and `y` one per bag row.

**Formalization Note** Ambient coordinates: `x` and `u` are vectors in `F^n` (all columns)
and `y` a vector in `F^m` (all rows); `x` is supported on the bag columns, `u` on the
interior columns and `y` on the bag rows, so this is (13) with the bag coordinates embedded in
`F^n`, `F^m`. The equation `M_t[V_t, V_t] (u; x) = (0; y)` reads: the entries of
`M_t (u + x)` vanish on the interior rows and equal `y` on the bag rows. It is (13) when the
interior and the bag are disjoint (rows and columns), as in a tree decomposition; the theorems
using it assume this. -/
def relOfPartial {F : Type*} [Field F] {m n : ℕ} (M : Matrix (Fin m) (Fin n) F)
    (Ir Br : Finset (Fin m)) (Ic Bc : Finset (Fin n)) :
    Submodule F ((Fin n → F) × (Fin m → F)) where
  carrier := {p | (∀ j ∉ Bc, p.1 j = 0) ∧ (∀ i ∉ Br, p.2 i = 0) ∧
    ∃ u : Fin n → F, (∀ j ∉ Ic, u j = 0) ∧ (∀ i ∈ Ir, (M *ᵥ (u + p.1)) i = 0) ∧
      ∀ i ∈ Br, (M *ᵥ (u + p.1)) i = p.2 i}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl, 0, fun _ _ => rfl, by simp, by simp⟩
  add_mem' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ ⟨hx, hy, u, hu, h0, h1⟩ ⟨hx', hy', u', hu', h0', h1'⟩
    dsimp only at hx hy h0 h1 hx' hy' h0' h1'
    have e : u + u' + (x + x') = (u + x) + (u' + x') := by abel
    refine ⟨fun j hj => ?_, fun i hi => ?_, u + u', fun j hj => ?_, fun i hi => ?_,
      fun i hi => ?_⟩
    · simp [hx j hj, hx' j hj]
    · simp [hy i hi, hy' i hi]
    · simp [hu j hj, hu' j hj]
    · rw [Prod.fst_add, e, mulVec_add, Pi.add_apply, h0 i hi, h0' i hi, add_zero]
    · rw [Prod.fst_add, Prod.snd_add, e, mulVec_add, Pi.add_apply, h1 i hi, h1' i hi,
        Pi.add_apply]
  smul_mem' := by
    rintro r ⟨x, y⟩ ⟨hx, hy, u, hu, h0, h1⟩
    dsimp only at hx hy h0 h1
    refine ⟨fun j hj => ?_, fun i hi => ?_, r • u, fun j hj => ?_, fun i hi => ?_,
      fun i hi => ?_⟩
    · simp [hx j hj]
    · simp [hy i hi]
    · simp [hu j hj]
    · rw [Prod.smul_fst, ← smul_add, mulVec_smul, Pi.smul_apply, h0 i hi, smul_zero]
    · rw [Prod.smul_fst, Prod.smul_snd, ← smul_add, mulVec_smul, Pi.smul_apply, h1 i hi,
        Pi.smul_apply]

end MinrankTW


