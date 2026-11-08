-- Prove2me | Definitions.Def_AsymSpecConn_flatRank
-- name    : AsymSpecConn_flatRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:04.173061+00:00
-- url     : https://prove2.me/theorems/93b91265-8daf-4132-9099-903aa61ebb5f
-- title:
--   $i$-flattening rank $R_i$ and concise tensors
-- statement:
--   Let $t\in V_1\otimes\dots\otimes V_k$ and $i\in[k]$. The **$i$-support** of $t$ is the smallest subspace $U\subseteq V_i$ with $t\in V_1\otimes\dots\otimes U\otimes\dots\otimes V_k$, and the **$i$-flattening rank** $R_i(t)$ is its dimension. The tensor $t$ is **$i$-concise** if $R_i(t)=\dim V_i$, and **concise** if it is $i$-concise for every $i$.
--
--   The module also gives $R_i$ on equivalence classes, since equivalent tensors have the same flattening ranks.
--
--   **Formalization Note** $R_i$ is the published `MME.flatteningRank` of the split $\{i\}$ versus the other legs: the rank of $t$ viewed as a linear map $V_i^*\to\bigotimes_{j\ne i}V_j$, which is the dimension of the $i$-support. Both sides of the split are nonempty because $k\ge2$. Legs are indexed by $\mathrm{Fin}\,k$, so the source's leg $i$ is $i-1$ here.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), §3, p.21

import Mathlib
import Definitions.Def_mme_tensor_quotient

set_option autoImplicit false

namespace AsymSpecConn

universe u

/-- The split `{i} ⊔ ([k] \ {i})` of the legs, used for the `i`-flattening (§3, p.21 of
Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)). Its complement is nonempty because `k ≥ 2`. -/
def legSplit {k : ℕ} (hk : 2 ≤ k) (i : Fin k) : MME.Split (Fin k) where
  S := {i}
  hS := Finset.singleton_nonempty i
  hSc := by
    by_cases h : i.val = 0
    · exact ⟨⟨1, by omega⟩, by simp [Fin.ext_iff, h]⟩
    · exact ⟨⟨0, by omega⟩, by simp [Fin.ext_iff]; omega⟩

/-- **The `i`-flattening rank** `R_i(t)` (§3, p.21 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)): the dimension of
the `i`-support of `t`, the smallest subspace `U ⊆ V_i` with `t ∈ V₁ ⊗ ⋯ ⊗ U ⊗ ⋯ ⊗ V_k`.

**Formalization Note** This is the published `MME.flatteningRank` of the split `{i}` versus the
other legs: the rank of `t` viewed as a linear map `V_i^* → ⨂_{j ≠ i} V_j`, which equals the
dimension of the `i`-support. Legs are indexed by `Fin k` (0-based: leg `i` of the paper is
`i - 1`). -/
noncomputable def flatRank {K : Type u} [Field K] {k : ℕ} (hk : 2 ≤ k) (i : Fin k)
    (X : MME.TensorObj K k) : ℕ :=
  MME.flatteningRank (legSplit hk i) X

/-- `R_i` on equivalence classes `MME.TensorQ K k`: equivalent tensors (mutual restrictions)
have the same flattening rank, by `MME.flatteningRank_mono`. -/
noncomputable def flatRankQ {K : Type u} [Field K] {k : ℕ} (hk : 2 ≤ k) (i : Fin k) :
    MME.TensorQ K k → ℕ :=
  Quotient.lift (flatRank hk i) (fun _ _ h =>
    le_antisymm (MME.flatteningRank_mono _ h.1) (MME.flatteningRank_mono _ h.2))

theorem flatRankQ_toQ {K : Type u} [Field K] {k : ℕ} (hk : 2 ≤ k) (i : Fin k)
    (X : MME.TensorObj K k) : flatRankQ hk i (MME.TensorQ.toQ X) = flatRank hk i X := rfl

/-- **Concise tensor** (§3, p.21 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)): `t` is `i`-concise if its `i`-support
is all of `V_i`, i.e. `R_i(t) = dim V_i`, and concise if it is `i`-concise for every leg `i`. -/
def IsConcise {K : Type u} [Field K] {k : ℕ} (hk : 2 ≤ k) (X : MME.TensorObj K k) : Prop :=
  ∀ j : Fin k, flatRank hk j X = Module.finrank K (X.V j)

end AsymSpecConn


