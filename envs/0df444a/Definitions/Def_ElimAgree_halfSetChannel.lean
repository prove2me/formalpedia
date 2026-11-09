-- Prove2me | Definitions.Def_ElimAgree_halfSetChannel
-- name    : ElimAgree_halfSetChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:45.819754+00:00
-- url     : https://prove2.me/theorems/907867d3-4388-4636-96f4-211a54ba2129
-- title:
--   The half-set channels $\kappa_+$ and $\kappa_-$
-- statement:
--   Let $U$ be a finite set and $\binom{U}{\ell}$ the family of its $\ell$-subsets. The channel $\kappa_+$ maps an $\ell$-set $S$ to a uniform element of $S$; the channel $\kappa_-$ maps it to a uniform element of its complement $U\setminus S$. When $|U|=2\ell$ both are channels from $\binom U\ell$ to $U$:
--   $$\kappa_+(S,j)=\frac{1}{\ell}\mathbf 1[j\in S],\qquad \kappa_-(S,j)=\frac1\ell\mathbf 1[j\notin S].$$
--   Write $u_\ell$ for the uniform law on $\binom U\ell$ and $u_1$ for the uniform law on $U$.
--
--   Lemma 3.2 bounds the contraction of relative entropy under these channels.
--
--   **Formalization Note** The sign is a Boolean: `true` is $\kappa_+$, `false` is $\kappa_-$.
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), §3.2, p.8 (PDF p.10)

import Mathlib

namespace ElimAgree

/-- The `ℓ`-subsets `(U choose ℓ)` of a finite set `U`. -/
abbrev LSet (U : Type) [DecidableEq U] (ℓ : ℕ) : Type := {S : Finset U // S.card = ℓ}

variable {U : Type} [Fintype U] [DecidableEq U]

/-- The channel `κ+` (Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement
in Elimination*, manuscript, STOC 2027 submission, §3.2, p.8): it maps an `ℓ`-set `S` to a
uniform element of `S`, so `κ+(S, j) = 1/ℓ` for `j ∈ S` and `0` otherwise. -/
noncomputable def kPlus (ℓ : ℕ) : LSet U ℓ → U → ℝ :=
  fun S j => if j ∈ S.1 then 1 / (ℓ : ℝ) else 0

/-- The channel `κ−` (§3.2, p.8): it maps an `ℓ`-set `S ⊆ U`, `|U| = 2ℓ`, to a uniform element
of its complement `U ∖ S` (which has `ℓ` elements), so `κ−(S, j) = 1/ℓ` for `j ∉ S`. -/
noncomputable def kMinus (ℓ : ℕ) : LSet U ℓ → U → ℝ :=
  fun S j => if j ∉ S.1 then 1 / (ℓ : ℝ) else 0

/-- `κ±` indexed by the sign: `true` is `κ+`, `false` is `κ−`. -/
noncomputable def halfSetChannel (ℓ : ℕ) (s : Bool) : LSet U ℓ → U → ℝ :=
  if s then kPlus ℓ else kMinus ℓ

end ElimAgree


