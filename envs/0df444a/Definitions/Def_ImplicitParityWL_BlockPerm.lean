-- Prove2me | Definitions.Def_ImplicitParityWL_BlockPerm
-- name    : ImplicitParityWL_BlockPerm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:10:37.273939+00:00
-- url     : https://prove2.me/theorems/5cab6106-2ae0-4e7a-8f0c-01d469d7558b
-- title:
--   Block-induced permutations
-- statement:
--   A permutation $\pi:\mathfrak c\to\mathfrak c$ is **block-induced** if there are a permutation $f$ of $[k]$ and $\delta_1,\dots,\delta_k\in\mathbb F_2^\ell$ with $\sum_i\delta_i=0$ such that $\pi(i,b)=(f(i),b+\delta_i)$ for all $(i,b)$. For a word $x$, $(\pi x)_{i,b}=x_{\pi^{-1}(i,b)}$; such a permutation maps addresses to addresses.
--
--   Block-induced permutations are how an equation schema relates the addresses of its argument locations.
--
--   **Formalization Note** The structure stores the data $(f,\delta)$, which $\pi$ determines. The action on arrays is $(\pi a)_{f(i)}=a_i+\delta_i$; a proved check in the mission's verification file shows that this is the page's action on indicator vectors and that $\mathrm{supp}(\pi a)=\pi(\mathrm{supp}\,a)$.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), §4.3, p.20

import Mathlib
import Definitions.Def_ImplicitParityWL_Address

namespace ImplicitParityWL

/-- A **block-induced permutation** of `𝔠` (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the
Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, §4.3, p.20),
given by its data: a permutation `f` of the blocks and `δ₁, …, δ_k ∈ 𝔽₂^ℓ` with `∑ δ_i = 0`.

**Formalization Note** The page calls a permutation `π : 𝔠 → 𝔠` block-induced if such data exist with
`π(i, b) = (f(i), b + δ_i)`. The data are determined by `π`, so storing them changes no instance. -/
structure BlockPerm (k ℓ : ℕ) where
  /-- The permutation of the blocks. -/
  f : Equiv.Perm (Fin k)
  /-- The translations of the block coordinates. -/
  δ : Fin k → BlockCoord ℓ
  /-- The translations sum to zero. -/
  sum_δ : ∑ i, δ i = 0

namespace BlockPerm

variable {k ℓ : ℕ}

/-- The permutation `(i, b) ↦ (f(i), b + δ_i)` of `𝔠` (§4.3, p.20). -/
def toPerm (π : BlockPerm k ℓ) : Equiv.Perm (Coord k ℓ) where
  toFun c := (π.f c.1, c.2 + π.δ c.1)
  invFun c := (π.f.symm c.1, c.2 - π.δ (π.f.symm c.1))
  left_inv c := by simp
  right_inv c := by simp

instance : CoeFun (BlockPerm k ℓ) (fun _ => Coord k ℓ → Coord k ℓ) := ⟨fun π => π.toPerm⟩

/-- The address `πa` (§4.3, p.20), in array form: block `f(i)` of `πa` holds `a_i + δ_i`, which is the
page's `(πa)_{i,b} = a_{π⁻¹(i,b)}` on the indicator vector. -/
def act (π : BlockPerm k ℓ) (a : Address k ℓ) : Address k ℓ :=
  ⟨fun j => a.1 (π.f.symm j) + π.δ (π.f.symm j), by
    rw [Equiv.sum_comp π.f.symm (fun i => a.1 i + π.δ i), Finset.sum_add_distrib, a.2, π.sum_δ,
      add_zero]⟩

/-- The identity permutation of `𝔠`, as a block-induced permutation. -/
def id : BlockPerm k ℓ := ⟨1, fun _ => 0, by simp⟩

end BlockPerm

end ImplicitParityWL


