-- Prove2me | Definitions.Def_ImplicitParityWL_CheckMatrix
-- name    : ImplicitParityWL_CheckMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:10:35.03521+00:00
-- url     : https://prove2.me/theorems/aafe45d2-2908-4b72-8e08-e18a96b604ac
-- title:
--   The check matrix $B$, the restricted matrix $B_e$ and the masks $\mathrm{rowspan}(B_e)$
-- statement:
--   The code $C$ is the kernel of a matrix $B\in\mathbb F_2^{(k-1+\ell)\times\mathfrak c}$: $k-1$ block-parity rows comparing blocks $1,\dots,k-1$ with block $k$, followed by $\ell$ checksum rows. For a coordinate domain $\mathfrak c_e\subseteq\mathfrak c$, the matrix $B_e$ is the restriction of $B$ to the columns in $\mathfrak c_e$. A **mask** is a vector in $\mathrm{rowspan}(B_e)$.
--
--   Masks are the row-space labels of the strip vertices of the graph compiler, and $2^{\mathrm{rank}\,B_e}$ is the size of a mask color class.
--
--   **Formalization Note** The page also deletes zero rows of $B_e$, which changes neither the row space nor the rank. Masks are extended by zero outside $\mathfrak c_e$, so that the masks of all schemas are vectors on $\mathfrak c$.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Fact 4.5, p.18; Definition 4.7, p.20; §4.4, p.21; §7.1, p.36

import Mathlib
import Definitions.Def_ImplicitParityWL_Address

namespace ImplicitParityWL

variable {k ℓ : ℕ}

/-- The check matrix `B ∈ 𝔽₂^{(k-1+ℓ)×𝔠}` of the code `C` (Curticapean, Liu, Neuen, Seppelt, *Lower
Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3,
2026, Fact 4.5, p.18): `k - 1` block-parity rows comparing blocks `1, …, k - 1` with block `k`,
followed by `ℓ` checksum rows, in the order fixed in §7.1, p.36.

**Formalization Note** The parity row `p : Fin (k - 1)` has a `1` exactly in the blocks `p` and the
last block (the index `k - 1`). Only the row space matters (Definition 4.7, p.20). -/
def checkMatrix (k ℓ : ℕ) : Matrix (Fin (k - 1) ⊕ Fin ℓ) (Coord k ℓ) (ZMod 2) := fun r c =>
  match r with
  | Sum.inl p => if c.1.val = p.val ∨ c.1.val + 1 = k then 1 else 0
  | Sum.inr j => c.2 j

/-- The restricted check matrix `B_e` of a coordinate domain `𝔠_e` (Definition 4.7, p.20): the
restriction of `B` to the columns in `𝔠_e`.

**Formalization Note** The page also deletes the zero rows, which changes neither the row space nor
the rank. -/
def restrictedCheck (dom : Finset (Coord k ℓ)) :
    Matrix (Fin (k - 1) ⊕ Fin ℓ) {c // c ∈ dom} (ZMod 2) :=
  (checkMatrix k ℓ).submatrix id Subtype.val

open scoped Classical in
/-- The masks of a coordinate domain `𝔠_e`: `rowspan(B_e)` (§4.4, p.21), extended by zero outside
`𝔠_e` so that masks of all schemas are vectors on `𝔠`. -/
noncomputable def maskSpace (dom : Finset (Coord k ℓ)) : Submodule (ZMod 2) (Word k ℓ) :=
  Submodule.span (ZMod 2) (Set.range fun (r : Fin (k - 1) ⊕ Fin ℓ) (c : Coord k ℓ) =>
    if c ∈ dom then checkMatrix k ℓ r c else 0)

end ImplicitParityWL


