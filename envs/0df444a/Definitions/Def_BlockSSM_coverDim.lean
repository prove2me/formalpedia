-- Prove2me | Definitions.Def_BlockSSM_coverDim
-- name    : BlockSSM_coverDim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:21:35.611731+00:00
-- url     : https://prove2.me/theorems/201ec8e9-3add-43ac-837c-a0a4686d5a2b
-- title:
--   Cover invariant $D_b(G)$
-- statement:
--   $$
--   D_b(G)=\min_{\substack{\phi:H\twoheadrightarrow G,\ V\ \text{faithful}\\ \text{all irreducible degrees in }V\le b}}\dim V,
--   $$
--   the minimum over all surjections $\phi$ from a finite group $H$ onto $G$ and all faithful complex representations $V$ of $H$ whose irreducible degrees are at most $b$. A cover is any surjection of finite groups; it need not be central. An empty feasible set has minimum $\infty$. The zero-dimensional representation of the trivial group is allowed, so $D_b(1)=0$. It is the right-hand side of the mission's goal.
--
--   **Formalization Note** The minimum is an infimum in $\mathbb N\cup\{\infty\}$. A $d$-dimensional representation is taken on $\mathbb C^d$, and $H$ in the lowest universe; every feasible pair has an isomorphic copy of this form, even when $G$ lives in a higher universe.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Definition 2, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_BlockSSM_IrrepDegreesLE

universe u

namespace BlockSSM

/-- **The cover invariant `D_b(G)`.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Definition 2, p.2 (PDF p.3): `D_b(G)` is the minimum of
`dim V` over `φ : H ↠ G` and `V` faithful with all irreducible degrees in `V` at most `b`. "A cover
is any surjection of finite groups; it need not be central. Empty feasible sets have minimum ∞. The
zero-dimensional representation of the trivial group is allowed, so D_b(1) = 0."

**Formalization Note.** The infimum is taken in `ℕ∞`, where `sInf ∅ = ⊤` is the paper's `∞`. A
`d`-dimensional representation is taken on `Fin d → ℂ`, and the cover `H` in `Type`: every
`d`-dimensional representation is isomorphic to one on `Fin d → ℂ`, and every finite group has an
isomorphic copy in `Type` (on some `Fin k`), even when `G` lives in a higher universe. `φ` is only
required to be surjective, and `d = 0` is allowed. -/
noncomputable def coverDim (G : Type u) [Group G] (b : ℕ∞) : ℕ∞ :=
  sInf {D : ℕ∞ | ∃ d : ℕ, D = (d : ℕ∞) ∧
    ∃ (H : Type) (_ : Group H) (_ : Finite H) (φ : H →* G) (ρ : Representation ℂ H (Fin d → ℂ)),
      Function.Surjective φ ∧ Function.Injective ρ ∧ IrrepDegreesLE ρ b}

end BlockSSM


