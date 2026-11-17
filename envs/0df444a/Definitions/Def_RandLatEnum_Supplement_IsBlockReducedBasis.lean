-- Prove2me | Definitions.Def_RandLatEnum_Supplement_IsBlockReducedBasis
-- name    : RandLatEnum_Supplement_IsBlockReducedBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:59:42.287567+00:00
-- url     : https://prove2.me/theorems/e303a8d3-fe32-485c-80ab-9f877f948917
-- title:
--   Basis block-reduced along a chain of ranks
-- statement:
--   Let $r\ge 1$, ranks $0=\kappa_0<\kappa_1<\dots<\kappa_r=n$ and orientations $\sigma_0,\dots,\sigma_{r-1}\in\{\text{HKZ},\text{reversed dual-HKZ}\}$. An ordered family $B=(b_1,\dots,b_n)$ is **block-reduced along $\kappa$ with orientations $\sigma$** if for every block $i$ the vectors
--   $$\pi_{\kappa_i+1}(b_{\kappa_i+1}),\dots,\pi_{\kappa_i+1}(b_{\kappa_{i+1}}),$$
--   projected orthogonally to $\operatorname{span}(b_1,\dots,b_{\kappa_i})$, form an HKZ-reduced family (if $\sigma_i=$ HKZ) or a reversed dual-HKZ family (if $\sigma_i=$ reversed dual-HKZ).
--
--   For a basis of $L$, the sublattices $M_i=\mathbb Z b_1+\dots+\mathbb Z b_{\kappa_i}$ form a chain $\{0\}=M_0\subseteq\dots\subseteq M_r=L$ of primitive sublattices, and the projected blocks are bases of the quotients $\pi_{M_i^\perp}(M_{i+1})$. These are the bases of Theorem 1.3.
--
--   **Formalization Note** HKZ is `KannanLattice.Core.IsReduced`, reversed dual-HKZ is `IsReduced (revBasis (dualBasis ·))` as in the published `RandLatEnum.eq_4_5`; orientations are booleans (`true` = HKZ). Positions are 0-based.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08adef70deb2f23a9a830e01c5a5b031ddaf5e0d4f88ce5174d67214b37), Theorem 1.3, p.4; §5.3, p.25

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_KannanLattice_Core_IsReduced
import Definitions.Def_RandLatEnum_dualBasis
import Definitions.Def_RandLatEnum_revBasis

namespace RandLatEnum.Supplement

open KannanLattice.Core RandLatEnum

/-- `b` is **block-reduced along the ranks `κ` with orientations `σ`** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Theorem 1.3,
p.4, and §5.3, p.25: "combining (lifted) HKZ and reversed dual-HKZ bases of (orthogonal quotients
of) these blocks"): the ranks satisfy `0 = κ_0 < κ_1 < ⋯ < κ_r = n`, and for each block `i < r` the
vectors `b_{κ_i+1}, …, b_{κ_{i+1}}`, projected orthogonally to `span(b_1, …, b_{κ_i})`, form
an HKZ family (`σ i = true`) or a reversed dual-HKZ family (`σ i = false`). The sublattices
`M_i = ℤ-span(b_1, …, b_{κ_i})` of the theorem are then a chain `0 = M_0 ⊆ M_1 ⊆ ⋯ ⊆ M_r = L` of
primitive sublattices, and the projected blocks are bases of the quotients `π_{M_i⊥}(M_{i+1})`.

**Formalization Note.** Ranks are 0-based positions: block `i` is the positions
`κ_i, …, κ_{i+1} − 1`. "Reversed dual-HKZ" is the encoding of the published `RandLatEnum.eq_4_5`,
`IsReduced (revBasis (dualBasis ·))`; HKZ is `KannanLattice.Core.IsReduced`. The `dite` in the
block family never takes its `0` branch, since `κ_i + j < κ_{i+1} ≤ n`. -/
def IsBlockReducedBasis {n k : ℕ} (r : ℕ) (κ : Fin (r + 1) → ℕ) (σ : Fin r → Bool)
    (b : Fin n → EuclideanSpace ℝ (Fin k)) : Prop :=
  κ 0 = 0 ∧ κ (Fin.last r) = n ∧ StrictMono κ ∧
    ∀ i : Fin r,
      let blk : Fin (κ i.succ - κ i.castSucc) → EuclideanSpace ℝ (Fin k) := fun j =>
        if h : κ i.castSucc + j.val < n then
          (Submodule.span ℝ (b '' {l : Fin n | (l : ℕ) < κ i.castSucc}))ᗮ.starProjection
            (b ⟨κ i.castSucc + j.val, h⟩)
        else 0
      if σ i then IsReduced blk else IsReduced (revBasis (dualBasis blk))

end RandLatEnum.Supplement


