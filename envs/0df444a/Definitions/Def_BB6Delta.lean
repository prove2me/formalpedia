-- Prove2me | Definitions.Def_BB6Delta
-- name    : BB6Delta
-- status  : Definition
-- author  : @alon yuval
-- created : 2026-11-23T18:07:22.78629+00:00
-- url     : https://prove2.me/theorems/e569cb91-a5c1-4548-81de-5f3114ecb366
-- title:
--   Mignotte–Voutier interpolation determinant Δ for integer α (three logarithms)
-- statement:
--   The interpolation determinant of Mignotte–Voutier, *A kit for linear forms in three logarithms* (arXiv:2205.08899), eq. (2.6), specialised to positive integers $\alpha_1,\alpha_2,\alpha_3$:
--   $$\Delta = \det\Bigl(\tbinom{r_j b'_3 + t_j b'_1}{k_i}\tbinom{s_j b''_3 + t_j b''_2}{m_i}\,\alpha_1^{\ell_i r_j}\alpha_2^{\ell_i s_j}\alpha_3^{\ell_i t_j}\Bigr)_{1\le i,j\le N},$$
--   where rows are indexed by triples $(k_i,m_i,\ell_i)$ and columns by triples $(r_j,s_j,t_j)$. `deltaZ` is the integer determinant and `deltaR` the same determinant over $\mathbb R$. Used for the BB(6) Baker roadmap (`BB6Baker.bw_instance`) with $(\alpha_1,\alpha_2,\alpha_3) = (2, c, 3)$.
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, arXiv:2205.08899, Section 2.2, eq. (2.6).

import Mathlib

namespace BB6Delta

/-- Entry of the Mignotte–Voutier interpolation matrix (arXiv:2205.08899, eq. (2.6)) specialised to
positive-integer α₁, α₂, α₃. Row data `(k, m, ℓ)`, column data `(r, s, t)`, and
`b1' = b′₁, b3' = b′₃, b2'' = b″₂, b3'' = b″₃` as in (2.3). -/
def entryNat (b1' b3' b2'' b3'' α1 α2 α3 : ℕ) (kml rst : ℕ × ℕ × ℕ) : ℕ :=
  Nat.choose (rst.1 * b3' + rst.2.2 * b1') kml.1 *
    Nat.choose (rst.2.1 * b3'' + rst.2.2 * b2'') kml.2.1 *
    α1 ^ (kml.2.2 * rst.1) * α2 ^ (kml.2.2 * rst.2.1) * α3 ^ (kml.2.2 * rst.2.2)

/-- The interpolation determinant Δ as an integer. -/
def deltaZ (N : ℕ) (b1' b3' b2'' b3'' α1 α2 α3 : ℕ) (kml rst : Fin N → ℕ × ℕ × ℕ) : ℤ :=
  (Matrix.of fun i j => ((entryNat b1' b3' b2'' b3'' α1 α2 α3 (kml i) (rst j) : ℕ) : ℤ)).det

/-- The same determinant computed over ℝ (the object bounded analytically in Prop. 3.7). -/
noncomputable def deltaR (N : ℕ) (b1' b3' b2'' b3'' α1 α2 α3 : ℕ) (kml rst : Fin N → ℕ × ℕ × ℕ) : ℝ :=
  (Matrix.of fun i j =>
    ((Nat.choose ((rst j).1 * b3' + (rst j).2.2 * b1') (kml i).1 : ℝ) *
     (Nat.choose ((rst j).2.1 * b3'' + (rst j).2.2 * b2'') (kml i).2.1 : ℝ) *
     (α1 : ℝ) ^ ((kml i).2.2 * (rst j).1) * (α2 : ℝ) ^ ((kml i).2.2 * (rst j).2.1) *
     (α3 : ℝ) ^ ((kml i).2.2 * (rst j).2.2))).det

end BB6Delta


