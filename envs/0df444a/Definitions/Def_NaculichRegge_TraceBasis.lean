-- Prove2me | Definitions.Def_NaculichRegge_TraceBasis
-- name    : NaculichRegge_TraceBasis
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T23:15:20.844951+00:00
-- url     : https://prove2.me/theorems/dcf3fbb1-7229-4f55-b6be-5748bdbf1951
-- title:
--   Extended trace basis $t^{(\ell)}_\lambda$, colour-ordered amplitudes of a Regge-basis amplitude, and the null vectors
-- statement:
--   Given a loop order $\ell$, the $\ell$-loop extended trace basis (Naculich, eq. (2.3)) consists of the $3\ell+3$ elements
--   $$t^{(\ell)}_{1+6k}=N^{\ell-2k}c[1],\ t^{(\ell)}_{2+6k}=N^{\ell-2k}c[2],\ t^{(\ell)}_{3+6k}=N^{\ell-2k}c[3],\ t^{(\ell)}_{4+6k}=N^{\ell-2k-1}c[4],\ t^{(\ell)}_{5+6k}=N^{\ell-2k-1}c[5],\ t^{(\ell)}_{6+6k}=N^{\ell-2k-1}c[6],$$
--   with 1-based indices $1\le\lambda\le3\ell+3$. The coordinate $\lambda$ of a colour vector is the coefficient of the corresponding power of $N$ in the corresponding trace-basis component. For coefficients $B_{ik}$ and a prefactor $\kappa$ (standing for $A_1^{(0)}\tilde a^\ell$), the colour-ordered amplitudes $A^{(\ell)}_\lambda$ of the amplitude
--   $$\mathcal A^{(\ell)}=\kappa\sum_{i=0}^{\ell}\sum_k B_{ik}N^{\ell-i}C_{ik}$$
--   (eq. (4.24)) are its coordinates in the extended trace basis, eq. (2.4). Finally the four $\ell$-loop null vectors (for $\ell\ge2$) are the two-loop vectors (2.10) (even $\ell$) or three-loop vectors (2.12) (odd $\ell$), preceded by $6m$ zeros where $\ell=2m+2$ resp. $\ell=2m+3$; they encode the group-theory constraints (2.14)–(2.15).
-- source:
--   S. G. Naculich, "All-loop-orders relation between Regge limits of N = 4 SYM and N = 8 supergravity four-point amplitudes", arXiv:2012.00030v2, https://arxiv.org/abs/2012.00030, pp. 5–7, 16; eqs. (2.3), (2.4), (2.10), (2.12), (2.14), (2.15), (4.24)

import Definitions.Def_NaculichRegge_ColorAlgebra

/-!
# The extended trace basis, Regge-basis amplitudes and the group-theory null vectors

Source: S. G. Naculich, arXiv:2012.00030v2, eqs. (2.3)–(2.4), (2.10), (2.12), (2.14)–(2.15),
(4.24).

Indices `λ` of the extended trace basis are **1-based**, `1 ≤ λ ≤ 3ℓ + 3`, as in the paper.
-/

namespace NaculichRegge

open Polynomial

/-- The power of `N` carried by the extended trace-basis element `t_λ^{(ℓ)}`, eq. (2.3):
writing `λ = j + 1 + 6q` with `0 ≤ j < 6`, it is `ℓ − 2q` for `j ∈ {0,1,2}` (elements `c[1..3]`)
and `ℓ − 2q − 1` for `j ∈ {3,4,5}` (elements `c[4..6]`). -/
def extDegree (ℓ lam : ℕ) : ℕ :=
  if (lam - 1) % 6 < 3 then ℓ - 2 * ((lam - 1) / 6) else ℓ - 2 * ((lam - 1) / 6) - 1

/-- The trace-basis slot `c[j+1]` underlying `t_λ^{(ℓ)}`: `j = (λ − 1) mod 6`. -/
def extSlot (lam : ℕ) : Fin 6 := ⟨(lam - 1) % 6, Nat.mod_lt _ (by norm_num)⟩

/-- The extended trace-basis element `t_λ^{(ℓ)} = N^{extDegree ℓ λ} c[extSlot λ + 1]`, eq. (2.3),
for `1 ≤ λ ≤ 3ℓ + 3` (and `0` outside this range). -/
noncomputable def extBasisVec (ℓ lam : ℕ) : ColorVec :=
  if 1 ≤ lam ∧ lam ≤ 3 * ℓ + 3 then Pi.single (extSlot lam) (X ^ extDegree ℓ lam) else 0

/-- The `λ`-th coordinate of a colour factor in the `ℓ`-loop extended trace basis:
the coefficient of `N^{extDegree ℓ λ}` in its `c[extSlot λ + 1]` component,
for `1 ≤ λ ≤ 3ℓ + 3` (and `0` outside this range). -/
noncomputable def extCoord (ℓ : ℕ) (v : ColorVec) (lam : ℕ) : ℂ :=
  if 1 ≤ lam ∧ lam ≤ 3 * ℓ + 3 then (v (extSlot lam)).coeff (extDegree ℓ lam) else 0

/-- The `ℓ`-loop colour structure written in the Regge basis, eq. (4.24) without the prefactor:
`∑_{(i,k)} B_{ik} N^{ℓ−i} C_{ik}`, summed over the admissible pairs of eq. (4.25). -/
noncomputable def reggeAmplitude (ℓ : ℕ) (B : ℕ × ℕ → ℂ) : ColorVec :=
  ∑ p ∈ reggeIndex ℓ, (C (B p) * X ^ (ℓ - p.1)) • reggeColor p.1 p.2

/-- The `ℓ`-loop colour-ordered amplitudes `A_λ^{(ℓ)}` (eq. (2.4)) of the amplitude
`𝒜^{(ℓ)} = κ ∑_{(i,k)} B_{ik} N^{ℓ−i} C_{ik}` of eq. (4.24), where `κ` stands for the
prefactor `A₁^{(0)} ã^ℓ`. -/
noncomputable def colorOrderedAmp (ℓ : ℕ) (κ : ℂ) (B : ℕ × ℕ → ℂ) (lam : ℕ) : ℂ :=
  κ * extCoord ℓ (reggeAmplitude ℓ B) lam

/-- The four two-loop null vectors, eq. (2.10). -/
def twoLoopNull : Fin 4 → List ℂ :=
  ![[6, 6, 6, -1, -1, -1, 0, 0, 0],
    [0, 0, 0, 1, -2, 1, 1, -2, 1],
    [0, 0, 0, 1, 0, -1, 1, 0, -1],
    [0, 0, 0, 0, 0, 0, 1, 1, 1]]

/-- The four three-loop null vectors, eq. (2.12). -/
def threeLoopNull : Fin 4 → List ℂ :=
  ![[6, 6, 6, -1, -1, -1, 2, 2, 2, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 6, 6, 6, -1, -1, -1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]]

/-- The `r`-th `ℓ`-loop null vector (for `ℓ ≥ 2`), as a function of the 1-based index `λ`:
for even `ℓ = 2m + 2` it is the two-loop null vector (2.10) preceded by `6m` zeros, and for odd
`ℓ = 2m + 3` the three-loop null vector (2.12) preceded by `6m` zeros (paragraphs above
eqs. (2.14) and (2.15)). Entries beyond the list are `0`. -/
def nullVector (ℓ : ℕ) (r : Fin 4) (lam : ℕ) : ℂ :=
  if Even ℓ then
    (if lam ≤ 6 * ((ℓ - 2) / 2) then 0 else (twoLoopNull r).getD (lam - 1 - 6 * ((ℓ - 2) / 2)) 0)
  else
    (if lam ≤ 6 * ((ℓ - 3) / 2) then 0 else (threeLoopNull r).getD (lam - 1 - 6 * ((ℓ - 3) / 2)) 0)

end NaculichRegge


