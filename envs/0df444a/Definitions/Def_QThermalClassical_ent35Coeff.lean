-- Prove2me | Definitions.Def_QThermalClassical_ent35Coeff
-- name    : QThermalClassical_ent35Coeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:11:37.613464+00:00
-- url     : https://prove2.me/theorems/2d1858b5-ef11-4490-9e8e-c289e7f7a7bb
-- title:
--   The entangled Hamiltonian (408) of Theorem 35
-- statement:
--   On the lattice $\Lambda_L=\{1,\dots,L\}^D$ with $m\ge2$, place at each site $x$ qubits $q_{x,i,j,\ell}$ ($1\le i<j\le m$, $\ell\in\{1,2\}$) and control qubits $c_{x,1},\dots,c_{x,m}$. With
--   $$
--   Q_{x,i}=\Big(\prod_{j<i}Z_{q_{x,j,i,1}}\Big)\Big(\prod_{j>i}X_{q_{x,i,j,1}}\Big)\Big(\prod_{j<i}Z_{q_{x,j,i,2}}\Big)\Big(\prod_{j>i}X_{q_{x,i,j,2}}\Big)\qquad(409),
--   $$
--   the Hamiltonian of Theorem 35 is
--   $$
--   H=-a\sum_{x\in\Lambda_L}\sum_{i=1}^mQ_{x,i}-\sum_{x,y\in\Lambda_L}\sum_{i=1}^mJ_{x,y}\,Q_{x,i}Z_{c_{y,i}}\qquad(408).
--   $$
--
--   **Formalization Note** The lattice is $\{0,\dots,L-1\}^D$ (`Fin D → Fin L`), the pairs $i<j$ a subtype of $[m]^2$. $H$ is given by its coefficient function (the sum of the coefficients of the terms of (408) equal to a given word); the double sum runs over ordered pairs $(x,y)$, including $x=y$.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 35, eqs. (408)–(409), p.84

import Mathlib
import Definitions.Def_QThermalClassical_pauliOp

set_option autoImplicit false

namespace QThermalClassical

/-- The qubits of Theorem 35 on the lattice `Λ_L = {1, …, L}^D` (as `Fin D → Fin L`) with
`m` indices: data qubits `q_{x,i,j,ℓ}` for `x ∈ Λ_L`, `1 ≤ i < j ≤ m`, `ℓ ∈ {1, 2}` (the left
summand, indices `Fin m` and `ℓ ∈ Fin 2`) and control qubits `c_{x,i}` (the right summand). -/
abbrev Ent35Qubit (D L m : ℕ) : Type :=
  ((Fin D → Fin L) × {p : Fin m × Fin m // p.1 < p.2} × Fin 2) ⊕ ((Fin D → Fin L) × Fin m)

/-- The Pauli word of `Q_{x,i} = (∏_{j<i} Z_{q_{x,j,i,1}})(∏_{j>i} X_{q_{x,i,j,1}})
(∏_{j<i} Z_{q_{x,j,i,2}})(∏_{j>i} X_{q_{x,i,j,2}})`, eq. (409): `Z` (index 3) on
`q_{x,j,i,ℓ}`, `X` (index 1) on `q_{x,i,j,ℓ}`, identity elsewhere. -/
def ent35WordQ {D L m : ℕ} (x : Fin D → Fin L) (i : Fin m) : PauliWord (Ent35Qubit D L m)
  | Sum.inl (x', p, _) => if x' = x ∧ p.1.2 = i then 3 else if x' = x ∧ p.1.1 = i then 1 else 0
  | Sum.inr _ => 0

/-- The Pauli word of `Q_{x,i} Z_{c_{y,i}}` (eq. (408)). -/
def ent35WordQZ {D L m : ℕ} (x y : Fin D → Fin L) (i : Fin m) : PauliWord (Ent35Qubit D L m)
  | Sum.inl r => ent35WordQ x i (Sum.inl r)
  | Sum.inr (y', i') => if y' = y ∧ i' = i then 3 else 0

/-- The coefficient function of the Hamiltonian (408) of Theorem 35,
`H = −a Σ_{x∈Λ_L} Σ_{i=1}^m Q_{x,i} − Σ_{x,y∈Λ_L} Σ_{i=1}^m J_{x,y} Q_{x,i} Z_{c_{y,i}}`:
the coefficient of a word is the sum of the coefficients of the terms of (408) equal to it, so
that `ham (ent35Coeff D L m a J)` is the operator (408).

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 35, eqs. (408)–(409), p.84.

**Formalization Note.** The double sum over `x, y ∈ Λ_L` runs over ordered pairs, including
`x = y`, as printed. -/
def ent35Coeff (D L m : ℕ) (a : ℝ) (J : (Fin D → Fin L) → (Fin D → Fin L) → ℝ) :
    PauliWord (Ent35Qubit D L m) → ℝ :=
  fun P => (∑ x, ∑ i : Fin m, if P = ent35WordQ x i then -a else 0) +
    ∑ x, ∑ y, ∑ i : Fin m, if P = ent35WordQZ x y i then -J x y else 0

end QThermalClassical


