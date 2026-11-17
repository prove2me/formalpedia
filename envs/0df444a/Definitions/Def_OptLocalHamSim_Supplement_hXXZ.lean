-- Prove2me | Definitions.Def_OptLocalHamSim_Supplement_hXXZ
-- name    : OptLocalHamSim_Supplement_hXXZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:17:32.249115+00:00
-- url     : https://prove2.me/theorems/fffe667f-37ab-4934-9d96-86abb7a5b540
-- title:
--   The uniform XXZ Hamiltonian $H_{\mathrm{XXZ}}$ with open boundaries, Eq. (3)
-- statement:
--   Let $\Lambda$ be a $D$-dimensional rectangular lattice carrying one qubit at every site, with the lattice ($\ell^1$) metric. Write $X_x, Y_x, Z_x$ for the Pauli operators acting on the qubit at site $x$ and as the identity on all other qubits, in the computational basis $|0\rangle,|1\rangle$:
--   $$
--   X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad Y=\begin{pmatrix}0&-i\\ i&0\end{pmatrix},\qquad Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
--   $$
--   For real parameters $J_{\mathrm{hop}}$ and $\Delta$, the **uniform XXZ Hamiltonian** is
--   $$
--   H_{\mathrm{XXZ}}=J_{\mathrm{hop}}\sum_{\langle x,y\rangle}\Big(\frac{X_xX_y+Y_xY_y}{2}+\Delta\,Z_xZ_y\Big),
--   $$
--   where the sum runs over the unordered pairs $\{x,y\}$ of sites at lattice distance $1$, each pair counted once, with open boundaries (no wrap-around).
--
--   This is the explicit model for which the paper proves its circuit-depth lower bound (Theorem 17); the hopping term $(XX+YY)/2$ exchanges an excitation between neighbouring sites, and $\Delta$ sets the strength of the $ZZ$ interaction.
--
--   **Formalization Note** $X,Y,Z$ are the published Pauli matrices `CompNonlocal.pauli 0, 1, 2` (same basis convention). The Hamiltonian is written as the published `Ham h`, a sum over all sets $Z$ of sites of a term `xxzTerm`, which is $J_{\mathrm{hop}}((X^{\otimes Z}+Y^{\otimes Z})/2+\Delta Z^{\otimes Z})$ when $Z=\{x,y\}$ is a nearest-neighbour bond and $0$ otherwise, so each bond appears exactly once. The lattice may be any rectangle; the paper's cube $\{1,\dots,\ell_{\mathrm{sys}}\}^D$ is the case of equal sides, translated to start at $0$. The paper's choice $J_{\mathrm{hop}}=J/[2D(1+|\Delta|)]$ is made in the theorem, not here.
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), §1.2, Eq. (3), p.6 (PDF p.6); §6, p.37 (PDF p.37)

import Mathlib
import Definitions.Def_OptLocalHamSim_Site
import Definitions.Def_OptLocalHamSim_IsLocalHam
import Definitions.Def_CompNonlocal_pauli

namespace OptLocalHamSim.Supplement

open OptLocalHamSim

variable {D : ℕ} {L : Fin D → ℕ}

/-- The operator `m^{⊗Z} ⊗ I`: the one-qubit matrix `m` on the (single) data qubit of every site of
`Z`, and the identity on all other qubits. For `Z = {x, y}` with `x ≠ y` and `m = X` this is the
two-site operator `X_x X_y`. -/
def pauliOn (Z : Finset (Site L)) (m : Matrix Bool Bool ℂ) :
    Matrix (Dat L 1 → Bool) (Dat L 1 → Bool) ℂ :=
  Matrix.of fun x y =>
    if ∀ j : Dat L 1, j.1 ∉ Z → x j = y j then ∏ s ∈ Z, m (x (s, 0)) (y (s, 0)) else 0

/-- A **nearest-neighbor bond**: an unordered pair `{x, y}` of sites at lattice distance one
(open boundaries: no wrap-around). -/
def IsBond (Z : Finset (Site L)) : Prop := ∃ x y : Site L, l1dist x y = 1 ∧ Z = {x, y}

open Classical in
/-- The interaction of the uniform XXZ model on a set of sites `Z`:
`J_hop ((X_xX_y + Y_xY_y)/2 + ∆ Z_xZ_y)` if `Z = {x, y}` is a nearest-neighbor bond, and `0`
otherwise. -/
noncomputable def xxzTerm (Jhop Δ : ℝ) (Z : Finset (Site L)) :
    Matrix (Dat L 1 → Bool) (Dat L 1 → Bool) ℂ :=
  if IsBond Z then
    (Jhop : ℂ) • ((1 / 2 : ℂ) • (pauliOn Z (CompNonlocal.pauli 0) + pauliOn Z (CompNonlocal.pauli 1)) +
      (Δ : ℂ) • pauliOn Z (CompNonlocal.pauli 2))
  else 0

/-- **The uniform XXZ Hamiltonian, Eq. (3)** (Shen, Wu, Yao, Yuan, Zhang, *Toward an Optimal Quantum
Algorithm for Geometrically Local Hamiltonian Simulation*, STOC 2027 submission, held version,
sha256 44a9768a…, §1.2, p.6, and §6, p.37):
`H_XXZ = J_hop ∑_{⟨x,y⟩} ((X_xX_y + Y_xY_y)/2 + ∆ Z_xZ_y)`, the sum over nearest-neighbor pairs with
open boundaries.

**Formalization Note**
* One data qubit per site (`Dat L 1`); the lattice is any rectangle `L`, the paper's cube is
  `L = fun _ => ℓ_sys` (a translate of `{1,…,ℓ_sys}^D`).
* The sum runs over the sets `Z` of sites, as the published `Ham`; the term on `Z` is nonzero only for
  a nearest-neighbor bond `Z = {x, y}`, `l1dist x y = 1`, so every unordered pair appears exactly
  once.
* `X_x, Y_x, Z_x` act on the qubit at `x` and as the identity elsewhere; `X, Y, Z` are the published
  Pauli matrices `CompNonlocal.pauli 0, 1, 2` (basis `false = |0⟩`, `Y = [[0, −i], [i, 0]]`,
  `Z = diag(1, −1)`).
* `J_hop` and `∆` are free real parameters; the paper's choice `J_hop = J/[2D(1 + ∆₀)]` is made in
  the theorem that uses this Hamiltonian. -/
noncomputable def hXXZ (L : Fin D → ℕ) (Jhop Δ : ℝ) :
    Matrix (Dat L 1 → Bool) (Dat L 1 → Bool) ℂ :=
  Ham (xxzTerm (L := L) Jhop Δ)

end OptLocalHamSim.Supplement


