-- Prove2me | Definitions.Def_graphene_tb_hamiltonian
-- name    : graphene_tb_hamiltonian
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-19T20:07:41.17814+00:00
-- url     : https://prove2.me/theorems/6df346c3-a9da-4395-b6aa-6f6dd21c9dae
-- title:
--   Bloch Hamiltonian of the graphene tight-binding model
-- statement:
--   The nearest-neighbour tight-binding data of graphene, for a carbon–carbon distance $a$ and
--   a hopping amplitude $t$ (Eqs. (9), (10), (12)–(14), (25)–(26), (31), (33) of the source):
--
--   - the structure factor $\Delta_k=\sum_{j}e^{i\,k\cdot\delta_j}$ summed over the three
--     nearest-neighbour vectors;
--   - the $2\times2$ Bloch Hamiltonian in the $(A,B)$ sublattice basis
--     $$h(k)=-t\begin{pmatrix}0&\Delta_k\\ \overline{\Delta_k}&0\end{pmatrix};$$
--   - the upper band energy $E_+(k)=t\,|\Delta_k|$ (the lower band is $-E_+$);
--   - $f(k)=2\cos(\sqrt3 k_ya)+4\cos\!\bigl(\tfrac{3k_xa}{2}\bigr)\cos\!\bigl(\tfrac{\sqrt3k_ya}{2}\bigr)$;
--   - the Pauli matrices $\sigma_x,\sigma_y,\sigma_z$;
--   - the Fermi velocity $v_F=\tfrac{3at}{2}$ (units with $\hbar=1$);
--   - the linearised Hamiltonians $v_F(q_x\sigma_x-q_y\sigma_y)$ at $K$ and
--     $v_F(q_x\sigma_x+q_y\sigma_y)$ at $K'$, and the massive Dirac Hamiltonian
--     $v_F(q_x\sigma_x+q_y\sigma_y+M\sigma_z)$.
-- source:
--   Franz Utermohlen, Tight-Binding Model for Graphene, lecture notes, September 12, 2018 (Ohio State University); equation numbers as in that text.

import Definitions.Def_graphene_lattice

/-!
# Graphene: the nearest-neighbour tight-binding Bloch Hamiltonian

The Bloch Hamiltonian of the nearest-neighbour tight-binding model of graphene, its
band energies, the Pauli matrices, and the linearised (Dirac) Hamiltonians, following
F. Utermohlen, *Tight-Binding Model for Graphene* (September 12, 2018), Eqs. (9), (10),
(12), (14), (25), (26), (31), (33).

Here `a` is the carbon–carbon distance and `t` the nearest-neighbour hopping amplitude.
-/

namespace GrapheneTightBinding

/-- The structure factor `Δ_k = ∑_δ exp(i k·δ)`, the sum running over the three
nearest-neighbour vectors. (Eq. 10) -/
noncomputable def Delta (a : ℝ) (k : ℝ × ℝ) : ℂ :=
  ∑ j : Fin 3, Complex.exp (Complex.I * (dotp k (nnVec a j) : ℝ))

/-- The `2 × 2` Bloch Hamiltonian `h(k) = -t * !![0, Δ_k; conj Δ_k, 0]` in the
sublattice basis `(A, B)`. (Eq. 9) -/
noncomputable def hMat (a t : ℝ) (k : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  -(t : ℂ) • !![0, Delta a k; (starRingEnd ℂ) (Delta a k), 0]

/-- The upper band energy `E₊(k) = t |Δ_k|`; the lower band is its negative. -/
noncomputable def bandEnergy (a t : ℝ) (k : ℝ × ℝ) : ℝ := t * ‖Delta a k‖

/-- The function `f(k) = 2 cos(√3 k_y a) + 4 cos(3 k_x a/2) cos(√3 k_y a/2)`. (Eq. 14) -/
noncomputable def bandFun (a : ℝ) (k : ℝ × ℝ) : ℝ :=
  2 * Real.cos (Real.sqrt 3 * k.2 * a) +
    4 * Real.cos (3 * k.1 * a / 2) * Real.cos (Real.sqrt 3 * k.2 * a / 2)

/-- The Pauli matrix `σ_x`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli matrix `σ_y`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli matrix `σ_z`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Fermi velocity `v_F = 3at/2` (in units with `ħ = 1`). (Eq. 26) -/
noncomputable def fermiVel (a t : ℝ) : ℝ := 3 * a * t / 2

/-- The linearised Hamiltonian at the Dirac point `K`:
`v_F (q_x σ_x - q_y σ_y)`. (Eqs. 25, 27) -/
noncomputable def diracHamK (a t : ℝ) (q : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (fermiVel a t : ℂ) • ((q.1 : ℂ) • pauliX - (q.2 : ℂ) • pauliY)

/-- The linearised Hamiltonian at the Dirac point `K'`:
`v_F (q_x σ_x + q_y σ_y)`. (Eq. 31) -/
noncomputable def diracHamKp (a t : ℝ) (q : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (fermiVel a t : ℂ) • ((q.1 : ℂ) • pauliX + (q.2 : ℂ) • pauliY)

/-- The massive (gapped) Dirac Hamiltonian
`v_F (q_x σ_x + q_y σ_y + M σ_z)` obtained by adding a `σ_z` term. (Eq. 33) -/
noncomputable def massiveDiracHam (a t M : ℝ) (q : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (fermiVel a t : ℂ) • ((q.1 : ℂ) • pauliX + (q.2 : ℂ) • pauliY + (M : ℂ) • pauliZ)

end GrapheneTightBinding


