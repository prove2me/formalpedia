-- Prove2me | Definitions.Def_KramersWannier_defs
-- name    : KramersWannier_defs
-- status  : Definition
-- author  : @Alien60
-- created : 2026-10-10T13:46:27.087366+00:00
-- url     : https://prove2.me/theorems/e9a8350e-e0df-43ba-988e-2cee6abf1648
-- title:
--   Pauli operators, Z2 symmetry, translation and the Kramers-Wannier operator on a periodic qubit chain
-- statement:
--   For $L$ qubits on a ring: basis labels `Config L` $=(\mathbb Z/2)^L$, operators `Op L` (complex matrices indexed by configurations), the sign `sgn` $a\mapsto(-1)^a$, Pauli operators `pauliX j` (flip spin $j$) and `pauliZ j` (diagonal $(-1)^{s_j}$), the $\mathbb Z_2$ symmetry `eta` $=\prod_jX_j$ (flip all spins), the translation `transl` ($T|s\rangle=|s'\rangle$, $s'_k=s_{k-1}$, indices mod $L$), and the Kramers-Wannier operator `kwD` with $\langle t|\mathsf D|s\rangle=2^{-L/2}(-1)^{\sum_k t_k(s_k+s_{k+1})}$.
-- source:
--   N. Seiberg, S. Seifnashri, S.-H. Shao, Non-invertible symmetries and LSM-type constraints on a tensor product Hilbert space, SciPost Phys. 16, 154 (2024), https://arxiv.org/abs/2401.12281, §1.1 eqs. (1.1)-(1.5), §2.1 eq. (2.10), §2.4.1 eqs. (2.64)-(2.65), footnote 1

import Mathlib

/-!
# The Kramers–Wannier operator on a periodic qubit chain (Seiberg–Seifnashri–Shao 2024)

N. Seiberg, S. Seifnashri, S.-H. Shao, *Non-invertible symmetries and LSM-type constraints on a
tensor product Hilbert space*, SciPost Phys. 16, 154 (2024), arXiv:2401.12281, §1.1 and §2.

A chain of `L` qubits with periodic boundary conditions (site `j` and site `j + L` are identified,
realised by modular arithmetic in `Fin L`). The Hilbert space `(ℂ²)^{⊗L}` is identified with
functions on the computational (`Z`-eigen)basis `Config L = Fin L → ZMod 2`, where `s j = 0`
means `Z_j = +1` and `s j = 1` means `Z_j = -1`. Operators are complex matrices indexed by
`Config L`.

* `pauliX j`, `pauliZ j`: the Pauli operators on site `j` (`X_j` flips `s j`, `Z_j = (-1)^{s j}`);
* `eta`: the `ℤ₂` symmetry `η = ∏_j X_j` (flips every spin), eq. (1.2);
* `transl`: the lattice translation `T`, with `T X_j T⁻¹ = X_{j+1}`, `T Z_j T⁻¹ = Z_{j+1}`,
  eqs. (1.1), (2.10); in the basis, `T |s⟩ = |s'⟩` with `s'_{k} = s_{k-1}`;
* `kwD`: the Kramers–Wannier operator `D` with matrix elements
  `⟨t| D |s⟩ = 2^{-L/2} (-1)^{∑_k t_k (s_k + s_{k+1})}`.
  This explicit formula is taken as the definition; it is the operator satisfying (1.4)–(1.5) and
  (2.65) in the paper's normalisation (footnote 1). Its equality with the matrix-product presentation
  (2.64) is not part of this development.
-/

namespace KramersWannier

/-- Computational-basis labels of `L` qubits: `s j ∈ ZMod 2` is the `Z_j` eigenvalue `(-1)^{s j}`. -/
abbrev Config (L : ℕ) := Fin L → ZMod 2

/-- The sign `(-1)^a` for `a ∈ ZMod 2`. -/
def sgn (a : ZMod 2) : ℂ := if a = 0 then 1 else -1

/-- Operators on `(ℂ²)^{⊗L}`, as matrices in the computational basis. -/
abbrev Op (L : ℕ) := Matrix (Config L) (Config L) ℂ

variable (L : ℕ)

/-- Pauli `X_j`: flips the spin on site `j`, `X_j |s⟩ = |s + e_j⟩`. -/
def pauliX (j : Fin L) : Op L := fun t s => if t = s + Pi.single j 1 then 1 else 0

/-- Pauli `Z_j`: diagonal, `Z_j |s⟩ = (-1)^{s j} |s⟩`. -/
def pauliZ (j : Fin L) : Op L := Matrix.diagonal fun s => sgn (s j)

/-- The `ℤ₂` symmetry operator `η = ∏_j X_j` (eq. (1.2)): flips every spin. -/
def eta : Op L := fun t s => if t = s + 1 then 1 else 0

/-- Lattice translation `T` (eqs. (1.1), (2.10): `T X_j T⁻¹ = X_{j+1}`):
`T |s⟩ = |s'⟩` with `s'_k = s_{k-1}`, indices mod `L`. -/
def transl [NeZero L] : Op L := fun u s => if u = (fun k => s (k - 1)) then 1 else 0

/-- The non-invertible Kramers–Wannier operator `D` (eqs. (1.4), (1.5), (2.64)):
`⟨t| D |s⟩ = 2^{-L/2} (-1)^{∑_k t_k (s_k + s_{k+1})}`, indices mod `L`. -/
noncomputable def kwD [NeZero L] : Op L :=
  fun t s => ((Real.sqrt 2 : ℂ)⁻¹) ^ L * sgn (∑ k, t k * (s k + s (k + 1)))

end KramersWannier


