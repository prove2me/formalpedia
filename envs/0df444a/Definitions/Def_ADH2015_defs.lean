-- Prove2me | Definitions.Def_ADH2015_defs
-- name    : ADH2015_defs
-- status  : Definition
-- author  : @Alien60
-- created : 2026-10-09T08:59:27.382544+00:00
-- url     : https://prove2.me/theorems/463544a1-7f09-4a44-9830-0b7ac49c1d99
-- title:
--   Code subspaces, logical operators and subsystem representations; the three-qutrit and two-qubit codes (ADH 2015)
-- statement:
--   Shared vocabulary of the mission, for a finite-dimensional $\mathcal H=\mathcal H_E\otimes\mathcal H_{\bar E}$ ($E$ first) and a code subspace $\mathcal H_{\mathcal C}$: operators **acting within** the code subspace ($O$ and $O^\dagger$ preserve it; footnote 8, Eq. (3.26)); **representations** of such an operator on $\bar E$ (by $\mathbb 1_E\otimes Y$) or on $E$ (by $X\otimes\mathbb 1_{\bar E}$), reproducing $O$ and $O^\dagger$ on code states (Eqs. (3.21), (3.27)); and the erasure-correction condition (3.19) that the projection of every $X_E$ onto the code subspace is proportional to the identity. It also defines the three-qutrit code $|\tilde\imath\rangle=\tfrac1{\sqrt3}\sum_a|a,a+i,a+2i\rangle$ (Eq. (3.3)), encoded states, single-qutrit reduced density matrices, the permutation $U_{12}$ of Eq. (3.6), and the two-qubit code of Section 3.5 spanned by $(|00\rangle+|11\rangle)/\sqrt2$, $(|01\rangle+|10\rangle)/\sqrt2$ with its logical $X$ and $Z$ and the Pauli $X$.
-- source:
--   A. Almheiri, X. Dong, D. Harlow, Bulk Locality and Quantum Error Correction in AdS/CFT, JHEP 04 (2015) 163, https://arxiv.org/abs/1411.7041v3, Section 3 (Eqs. (3.3), (3.6), (3.19), (3.21), (3.26)–(3.27)), footnote 8

import Mathlib

/-!
# Bulk locality and quantum error correction: erasure correction on a code subspace

Definitions for the mission drafted from A. Almheiri, X. Dong and D. Harlow,
*Bulk Locality and Quantum Error Correction in AdS/CFT*, JHEP 04 (2015) 163,
arXiv:1411.7041v3, Section 3 and Appendix B.

The physical Hilbert space is a tensor product `ℋ_E ⊗ ℋ_Ē` of finite-dimensional factors,
encoded as vectors indexed by `e × ē` (`E` = erased part first, `Ē` = retained part second).
A code subspace is a complex subspace `C` of these vectors. Operators are complex matrices;
`Oᴴ` is the Hermitian conjugate and `⟨w|u⟩ = star w ⬝ᵥ u`.
-/

namespace ADH2015

open Matrix
open scoped Kronecker

noncomputable section

/-- Footnote 8 / Eq. (3.26): `O` acts within the code subspace together with its Hermitian
conjugate, i.e. `O` and `O†` both map `C` into `C`. -/
def ActsWithin {ι : Type*} [Fintype ι] (C : Submodule ℂ (ι → ℂ)) (O : Matrix ι ι ℂ) : Prop :=
  ∀ v ∈ C, O *ᵥ v ∈ C ∧ Oᴴ *ᵥ v ∈ C

/-- Eqs. (3.21)/(3.27): `O` can be represented by an operator `O_Ē = 𝟙_E ⊗ Y` acting only on
`Ē`, in the sense that `O_Ē|ψ⟩ = O|ψ⟩` and `O_Ē†|ψ⟩ = O†|ψ⟩` for every `|ψ⟩` in the code
subspace. -/
def HasRepOnBar {e ē : Type*} [Fintype e] [Fintype ē] [DecidableEq e]
    (C : Submodule ℂ (e × ē → ℂ)) (O : Matrix (e × ē) (e × ē) ℂ) : Prop :=
  ∃ Y : Matrix ē ē ℂ, ∀ v ∈ C,
    ((1 : Matrix e e ℂ) ⊗ₖ Y) *ᵥ v = O *ᵥ v ∧ ((1 : Matrix e e ℂ) ⊗ₖ Y)ᴴ *ᵥ v = Oᴴ *ᵥ v

/-- The same notion for the first factor: `O` is represented on the code subspace by an
operator `X ⊗ 𝟙_Ē` acting only on `E` (together with its Hermitian conjugate). -/
def HasRepOnE {e ē : Type*} [Fintype e] [Fintype ē] [DecidableEq ē]
    (C : Submodule ℂ (e × ē → ℂ)) (O : Matrix (e × ē) (e × ē) ℂ) : Prop :=
  ∃ X : Matrix e e ℂ, ∀ v ∈ C,
    (X ⊗ₖ (1 : Matrix ē ē ℂ)) *ᵥ v = O *ᵥ v ∧ (X ⊗ₖ (1 : Matrix ē ē ℂ))ᴴ *ᵥ v = Oᴴ *ᵥ v

/-- Eq. (3.19): for every operator `X_E` acting on `E`, its projection onto the code subspace
is proportional to the identity: `⟨ψ̃'|X_E|ψ̃⟩ = C(X) ⟨ψ̃'|ψ̃⟩` for all code states (equivalently
`⟨ĩ|X_E|j̃⟩ = δ_{ij} C(X)` in an orthonormal basis of the code subspace). This is the
condition that the erasure of `E` is correctable. -/
def CorrectsErasureOfE {e ē : Type*} [Fintype e] [Fintype ē] [DecidableEq ē]
    (C : Submodule ℂ (e × ē → ℂ)) : Prop :=
  ∀ X : Matrix e e ℂ, ∃ c : ℂ, ∀ v ∈ C, ∀ w ∈ C,
    star w ⬝ᵥ ((X ⊗ₖ (1 : Matrix ē ē ℂ)) *ᵥ v) = c * (star w ⬝ᵥ v)

/-! ### The three-qutrit code (Section 3.1) -/

/-- A qutrit, with basis `|0⟩, |1⟩, |2⟩`. Addition is modulo 3. -/
abbrev Qutrit := Fin 3

/-- Eq. (3.3): the code basis state `|ĩ⟩ = (1/√3) ∑_{a} |a, a+i, a+2i⟩` (indices mod 3) of three
qutrits, i.e. `|0̃⟩ = (|000⟩+|111⟩+|222⟩)/√3`, `|1̃⟩ = (|012⟩+|120⟩+|201⟩)/√3`,
`|2̃⟩ = (|021⟩+|102⟩+|210⟩)/√3`. Three-qutrit vectors are indexed by `((q₁, q₂), q₃)`. -/
def codeKet (i : Qutrit) : (Qutrit × Qutrit) × Qutrit → ℂ :=
  fun x => if x.1.2 = x.1.1 + i ∧ x.2 = x.1.1 + i + i then ((1 / Real.sqrt 3 : ℝ) : ℂ) else 0

/-- Eq. (3.2): the encoded state `|ψ̃⟩ = ∑ᵢ aᵢ |ĩ⟩`. -/
def encode (a : Qutrit → ℂ) : (Qutrit × Qutrit) × Qutrit → ℂ :=
  ∑ i, a i • codeKet i

/-- The reduced density matrix of qutrit `k` (`k = 0, 1, 2` for the first, second, third
qutrit) of a three-qutrit vector `ψ`, obtained by tracing out the other two qutrits of
`|ψ⟩⟨ψ|`. -/
def reducedQutrit (ψ : (Qutrit × Qutrit) × Qutrit → ℂ) (k : Fin 3) : Matrix Qutrit Qutrit ℂ :=
  Matrix.of fun x y =>
    if k = 0 then ∑ b, ∑ c, ψ ((x, b), c) * star (ψ ((y, b), c))
    else if k = 1 then ∑ a, ∑ c, ψ ((a, x), c) * star (ψ ((a, y), c))
    else ∑ a, ∑ b, ψ ((a, b), x) * star (ψ ((a, b), y))

/-- Eq. (3.6): the permutation of two-qutrit basis states
`|00⟩→|00⟩, |11⟩→|01⟩, |22⟩→|02⟩, |01⟩→|12⟩, |12⟩→|10⟩, |20⟩→|11⟩, |02⟩→|21⟩, |10⟩→|22⟩,
|21⟩→|20⟩`. -/
def u12Map (x : Qutrit × Qutrit) : Qutrit × Qutrit :=
  (![![(0, 0), (1, 2), (2, 1)], ![(2, 2), (0, 1), (1, 0)], ![(1, 1), (2, 0), (0, 2)]] :
    Fin 3 → Fin 3 → Qutrit × Qutrit) x.1 x.2

/-- Eq. (3.6): the operator `U₁₂` on the first two qutrits, `U₁₂|x⟩ = |u12Map x⟩`. -/
def U12 : Matrix (Qutrit × Qutrit) (Qutrit × Qutrit) ℂ :=
  Matrix.of fun y x => if y = u12Map x then 1 else 0

/-! ### The two-qubit example (Section 3.5) -/

/-- A qubit; two-qubit vectors are indexed by `(q₁, q₂)`, the first qubit first. -/
abbrev Qubit := Fin 2

/-- `(|00⟩ + |11⟩)/√2`. -/
def phiPlus : Qubit × Qubit → ℂ :=
  fun x => if x.1 = x.2 then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0

/-- `(|01⟩ + |10⟩)/√2`. -/
def psiPlus : Qubit × Qubit → ℂ :=
  fun x => if x.1 ≠ x.2 then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0

/-- Section 3.5: the two-qubit code subspace spanned by `(|00⟩+|11⟩)/√2` and `(|01⟩+|10⟩)/√2`. -/
def twoQubitCode : Submodule ℂ (Qubit × Qubit → ℂ) :=
  Submodule.span ℂ {phiPlus, psiPlus}

/-- The logical `X`, exchanging the two code states: `|ψ₊⟩⟨φ₊| + |φ₊⟩⟨ψ₊|`. -/
def logicalX : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ :=
  Matrix.of fun p q => psiPlus p * star (phiPlus q) + phiPlus p * star (psiPlus q)

/-- The logical `Z`, with `(|00⟩+|11⟩)/√2` as `+1` and `(|01⟩+|10⟩)/√2` as `-1` eigenstate:
`|φ₊⟩⟨φ₊| - |ψ₊⟩⟨ψ₊|`. -/
def logicalZ : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ :=
  Matrix.of fun p q => phiPlus p * star (phiPlus q) - psiPlus p * star (psiPlus q)

/-- Pauli `X` (bit flip) on one qubit. -/
def pauliX : Matrix Qubit Qubit ℂ := !![0, 1; 1, 0]

end

end ADH2015


