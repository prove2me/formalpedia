-- Prove2me | Definitions.Def_AutoQMem_Lindblad_Supplement_SyndromeChannel
-- name    : AutoQMem_Lindblad_Supplement_SyndromeChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:38:47.73447+00:00
-- url     : https://prove2.me/theorems/9cfa34d9-23af-428d-8094-b0b938f2953a
-- title:
--   Syndrome-based quantum channel $Q_*$ and its induced discrete sector chains
-- statement:
--   Fix an $n$-qubit CSS code with parity checks $H_X,H_Z$ and stabilizer algebras $\mathcal A\supseteq\mathcal A_X,\mathcal A_Z$. A **syndrome-based quantum channel** is given by syndrome functions $f_{u_X,u_Z,\alpha}\in\mathcal A$, indexed by sector flips $u_X,u_Z\in\mathbb F_2^n$ and a finite label $\alpha$, with Kraus completeness $\sum_{u_X,u_Z,\alpha}f^\dagger_{u_X,u_Z,\alpha}f_{u_X,u_Z,\alpha}=I$, such that the **sector probability operators**
--   $$P^{(X)}_{u_X}=\sum_{u_Z,\alpha}f^\dagger_{u_X,u_Z,\alpha}f_{u_X,u_Z,\alpha}\in\mathcal A_X,\qquad P^{(Z)}_{u_Z}=\sum_{u_X,\alpha}f^\dagger_{u_X,u_Z,\alpha}f_{u_X,u_Z,\alpha}\in\mathcal A_Z .$$
--   The channel is
--   $$Q_*(\rho)=\sum_{u_X,u_Z,\alpha}K_{u_X,u_Z,\alpha}\,\rho\,K^\dagger_{u_X,u_Z,\alpha},\qquad K_{u_X,u_Z,\alpha}=X^{u_Z}Z^{u_X}f_{u_X,u_Z,\alpha}.$$
--   Its **induced sector chains** have flip probabilities $p_X(u\mid s)=P^{(X)}_u(s)$ (the syndrome eigenvalue at $s$) and one-step backward transition matrix
--   $$B_X(e,e')=\sum_u p_X(u\mid H_Xe)\,[e'=e\oplus u],$$
--   so that $B_X^r(e,y)=\Pr[\chi_r=y\mid\chi_0=e]$; the Z sector is symmetric. A map is **syndrome-based** if it is $Q_*$ for some such data.
--
--   These are the objects of the synchronous memory equivalence (Theorem 8) and of the 4D Toom channel (Theorem 3).
--
--   **Formalization Note** One finite label type is shared by all $(u_X,u_Z)$ (pad with zero operators). The syndrome eigenvalue is the base `eigX`, $\operatorname{Tr}(A\Pi^X_s)/\operatorname{Tr}(\Pi^X_s)$, whose real part is taken.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.35, eqs. (58)–(62), pp. 25–26 (PDF pp. 27–28); Definition 2.36, eqs. (63)–(68), p. 26 (PDF p. 28)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_CSSCode_eigX
open Matrix

namespace AutoQMem.Lindblad.Supplement

open AutoQMem.Lindblad

/-- **Syndrome-based quantum channel (its Kraus data).** Drechsler, Oreg, Aharonov, *Autonomous
Quantum Memories from Classical Stochastic Processes*, arXiv:2610.05589 (PDF of 2026-11-03),
Definition 2.35, eqs. (58)–(61), pp. 25–26 (PDF 27–28): "A CPTP map Q_* is syndrome-based for the
CSS code if it admits a Kraus representation Q_*(ρ) = Σ_{u_X,u_Z,α} K ρ K†, where
K_{u_X,u_Z,α} := X^{u_Z} Z^{u_X} f_{u_X,u_Z,α}, f_{u_X,u_Z,α} ∈ A, with u_X ∈ Ω_X and u_Z ∈ Ω_Z.
The Kraus completeness relation is Σ f† f = I. … P^{(X)}_{u_X} := Σ_{u_Z,α} f† f,
P^{(Z)}_{u_Z} := Σ_{u_X,α} f† f. We require the syndrome-based condition per sector
P^{(X)}_{u_X} ∈ A_X, P^{(Z)}_{u_Z} ∈ A_Z for every u_X, u_Z."

**Formalization Note.**
* `f uX uZ α` is the syndrome function `f_{u_X,u_Z,α}`; `α` ranges over one finite type `ι`
  shared by all `(u_X, u_Z)` (families with `(u_X, u_Z)`-dependent finite index sets are covered by
  padding with zero operators).
* The condition (61) is imposed on the sector probability operators, not on each `f`.
* The channel itself is `SyndromeChannel.apply`; it is CPTP by the Kraus form and completeness. -/
structure SyndromeChannel {n mX mZ : ℕ} (C : CSSCode n mX mZ) (ι : Type) [Fintype ι] : Type where
  /-- The syndrome functions `f_{u_X,u_Z,α}`. -/
  f : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ι → Op n
  /-- Every syndrome function lies in the stabilizer algebra `A` (eq. (59)). -/
  mem : ∀ uX uZ α, f uX uZ α ∈ C.alg
  /-- Kraus completeness `Σ_{u_X,u_Z,α} f† f = I`. -/
  complete : ∑ uX, ∑ uZ, ∑ α, (f uX uZ α)ᴴ * f uX uZ α = 1
  /-- Eq. (61), X part: `P^{(X)}_{u_X} = Σ_{u_Z,α} f† f ∈ A_X`. -/
  probX_mem : ∀ uX, ∑ uZ, ∑ α, (f uX uZ α)ᴴ * f uX uZ α ∈ C.algX
  /-- Eq. (61), Z part: `P^{(Z)}_{u_Z} = Σ_{u_X,α} f† f ∈ A_Z`. -/
  probZ_mem : ∀ uZ, ∑ uX, ∑ α, (f uX uZ α)ᴴ * f uX uZ α ∈ C.algZ

namespace SyndromeChannel

variable {n mX mZ : ℕ} {C : CSSCode n mX mZ} {ι : Type} [Fintype ι]

/-- The Kraus operator `K_{u_X,u_Z,α} = X^{u_Z} Z^{u_X} f_{u_X,u_Z,α}` (Definition 2.35, eq. (59)).
The physical Pauli `Z^{u_X}` produces the X-sector flip `u_X` (p. 26). -/
noncomputable def kraus (K : SyndromeChannel C ι) (uX uZ : Fin n → ZMod 2) (α : ι) : Op n :=
  pauliX uZ * pauliZ uX * K.f uX uZ α

/-- The channel `Q_*(ρ) = Σ_{u_X,u_Z,α} K ρ K†` (Definition 2.35, eq. (58)), Schrödinger picture. -/
noncomputable def apply (K : SyndromeChannel C ι) (ρ : Op n) : Op n :=
  ∑ uX, ∑ uZ, ∑ α, K.kraus uX uZ α * ρ * (K.kraus uX uZ α)ᴴ

/-- The X-sector probability operator `P^{(X)}_{u_X} := Σ_{u_Z,α} f† f` (eq. (60)). -/
noncomputable def probX (K : SyndromeChannel C ι) (uX : Fin n → ZMod 2) : Op n :=
  ∑ uZ, ∑ α, (K.f uX uZ α)ᴴ * K.f uX uZ α

/-- The Z-sector probability operator `P^{(Z)}_{u_Z} := Σ_{u_X,α} f† f` (eq. (60)). -/
noncomputable def probZ (K : SyndromeChannel C ι) (uZ : Fin n → ZMod 2) : Op n :=
  ∑ uX, ∑ α, (K.f uX uZ α)ᴴ * K.f uX uZ α

/-- The induced X-sector flip probabilities `p_X(u | s) := P^{(X)}_u(s)` (Definition 2.36,
eq. (63), p. 26, PDF 28).

**Formalization Note.** The syndrome eigenvalue is the base `CSSCode.eigX`; it is real and
nonnegative at valid syndromes (`P^{(X)}_u` is positive semidefinite and lies in `A_X`), and `.re`
only fixes the type. It is only evaluated at syndromes `H_X e`. -/
noncomputable def pX (K : SyndromeChannel C ι) (u : Fin n → ZMod 2) (s : Fin mX → ZMod 2) : ℝ :=
  (C.eigX (K.probX u) s).re

/-- The induced Z-sector flip probabilities `p_Z(u | s) := P^{(Z)}_u(s)` (Definition 2.36, eq. (64)). -/
noncomputable def pZ (K : SyndromeChannel C ι) (u : Fin n → ZMod 2) (s : Fin mZ → ZMod 2) : ℝ :=
  (C.eigZ (K.probZ u) s).re

/-- The one-step backward transition operator `B_X` of the induced X-sector chain (Definition 2.36,
eqs. (65)–(66), p. 26, PDF 28): `(B_X h)(e) = Σ_u p_X(u | H_X e) h(e ⊕ u)`.

**Formalization Note.** Written as the real matrix with `(B_X h)(e) = Σ_{e'} B_X e e' h(e')`, so
`B_X e e' = Pr[χ_{r+1} = e' | χ_r = e]` and `(B_X ^ r) e y = Pr[χ_r = y | χ_0 = e]` (eq. (68)). -/
noncomputable def BX (K : SyndromeChannel C ι) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℝ :=
  Matrix.of fun e e' => ∑ u, K.pX u (C.HX *ᵥ e) * if e' = e + u then 1 else 0

/-- The one-step backward transition operator `B_Z` (Definition 2.36, eq. (67)):
`(B_Z h)(e) = Σ_u p_Z(u | H_Z e) h(e ⊕ u)`. -/
noncomputable def BZ (K : SyndromeChannel C ι) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℝ :=
  Matrix.of fun e e' => ∑ u, K.pZ u (C.HZ *ᵥ e) * if e' = e + u then 1 else 0

end SyndromeChannel

/-- **A map is a syndrome-based quantum channel** (Definition 2.35): it equals the Kraus map of some
syndrome-based Kraus data, for some finite index type. -/
def IsSyndromeBased {n mX mZ : ℕ} (C : CSSCode n mX mZ) (Qm : Op n → Op n) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (K : SyndromeChannel C ι), K.apply = Qm

end AutoQMem.Lindblad.Supplement


