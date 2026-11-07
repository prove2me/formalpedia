-- Prove2me | Definitions.Def_TightQLB_Recording
-- name    : TightQLB_Recording
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:10.510538+00:00
-- url     : https://prove2.me/theorems/9e579209-2f86-4bed-951e-8b9f397b0631
-- title:
--   The recording representation: $\mathcal F$, recorded sets, $a_x$, $a_x^\dagger$, $D$, $b_z=N^{-1/2}\sum_x\chi_z(x)a_x$ and the progress measure $\lambda$
-- statement:
--   Let $H$ be a finite-dimensional space and $\mathcal F$ the space of all functions $f\mapsto\Phi(f)\in H$ of the sign function, with $\langle\Phi,\Phi'\rangle=\mathbb E_f\langle\Phi(f),\Phi'(f)\rangle$. For a set $S\subseteq\{0,1\}^n$ let $\chi_S(f)=\prod_{y\in S}f(y)$, with $\chi_\emptyset=1$. Every $\Phi$ expands as
--
--   $$
--   \Phi=\sum_S\chi_S\Phi_S,\qquad\Phi_S=\mathbb E_f[\chi_S(f)\Phi(f)]\in H.
--   $$
--
--   $\mathcal X_x$ is multiplication by $f(x)$. The operators $a_x$ and $a_x^\dagger$ are given on the basis by $a_x(\chi_Sh)=\mathbf 1[x\in S]\chi_{S\setminus\{x\}}h$ and $a_x^\dagger(\chi_Sh)=\mathbf 1[x\notin S]\chi_{S\cup\{x\}}h$; further $n_x=a_x^\dagger a_x$, $D=\sum_xn_x$, and
--
--   $$
--   b_z=\frac1{\sqrt N}\sum_x\chi_z(x)a_x,\qquad\lambda(\Phi)=\Bigl(\sum_z\|b_z^2\Phi\|^2\Bigr)^{1/2}.
--   $$
--
--   An operator $T$ on $H$ acts on $\mathcal F$ pointwise. These operators carry the whole analysis: the score is a sum of norms of $(b_z+b_z^\dagger)\Psi_z$, and $\lambda$ is the progress measure bounded under queries.
--
--   **Formalization Note** An element of $\mathcal F$ is `Fn n H = (Qubits n → Bool) → H → ℂ`, for a finite type `H`. `ip` is conjugate-linear in its first argument and averages over $f$ (it does not sum), and `nsq Φ` is the real part of `ip Φ Φ`. `aOp` and `aOpAdj` are the basis formulas extended linearly through the expansion (they are defined from `coeff`). $b_z^\dagger$ is `bOpAdj z`, with the same real coefficients as `bOp z`.
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), §4.1, Eqs. (19)–(23), pp. 21–22 (PDF pp. 24–25); §4.2, Eq. (27), p. 24 (PDF p. 27)

import Mathlib
import Definitions.Def_TightQLB_Fourier
open QAlgorithms

namespace TightQLB

/-!
# The recording representation: the space `F`, recorded sets, removal operators, progress measure

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…), §4.1, Eqs. (19)–(23),
pp.21–22 (PDF pp.24–25), and §4.2, Eq. (27), p.24 (PDF p.27).

For a finite-dimensional space `H`, `F` is the space of functions `f ↦ Φ(f) ∈ H` of the sign function,
with `⟨Φ, Φ′⟩ = E_f⟨Φ(f), Φ′(f)⟩`. Every `Φ` expands as `Φ = Σ_S χ_S Φ_S`, `Φ_S = E_f[χ_S(f)Φ(f)]`,
with `χ_S(f) = Π_{y∈S} f(y)` (19). `𝒳_x` is multiplication by `f(x)` (20); `a_x(χ_S h) = 1[x ∈ S]χ_{S∖{x}} h`
and `a_x†(χ_S h) = 1[x ∉ S]χ_{S∪{x}} h` (21); `n_x = a_x† a_x`, `D = Σ_x n_x`;
`b_z = N^{−1/2} Σ_x χ_z(x) a_x` (23); `λ(Φ) = (Σ_z ‖b_z² Φ‖²)^{1/2}` (27).

**Formalization Note.**
* `H` is the coordinate space of a finite type `H`; an element of `F` is `Fn n H = (Qubits n → Bool) → H → ℂ`
  (sign functions encoded by bit functions, `f(x) = (−1)^{fb x}`).
* `ip` is conjugate-linear in its first argument and is the **average** over `f`, so a state of norm 1
  for every `f` has `nsq = 1`. `nsq Φ = Re ⟨Φ, Φ⟩ = ‖Φ‖²`.
* `aOp x` and `aOpAdj x` are (21) extended linearly through the expansion (19): they are defined from
  the coefficients `coeff Φ S = Φ_S`. `b_z†` is `bOpAdj z = N^{−1/2} Σ_x χ_z(x) a_x†` (χ is real).
* An operator `T` on `H` acts pointwise: `pw T Φ = (f ↦ TΦ(f))`.
* `N^{−1/2}` is `(Real.sqrt (2^n))⁻¹`.
-/

/-- §4.1, p.21 (PDF p.24): the space `F` of functions from sign functions to `H`. -/
abbrev Fn (n : ℕ) (H : Type) := (Qubits n → Bool) → H → ℂ

variable {n : ℕ} {H : Type} [Fintype H]

/-- §4.1, p.21 (PDF p.24): `⟨Φ, Ψ⟩ = E_f ⟨Φ(f), Ψ(f)⟩`, conjugate-linear in the first argument. -/
noncomputable def ip (Φ Ψ : Fn n H) : ℂ :=
  (Fintype.card (Qubits n → Bool) : ℂ)⁻¹ * ∑ fb, ∑ h, star (Φ fb h) * Ψ fb h

/-- `‖Φ‖² = E_f ‖Φ(f)‖²`. -/
noncomputable def nsq (Φ : Fn n H) : ℝ :=
  (ip Φ Φ).re

/-- §4.1, p.21 (PDF p.24): the character `χ_S(f) = Π_{y ∈ S} f(y)` of a set `S`, with `χ_∅ = 1`. -/
noncomputable def charS (S : Finset (Qubits n)) (fb : Qubits n → Bool) : ℝ :=
  ∏ y ∈ S, fval fb y

/-- Eq. (19), p.21 (PDF p.24): the coefficient `Φ_S = E_f[χ_S(f) Φ(f)] ∈ H`. -/
noncomputable def coeff {H : Type} (Φ : Fn n H) (S : Finset (Qubits n)) : H → ℂ :=
  fun h => (Fintype.card (Qubits n → Bool) : ℂ)⁻¹ * ∑ fb, (charS S fb : ℂ) * Φ fb h

/-- Eq. (20), p.21 (PDF p.24): `𝒳_x`, multiplication by `f(x)`. -/
noncomputable def mulX {H : Type} (x : Qubits n) (Φ : Fn n H) : Fn n H :=
  fun fb h => (fval fb x : ℂ) * Φ fb h

/-- Eq. (21), p.21 (PDF p.24): the removal operator `a_x`, `a_x(χ_S h) = 1[x ∈ S] χ_{S∖{x}} h`,
extended linearly through (19). -/
noncomputable def aOp {H : Type} (x : Qubits n) (Φ : Fn n H) : Fn n H :=
  fun fb h => ∑ S ∈ Finset.univ.filter (fun S : Finset (Qubits n) => x ∈ S),
    (charS (S.erase x) fb : ℂ) * coeff Φ S h

/-- Eq. (21), p.21 (PDF p.24): the recording operator `a_x†`, `a_x†(χ_S h) = 1[x ∉ S] χ_{S∪{x}} h`,
extended linearly through (19). -/
noncomputable def aOpAdj {H : Type} (x : Qubits n) (Φ : Fn n H) : Fn n H :=
  fun fb h => ∑ S ∈ Finset.univ.filter (fun S : Finset (Qubits n) => x ∉ S),
    (charS (insert x S) fb : ℂ) * coeff Φ S h

/-- (22), p.22 (PDF p.25): the number operator `n_x = a_x† a_x`. -/
noncomputable def numOp {H : Type} (x : Qubits n) (Φ : Fn n H) : Fn n H :=
  aOpAdj x (aOp x Φ)

/-- p.22 (PDF p.25): `D = Σ_x n_x`, which counts the recorded points. -/
noncomputable def Dop {H : Type} (Φ : Fn n H) : Fn n H :=
  ∑ x, numOp x Φ

/-- Eq. (23), p.22 (PDF p.25): `b_z = N^{−1/2} Σ_x χ_z(x) a_x`. -/
noncomputable def bOp {H : Type} (z : Qubits n) (Φ : Fn n H) : Fn n H :=
  (Real.sqrt ((2 : ℝ) ^ n))⁻¹ • ∑ x, chi z x • aOp x Φ

/-- The adjoint `b_z† = N^{−1/2} Σ_x χ_z(x) a_x†` of (23) (the characters are real). -/
noncomputable def bOpAdj {H : Type} (z : Qubits n) (Φ : Fn n H) : Fn n H :=
  (Real.sqrt ((2 : ℝ) ^ n))⁻¹ • ∑ x, chi z x • aOpAdj x Φ

/-- p.21 (PDF p.24): an operator `T` on `H` acting pointwise on `F`, `(TΦ)(f) = TΦ(f)`. -/
def pw (T : Matrix H H ℂ) (Φ : Fn n H) : Fn n H :=
  fun fb => T.mulVec (Φ fb)

/-- Eq. (27), p.24 (PDF p.27): the progress measure `λ(Φ) = (Σ_z ‖b_z² Φ‖²)^{1/2}`. -/
noncomputable def lam (Φ : Fn n H) : ℝ :=
  Real.sqrt (∑ z, nsq (bOp z (bOp z Φ)))

end TightQLB


