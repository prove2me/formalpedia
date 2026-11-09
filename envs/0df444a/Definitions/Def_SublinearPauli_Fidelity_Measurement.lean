-- Prove2me | Definitions.Def_SublinearPauli_Fidelity_Measurement
-- name    : SublinearPauli_Fidelity_Measurement
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:41:36.411973+00:00
-- url     : https://prove2.me/theorems/9dd3c64b-189a-4ace-ae16-595d53d44f8c
-- title:
--   §4.2, P1 and eq. (1) — Pauli basis POVM, Born law, shadow overlap $s_\rho$, biased norm $N_\sigma$ and Pauli shadow norm
-- statement:
--   A **Pauli basis** is $B=B_1\otimes\cdots\otimes B_N\in\mathcal B=\{X,Y,Z\}^{\otimes N}$; there are $3^N$ of them. Measuring a copy of a state $\sigma$ in basis $B$ is the POVM with $d=2^N$ outcomes $x\in\{-1,1\}^N$,
--   $$M_x^B=\bigotimes_{i=1}^N\frac{I+x_iB_i}{2},$$
--   and by Born's rule outcome $x$ has probability $\Pr[X_B=x]=\operatorname{Tr}[\sigma M_x^B]$.
--
--   For $S\subseteq[N]$ write $B^S$ for the Pauli word equal to $B_i$ on $S$ and $I$ off $S$, and $\chi_S(x)=\prod_{i\in S}x_i$. For a target $O$ (in the paper, the known state $\rho$), the **shadow overlap statistic** of protocol P1 is
--   $$s_O(B,x)=\frac1{\sqrt d}\sum_{S\subseteq[N]}\frac{\hat O(B^S)\,\chi_S(x)}{3^{N-|S|}}.$$
--   The **$\sigma$-biased Pauli norm** of $O$ is
--   $$N_\sigma(O)=\sum_{B\in\mathcal B}\mathbb E_{x\sim\sigma,B}\bigl[s_O(B,x)^2\bigr],$$
--   the sum over bases not normalized. The squared **Pauli shadow norm** is
--   $$\bigl(\|O\|^{(\mathrm{pauli})}_{\mathrm{shadow}}\bigr)^2=\frac1d\max_{\sigma}\ \mathbb E_{B\sim\mathcal B}\Bigl[\mathbb E_{x\sim\sigma,B}\Bigl[\Bigl(\sum_{S\subseteq[N]}\hat O(B^S)\,3^{|S|}\chi_S(x)\Bigr)^2\Bigr]\Bigr],$$
--   with $B$ uniform on $\mathcal B$ and the maximum over all $N$-qubit density matrices $\sigma$.
--
--   These are the measurement model, the estimator and the second-moment quantities in which Theorems 1 and 2 are stated.
--
--   **Formalization Note** The POVM element is written entrywise as the product over qubits of the entries of $(I+x_iB_i)/2$, with the same single-qubit matrices as the Pauli words; outcomes $x$ are points of the published hypercube `PSDPolyApprox.Cube` and $\chi_S$ is the published `PSDPolyApprox.chi`. Born probabilities are the real part of the trace. The outer optimization in the shadow norm is a supremum over density matrices; Theorem 2 states that it is attained, so it is a maximum.
--
--   The single-qubit factors reuse `DirectFidelity.State.pauli1` at the same four letter labels. No direct-fidelity sampling law or pure-state promise is used.
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #230 (October 2026), PDF sha256 a007d4d449494d7b3589233107d1fc0190d256341e1bcbb1b95965363d6e10c4, §4.2 p.9 (M_x^B, Born rule, B^S, χ_S), protocol P1 p.6 (s_i), Pauli shadow norm p.6, eq. (1) p.12 (N_σ(ρ))

import Mathlib
import Definitions.Def_SublinearPauli_Fidelity_Pauli
import Definitions.Def_PSDPolyApprox_chi

open ClassicalShadow.Linear

namespace SublinearPauli.Fidelity

/-- A single-qubit measurement axis `X, Y` or `Z`. -/
inductive Axis
  | X | Y | Z
  deriving DecidableEq, Repr

instance : Fintype Axis :=
  ⟨{Axis.X, Axis.Y, Axis.Z}, by intro A; cases A <;> simp⟩

/-- The letter of an axis. -/
def Axis.toLetter : Axis → Letter
  | .X => .X
  | .Y => .Y
  | .Z => .Z

/-- A Pauli basis `B ∈ 𝓑 = {X, Y, Z}^{⊗N}` (P1, p.6; §4.2, p.9). -/
abbrev PauliBasis (N : ℕ) := Fin N → Axis

/-- `B^S = ⊗_i (1{i ∈ S} B_i + 1{i ∉ S} I)` (p.6). -/
def restrict {N : ℕ} (B : PauliBasis N) (S : Finset (Fin N)) : PauliString N :=
  fun j => if j ∈ S then (B j).toLetter else Letter.I

/-- The single-qubit Pauli matrix of a letter: the factor `i^{xz} X^x Z^z` of the published Pauli
strings, entry `(a, b)` equal to `i^{xz} (-1)^{z b}` if `a = b + x` and `0` otherwise. -/
noncomputable def pauli1 (L : Letter) : Matrix (Fin 2) (Fin 2) ℂ :=
  DirectFidelity.State.pauli1 L.index

/-- The Pauli-basis POVM element `M_x^B = ⊗_{i=1}^N (I + x_i B_i)/2`, for `B ∈ 𝓑` and
`x ∈ {−1, 1}^N` (§4.2, p.9), as the entrywise product of the single-qubit factors. -/
noncomputable def povm {N : ℕ} (B : PauliBasis N) (x : PSDPolyApprox.Cube N) : Op N :=
  Matrix.of fun a b => ∏ j, (((if a j = b j then 1 else 0) +
    (((x j : ℤ) : ℂ)) * pauli1 (B j).toLetter (a j) (b j)) / 2)

/-- Born's rule: the probability `Pr[X_B = x] = Tr[σ M_x^B]` of outcome `x` when a copy of `σ` is
measured in basis `B` (real part; real for Hermitian `σ`). -/
noncomputable def bornProb {N : ℕ} (σ : Op N) (B : PauliBasis N) (x : PSDPolyApprox.Cube N) : ℝ :=
  (σ * povm B x).trace.re

/-- The shadow overlap statistic of P1 (p.6):
`s_O(B, x) = (1/√d) Σ_{S ⊆ [N]} Ô(B^S) χ_S(x) / 3^{N−|S|}`. -/
noncomputable def overlapStat {N : ℕ} (O : Op N) (B : PauliBasis N) (x : PSDPolyApprox.Cube N) : ℝ :=
  (1 / Real.sqrt ((2 : ℝ) ^ N)) *
    ∑ S : Finset (Fin N), coeff O (restrict B S) * PSDPolyApprox.chi S x / (3 : ℝ) ^ (N - S.card)

/-- The `σ`-biased Pauli norm (eq. (1), p.12):
`N_σ(O) = Σ_{B ∈ 𝓑} E_{x ∼ σ, B}[ s_O(B, x)² ]`, the inner expectation under Born's rule; the sum
over `B` is not normalised. -/
noncomputable def biasedNorm {N : ℕ} (σ O : Op N) : ℝ :=
  ∑ B : PauliBasis N, ∑ x : PSDPolyApprox.Cube N, bornProb σ B x * overlapStat O B x ^ 2

/-- The squared Pauli shadow norm (p.6):
`(‖O‖_shadow^{(pauli)})² = (1/d) max_σ E_{B ∼ 𝓑}[ E_σ[ (Σ_{S ⊆ [N]} Ô(B^S) 3^{|S|} χ_S(x))² ] ]`,
`B` uniform on the `3^N` bases, the outer optimisation over all density matrices `σ`
(written as a supremum; Theorem 2 asserts it is attained). -/
noncomputable def shadowNormSq {N : ℕ} (O : Op N) : ℝ :=
  (1 / (2 : ℝ) ^ N) * ⨆ σ : {σ : Op N // WildeQIT.IsDensityOperator σ},
    (1 / (3 : ℝ) ^ N) * ∑ B : PauliBasis N, ∑ x : PSDPolyApprox.Cube N,
      bornProb σ.1 B x * (∑ S : Finset (Fin N),
        coeff O (restrict B S) * (3 : ℝ) ^ S.card * PSDPolyApprox.chi S x) ^ 2

end SublinearPauli.Fidelity


