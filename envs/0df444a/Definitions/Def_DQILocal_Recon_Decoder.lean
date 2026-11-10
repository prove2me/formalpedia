-- Prove2me | Definitions.Def_DQILocal_Recon_Decoder
-- name    : DQILocal_Recon_Decoder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:06:16.761841+00:00
-- url     : https://prove2.me/theorems/b768b4b5-4a64-41e6-acec-92b6367e7b29
-- title:
--   Product states, POVMs, decoders, block success, symbol error and $t$-local estimates (Definitions 3.2, 3.4)
-- statement:
--   For a spectrum $\nu$ and $y\in\mathbb Z_q$ let $|\psi^\nu_y\rangle=\sum_z\sqrt{\nu(z)}\,\omega^{yz}|z\rangle$ (eq. (5)). For a codeword $c$ the received state is the product state $|\psi_c\rangle=\bigotimes_j|\psi^{p}_{c_j}\rangle$ of the product amplitude function.
--
--   A **decoder** (Definition 3.2) is a measurement (POVM) $\{F_{\hat c}\}_{\hat c\in\mathbb Z_q^m}$ on the $m$ qudits. With $c$ uniform on $C$:
--
--   1. its **block success** is $\Pr[\hat c=c]=\frac1{|C|}\sum_{c\in C}\langle\psi_c|F_c|\psi_c\rangle$;
--   2. its **symbol error at $j$** is $\Pr[\hat c_j\ne c_j]$.
--
--   The decoder makes a **$t$-local estimate at $i$** (Definition 3.4) if there is a POVM $\{E_y\}_{y\in\mathbb Z_q}$ on the qudits of $N_t(i)$ such that
--
--   $$\Pr[\hat c_i=y\mid c]=\operatorname{tr}\bigl((E_y\otimes I)|\psi_c\rangle\langle\psi_c|\bigr)\qquad\text{for every }c\in C\text{ and every }y .$$
--
--   `localSuccess` is the probability that a POVM $E$ on the qudits of $N_t(i)$ outputs $c_i$; `optLocal` is the largest probability with which a $t$-local estimate at $i$ equals $c_i$, i.e. the supremum of $1-\Pr[\hat c_i\ne c_i]$ over all decoders that make a $t$-local estimate at $i$.
--
--   **Formalization Note** States are vectors in $\mathbb C^{\mathbb Z_q^S}$ in the computational basis; a POVM has positive semidefinite elements summing to the identity. A measurement with ancillas and work registers is a POVM on the system (Naimark), so decoders and local estimates are POVMs. $E\otimes I$ is written entrywise: $E(x|_N,x'|_N)$ when $x,x'$ agree off $N$, else $0$. The set defining `optLocal` is nonempty and bounded by one.
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), eqs. (3), (5), p. 16; Definition 3.2, p. 17; Definition 3.4, p. 21; Corollary 5.6, p. 35 (optimum)

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra
import Definitions.Def_DQILocal_Recon_LocalConditions

namespace DQILocal.Recon

open scoped BigOperators ComplexOrder

/-- **The single-symbol states `|ψ^ν_y⟩`.**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), eq. (5), p. 16:
`|ψ^ν_y⟩ = Σ_{z ∈ ℤ_q} √ν(z) ω^{yz} |z⟩`, a vector of `ℂ^{ℤ_q}` in the computational basis. -/
noncomputable def psi {q : ℕ} [NeZero q] (ν : ZMod q → ℝ) (y : ZMod q) : ZMod q → ℂ :=
  fun z => (Real.sqrt (ν z) : ℂ) * omega q (y * z)

/-- **Product states.** For a finite set `S` of symbols and an assignment `c : S → ℤ_q`,
`psiProd ν c = ⊗_{s ∈ S} |ψ^ν_{c_s}⟩`, a vector of `ℂ^{ℤ_q^S}`:
`(psiProd ν c)(x) = Π_s √ν(x_s) ω^{c_s x_s}` (eqs. (3), (5), p. 16). With `S = [m]` and `ν = p`
this is the received state `|ψ_c⟩ = ⊗_j |ψ^p_{c_j}⟩` of the product amplitude function (p. 16). -/
noncomputable def psiProd {q : ℕ} [NeZero q] {S : Type} [Fintype S] (ν : ZMod q → ℝ)
    (c : S → ZMod q) : (S → ZMod q) → ℂ :=
  fun x => ∏ s, (Real.sqrt (ν (x s)) : ℂ) * omega q (c s * x s)

/-- A POVM with finite outcome set `O` on `ℂ^ι`: every element positive semidefinite, and the
elements sum to the identity (§3.4, p. 21; "measurement"). -/
def IsPOVM {O ι : Type} [Fintype O] [Fintype ι] [DecidableEq ι] (E : O → Matrix ι ι ℂ) : Prop :=
  (∀ o, (E o).PosSemidef) ∧ ∑ o, E o = 1

/-- `⟨ψ| M |ψ⟩` (real part): the probability of a POVM element `M` on the pure state `ψ`
(`tr(M |ψ⟩⟨ψ|)`). -/
noncomputable def expectVal {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) (ψ : ι → ℂ) : ℝ :=
  (dotProduct (star ψ) (M.mulVec ψ)).re

/-- The code `C` as a finite set (§3.2, p. 16). -/
noncomputable def codeFinset (q : ℕ) [NeZero q] {m : ℕ} {κ : Type} [Fintype κ]
    (B : Matrix (Fin m) κ Bool) : Finset (Fin m → ZMod q) := by
  classical
  exact Finset.univ.filter fun c => c ∈ code q B

/-- **Decoder outcome probability (Definition 3.2, p. 17).** A decoder is a POVM `F` on the `m`
received qudits with outcomes `ĉ ∈ ℤ_q^m`; `decProb p F c ĉ = ⟨ψ_c| F_ĉ |ψ_c⟩` is the probability
of the outcome `ĉ` on the received state `|ψ_c⟩ = ⊗_j |ψ^p_{c_j}⟩`.

**Formalization Note.** A measurement that uses ancillas and work registers is a POVM on the
received system (Naimark), and conversely; the decoder is that POVM. -/
noncomputable def decProb {q : ℕ} [NeZero q] {m : ℕ} (p : ZMod q → ℝ)
    (F : (Fin m → ZMod q) → Matrix (Fin m → ZMod q) (Fin m → ZMod q) ℂ)
    (c ĉ : Fin m → ZMod q) : ℝ :=
  expectVal (F ĉ) (psiProd p c)

/-- **Block success (Definition 3.2, p. 17)**: `Pr[ĉ = c]`, averaged over `c` uniform on `C` and
over the outcome. -/
noncomputable def blockSuccess {q : ℕ} [NeZero q] {m : ℕ} {κ : Type} [Fintype κ]
    (p : ZMod q → ℝ) (B : Matrix (Fin m) κ Bool)
    (F : (Fin m → ZMod q) → Matrix (Fin m → ZMod q) (Fin m → ZMod q) ℂ) : ℝ :=
  (1 / ((codeFinset q B).card : ℝ)) * ∑ c ∈ codeFinset q B, decProb p F c c

/-- **Symbol error at `i` (Definition 3.2, p. 17)**: `Pr[ĉ_i ≠ c_i]`, averaged over `c` uniform on
`C` and over the outcome. -/
noncomputable def symbolError {q : ℕ} [NeZero q] {m : ℕ} {κ : Type} [Fintype κ]
    (p : ZMod q → ℝ) (B : Matrix (Fin m) κ Bool)
    (F : (Fin m → ZMod q) → Matrix (Fin m → ZMod q) (Fin m → ZMod q) ℂ) (i : Fin m) : ℝ :=
  (1 / ((codeFinset q B).card : ℝ)) *
    ∑ c ∈ codeFinset q B, ∑ ĉ ∈ Finset.univ.filter (fun ĉ : Fin m → ZMod q => ĉ i ≠ c i),
      decProb p F c ĉ

/-- `E ⊗ I`: an operator `E` on the qudits of a set `N` of symbols, extended by the identity on the
other symbols. Entry `(x, x')` is `E(x|_N, x'|_N)` if `x` and `x'` agree outside `N`, else `0`. -/
noncomputable def liftLocal {q : ℕ} {m : ℕ} (N : Finset (Fin m))
    (E : Matrix (N → ZMod q) (N → ZMod q) ℂ) : Matrix (Fin m → ZMod q) (Fin m → ZMod q) ℂ := by
  classical
  exact fun x x' => if (∀ j, j ∉ N → x j = x' j) then E (fun s => x s.1) (fun s => x' s.1) else 0

/-- **`t`-local estimate at `i` (Definition 3.4, p. 21).** The decoder `F` makes a `t`-local estimate
at `i` if there is a POVM `{E_y}_{y ∈ ℤ_q}` on the qudits of `N_t(i)` such that
`Pr[ĉ_i = y | c] = tr((E_y ⊗ I) |ψ_c⟩⟨ψ_c|)` for every `c ∈ C` and every `y`.

**Formalization Note.** "The POVM may be fully collective on `N_t(i)` and may use ancillas"
(p. 21): a POVM on the qudits of `N_t(i)` covers both (Naimark). -/
def IsLocalEstimate (q : ℕ) [NeZero q] {m : ℕ} {κ : Type} [Fintype κ] (p : ZMod q → ℝ)
    (B : Matrix (Fin m) κ Bool) (i : Fin m) (t : ℕ)
    (F : (Fin m → ZMod q) → Matrix (Fin m → ZMod q) (Fin m → ZMod q) ℂ) : Prop :=
  ∃ E : ZMod q → Matrix (ballSym B i t → ZMod q) (ballSym B i t → ZMod q) ℂ, IsPOVM E ∧
    ∀ c ∈ code q B, ∀ y : ZMod q,
      ∑ ĉ ∈ Finset.univ.filter (fun ĉ : Fin m → ZMod q => ĉ i = y), decProb p F c ĉ =
        expectVal (liftLocal (ballSym B i t) (E y)) (psiProd p c)

/-- The probability that the POVM `E` on the qudits of `N_t(i)` outputs `c_i`, for `c` uniform on
`C` (the qudits of `N_t(i)` are in the state `⊗_{j ∈ N_t(i)} |ψ^p_{c_j}⟩`, p. 30). -/
noncomputable def localSuccess {q : ℕ} [NeZero q] {m : ℕ} {κ : Type} [Fintype κ]
    (p : ZMod q → ℝ) (B : Matrix (Fin m) κ Bool) (i : Fin m) (t : ℕ)
    (E : ZMod q → Matrix (ballSym B i t → ZMod q) (ballSym B i t → ZMod q) ℂ) : ℝ :=
  (1 / ((codeFinset q B).card : ℝ)) *
    ∑ c ∈ codeFinset q B, expectVal (E (c i)) (psiProd p (fun s : ballSym B i t => c s.1))

/-- **The largest probability with which a `t`-local estimate at `i` equals `c_i`** (Corollary 5.6,
p. 35): the supremum of `1 - symbolError F i` over all decoders `F` that make a `t`-local estimate
at `i`.

**Formalization Note.** The set is nonempty (the decoder `F_ĉ = [ĉ = 0] I` makes a `t`-local
estimate with `E_y = [y = 0] I`) and bounded above by one, so `sSup` is the true supremum. -/
noncomputable def optLocal (q : ℕ) [NeZero q] {m : ℕ} {κ : Type} [Fintype κ] (p : ZMod q → ℝ)
    (B : Matrix (Fin m) κ Bool) (i : Fin m) (t : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ F : (Fin m → ZMod q) → Matrix (Fin m → ZMod q) (Fin m → ZMod q) ℂ,
    IsPOVM F ∧ IsLocalEstimate q p B i t F ∧ r = 1 - symbolError p B F i}

end DQILocal.Recon


