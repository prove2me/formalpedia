-- Prove2me | Definitions.Def_DQILocal_Recon_Supplement_Condensation
-- name    : DQILocal_Recon_Supplement_Condensation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:27:24.803383+00:00
-- url     : https://prove2.me/theorems/9c2ae90a-ac49-4a1e-b9ec-08012953e183
-- title:
--   Coset law $W_{B,\alpha}$, relative entropy $F_B(\alpha)$, $\bar F$, $\alpha_c$, $\beta_c$, and the pretty-good measurement $P_{\mathrm{PGM}}(B,\beta)$
-- statement:
--   Let $q=2$ and $f(z)=z$.
--
--   1. For $\alpha\in(0,\tfrac12)$, $W_{B,\alpha}(X)=\Pr[E+K=X]$ for $E\in\mathbb Z_2^m$ with independent Bernoulli($\alpha$) entries, and
--   $$F_B(\alpha)=D_{\mathrm{KL}}(W_{B,\alpha}\,\|\,U_B)=\sum_XW_{B,\alpha}(X)\ln\bigl(|C|\,W_{B,\alpha}(X)\bigr),$$
--   with $U_B$ the uniform law on the $|C|$ cosets of $K$.
--   2. $\bar F(\alpha)=\lim_{n\to\infty}\frac1n\mathbb E_BF_B(\alpha)$ for $B$ from the configuration model without the conditioning.
--   3. $\alpha_c=\sup\{\alpha\in(0,\tfrac12):\bar F(\alpha)>0\}$, and the **condensation threshold** is $\beta_c=\ln\frac{1-\alpha_c}{\alpha_c}$.
--   4. For the states $|\psi_c\rangle=\bigotimes_j|\psi^{p_\beta}_{c_j}\rangle$, $c\in C$, with average state $\rho=|C|^{-1}\sum_c|\psi_c\rangle\langle\psi_c|$, the **pretty-good measurement** has elements $E_c=\rho^{-1/2}\bigl(|C|^{-1}|\psi_c\rangle\langle\psi_c|\bigr)\rho^{-1/2}$, with the inverse square root on the support of $\rho$ and the projection onto $\ker\rho$ added to the outcome $0$.
--   5. $P_{\mathrm{PGM}}(B,\beta)$ is its block success $|C|^{-1}\sum_c\langle\psi_c|E_c|\psi_c\rangle$.
--
--   $\beta_c$ is the threshold of Theorem 7.7: below it the PGM succeeds and above it every decoder fails.
--
--   **Formalization Note** The sum over cosets is written as an expectation over $E$. $\bar F$ is a limit whose existence the paper proves (Proposition 7.6(3)); it is written with `limUnder` along the admissible $m$, $n=km/D$. $P_{\mathrm{PGM}}$ is defined from the measurement, not by the closed form (19).
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), §7.2, pp. 56–57 (PGM, block success); §7.3, pp. 60–61 (W_{B,α}, F_B, F̄, α_c, β_c); p. 62 (P_PGM(B,β))

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra
import Definitions.Def_DQILocal_Recon_LocalConditions
import Definitions.Def_DQILocal_Recon_Decoder
import Definitions.Def_DQILocal_Recon_Supplement_Amplitude
import Definitions.Def_DQILocal_Recon_Supplement_ConfigModel

namespace DQILocal.Recon.Supplement

open scoped BigOperators Matrix
open DQILocal.Recon Filter

/-- **The Max-XORSAT cost** `f(z) = z` on `ℤ_2` (read through `z.val`, the base convention). -/
def fXor : ZMod 2 → ℝ := fun z => (z.val : ℝ)

/-- **Bernoulli law on `ℤ_2^m`.**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), §7.3, p. 60: the law of
`E ∈ ℤ_2^m` with independent Bernoulli(`α`) entries, `Pr[E = e] = Π_j α^{e_j} (1 - α)^{1 - e_j}`. -/
noncomputable def bernVec {m : ℕ} (α : ℝ) (e : Fin m → ZMod 2) : ℝ :=
  ∏ j, if e j = 0 then 1 - α else α

/-- **The coset law `W_{B,α}` (p. 60)**, evaluated at the coset `e + K`:
`W_{B,α}(e + K) = Pr[E + K = e + K] = Σ_{e' ∈ e + K} Pr[E = e']`. -/
noncomputable def cosetLaw {m : ℕ} {κ : Type} [Fintype κ] (B : Matrix (Fin m) κ Bool) (α : ℝ)
    (e : Fin m → ZMod 2) : ℝ := by
  classical
  exact ∑ e' ∈ Finset.univ.filter (fun e' => InCoset 2 B e e'), bernVec α e'

/-- **The relative entropy `F_B(α) = D_KL(W_{B,α} ‖ U_B)` (p. 60)**, with `U_B` the uniform law on
the `|C|` cosets of `K`: `F_B(α) = Σ_X W_{B,α}(X) ln(|C| W_{B,α}(X))`.

**Formalization Note.** The sum over cosets `X` is written as the expectation over `E`:
`Σ_X W(X) g(X) = Σ_e Pr[E = e] g(e + K)`, which groups the terms of each coset. For
`α ∈ (0, ½)` every `W_{B,α}(X)` is positive, so no `0 ln 0` term occurs. -/
noncomputable def relEntFB {m : ℕ} {κ : Type} [Fintype κ] (B : Matrix (Fin m) κ Bool) (α : ℝ) : ℝ :=
  ∑ e : Fin m → ZMod 2, bernVec α e * Real.log (((codeFinset 2 B).card : ℝ) * cosetLaw B α e)

/-- **`F̄(α) = lim_{n→∞} (1/n) E_B F_B(α)` (Proposition 7.6(3), p. 61)** for `B` from the
configuration model without the conditioning, the limit taken along admissible `m`, `n = km/D`.

**Formalization Note.** The paper defines `F̄` as this limit, whose existence is Proposition 7.6(3)
(from van den Brand–Jaafari); it is written with `limUnder` (if the limit did not exist the value
would be arbitrary), not replaced by a `limsup` or `liminf`. -/
noncomputable def Fbar (k D : ℕ) (α : ℝ) : ℝ :=
  limUnder (admissible k D) fun m =>
    (1 / ((k * m / D : ℕ) : ℝ)) * cfgExpect .pairing k D m (fun B => relEntFB B α)

/-- **`α_c = sup{α ∈ (0, ½) : F̄(α) > 0}` (p. 61).**

**Formalization Note.** The set is bounded by `½`; the paper shows it contains `(0, α_H)` with
`H_2(α_H) = 1 - k/D > 0` (p. 61), so `sSup` is the true supremum. -/
noncomputable def alphaC (k D : ℕ) : ℝ :=
  sSup {α : ℝ | α ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧ 0 < Fbar k D α}

/-- **The condensation threshold `β_c = ln((1 - α_c)/α_c)` (p. 61)**, so that `α_c = p_{β_c}(1)`. -/
noncomputable def betaC (k D : ℕ) : ℝ := Real.log ((1 - alphaC k D) / alphaC k D)

/-- The average state `ρ = |C|^{-1} Σ_{c ∈ C} |ψ_c⟩⟨ψ_c|` of the decoding problem for `Φ_β`
(§7.2, p. 57; `|ψ_c⟩ = ⊗_j |ψ^{p_β}_{c_j}⟩`, base `psiProd`). -/
noncomputable def avgState {m : ℕ} {κ : Type} [Fintype κ] (B : Matrix (Fin m) κ Bool) (β : ℝ) :
    Matrix (Fin m → ZMod 2) (Fin m → ZMod 2) ℂ :=
  (1 / ((codeFinset 2 B).card : ℂ)) • ∑ c ∈ codeFinset 2 B,
    Matrix.vecMulVec (psiProd (gibbsWeight 2 fXor β) c) (star (psiProd (gibbsWeight 2 fXor β) c))

/-- **The pretty-good measurement (§7.2, p. 56–57)** for the states `|ψ_c⟩`, `c` uniform on `C`:
`E_c = ρ^{-1/2} (|C|^{-1} |ψ_c⟩⟨ψ_c|) ρ^{-1/2}` for `c ∈ C`, where `ρ^{-1/2}` is the inverse square
root on the support of `ρ` (continuous functional calculus with `x ↦ (√x)⁻¹`, which is `0` at `0`),
the projection `I - Π_supp ρ` onto `ker ρ` added to the outcome `0`, and `E_ĉ = 0` for `ĉ ∉ C`.

**Formalization Note.** The elements sum to the identity; the added kernel projection does not
change the success probability, because every `|ψ_c⟩` lies in the support of `ρ`. -/
noncomputable def pgm {m : ℕ} {κ : Type} [Fintype κ] (B : Matrix (Fin m) κ Bool) (β : ℝ)
    (ĉ : Fin m → ZMod 2) : Matrix (Fin m → ZMod 2) (Fin m → ZMod 2) ℂ := by
  classical
  exact
    if ĉ ∈ code 2 B then
      cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (avgState B β) *
          ((1 / ((codeFinset 2 B).card : ℂ)) •
            Matrix.vecMulVec (psiProd (gibbsWeight 2 fXor β) ĉ)
              (star (psiProd (gibbsWeight 2 fXor β) ĉ))) *
          cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (avgState B β) +
        (if ĉ = 0 then 1 - cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) (avgState B β) else 0)
    else 0

/-- **`P_PGM(B, β)` (p. 60, p. 62)**: the block success of the pretty-good measurement for the
decoding problem induced by DQI with `Φ_β` (Definition 3.2; base `blockSuccess`).

**Formalization Note.** Defined as the block success of the measurement itself, not by the closed
form (19) of Lemma 7.2. -/
noncomputable def PPGM {m : ℕ} {κ : Type} [Fintype κ] (B : Matrix (Fin m) κ Bool) (β : ℝ) : ℝ :=
  blockSuccess (gibbsWeight 2 fXor β) B (pgm B β)

end DQILocal.Recon.Supplement


