-- Prove2me | Definitions.Def_DQILocal_Recon_Supplement_Regev
-- name    : DQILocal_Recon_Supplement_Regev
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:25:31.091221+00:00
-- url     : https://prove2.me/theorems/f9c145db-2a08-48f4-abd6-01162dea5bd2
-- title:
--   Coherent decoders and the output law $\nu_{x_0}$ of Regev's reduction
-- statement:
--   A **coherent decoder** on $m$ received qudits is a finite set $W$ of basis states of its work registers, an initial work state $w_0$, a map $\mathrm{out}:W\to\mathbb Z_q^m$ reading the outcome register, and a unitary $U$ on $\mathbb C^{\mathbb Z_q^m\times W}$. With $\Pi_{\hat c}$ the projection onto the basis states $(y,w)$ with $\mathrm{out}(w)=\hat c$, it induces the POVM $F_{\hat c}=\langle w_0|U^\dagger\Pi_{\hat c}U|w_0\rangle$ on the received qudits.
--
--   **Regev's reduction** with offset $x_0$ and amplitude function $\Phi$ runs as follows:
--
--   1. prepare $|C|^{-1/2}\sum_{c\in C}\omega^{-c\cdot x_0}|c\rangle_A\otimes|\psi^\Phi_c\rangle\otimes|w_0\rangle$;
--   2. apply $U$ to the received and work registers;
--   3. check that the decoded word equals the content of the register $A$ (project onto $\mathrm{out}(w)=a$), restarting if it does not; on success renormalize;
--   4. subtract the outcome from $A$ and apply $U^\dagger$;
--   5. measure the received register, giving a pattern $x$ with law $\nu'_{x_0}$.
--
--   The **output law** $\nu_{x_0}$ is the image of $\nu'_{x_0}$ under the map that fixes every $x\in x_0+K$ and sends every other $x$ to $x_0$. "The violation pattern output by DQI" is a sample from $\nu_{x_0}$, and $\mathbb E_{x_0}\mathbb E_{x\sim\nu_{x_0}}h(x)$ averages over a uniformly random offset.
--
--   The output of the reduction depends on the unitary and not only on the induced POVM, which is why the theorems about DQI's output quantify over coherent decoders.
--
--   **Formalization Note** Restarting after a failed check does not change the output law (each attempt is independent), so the output is one attempt conditioned on passing; the conditioning is the renormalization. If the check passed with probability $0$, the renormalized vector would be $0$; the theorems assume positive block success.
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), §3.2, p. 16 (third step of DQI: coherent decoder); p. 17 (Regev's reduction in the paper's form, proof of Theorem 3.3, eq. (6)); p. 18 (the law ν'_{x0} and the replacement map)

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra
import Definitions.Def_DQILocal_Recon_LocalConditions
import Definitions.Def_DQILocal_Recon_Decoder
import Definitions.Def_DQILocal_Recon_Supplement_Amplitude

namespace DQILocal.Recon.Supplement

open scoped BigOperators ComplexOrder
open DQILocal.Recon

/-- **Coherent decoders.**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), §3.2, p. 16 (third step
of DQI: "running in reverse a coherent decoder"), and the proof of Theorem 3.3, p. 17 ("Dilate the
decoder to a unitary `U` that retains all work registers, let `Π_c` project onto the outcome `c` in
its outcome register").

A coherent decoder on `m` received qudits consists of a finite set `W` of basis states of its work
registers (the outcome register included), an initial work state `w₀`, the map `out : W → ℤ_q^m`
that reads the outcome register, and a unitary `U` on `ℂ^{ℤ_q^m × W}` (received register × work
registers).

**Formalization Note.** Regev's reduction runs the decoder coherently, so its output depends on
the unitary and not only on the POVM that the decoder induces (`inducedPOVM`); the theorems
quantify over every finite `W`, `w₀`, `out` and unitary `U`. Every POVM with outcomes in `ℤ_q^m`
is induced by some coherent decoder (Naimark). -/
structure CoherentDecoder (q m : ℕ) [NeZero q] (W : Type) [Fintype W] [DecidableEq W] where
  /-- initial state of the work registers -/
  w₀ : W
  /-- the content of the outcome register -/
  out : W → (Fin m → ZMod q)
  /-- the unitary acting on the received and work registers -/
  U : Matrix ((Fin m → ZMod q) × W) ((Fin m → ZMod q) × W) ℂ
  unitary : U ∈ Matrix.unitaryGroup ((Fin m → ZMod q) × W) ℂ

variable {q m : ℕ} [NeZero q] {W : Type} [Fintype W] [DecidableEq W]

/-- **The POVM induced on the received qudits**: `F_ĉ(x, x') = ⟨x, w₀| U† Π_ĉ U |x', w₀⟩`, where
`Π_ĉ` projects onto the basis states `(y, w)` with `out(w) = ĉ`. A coherent decoder "makes a
`t`-local estimate" or "has block success `s`" when its induced POVM does (Definitions 3.2, 3.4). -/
noncomputable def inducedPOVM (Dec : CoherentDecoder q m W) (ĉ : Fin m → ZMod q) :
    Matrix (Fin m → ZMod q) (Fin m → ZMod q) ℂ := by
  classical
  exact fun x x' => ∑ yw ∈ Finset.univ.filter (fun yw : (Fin m → ZMod q) × W => Dec.out yw.2 = ĉ),
    star (Dec.U yw (x, Dec.w₀)) * Dec.U yw (x', Dec.w₀)

/-- The register of Regev's reduction: the codeword register `A` (`ℤ_q^m`), the received register
(`ℤ_q^m`) and the work registers (`W`). -/
abbrev RegevReg (q m : ℕ) (W : Type) := (Fin m → ZMod q) × ((Fin m → ZMod q) × W)

/-- **Step 0 of Regev's reduction (p. 16, p. 17)**: the input
`|C|^{-1/2} Σ_{c ∈ C} ω^{-c·x₀} |c⟩_A ⊗ |ψ^Φ_c⟩ ⊗ |w₀⟩`. -/
noncomputable def regevInit {κ : Type} [Fintype κ] (Φ : (Fin m → ZMod q) → ℂ)
    (B : Matrix (Fin m) κ Bool) (Dec : CoherentDecoder q m W) (x₀ : Fin m → ZMod q) :
    RegevReg q m W → ℂ := by
  classical
  exact fun r => if r.1 ∈ code q B ∧ r.2.2 = Dec.w₀ then
    ((Real.sqrt ((codeFinset q B).card : ℝ))⁻¹ : ℂ) * omega q (-(r.1 ⬝ᵥ x₀)) * psiGen Φ r.1 r.2.1
    else 0

/-- **Step 1**: apply `U` to the received and work registers. -/
noncomputable def regevAfterU (Dec : CoherentDecoder q m W) (v : RegevReg q m W → ℂ) :
    RegevReg q m W → ℂ :=
  fun r => ∑ z : (Fin m → ZMod q) × W, Dec.U r.2 z * v (r.1, z)

/-- **Step 2, the check (p. 17)**: project onto "the decoded word equals the content of the codeword
register", i.e. onto the basis states with `out(w) = a`. -/
noncomputable def regevProjectCheck (Dec : CoherentDecoder q m W) (v : RegevReg q m W → ℂ) :
    RegevReg q m W → ℂ := by
  classical
  exact fun r => if Dec.out r.2.2 = r.1 then v r else 0

/-- The probability that the check passes: the squared norm of the projected vector. -/
noncomputable def regevPassProb {κ : Type} [Fintype κ] (Φ : (Fin m → ZMod q) → ℂ)
    (B : Matrix (Fin m) κ Bool) (Dec : CoherentDecoder q m W) (x₀ : Fin m → ZMod q) : ℝ :=
  ∑ r, ‖regevProjectCheck Dec (regevAfterU Dec (regevInit Φ B Dec x₀)) r‖ ^ 2

/-- **The state of Regev's reduction after the check has passed and after the uncomputation
(proof of Theorem 3.3, p. 17)**: renormalize the post-check vector, subtract the outcome from the
codeword register (`|a⟩|w⟩ ↦ |a - out(w)⟩|w⟩`), and apply `U†`. Its value is
`|0⟩_A ⊗ |A_{x₀}⟩` with `|A_{x₀}⟩ = (|C| s)^{-1/2} Σ_c ω^{-c·x₀} U†Π_cU (|ψ^Φ_c⟩|w₀⟩)`.

**Formalization Note.** Restarting after a failed check does not change the law of the output
(each attempt is independent and the check passes with the same probability), so the output is
the result of one attempt conditioned on the check passing; the conditioning is the
renormalization. When the pass probability is `0` the renormalized vector is `0` (division by
`0`); the theorems assume block success `> 0`, under which it is positive. -/
noncomputable def regevFinal {κ : Type} [Fintype κ] (Φ : (Fin m → ZMod q) → ℂ)
    (B : Matrix (Fin m) κ Bool) (Dec : CoherentDecoder q m W) (x₀ : Fin m → ZMod q) :
    RegevReg q m W → ℂ :=
  let post := fun r => regevProjectCheck Dec (regevAfterU Dec (regevInit Φ B Dec x₀)) r /
    ((Real.sqrt (regevPassProb Φ B Dec x₀) : ℝ) : ℂ)
  let sub := fun r : RegevReg q m W => post (r.1 + Dec.out r.2.2, r.2)
  fun r => ∑ z : (Fin m → ZMod q) × W, star (Dec.U z r.2) * sub (r.1, z)

/-- **The law `ν'_{x₀}` of the violation pattern before the replacement (p. 18)**: measure the
received register of the final state in the computational basis,
`ν'_{x₀}(x) = Σ_{a, w} |final(a, x, w)|²`. -/
noncomputable def regevPatternLaw {κ : Type} [Fintype κ] (Φ : (Fin m → ZMod q) → ℂ)
    (B : Matrix (Fin m) κ Bool) (Dec : CoherentDecoder q m W) (x₀ : Fin m → ZMod q)
    (x : Fin m → ZMod q) : ℝ :=
  ∑ a : Fin m → ZMod q, ∑ w : W, ‖regevFinal Φ B Dec x₀ (a, (x, w))‖ ^ 2

/-- **The output law `ν_{x₀}` of Regev's reduction (p. 17, p. 18).** "If the decoder is not exact,
this pattern can lie outside the coset `x₀ + K`, and the procedure then outputs `x₀`": `ν_{x₀}` is
the image of `ν'_{x₀}` under the map that fixes every `x ∈ x₀ + K` and sends every other `x` to
`x₀`. "The violation pattern output by DQI" (Theorems 6.5, 6.9) is a sample from `ν_{x₀}`. -/
noncomputable def regevLaw {κ : Type} [Fintype κ] (Φ : (Fin m → ZMod q) → ℂ)
    (B : Matrix (Fin m) κ Bool) (Dec : CoherentDecoder q m W) (x₀ : Fin m → ZMod q)
    (x : Fin m → ZMod q) : ℝ := by
  classical
  exact if InCoset q B x₀ x then
      regevPatternLaw Φ B Dec x₀ x +
        (if x = x₀ then
          ∑ x' ∈ Finset.univ.filter (fun x' => ¬ InCoset q B x₀ x'), regevPatternLaw Φ B Dec x₀ x'
         else 0)
    else 0

/-- `E_{x₀} E_{x ∼ ν_{x₀}} h(x)`: the expectation of `h` at the output of Regev's reduction,
averaged over a uniformly random offset. -/
noncomputable def regevExpect {κ : Type} [Fintype κ] (Φ : (Fin m → ZMod q) → ℂ)
    (B : Matrix (Fin m) κ Bool) (Dec : CoherentDecoder q m W) (h : (Fin m → ZMod q) → ℝ) : ℝ :=
  offsetAvg fun x₀ => ∑ x, regevLaw Φ B Dec x₀ x * h x

end DQILocal.Recon.Supplement


