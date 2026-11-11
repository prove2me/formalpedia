-- Prove2me | Definitions.Def_QFairEx_encVec
-- name    : QFairEx_encVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:28.873945+00:00
-- url     : https://prove2.me/theorems/c1333d37-0458-4cb3-aa44-e6968702d5fc
-- title:
--   Encodings $E_p$ of a qubit into an accepting subspace and decodings $D_p$
-- statement:
--   Given vectors $e_{p,0},e_{p,1}$ (orthonormal states in $S_p$), the **encoding** is
--   $$E_p(\alpha|0\rangle+\beta|1\rangle)=\alpha|e_{p,0}\rangle+\beta|e_{p,1}\rangle.$$
--   On a two-qubit operator $Y$ (qubit $1$ the challenge $|\phi_1\rangle$ for $P_0$, qubit $2$ the challenge $|\phi_2\rangle$ for $P_1$) the encoded input is $(E_0\otimes E_1)Y(E_0\otimes E_1)^\dagger$ on $\iota_0\times\iota_1$; for $Y=|\phi_1\phi_2\rangle\langle\phi_1\phi_2|$ it is $|\psi_0\rangle\langle\psi_0|\otimes|\psi_1\rangle\langle\psi_1|$ with $\psi_0=E_0\phi_1$, $\psi_1=E_1\phi_2$.
--
--   The **decoding channel** is $D_p(\sigma)=E_p^\dagger\sigma E_p+\operatorname{tr}\bigl((I-E_pE_p^\dagger)\sigma\bigr)|0\rangle\langle0|$; for orthonormal $e_p$ it is a quantum channel with $D_p(E_p\rho E_p^\dagger)=\rho$.
--
--   **Formalization Note** The paper realizes $D_p$ by a unitary $U_p$ on qubit registers followed by discarding ancillas; for a general register this definition fixes one channel with the property the proof uses (it inverts $E_p$ on its image). Orthonormality is a hypothesis of the theorems.
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), §4.2.2, "Encoded challenge inputs", p.22; Algorithm 4.11, step 1, p.24

import Mathlib
import Definitions.Def_QFairEx_kronMap

namespace QFairEx

open Matrix

/-- **The encoding isometry `E_p`** on vectors.
Chung, Lee, Raizes, Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of
2026-11-02, sha256 0099b883…), §4.2.2, "Encoded challenge inputs", p.22: "Choose orthonormal
states |e0,0⟩, |e0,1⟩ ∈ S0 and |e1,0⟩, |e1,1⟩ ∈ S1. For p ∈ {0, 1}, define the isometry Ep by
Ep(α|0⟩ + β|1⟩) := α|ep,0⟩ + β|ep,1⟩."

`encVec e ϕ = ϕ₀ e₀ + ϕ₁ e₁` for a qubit vector `ϕ : Fin 2 → ℂ` and the pair `e : Fin 2 → ι → ℂ`.
It is an isometry when `e` is orthonormal (`IsOrthonormalPair e`); this is a hypothesis of the
theorems, not built into the definition. -/
def encVec {ι : Type} (e : Fin 2 → ι → ℂ) (ϕ : Fin 2 → ℂ) : ι → ℂ := ∑ a, ϕ a • e a

/-- **Encoded two-qubit input `(E₀ ⊗ E₁) Y (E₀ ⊗ E₁)†`** on `ι0 × ι1`, for a two-qubit operator `Y`
on the registers of the game (basis `Fin 2 → Fin 2`, qubit `0` = challenge `|ϕ₁⟩` given to P₀
through `E₀`, qubit `1` = challenge `|ϕ₂⟩` given to P₁ through `E₁`). For
`Y = |ϕ₁ ϕ₂⟩⟨ϕ₁ ϕ₂|` it is `|ψ₀⟩⟨ψ₀| ⊗ |ψ₁⟩⟨ψ₁|` with `ψ₀ = E₀ϕ₁`, `ψ₁ = E₁ϕ₂` (Algorithm 4.11,
step 1, p.24). -/
def encodeInput {ι0 ι1 : Type} (e0 : Fin 2 → ι0 → ℂ) (e1 : Fin 2 → ι1 → ℂ)
    (Y : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) : Matrix (ι0 × ι1) (ι0 × ι1) ℂ :=
  fun i j => ∑ a : Fin 2 → Fin 2, ∑ b : Fin 2 → Fin 2,
    e0 (a 0) i.1 * e1 (a 1) i.2 * Y a b * star (e0 (b 0) j.1) * star (e1 (b 1) j.2)

/-- **The decoding channel `D_p`**: `D(σ) = E†σE + tr((I − EE†)σ) |0⟩⟨0|`, where `E` is the
`ι × 2` matrix with columns `e 0`, `e 1`.
Chung, Lee, Raizes, Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of
2026-11-02, sha256 0099b883…), §4.2.2, p.22: "Let Dp be the decoding channel that applies U†p
and discards the ancillary registers. On the image of Ep, this recovers the original qubit".

**Formalization Note.** The paper realizes `D_p` through a unitary `U_p` on qubit registers;
for a general register `ι` this definition fixes one CPTP map (for orthonormal `e`) with the
property the paper uses, `D(EρE†) = ρ`; off the image of `E_p` it sends the remaining weight to
`|0⟩⟨0|`. `tr((I − EE†)σ)` is written `tr σ − tr(E†σE)`. -/
def decode {ι : Type} [Fintype ι] (e : Fin 2 → ι → ℂ) (σ : Matrix ι ι ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Matrix.of fun i a => e a i)ᴴ * σ * Matrix.of (fun i a => e a i) +
    (σ.trace - ((Matrix.of fun i a => e a i)ᴴ * σ * Matrix.of (fun i a => e a i)).trace) •
      Matrix.single 0 0 1

end QFairEx


