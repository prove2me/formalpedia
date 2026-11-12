-- Prove2me | Definitions.Def_QubitTracking_rigidityIso
-- name    : QubitTracking_rigidityIso
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:27:43.759569+00:00
-- url     : https://prove2.me/theorems/a1241086-730e-4605-a778-b3601a3f37b0
-- title:
--   The EPR-pair rigidity isometry $\Phi_{\mathbf B}$ and EPR overlaps
-- statement:
--   For observables $X_{\mathbf B}(a)$, $Z_{\mathbf B}(b)$ ($a,b\in\{0,1\}^n$) on a finite-dimensional $\mathcal H_{\mathbf B}$ (self-adjoint with square $1$), the rigidity map of Lemma 7.6 is
--   $$\Phi_{\mathbf B}|\varphi\rangle=\Big(\frac1{2^n}\sum_{a,b}X_{\mathbf B}(a)Z_{\mathbf B}(b)\otimes\sigma_X(a)\sigma_Z(b)\otimes I\Big)|\varphi\rangle_{\mathbf B}|\mathrm{EPR}\rangle^{\otimes n},$$
--   with values in $\hat{\mathcal H}_{\mathbf B}\otimes(\mathbb C^2)^{\otimes n}_{\mathbf B'}$, $\hat{\mathcal H}_{\mathbf B}=\mathcal H_{\mathbf B}\otimes(\mathbb C^2)^{\otimes n}$. The **EPR overlap** of a vector $\chi$ on $\mathbf A\otimes\hat{\mathcal H}\otimes\mathbf B'$ is $\|(\langle\mathrm{EPR}|^{\otimes n}_{\mathbf A\mathbf B'}\otimes I)\chi\|^2$, and $\|\Pi_{\mathrm{eq}}\chi\|^2$ with $\Pi_{\mathrm{eq}}=\sum_x|x\rangle\langle x|_{\mathbf A}\otimes|x\rangle\langle x|_{\tilde{\mathbf B}}\otimes I$ measures agreement of $\mathbf A$ with the first $n$ qubits of the other register.
--
--   These are the objects of Lemma 7.6 and Corollary 7.7.
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Lemma 7.6 and Corollary 7.7, pp.53–54

import Definitions.Def_QubitTracking_Bits

set_option autoImplicit false

open Matrix

namespace QubitTracking

/-! EPR-pair rigidity (Lemma 7.6, Corollary 7.7).

Source: Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time*,
arXiv:2605.30732 (held version, sha256 bf98e5b5…), Lemma 7.6 ([VZ21] Lemma 5.4) and
Corollary 7.7, pp.53–54. States on `(ℂ²)^{⊗n}_𝐀 ⊗ ℋ_𝐁` are vectors indexed by
`Bits (Fin n) × β`, with `ℋ_𝐁 = ℂ^β` finite dimensional. -/

/-- `(M ⊗ I)ψ` for an operator `M` on the first factor. -/
noncomputable def actLeft {α α' β : Type} [Fintype α] (M : Matrix α' α ℂ) (ψ : α × β → ℂ) :
    α' × β → ℂ :=
  fun p => ∑ a, M p.1 a * ψ (a, p.2)

/-- `(I ⊗ M)ψ` for an operator `M` on the second factor. -/
noncomputable def actRight {α β β' : Type} [Fintype β] (M : Matrix β' β ℂ) (ψ : α × β → ℂ) :
    α × β' → ℂ :=
  fun p => ∑ b, M p.2 b * ψ (p.1, b)

/-- A (finite-dimensional) **observable** in the sense of Lemma 7.6: a self-adjoint operator with
`O² = 1` (a `±1`-valued observable; such an operator is unitary). -/
def IsObservable {β : Type} [Fintype β] [DecidableEq β] (O : Matrix β β ℂ) : Prop :=
  Oᴴ = O ∧ O * O = 1

/-- **The rigidity isometry `Φ_𝐁`** of Lemma 7.6 (p.54), built from the observables `X_𝐁(a)`,
`Z_𝐁(b)`:
`Φ_𝐁|φ⟩ = (2^{-n} ∑_{a,b} X_𝐁(a) Z_𝐁(b) ⊗ σ_X(a) σ_Z(b) ⊗ I) |φ⟩_𝐁 |EPR⟩^{⊗n}`,
with values in `ℋ̂_𝐁 ⊗ (ℂ²)^{⊗n}_{𝐁′}`, `ℋ̂_𝐁 = ℋ_𝐁 ⊗ (ℂ²)^{⊗n}` (the first halves of the `n` EPR
pairs) and `𝐁′` the last `n` halves. Output index: `((h, y), y′)` with `h ∈ β`, `y` the first halves,
`y′ ∈ 𝐁′`. -/
noncomputable def rigidityIso {n : ℕ} {β : Type} [Fintype β] (X Z : Bits (Fin n) → Matrix β β ℂ) :
    Matrix ((β × Bits (Fin n)) × Bits (Fin n)) β ℂ :=
  fun o h₀ => ((2 : ℂ) ^ n)⁻¹ * ∑ a : Bits (Fin n), ∑ b : Bits (Fin n),
    (X a * Z b) o.1.1 h₀ * ((sigmaX a * sigmaZ b) o.1.2 o.2 * ((Real.sqrt 2 : ℂ) ^ n)⁻¹)

/-- **EPR fidelity on `𝐀𝐁′`**: `Tr(⟨EPR|^{⊗n}_{𝐀𝐁′} |χ⟩⟨χ| |EPR⟩^{⊗n}_{𝐀𝐁′}) = ‖(⟨EPR|_{𝐀𝐁′} ⊗ I)χ‖²`
for `χ` on `𝐀 ⊗ (ℋ̂ ⊗ 𝐁′)`, the `j`-th qubit of `𝐀` paired with the `j`-th qubit of `𝐁′`. -/
noncomputable def eprOverlap {n : ℕ} {γ : Type} [Fintype γ] (χ : Bits (Fin n) × (γ × Bits (Fin n)) → ℂ) :
    ℝ :=
  ∑ g : γ, Complex.normSq (∑ x : Bits (Fin n), ((Real.sqrt 2 : ℂ) ^ n)⁻¹ * χ (x, (g, x)))

/-- `‖Π_eq χ‖²` for `Π_eq = ∑_x |x⟩⟨x|_𝐀 ⊗ |x⟩⟨x|_{𝐁̃} ⊗ I_{𝐁̃′}` (Corollary 7.7, p.54), `χ` on
`𝐀 ⊗ (𝐁̃ ⊗ 𝐁̃′)`. -/
noncomputable def eqOverlap {n : ℕ} {γ : Type} [Fintype γ] (χ : Bits (Fin n) × (Bits (Fin n) × γ) → ℂ) :
    ℝ :=
  ∑ x : Bits (Fin n), ∑ g : γ, Complex.normSq (χ (x, (x, g)))

end QubitTracking


