-- Prove2me | Definitions.Def_DQILocal_Recon_Supplement_Amplitude
-- name    : DQILocal_Recon_Supplement_Amplitude
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:24:57.930818+00:00
-- url     : https://prove2.me/theorems/24b62ebc-799c-4385-b964-5d50cdbb18f1
-- title:
--   Amplitude functions, the states $|\psi^\Phi_c\rangle$, coset masses, target law, total variation, block success and local estimates for general $\Phi$
-- statement:
--   Fix $q\ge2$, a 0/1 matrix $B$ with $m$ rows read over $\mathbb Z_q$, the subgroup $K=\{Bz\}\subseteq\mathbb Z_q^m$ and the code $C=K^\perp=\{c:B^\top c=0\}$.
--
--   1. An **amplitude function** is $\Phi:\mathbb Z_q^m\to\mathbb C$ with $\sum_x|\Phi(x)|^2=1$. For $c\in\mathbb Z_q^m$,
--   $$|\psi^\Phi_c\rangle=\sum_{x\in\mathbb Z_q^m}\Phi(x)\,\omega^{c\cdot x}\,|x\rangle=Z^c|\Phi\rangle,\qquad \omega=e^{2\pi i/q}.$$
--   2. The **product amplitude function** of a probability vector $\nu$ on $\mathbb Z_q$ is $\Phi(x)=\prod_j\sqrt{\nu(x_j)}$; for $\nu=p_\beta$ it is $\Phi_\beta$, and $|\psi^{\Phi_\beta}_c\rangle=\bigotimes_j|\psi^{p_\beta}_{c_j}\rangle$.
--   3. $\Phi$ is **symmetric** for a cost $f$ if $\Phi(x)$ depends only on the total cost $\sum_jf(x_j)$.
--   4. The **mass** of the coset $x_0+K$ is $W_\Phi(x_0+K)=\sum_{x\in x_0+K}|\Phi(x)|^2$, and the **target law** is $\pi^\Phi_{x_0}(x)=|\Phi(x)|^2/W_\Phi(x_0+K)$ on $x_0+K$ and $0$ elsewhere.
--   5. $\|\mu-\nu\|_{\mathrm{TV}}=\tfrac12\sum_x|\mu(x)-\nu(x)|$, and $\mathbb E_{x_0}$ is the average over the $q^m$ offsets $x_0$.
--   6. For a POVM $\{F_{\hat c}\}_{\hat c\in\mathbb Z_q^m}$, the **block success** is $|C|^{-1}\sum_{c\in C}\langle\psi^\Phi_c|F_c|\psi^\Phi_c\rangle$, and $F$ makes a **$t$-local estimate at $i$** if some POVM $\{E_y\}_{y\in\mathbb Z_q}$ on the qudits of $N_t(i)$ satisfies $\sum_{\hat c:\hat c_i=y}\langle\psi^\Phi_c|F_{\hat c}|\psi^\Phi_c\rangle=\langle\psi^\Phi_c|(E_y\otimes I)|\psi^\Phi_c\rangle$ for all $c\in C$ and $y$.
--
--   These extend the decoding problem of the base mission (product states only) to every amplitude function, as Definitions 3.2 and 3.4 do in the paper.
--
--   **Formalization Note** For the product amplitude function the states, the block success and the local estimate coincide with the base `psiProd`, `blockSuccess` and `IsLocalEstimate`; this is proved in the mission's sanity file. $c\cdot x$ is computed in $\mathbb Z_q$.
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), §3.2, p. 16 (amplitude functions, eq. (3), symmetric amplitude functions); Definition 3.2, p. 17; Theorem 3.3, p. 17 (coset mass, target law, total variation); Definition 3.4, p. 21

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra
import Definitions.Def_DQILocal_Recon_LocalConditions
import Definitions.Def_DQILocal_Recon_Decoder

namespace DQILocal.Recon.Supplement

open scoped BigOperators ComplexOrder
open DQILocal.Recon

/-- **Amplitude functions.**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), §3.2, p. 16: "An
amplitude function is a function `Φ : ℤ_q^m → ℂ` with `Σ_x |Φ(x)|² = 1`." -/
def IsAmplitude {q m : ℕ} [NeZero q] (Φ : (Fin m → ZMod q) → ℂ) : Prop :=
  ∑ x, ‖Φ x‖ ^ 2 = 1

/-- **The states `|ψ^Φ_c⟩` (eq. (3), p. 16)**: `|ψ^Φ_c⟩ = Σ_x Φ(x) ω^{c·x} |x⟩ = Z^c |Φ⟩`, a vector
of `ℂ^{ℤ_q^m}`; `c·x = Σ_j c_j x_j` is computed in `ℤ_q` and `ω^y = omega q y`. -/
noncomputable def psiGen {q m : ℕ} (Φ : (Fin m → ZMod q) → ℂ) (c : Fin m → ZMod q) :
    (Fin m → ZMod q) → ℂ :=
  fun x => Φ x * omega q (c ⬝ᵥ x)

/-- **The product amplitude function** `Φ(x) = Π_j √ν(x_j)` (p. 16); with `ν = p_β` it is the
product amplitude function of Gibbs form `Φ_β`.

**Formalization Note.** `psiGen (phiProd ν) c` is the base `psiProd ν c`
(`Π_j √ν(x_j) ω^{c_j x_j} = (Π_j √ν(x_j)) ω^{c·x}` because `y ↦ ω^y` is a character of `ℤ_q`), so
for `Φ = Φ_β` the decoding problem below is the base Definition 3.2. -/
noncomputable def phiProd {q m : ℕ} [NeZero q] (ν : ZMod q → ℝ) : (Fin m → ZMod q) → ℂ :=
  fun x => ∏ j, (Real.sqrt (ν (x j)) : ℂ)

/-- **Symmetric amplitude functions (p. 16)**: `Φ(x)` depends only on the total cost
`Σ_j f(x_j)` of the violation pattern. -/
def IsSymmetricAmp {q m : ℕ} (f : ZMod q → ℝ) (Φ : (Fin m → ZMod q) → ℂ) : Prop :=
  ∀ x x' : Fin m → ZMod q, ∑ j, f (x j) = ∑ j, f (x' j) → Φ x = Φ x'

/-- Membership in the coset `x₀ + K` (`K = {Bz}`, base `imageK`). -/
def InCoset (q : ℕ) {m : ℕ} {κ : Type} [Fintype κ] (B : Matrix (Fin m) κ Bool)
    (x₀ x : Fin m → ZMod q) : Prop :=
  x - x₀ ∈ imageK q B

/-- **Mass of a coset (p. 17, Theorem 3.3 part 1)**: `W_Φ(x₀ + K) = Σ_{x ∈ x₀ + K} |Φ(x)|²`. -/
noncomputable def cosetMass {q m : ℕ} [NeZero q] {κ : Type} [Fintype κ] (B : Matrix (Fin m) κ Bool)
    (Φ : (Fin m → ZMod q) → ℂ) (x₀ : Fin m → ZMod q) : ℝ := by
  classical
  exact ∑ x ∈ Finset.univ.filter (fun x => InCoset q B x₀ x), ‖Φ x‖ ^ 2

/-- **The target law `π^Φ_{x₀}` (Theorem 3.3 part 1, p. 17)**: `π^Φ_{x₀}(x) ∝ |Φ(x)|²` on `x₀ + K`,
i.e. `|Φ(x)|² / W_Φ(x₀ + K)` for `x ∈ x₀ + K` and `0` otherwise.

**Formalization Note.** Used only under the hypothesis that every coset has positive mass, where
it is a probability law. -/
noncomputable def targetLaw {q m : ℕ} [NeZero q] {κ : Type} [Fintype κ] (B : Matrix (Fin m) κ Bool)
    (Φ : (Fin m → ZMod q) → ℂ) (x₀ : Fin m → ZMod q) (x : Fin m → ZMod q) : ℝ := by
  classical
  exact if InCoset q B x₀ x then ‖Φ x‖ ^ 2 / cosetMass B Φ x₀ else 0

/-- **Total variation distance** `‖μ - ν‖_TV = ½ Σ_x |μ(x) - ν(x)|` on a finite set (p. 17). -/
noncomputable def tvDist {X : Type} [Fintype X] (μ ν : X → ℝ) : ℝ :=
  (1 / 2) * ∑ x, |μ x - ν x|

/-- **`E_{x₀}`: average over a uniformly random offset `x₀ ∈ ℤ_q^m`** (Theorem 3.3, p. 17):
`q^{-m} Σ_{x₀} g(x₀)`. -/
noncomputable def offsetAvg {q m : ℕ} [NeZero q] (g : (Fin m → ZMod q) → ℝ) : ℝ :=
  (1 / (Fintype.card (Fin m → ZMod q) : ℝ)) * ∑ x₀, g x₀
  -- `Fintype.card (Fin m → ZMod q) = q^m`

/-- **Block success for a general amplitude function (Definition 3.2, p. 17).** For a POVM `F` on
`ℂ^{ℤ_q^m}` with outcomes `ĉ ∈ ℤ_q^m`: `|C|^{-1} Σ_{c ∈ C} ⟨ψ^Φ_c| F_c |ψ^Φ_c⟩`. For `Φ = Φ_β`
it is the base `blockSuccess (gibbsWeight q f β)`. -/
noncomputable def blockSuccessGen {q : ℕ} [NeZero q] {m : ℕ} {κ : Type} [Fintype κ]
    (Φ : (Fin m → ZMod q) → ℂ) (B : Matrix (Fin m) κ Bool)
    (F : (Fin m → ZMod q) → Matrix (Fin m → ZMod q) (Fin m → ZMod q) ℂ) : ℝ :=
  (1 / ((codeFinset q B).card : ℝ)) * ∑ c ∈ codeFinset q B, expectVal (F c) (psiGen Φ c)

/-- **`t`-local estimate at `i` for a general amplitude function (Definition 3.4, p. 21; p. 41:
"Definition 3.4 applies to them").** There is a POVM `{E_y}_{y ∈ ℤ_q}` on the qudits of `N_t(i)`
with `Σ_{ĉ : ĉ_i = y} ⟨ψ^Φ_c|F_ĉ|ψ^Φ_c⟩ = ⟨ψ^Φ_c|(E_y ⊗ I)|ψ^Φ_c⟩` for every `c ∈ C` and `y`. For
`Φ = Φ_β` it is the base `IsLocalEstimate q (gibbsWeight q f β)`. -/
def IsLocalEstimateGen (q : ℕ) [NeZero q] {m : ℕ} {κ : Type} [Fintype κ]
    (Φ : (Fin m → ZMod q) → ℂ) (B : Matrix (Fin m) κ Bool) (i : Fin m) (t : ℕ)
    (F : (Fin m → ZMod q) → Matrix (Fin m → ZMod q) (Fin m → ZMod q) ℂ) : Prop :=
  ∃ E : ZMod q → Matrix (ballSym B i t → ZMod q) (ballSym B i t → ZMod q) ℂ, IsPOVM E ∧
    ∀ c ∈ code q B, ∀ y : ZMod q,
      ∑ ĉ ∈ Finset.univ.filter (fun ĉ : Fin m → ZMod q => ĉ i = y), expectVal (F ĉ) (psiGen Φ c) =
        expectVal (liftLocal (ballSym B i t) (E y)) (psiGen Φ c)

end DQILocal.Recon.Supplement


