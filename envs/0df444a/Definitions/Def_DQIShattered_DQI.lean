-- Prove2me | Definitions.Def_DQIShattered_DQI
-- name    : DQIShattered_DQI
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:29:10.577022+00:00
-- url     : https://prove2.me/theorems/0c16988c-7f10-4c1b-a2cb-250d07474c18
-- title:
--   The DQI procedure: $|\Phi_{\mathrm{target}}\rangle$, $\mathcal D_{\mathrm{target}}$, $\mathcal D_{\mathrm{actual}}$, $K_B$ and $\nu^{\mathrm{DQI}}_{B,J,\beta}$
-- statement:
--   Let $B\in\mathbb F_2^{M\times N}$, $J=(-1)^v$ and $\gamma=\frac12-\frac12\operatorname{sech}\beta$.
--
--   1. The **target state** (3.2) is $|\Phi_{\mathrm{target}}\rangle=|\ker B|^{-1/2}\sum_{x\in\mathbb F_2^N}\sqrt{\mu_{\beta,H_{B,J}}[(-1)^x]}\,|Bx\rangle$. $\mathcal D_{\mathrm{target}}(B,J,\beta)$ is its computational-basis measurement law.
--   2. The **Hadamard-domain target** (3.7), (3.9) is $|\hat\Phi_{\mathrm{target}}\rangle=\sum_{d\in C^\perp}\sum_{e}(-1)^{v\cdot e}\hat F(e)\,|d+e\rangle$, with $\hat F(e)=\sqrt{1-\gamma}^{\,M-|e|}\sqrt\gamma^{\,|e|}$.
--   3. **The DQI procedure with a decoder unitary $U$** (pp.11–12):
--      - start from $|C^\perp|^{-1/2}\sum_{d\in C^\perp}(-1)^{d\cdot v}|d\rangle_A|0\rangle_E|\psi_{d,\gamma}\rangle_R|w_0\rangle_W$, which is (3.12) followed by (3.14);
--      - apply $\tilde U=(I\otimes U^\dagger)\,\mathrm{CX}_{E\to A}\,(I\otimes U)$;
--      - apply $Z^v$ to $R$, as in (3.16);
--      - apply $H^{\otimes M}$ to $R$ and measure $R$.
--
--      The resulting law of $R$ is $\mathcal D_{\mathrm{actual}}(B,J,\beta)$.
--   4. The **post-processing channel** $K_B$ (p.13) acts on an outcome $y$ as follows. If $y\in C=\{Bx\}$, it outputs $(-1)^x$ for $x$ uniform on $\{x:Bx=y\}$. Otherwise it outputs a fixed $z_0=(-1)^{x_0}$.
--   5. The DQI output law is $\nu^{\mathrm{DQI}}_{B,J,\beta}=K_B\,\mathcal D_{\mathrm{actual}}(B,J,\beta)$.
--
--   **Formalization Note** "$U_{\mathrm{dec}}$ replaces the idealized decoder $\tilde U_{\mathrm{dec}}$" (Theorem 3.1) is read as compute–copy–uncompute. $\tilde U$ writes the decoder's estimate into the first register and uncomputes the decoder. For a perfect decoder it acts exactly as (3.13)–(3.15). The literal alternative, applying $U^\dagger$ directly, makes (3.17) false: a decoder can be followed by an estimate-dependent phase without changing its success probability, and that phase shifts $v$.
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), §3.1, pp.10–13, eqs. (3.2), (3.5), (3.7), (3.9)–(3.16); proof of Theorem 2.4, p.13

import Mathlib
import Definitions.Def_DQIShattered_Gibbs
import Definitions.Def_DQIShattered_Thresholds
import Definitions.Def_DQIShattered_Decoding

namespace DQIShattered

open Finset

/-- The sign `(−1)^a` of `a ∈ 𝔽₂`, as a complex number. -/
noncomputable def sgn (a : ZMod 2) : ℂ := (-1 : ℂ) ^ a.val

/-- **The Hadamard transform** `H^{⊗M}` on an `M`-qubit register:
`(H^{⊗M}ψ)(y) = 2^{−M/2} ∑_r (−1)^{y·r} ψ(r)`. -/
noncomputable def hadamardT {M : ℕ} (ψ : Reg M → ℂ) : Reg M → ℂ := fun y =>
  ((Real.sqrt 2)⁻¹ ^ M : ℝ) * ∑ r, sgn (y ⬝ᵥ r) * ψ r

/-- `ker B = {x ∈ 𝔽₂^N : Bx = 0}`. -/
noncomputable def kerB {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) : Finset (Fin N → ZMod 2) :=
  univ.filter fun x => B.mulVec x = 0

/-- **The target state** `|Φ_target⟩ = |ker B|^{−1/2} ∑_{x ∈ 𝔽₂^N} √(µ_{β,H_{B,J}}[(−1)^x]) |Bx⟩` of (3.2)
(Zhou, Shutty, Sellke, Jordan, arXiv:2609.40345, held version sha256 0c7f6fdf…, §3.1, p.10), with
`J = (−1)^v`. -/
noncomputable def phiTarget {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (v : Fin M → ZMod 2)
    (β : ℝ) : Reg M → ℂ := fun y =>
  ((Real.sqrt (kerB B).card)⁻¹ : ℝ) *
    ∑ x ∈ univ.filter (fun x => B.mulVec x = y), (Real.sqrt (gibbs B v β x) : ℂ)

/-- **The target distribution** `𝒟_target(B, J, β)(y) = |⟨y|Φ_target⟩|²` on `𝔽₂^M`, obtained by measuring
`|Φ_target⟩` in the computational basis (Theorem 3.1, p.12). -/
noncomputable def Dtarget {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (v : Fin M → ZMod 2) (β : ℝ)
    (y : Reg M) : ℝ :=
  Complex.normSq (phiTarget B v β y)

/-- **The Hadamard-domain target** `|Φ̂_target⟩ = ∑_{d ∈ C^⊥} ∑_{e ∈ 𝔽₂^M} (−1)^{v·e} F̂(e) |d + e⟩` of (3.7),
p.11, with the product amplitude `F̂(e) = √(1−γ)^{M−|e|} √γ^{|e|}` of (3.9) and `γ = gammaOf β` of (3.10). -/
noncomputable def phiHatTarget {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (v : Fin M → ZMod 2)
    (β : ℝ) : Reg M → ℂ := fun y =>
  ∑ d ∈ dualCode B, ∑ e : Reg M,
    if d + e = y then
      sgn (v ⬝ᵥ e) * ∏ j, (if e j = 0 then (Real.sqrt (1 - gammaOf β) : ℂ) else (Real.sqrt (gammaOf β) : ℂ))
    else 0

/-- A state of the four DQI registers: the first register `A` (holds `d`), and the decoder's estimate
register `E`, the received register `R` and its work register `W`. -/
abbrev DQIState (M : ℕ) (W : Type*) := Reg M × (Reg M × Reg M × W) → ℂ

/-- Step (3.12) followed by (3.14): `|C^⊥|^{−1/2} ∑_{d ∈ C^⊥} (−1)^{d·v} |d⟩_A ⊗ |0⟩_E ⊗ |ψ_{d,γ}⟩_R ⊗ |w₀⟩_W`,
with `γ = gammaOf β` (pp.11–12; `∑_e F̂(e)|d + e⟩ = |ψ_{d,γ}⟩`). -/
noncomputable def dqiStart {M N : ℕ} {W : Type*} [DecidableEq W] (B : Matrix (Fin M) (Fin N) (ZMod 2))
    (v : Fin M → ZMod 2) (β : ℝ) (w₀ : W) : DQIState M W := fun s =>
  if s.1 ∈ dualCode B ∧ s.2.1 = 0 ∧ s.2.2.2 = w₀ then
    ((Real.sqrt (dualCode B).card)⁻¹ : ℝ) * sgn (s.1 ⬝ᵥ v) * psiState s.1 (gammaOf β) s.2.2.1
  else 0

/-- `I_A ⊗ U` applied to a DQI state. -/
noncomputable def applyDec {M : ℕ} {W : Type*} [Fintype W]
    (U : Matrix (Reg M × Reg M × W) (Reg M × Reg M × W) ℂ) (ψ : DQIState M W) : DQIState M W :=
  fun s => ∑ t, U s.2 t * ψ (s.1, t)

/-- `I_A ⊗ U†` applied to a DQI state. -/
noncomputable def applyDecAdj {M : ℕ} {W : Type*} [Fintype W]
    (U : Matrix (Reg M × Reg M × W) (Reg M × Reg M × W) ℂ) (ψ : DQIState M W) : DQIState M W :=
  fun s => ∑ t, star (U t s.2) * ψ (s.1, t)

/-- The copy `|a⟩_A |e⟩_E ↦ |a + e⟩_A |e⟩_E` (bitwise CNOTs from `E` into `A`). -/
noncomputable def copyEA {M : ℕ} {W : Type*} (ψ : DQIState M W) : DQIState M W :=
  fun s => ψ (s.1 + s.2.1, s.2)

/-- **The output distribution `𝒟_actual(B, J, β)` of the DQI procedure with the decoder unitary `U`**
(Theorem 3.1, p.12; procedure (3.11)–(3.16), pp.11–12). Starting from `dqiStart` ((3.12) with `Z^v` on the
first register, (3.14)), apply `Ũ := (I_A ⊗ U†) · CX_{E→A} · (I_A ⊗ U)` (in place of `Ũ_dec†`, (3.15)), apply
`Z^v` to the received register (3.16), apply the Hadamard transform to it, and measure it in the
computational basis; the other registers are discarded.

**Formalization Note** "`U_dec` replaces the idealized decoder `Ũ_dec`" is read as compute–copy–uncompute:
`Ũ` writes the decoder's estimate into the first register and uncomputes the decoder. When `U` is a perfect
decoder (`U |0, ψ_{d,γ}, w₀⟩ = |d⟩_E ⊗ |junk⟩`), `Ũ` maps `|d⟩_A|0, ψ_{d,γ}, w₀⟩` to `|0⟩_A|0, ψ_{d,γ}, w₀⟩`, which
is (3.13)–(3.15); `Ũ` is self-inverse. -/
noncomputable def Dactual {M N : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (B : Matrix (Fin M) (Fin N) (ZMod 2)) (v : Fin M → ZMod 2) (β : ℝ)
    (U : Matrix (Reg M × Reg M × W) (Reg M × Reg M × W) ℂ) (w₀ : W) (y : Reg M) : ℝ :=
  let ψ := applyDecAdj U (copyEA (applyDec U (dqiStart B v β w₀)))
  let ψ' : DQIState M W := fun s => sgn (s.2.2.1 ⬝ᵥ v) * ψ s
  ∑ a : Reg M, ∑ e : Reg M, ∑ w : W,
    Complex.normSq (hadamardT (fun r => ψ' (a, (e, r, w))) y)

/-- **The post-processing channel `K_B`** (proof of Theorem 2.4, p.13): on input `y ∈ C = {Bx}`, output
`z = (−1)^x` for `x` uniform on `A_y = {x : Bx = y}`; on input `y ∉ C`, output the fixed configuration
`z₀ = (−1)^{x₀}`. `postProcess B x₀ p` is the output law for an input law `p`. -/
noncomputable def postProcess {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (x₀ : Fin N → ZMod 2)
    (p : Reg M → ℝ) (x : Fin N → ZMod 2) : ℝ :=
  (∑ y ∈ univ.image B.mulVec,
      p y * (if B.mulVec x = y then ((univ.filter fun x' => B.mulVec x' = y).card : ℝ)⁻¹ else 0)) +
    (if x = x₀ then ∑ y ∈ univ.filter (fun y => y ∉ univ.image B.mulVec), p y else 0)

/-- **The DQI sampler's output law** `ν^{DQI}_{B,J,β} := K_B 𝒟_actual(B, J, β)` (proof of Theorem 2.4,
p.13), for the decoder unitary `U` and the fixed configuration `z₀ = (−1)^{x₀}`. -/
noncomputable def nuDQI {M N : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (B : Matrix (Fin M) (Fin N) (ZMod 2)) (v : Fin M → ZMod 2) (β : ℝ)
    (U : Matrix (Reg M × Reg M × W) (Reg M × Reg M × W) ℂ) (w₀ : W) (x₀ : Fin N → ZMod 2) :
    (Fin N → ZMod 2) → ℝ :=
  postProcess B x₀ (Dactual B v β U w₀)

end DQIShattered


