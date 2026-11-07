-- Prove2me | Definitions.Def_RegevRecon_RegevPipeline
-- name    : RegevRecon_RegevPipeline
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:36.30063+00:00
-- url     : https://prove2.me/theorems/7ef73bce-3948-4042-b257-28c397fa6274
-- title:
--   Regev's reduction with a coherent decoder: code, received state, block error, output state and the overlap of (42)
-- statement:
--   For $B\in\mathbb F_p^{m\times n}$, let $C^\perp=\{d:B^Td=0\}$. The received state $|v_d\rangle$ is the product over $j$ of $\sum_e\tilde P(e)/\|P\|_2\,|d_j+e\rangle$, with $\tilde P$ the unitary Fourier transform of the envelope $P(a)=1$ on $S$ and $e^{-\beta/2}$ off it. A coherent decoder is a unitary $U_{\mathrm{dec}}$ on received, estimate and work registers; its **block error** $\varepsilon_B$ is the average over $d\in C^\perp$ of the probability that the estimate register of $U_{\mathrm{dec}}(|v_d\rangle|0\rangle)$ does not read $d$.
--
--   For offsets $\tau$, the pipeline prepares $|C^\perp|^{-1/2}\sum_{d}\omega^{-\langle\tau,d\rangle}|d\rangle\otimes U_{\mathrm{dec}}(|v_d\rangle|0\rangle)$, keeps the branch where the estimate agrees with $d$, subtracts it, normalizes, reverses $U_{\mathrm{dec}}$, applies $Z_\tau|y\rangle=\omega^{\langle\tau,y\rangle}|y\rangle$ and the inverse Fourier transform, and maps the received register to the $x$ register through a unitary extension of
--
--   $$
--   |c\rangle|0\rangle\mapsto|0\rangle\frac1{\sqrt{|\ker B|}}\sum_{x:Bx=c}|x\rangle\qquad(18).
--   $$
--
--   The overlap is $(\langle\psi_\beta|\otimes\langle0|_{\mathrm{work}})|\Psi_{B,\tau}\rangle$ for the instance with $F_j=\tau_j+S$.
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), §3, (6)–(24), pp.7–9; (27), p.10; pp.16–17

import Mathlib
import Definitions.Def_RegevRecon_GibbsState

namespace RegevRecon

open Finset Matrix
open scoped Kronecker

variable {p m n : ℕ} [Fact p.Prime]

/-- The code `C^⊥ = {d ∈ F_p^m : Bᵀ d = 0}`, Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), (6), p.7. -/
noncomputable def dualCode (B : Matrix (Fin m) (Fin n) (ZMod p)) : Finset (Fin m → ZMod p) :=
  univ.filter fun d => Bᵀ *ᵥ d = 0

/-- The envelope `P(a) = 1` for `a ∈ S`, `e^{−β/2}` otherwise, (21), p.8, with `F_j = S`. -/
noncomputable def envelope (S : Finset (ZMod p)) (β : ℝ) (a : ZMod p) : ℝ :=
  if a ∈ S then 1 else Real.exp (-β / 2)

/-- Its unitary Fourier transform, (11), p.7, (24), p.9. -/
noncomputable def envelopeFT (S : Finset (ZMod p)) (β : ℝ) (e : ZMod p) : ℂ :=
  ((Real.sqrt p : ℝ) : ℂ)⁻¹ * ∑ a, zeta (e * a) * (envelope S β a : ℂ)

/-- **The normalized received state** `|v_d⟩`, (14), p.7, (27), p.10, with every target set equal to `S`
(p.16): a product over the `m` symbols, each normalized by `‖P^(j)‖₂ = √c_β`. -/
noncomputable def receivedState (S : Finset (ZMod p)) (β : ℝ) (d : Fin m → ZMod p) :
    EuclideanSpace ℂ (Fin m → ZMod p) :=
  WithLp.toLp 2 fun r => ∏ j, (envelopeFT S β (r j - d j) / ((Real.sqrt (cBeta S β) : ℝ) : ℂ))

/-- The decoder's input `|v_d⟩ ⊗ |0⟩_estimate ⊗ |w₀⟩_work`. -/
noncomputable def decoderInput {W : Type*} [DecidableEq W] (S : Finset (ZMod p)) (β : ℝ) (w₀ : W)
    (d : Fin m → ZMod p) : EuclideanSpace ℂ ((Fin m → ZMod p) × (Fin m → ZMod p) × W) :=
  WithLp.toLp 2 fun x => if x.2.1 = 0 ∧ x.2.2 = w₀ then receivedState S β d x.1 else 0

/-- **The block error** of a coherent decoder `U` on a uniformly chosen codeword (p.16): the average over
`d ∈ C^⊥` of the probability that the estimate register of `U(|v_d⟩|0⟩)` does not read `d`. -/
noncomputable def blockError {W : Type*} [Fintype W] [DecidableEq W]
    (B : Matrix (Fin m) (Fin n) (ZMod p)) (S : Finset (ZMod p)) (β : ℝ)
    (U : Matrix ((Fin m → ZMod p) × (Fin m → ZMod p) × W)
      ((Fin m → ZMod p) × (Fin m → ZMod p) × W) ℂ) (w₀ : W) : ℝ :=
  ((dualCode B).card : ℝ)⁻¹ * ∑ d ∈ dualCode B,
    (1 - ∑ r : Fin m → ZMod p, ∑ w : W,
      ‖(U *ᵥ (WithLp.ofLp (decoderInput S β w₀ d))) (r, d, w)‖ ^ 2)

/-- The state after the phase and the decoding unitary (p.16), registers `d` and `(received, estimate, work)`:
`|C^⊥|^{−1/2} Σ_{d ∈ C^⊥} ω^{−⟨τ,d⟩} |d⟩ ⊗ U_dec(|v_d⟩|0⟩)`. -/
noncomputable def decodedState {W : Type*} [Fintype W] [DecidableEq W]
    (B : Matrix (Fin m) (Fin n) (ZMod p)) (S : Finset (ZMod p)) (β : ℝ)
    (U : Matrix ((Fin m → ZMod p) × (Fin m → ZMod p) × W)
      ((Fin m → ZMod p) × (Fin m → ZMod p) × W) ℂ) (w₀ : W) (τ : Fin m → ZMod p) :
    EuclideanSpace ℂ ((Fin m → ZMod p) × (Fin m → ZMod p) × (Fin m → ZMod p) × W) :=
  WithLp.toLp 2 fun x =>
    if x.1 ∈ dualCode B then
      ((Real.sqrt ((dualCode B).card : ℝ) : ℝ) : ℂ)⁻¹ * zeta (-(τ ⬝ᵥ x.1)) *
        (U *ᵥ (WithLp.ofLp (decoderInput S β w₀ x.1))) x.2
    else 0

/-- The accepting branch after the agreement test and the subtraction (pp.16–17): keep the terms where the
estimate agrees with register `d`, and subtract it from that register, which then reads `0`. Unnormalized. -/
noncomputable def acceptedState {W : Type*} [Fintype W] [DecidableEq W]
    (B : Matrix (Fin m) (Fin n) (ZMod p)) (S : Finset (ZMod p)) (β : ℝ)
    (U : Matrix ((Fin m → ZMod p) × (Fin m → ZMod p) × W)
      ((Fin m → ZMod p) × (Fin m → ZMod p) × W) ℂ) (w₀ : W) (τ : Fin m → ZMod p) :
    EuclideanSpace ℂ ((Fin m → ZMod p) × (Fin m → ZMod p) × (Fin m → ZMod p) × W) :=
  WithLp.toLp 2 fun x =>
    if x.1 = 0 then decodedState B S β U w₀ τ (x.2.2.1, x.2) else 0

/-- The inverse Fourier transform `QFT†|e⟩ = p^{−m/2} Σ_y ω^{−⟨e,y⟩} |y⟩` over `F_p^m` (inverse of (11), p.7). -/
noncomputable def qftInv (p m : ℕ) [Fact p.Prime] :
    Matrix (Fin m → ZMod p) (Fin m → ZMod p) ℂ :=
  Matrix.of fun y e => (((Real.sqrt p : ℝ) : ℂ) ^ m)⁻¹ * zeta (-(e ⬝ᵥ y))

/-- **The normalized output `|Ψ_{B,τ}⟩` before the map (18)**, p.17: normalize the accepting branch, reverse
`U_dec`, apply `Z_τ |y⟩ = ω^{⟨τ,y⟩}|y⟩` to the received register, then the inverse Fourier transform. -/
noncomputable def regevOutput {W : Type*} [Fintype W] [DecidableEq W]
    (B : Matrix (Fin m) (Fin n) (ZMod p)) (S : Finset (ZMod p)) (β : ℝ)
    (U : Matrix ((Fin m → ZMod p) × (Fin m → ZMod p) × W)
      ((Fin m → ZMod p) × (Fin m → ZMod p) × W) ℂ) (w₀ : W) (τ : Fin m → ZMod p) :
    EuclideanSpace ℂ ((Fin m → ZMod p) × (Fin m → ZMod p) × (Fin m → ZMod p) × W) :=
  WithLp.toLp 2
    ((((1 : Matrix (Fin m → ZMod p) (Fin m → ZMod p) ℂ) ⊗ₖ
        (((qftInv p m * Matrix.diagonal fun y => zeta (τ ⬝ᵥ y)) ⊗ₖ
          (1 : Matrix ((Fin m → ZMod p) × W) ((Fin m → ZMod p) × W) ℂ)) * star U)) *ᵥ
      (WithLp.ofLp ((‖acceptedState B S β U w₀ τ‖⁻¹ : ℂ) • acceptedState B S β U w₀ τ))))

/-- **The map (18), extended to a unitary** on `received ⊗ x`: `W` is unitary and sends `|c⟩|0⟩` to
`|0⟩ |ker B|^{−1/2} Σ_{x : Bx = c} |x⟩` for every `c ∈ C`, p.8. -/
def IsKernelMap (B : Matrix (Fin m) (Fin n) (ZMod p))
    (W : Matrix ((Fin m → ZMod p) × (Fin n → ZMod p)) ((Fin m → ZMod p) × (Fin n → ZMod p)) ℂ) :
    Prop :=
  W ∈ Matrix.unitaryGroup _ ℂ ∧
    ∀ (x₀ : Fin n → ZMod p) (r : Fin m → ZMod p) (x : Fin n → ZMod p),
      W (r, x) (B *ᵥ x₀, 0) =
        if r = 0 ∧ B *ᵥ x = B *ᵥ x₀ then
          ((Real.sqrt ((univ.filter fun y : Fin n → ZMod p => B *ᵥ y = 0).card : ℝ) : ℝ) : ℂ)⁻¹
        else 0

/-- **The overlap** `(⟨ψ_β| ⊗ ⟨0|_work) |Ψ_{B,τ}⟩` of (42), p.17, where the output has passed through the map
(18) (`W`, on the received register and a fresh `x` register in `|0⟩`); "work" is every other register. -/
noncomputable def regevOverlap {W' : Type*} [Fintype W'] [DecidableEq W']
    (B : Matrix (Fin m) (Fin n) (ZMod p)) (S : Finset (ZMod p)) (β : ℝ)
    (U : Matrix ((Fin m → ZMod p) × (Fin m → ZMod p) × W')
      ((Fin m → ZMod p) × (Fin m → ZMod p) × W') ℂ) (w₀ : W')
    (W : Matrix ((Fin m → ZMod p) × (Fin n → ZMod p)) ((Fin m → ZMod p) × (Fin n → ZMod p)) ℂ)
    (τ : Fin m → ZMod p) : ℂ :=
  ∑ x : Fin n → ZMod p, ((Real.sqrt (gibbsProb B (targetSets S τ) β x) : ℝ) : ℂ) *
    ∑ r : Fin m → ZMod p, W (0, x) (r, 0) * regevOutput B S β U w₀ τ (0, r, 0, w₀)

end RegevRecon


