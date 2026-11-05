-- Prove2me | Definitions.Def_MayersQKD_rhoX
-- name    : MayersQKD_rhoX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:42:33.49947+00:00
-- url     : https://prove2.me/theorems/ad32bc88-07ca-4ef0-a86e-75c10e0bc364
-- title:
--   The density operators $\rho_x$, $\rho^{(j)}$, the operators $U_\beta$ and the codes $C^{(j)\perp}$, $C_0^\perp$
-- statement:
--   Consider $N$ photons sent in the bases $\theta$. Let $f$ be an $(r+m)\times N$ boolean matrix and $C_x=\{\beta\mid f\beta=x\}$. With $k=N-r-m$,
--
--   $$
--   \rho_x=2^{-k}\sum_{\beta\in C_x}|\psi_{\beta,\theta}\rangle\langle\psi_{\beta,\theta}| .
--   $$
--
--   The unitary $U_\beta$ acts by $U_\beta|\psi_{\beta',\theta}\rangle=|\psi_{\beta\oplus\beta',\theta}\rangle$. The matrix of an operator $\rho$ in Bob's basis is $(\rho)_{\alpha,\alpha'}=\langle\psi_{\alpha,\hat\theta}|\rho|\psi_{\alpha',\hat\theta}\rangle$. For a family $\beta_1,\dots,\beta_k$, $C^{(j)}$ is the span of the first $j$ vectors and $\rho^{(j)}=2^{-j}\sum_{\beta\in C^{(j)}}|\psi_{\beta,\theta}\rangle\langle\psi_{\beta,\theta}|$. $C^\perp$ is the set of $z$ with $z\odot\beta=0$ for all $\beta\in C$, and $C_0^\perp$ is the span of the rows of $f$.
--
--   These are the objects of §9: the state of the photons of $E_1$ given what Alice announces.
--
--   **Formalization Note** $k$ is an integer exponent, so no truncated subtraction occurs. $U_\beta$ is written as $\sum_{\beta'}|\psi_{\beta\oplus\beta',\theta}\rangle\langle\psi_{\beta',\theta}|$, which is the page's definition on the orthonormal basis $\{|\psi_{\beta',\theta}\rangle\}$.
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, §8, pp.10–11; §9, pp.11–12

import Mathlib
import Definitions.Def_MayersBC_bb84State
import Definitions.Def_MayersQKD_Bits

namespace MayersQKD

open MayersBC

variable {N r m : ℕ}

/-- `∑_{β ∈ S} |ψ_{β,θ}⟩⟨ψ_{β,θ}|`, for a set `S` of strings. -/
noncomputable def stateSum (θ : Bases N) (S : Finset (Bits N)) : Photons N →L[ℂ] Photons N :=
  ∑ β ∈ S, InnerProductSpace.rankOne ℂ (bb84State θ β) (bb84State θ β)

open Classical in
/-- Mayers, arXiv:quant-ph/9606003v1, §8, p.10: `C_x = {β ∈ {0, 1}^N | f β = x}`. `C₀` is `C_x` at
`x = 0`. -/
noncomputable def coset (f : HashMatrix r m N) (x : Fin r ⊕ Fin m → ZMod 2) : Finset (Bits N) :=
  Finset.univ.filter fun β => f.mulVec β = x

/-- Mayers, arXiv:quant-ph/9606003v1, §8, p.11 and §9: `ρ_x = 2⁻ᵏ ∑_{β ∈ C_x} |ψ_{β,θ}⟩⟨ψ_{β,θ}|`
with `k = N − r − m`.

**Formalization Note.** `k` is an integer here (`zpow`), so there is no truncated subtraction. -/
noncomputable def rhoX (f : HashMatrix r m N) (θ : Bases N) (x : Fin r ⊕ Fin m → ZMod 2) :
    Photons N →L[ℂ] Photons N :=
  ((2 : ℂ) ^ ((r : ℤ) + m - N)) • stateSum θ (coset f x)

/-- Mayers, arXiv:quant-ph/9606003v1, §9, p.11: the transformation `U_β` on the photons, with
`U_β |ψ_{β′,θ}⟩ = |ψ_{β⊕β′,θ}⟩`.

**Formalization Note.** `{|ψ_{β′,θ}⟩}` is an orthonormal basis, so `U_β` is written as the sum of
`|ψ_{β⊕β′,θ}⟩⟨ψ_{β′,θ}|` over `β′`. -/
noncomputable def shiftU (θ : Bases N) (β : Bits N) : Photons N →L[ℂ] Photons N :=
  ∑ β', InnerProductSpace.rankOne ℂ (bb84State θ (β + β')) (bb84State θ β')

/-- Mayers, arXiv:quant-ph/9606003v1, §4, p.6: the matrix representation
`(ρ)_{α,α′} = ⟨ψ_α|ρ|ψ_{α′}⟩` of `ρ`, here in Bob's basis `{|ψ_{α,θ̂}⟩}`. -/
noncomputable def matEntry (θhat : Bases N) (ρ : Photons N →L[ℂ] Photons N) (α α' : Bits N) : ℂ :=
  inner ℂ (bb84State θhat α) (ρ (bb84State θhat α'))

/-- Mayers, arXiv:quant-ph/9606003v1, §9, p.12: `C^(j)`, the span of the first `j` vectors
`β₁, …, β_j` of a family. -/
noncomputable def prefixSpan {k : ℕ} (bs : Fin k → Bits N) (j : ℕ) : Submodule (ZMod 2) (Bits N) :=
  Submodule.span (ZMod 2) (bs '' {i | i.val < j})

open Classical in
/-- Mayers, arXiv:quant-ph/9606003v1, §9, p.12: `ρ^(j) = 2⁻ʲ ∑_{β ∈ C^(j)} |ψ_{β,θ}⟩⟨ψ_{β,θ}|`. -/
noncomputable def rhoPrefix {k : ℕ} (bs : Fin k → Bits N) (θ : Bases N) (j : ℕ) :
    Photons N →L[ℂ] Photons N :=
  ((1 / 2 : ℂ) ^ j) • stateSum θ (Finset.univ.filter fun β => β ∈ prefixSpan bs j)

/-- Mayers, arXiv:quant-ph/9606003v1, §9, p.12: the dual code `C⊥`, the strings `z` with
`z ⊙ β = 0` for every `β ∈ C`. Here `⊙` is `⬝ᵥ` over `GF(2)`. -/
def dualCode (C : Submodule (ZMod 2) (Bits N)) : Set (Bits N) :=
  {z | ∀ β ∈ C, z ⬝ᵥ β = 0}

/-- Mayers, arXiv:quant-ph/9606003v1, §8, p.10: `C₀⊥`, the span of the `r + m` rows of `f` seen as
vectors of `GF(2)^N`. -/
def rowCode (f : HashMatrix r m N) : Submodule (ZMod 2) (Bits N) :=
  Submodule.span (ZMod 2) (Set.range fun i => f i)

end MayersQKD


