-- Prove2me | Definitions.Def_FlexRigidity_Supplement_Basics
-- name    : FlexRigidity_Supplement_Basics
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:06:12.716994+00:00
-- url     : https://prove2.me/theorems/52b7646c-9750-4766-a258-1045b3f82d10
-- title:
--   Binary entropy in bits, bitwise operations over $\mathbb F_2$, two-universal families, and the lengths $m$ and $s$
-- statement:
--   Elementary notions shared by the protocols of §6.
--
--   1. The **binary entropy in bits** $h_{\mathrm{bin}}(p)=-p\log_2p-(1-p)\log_2(1-p)$ (all logarithms in the paper are base $2$).
--   2. For bit strings $u,v\in\{0,1\}^m$: the bitwise XOR $u\oplus v$ and the inner product $r\cdot x=\sum_j r_jx_j \bmod 2$ over $\mathbb F_2$; for a binary $\tau\times m$ matrix $R$, the product $Rx\in\{0,1\}^\tau$ over $\mathbb F_2$.
--   3. A family $\{h_d:K\to\{0,1\}^\ell\}_{d\in D}$ indexed by a finite seed set $D$ is **two-universal** if for all distinct $k,k'$,
--   $$\Pr_{D}[h_D(k)=h_D(k')]\le 2^{-\ell},$$
--   with $D$ uniform.
--   4. The key length of Protocol 2, $m=\lfloor(1-\gamma)n/2\rfloor$, and the syndrome length of Fact 6.3, $s=\lfloor 2m\,h_{\mathrm{bin}}(\delta_{\mathrm{err}})\rfloor$.
--
--   These are used by the statements of Theorems 6.6–6.14.
--
--   **Formalization Note** Mathlib's `Real.binEntropy` is in nats, so $h_{\mathrm{bin}}$ is it divided by $\ln 2$. Bits are `Bool`.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d0306379cc99bf71e2a9200405805925b8b1d8429e876e9655a3fe12c), p. 17 (log base 2), Protocol 2 p. 40 (m), Fact 6.3 p. 63 (s, h_bin), Protocols 4–5 pp. 65–67 (r·m, Rx), Fact 6.13 p. 71 (two-universal)

import Mathlib

set_option autoImplicit false

noncomputable section

namespace FlexRigidity.Supplement

/-- **Binary entropy in bits** `h_bin(p) = −p log₂ p − (1 − p) log₂(1 − p)` (Arqand–Kundu–Tan,
*Flexible rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, p. 17 ("log is base 2") and
Fact 6.3, p. 63).

**Formalization Note** Mathlib's `Real.binEntropy` is in nats; dividing by `log 2` gives bits. -/
def hbin (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

/-- Bitwise XOR `u ⊕ v` of two bit strings of length `m`. -/
def xorS {m : ℕ} (u v : Fin m → Bool) : Fin m → Bool := fun j => xor (u j) (v j)

/-- The inner product `r · x` over `𝔽₂` of two bit strings (p. 65, Fact 6.7 and Protocol 4). -/
def dotF2 {m : ℕ} (r x : Fin m → Bool) : Bool :=
  decide (Odd (Finset.univ.filter fun j => r j = true ∧ x j = true).card)

/-- The product `Rx` over `𝔽₂` of a binary `τ × m` matrix `R` (rows `R i`) and a string
`x ∈ {0,1}^m` (Protocol 5, p. 67). -/
def matVecF2 {τ m : ℕ} (R : Fin τ → Fin m → Bool) (x : Fin m → Bool) : Fin τ → Bool :=
  fun i => dotF2 (R i) x

/-- **Two-universal family** `{h_d : K → {0,1}^ℓ}_{d ∈ D}` (Fact 6.13, p. 71): for distinct
`k, k′`, `Pr_D[h_D(k) = h_D(k′)] ≤ 2^{−ℓ}` with `D` uniform on the finite seed set. -/
def IsTwoUniversal {D K : Type} [Fintype D] (ℓ : ℕ) (h : D → K → (Fin ℓ → Bool)) : Prop :=
  ∀ k k' : K, k ≠ k' →
    ((Finset.univ.filter fun d => h d k = h d k').card : ℝ) ≤ (Fintype.card D : ℝ) / 2 ^ ℓ

/-- The key length `m = ⌊(1 − γ) n / 2⌋` of Protocol 2 (p. 40), used by Protocols 3–6. -/
def mLen (γ : ℝ) (n : ℕ) : ℕ := ⌊(1 - γ) * n / 2⌋₊

/-- The syndrome length `s = ⌊2 m h_bin(δ_err)⌋` of Fact 6.3 (p. 63). -/
def synLen (δerr : ℝ) (m : ℕ) : ℕ := ⌊2 * m * hbin δerr⌋₊

end FlexRigidity.Supplement


