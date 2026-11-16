-- Prove2me | Definitions.Def_FlexRigidity_Supplement_Decision
-- name    : FlexRigidity_Supplement_Decision
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:10:20.496908+00:00
-- url     : https://prove2.me/theorems/9d328505-d7a7-4023-a2f0-4815f12775e5
-- title:
--   The decision experiment for Protocol 4 (Definition 6.2)
-- statement:
--   Protocol 4 adds to Protocol 3's key $k$ an independent uniform $r\in\{0,1\}^m$ and an independent uniform bit $z$; to encrypt a bit $d$, Alice encrypts a uniform $\mathbf m\in\{0,1\}^m$ as in Protocol 3 and appends $e=d\oplus z\oplus(r\cdot\mathbf m)$.
--
--   In the **decision experiment**, after acceptance Bob chooses the two distinct one-bit challenges $(d_0,d_1)=(d_0,1-d_0)$ by an instrument $\{J_{d_0}\}$ on his register, keeping the post-measurement state; Alice encrypts $d_b=d_0\oplus b$ for an independent uniform bit $b$; Bob splits with a channel $\Lambda_{d_0,c_{\mathrm{msg}},\sigma,e}$ into two decoders, which receive $(k,r,z)$ only after the split and output bits $b_1,b_2$ by measurements on their own registers. With $\rho^B_{k,a}$ as in Protocol 3,
--   $$\Pr_{P'}[\mathrm{Acc}\wedge\mathrm{Bad}_{\mathrm{dec}}]=\sum_{k,a,r,z,b,\mathbf m,d_0}\frac{1}{2^m\cdot2\cdot2\cdot2^m}\operatorname{Tr}\big[(F^1(b)\otimes F^2(b))\,\Lambda_{d_0,c,\sigma,e}(J_{d_0}(\rho^B_{k,a}))\big],$$
--   where $c=\mathbf m\oplus a$, $\sigma=\mathrm{syn}(a)$, $e=d_0\oplus b\oplus z\oplus(r\cdot\mathbf m)$ and the decoders' POVMs $F^j$ depend on $(k,r,z)$ and the public data. $\mathrm{Bad}_{\mathrm{dec}}=\{b_1=b_2=b\}$ is false on abort.
--
--   This is the experiment of Theorem 6.8.
--
--   **Formalization Note** For one-bit plaintexts the challenge pair is $\{0,1\}$ (p. 61), so Bob's choice is the bit $d_0$; the instrument has completely positive elements summing to a channel.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d0306379cc99bf71e2a9200405805925b8b1d8429e876e9655a3fe12c), Definition 6.2 p. 61, Protocol 4 p. 65

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_IsCPMap
import Definitions.Def_FlexRigidity_Supplement_Basics

set_option autoImplicit false

open scoped Matrix ComplexOrder
open QAlgorithms (Superop IsChannel)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr POVM)

noncomputable section

namespace FlexRigidity.Supplement

/-- **An attack in the decision experiment of Protocol 4 after preparation** (Arqand–Kundu–Tan,
*Flexible rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, Definition 6.2, p. 61, and
Protocol 4, p. 65). On acceptance Bob chooses his two distinct one-bit challenges `(d₀, d₁ = 1 − d₀)`
by an instrument `{J_{d₀}}` on his register (keeping the post-measurement state); after the
encryption he splits with a channel `Λ` that may depend on `d₀` and the public ciphertext
`(c_msg, σ, e)`; decoder `j` then receives the complete key `(k, r, z)` and outputs a bit with its own
measurement on its own register. -/
structure DecisionAttack (m s d : ℕ) where
  /-- dimension of Bob's register after choosing the challenges -/
  dJ : ℕ
  /-- Bob's challenge-choosing instrument, outcome `d₀` -/
  J : Bool → Superop (Fin d) (Fin dJ)
  /-- dimension of decoder 1's register -/
  d1 : ℕ
  /-- dimension of decoder 2's register -/
  d2 : ℕ
  /-- splitting channel, given `d₀`, `c_msg`, `σ`, `e` -/
  Λ : Bool → (Fin m → Bool) → (Fin s → Bool) → Bool → Superop (Fin dJ) (Fin d1 × Fin d2)
  /-- decoder 1's measurement, given `k, r, z, d₀, c_msg, σ, e`; outcome `b₁` -/
  F1 : (Fin m → Bool) → (Fin m → Bool) → Bool → Bool → (Fin m → Bool) → (Fin s → Bool) → Bool →
    Bool → Matrix (Fin d1) (Fin d1) ℂ
  /-- decoder 2's measurement, given `k, r, z, d₀, c_msg, σ, e`; outcome `b₂` -/
  F2 : (Fin m → Bool) → (Fin m → Bool) → Bool → Bool → (Fin m → Bool) → (Fin s → Bool) → Bool →
    Bool → Matrix (Fin d2) (Fin d2) ℂ

/-- `J` is an instrument (CP elements summing to a channel), the `Λ` are channels and the decoders'
measurements are POVMs. -/
def DecisionAttack.IsValid {m s d : ℕ} (att : DecisionAttack m s d) : Prop :=
  (∀ d0, IsCPMap (att.J d0)) ∧ IsChannel (fun ρ => ∑ d0, att.J d0 ρ) ∧
    (∀ d0 c σ e, IsChannel (att.Λ d0 c σ e)) ∧
    (∀ k r z d0 c σ e, POVM (att.F1 k r z d0 c σ e)) ∧
    (∀ k r z d0 c σ e, POVM (att.F2 k r z d0 c σ e))

/-- **`Pr_{P′}[Acc ∧ Bad_dec]`** for Protocol 4 (Definition 6.2 and Protocol 4, pp. 61, 65). The
preparation output on `Acc ∧ (x_E, a_E) = (k, a)` is `ρB (k, a)`; the key parts `r ∈ {0,1}^m` and
`z ∈ {0,1}`, the challenge bit `b` and the raw plaintext `msg ∈ {0,1}^m` are uniform and
independent; Alice encrypts `d_b = d₀ ⊕ b` as `c_msg = msg ⊕ a`, `σ = syn(a)`,
`e = d_b ⊕ z ⊕ (r · msg)`; `Bad_dec = {b₁ = b₂ = b}` (false on abort). -/
def decSucc {m s d : ℕ} (ρB : (Fin m → Bool × Bool) → Matrix (Fin d) (Fin d) ℂ)
    (syn : (Fin m → Bool) → Fin s → Bool) (att : DecisionAttack m s d) : ℝ :=
  ∑ xa : Fin m → Bool × Bool, ∑ r : Fin m → Bool, ∑ z : Bool, ∑ b : Bool, ∑ msg : Fin m → Bool,
    ∑ d0 : Bool,
      (1 / 2 ^ m : ℝ) * (1 / 2) * (1 / 2) * (1 / 2 ^ m : ℝ) *
        tr (Matrix.kronecker
              (att.F1 (fun j => (xa j).1) r z d0 (xorS msg fun j => (xa j).2)
                (syn fun j => (xa j).2) (xor (xor (xor d0 b) z) (dotF2 r msg)) b)
              (att.F2 (fun j => (xa j).1) r z d0 (xorS msg fun j => (xa j).2)
                (syn fun j => (xa j).2) (xor (xor (xor d0 b) z) (dotF2 r msg)) b) *
            att.Λ d0 (xorS msg fun j => (xa j).2) (syn fun j => (xa j).2)
              (xor (xor (xor d0 b) z) (dotF2 r msg)) (att.J d0 (ρB xa)))

end FlexRigidity.Supplement


