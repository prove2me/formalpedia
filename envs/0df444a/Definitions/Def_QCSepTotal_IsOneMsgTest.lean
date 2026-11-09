-- Prove2me | Definitions.Def_QCSepTotal_IsOneMsgTest
-- name    : QCSepTotal_IsOneMsgTest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:48.495769+00:00
-- url     : https://prove2.me/theorems/2f07942c-3ad0-48ca-8081-29a9315afc0a
-- title:
--   One-message randomized certificate tests (Proposition 2.4, property 3)
-- statement:
--   Two notions of a **one-message test** are fixed here.
--
--   1. *Generic test.* The sender holds $s_A$, the receiver holds $s_B$, and a condition $\mathrm{valid}(s_A,s_B)$ is to be tested. The sender draws a challenge $\omega$ uniformly from a finite nonempty set, independently of the inputs, and sends a message of $\ell$ bits computed from $\omega$ and $s_A$; the receiver decides acceptance from the message and $s_B$. The test accepts with probability $1$ when the condition holds, and with probability at most $1/64$ otherwise.
--   2. *Affine-share test.* An input $z\in\mathbb F_2^m$ and a certificate $p\in\mathbb F_2^{b_0}$ are additively shared, the sender holding $(z_A,p_A)$ and the receiver $(z_B,p_B)$, with $z=z_A+z_B$ and $p=p_A+p_B$. The sender draws a challenge $\omega\in\mathbb F_2^\ell$ uniformly, independently of the input and the certificate, and sends one message consisting of $\omega$ and four answer shares in $\mathbb F_2^w$, each an affine function of its share. The receiver decides acceptance from the message and its own share. The test accepts with probability $1$ when $V_0(z;p)=1$ and with probability at most $1/64$ otherwise. The message has $\ell+4w$ bits.
--
--   The affine-share test is property 3 of Proposition 2.4. The generic test is the hypothesis of Theorem 3.2, where Alice holds $x$ with her certificate share and Bob holds $y$ with his.
--
--   **Formalization Note** In the affine-share test, "affine" means affine over $\mathbb F_2$; an answer share in an extension field of $\mathbb F_2$ is represented as an element of $\mathbb F_2^w$. Its condition is symmetric in the two shares, so the same test can be run in either direction.
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), Proposition 2.4, property 3, p.6

import Mathlib

namespace QCSepTotal

/-- A **one-message randomized test** of length `len` (F. Le Gall, *Improved Separations between
Quantum and Classical Communication Complexity of Total Functions*, arXiv:2609.16726, held
version sha256 970e1476…, Proposition 2.4, property 3, p.6). The sender holds `sA : SA`, the
receiver holds `sB : SB`, and `valid sA sB` is the condition being tested. The sender draws a
challenge `ω` uniformly from `Fin k` (`k ≥ 1`), independently of the inputs, and sends the
`len`-bit message `send ω sA`; the receiver decides acceptance from the message and its own
share. The test accepts with probability `1` when `valid sA sB` holds and with probability at
most `1/64` otherwise. -/
def IsOneMsgTest {SA SB : Type} (valid : SA → SB → Bool) (len : ℕ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ (send : Fin k → SA → Fin len → Bool) (acc : (Fin len → Bool) → SB → Bool),
    (∀ sA sB, valid sA sB = true → ∀ ω, acc (send ω sA) sB = true) ∧
    (∀ sA sB, valid sA sB = false →
      ((Finset.univ.filter fun ω => acc (send ω sA) sB = true).card : ℝ) / k ≤ 1 / 64)

/-- The **test of Proposition 2.4, property 3** (arXiv:2609.16726, held version sha256
970e1476…, p.6), with its message structure: the input `z ∈ F₂^m` and the certificate
`p ∈ F₂^{b₀}` are additively shared, the sender holding `(z_A, p_A)` and the receiver
`(z_B, p_B)` with `z = z_A + z_B`, `p = p_A + p_B`. The sender draws a random challenge
`ω ∈ F₂^ℓ` uniformly, independently of the input and certificate, and sends one message
consisting of `ω` and four answer shares `a_1, …, a_4 ∈ F₂^w`, each an affine function of its
share; the receiver decides acceptance from the message and its own share. The test accepts with
probability `1` when `V₀(z; p) = 1` and with probability at most `1/64` otherwise. The message has
`ℓ + 4w` bits.

**Formalization Note.** Shares are pairs `(z_X, p_X)` in the `F₂`-vector space
`F₂^m × F₂^{b₀}`; "affine" is `F₂`-affine (an answer share over an extension field `F` of `F₂` is
an element of `F₂^w`). The condition is symmetric in the two shares, so the same test can be run
in either direction. -/
def IsAffineShareTest {m b₀ : ℕ} (V₀ : (Fin m → ZMod 2) → (Fin b₀ → ZMod 2) → Bool)
    (ℓ w : ℕ) : Prop :=
  ∃ (ans : (Fin ℓ → ZMod 2) → Fin 4 →
      ((Fin m → ZMod 2) × (Fin b₀ → ZMod 2)) →ᵃ[ZMod 2] (Fin w → ZMod 2))
    (acc : (Fin ℓ → ZMod 2) → (Fin 4 → Fin w → ZMod 2) →
      (Fin m → ZMod 2) × (Fin b₀ → ZMod 2) → Bool),
    (∀ sA sB : (Fin m → ZMod 2) × (Fin b₀ → ZMod 2), V₀ (sA.1 + sB.1) (sA.2 + sB.2) = true →
      ∀ ω, acc ω (fun i => ans ω i sA) sB = true) ∧
    (∀ sA sB : (Fin m → ZMod 2) × (Fin b₀ → ZMod 2), V₀ (sA.1 + sB.1) (sA.2 + sB.2) = false →
      ((Finset.univ.filter fun ω => acc ω (fun i => ans ω i sA) sB = true).card : ℝ) / 2 ^ ℓ
        ≤ 1 / 64)

end QCSepTotal


