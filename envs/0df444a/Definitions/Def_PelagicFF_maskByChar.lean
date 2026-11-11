-- Prove2me | Definitions.Def_PelagicFF_maskByChar
-- name    : PelagicFF_maskByChar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:54:35.565224+00:00
-- url     : https://prove2.me/theorems/7d1e977d-7538-40c4-bd61-cae5db962689
-- title:
--   Entrywise product $G\odot\chi_y$ of a truth table with a character
-- statement:
--   Let $N=2^n$. For a truth table $G\in\{-1,1\}^N$ (indexed by $x\in\{0,1\}^n$) and $y\in\{0,1\}^n$,
--   $$(G\odot\chi_y)(x)=G(x)\,(-1)^{x\cdot y}.$$
--
--   The map $V_\tau(G)=G\odot\chi_{y_\tau(G)}$ of the lower bound (p.30) turns the Fourier coefficient selected by Bob into an inner product: $\widehat h(y_\tau(G))=\langle F,V_\tau(G)\rangle/N$.
--
--   **Formalization Note** In the bit encoding the bit $G(x)$ is xored with the parity of $\#\{i: x_i=y_i=1\}$.
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), §4.2.2, p.30

import Mathlib

namespace PelagicFF

/-- The entrywise product `G ⊙ χ_y` of a truth table `G ∈ {−1,1}^N` (`N = 2ⁿ`) with the truth
table of the character `χ_y(x) = (−1)^{x·y}`, in the bit encoding: bit `G x` is xored with the
parity of `#{i | xᵢ ∧ yᵢ}`, so that `sign (maskByChar G y x) = sign (G x) · χ_y(x)`.

arXiv:2610.05585 (held version, sha256 4564aef3…), §4.2.2, p.30: "V_τ(G) := G ⊙ χ_{y_τ(G)}, where ⊙
denotes the entrywise product." -/
def maskByChar {n : ℕ} (G : (Fin n → Bool) → Bool) (y : Fin n → Bool) : (Fin n → Bool) → Bool :=
  fun x => xor (G x) (decide (Odd (Finset.univ.filter (fun i => x i && y i)).card))

end PelagicFF


