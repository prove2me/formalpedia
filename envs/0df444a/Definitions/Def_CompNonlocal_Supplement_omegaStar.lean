-- Prove2me | Definitions.Def_CompNonlocal_Supplement_omegaStar
-- name    : CompNonlocal_Supplement_omegaStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:11:29.270184+00:00
-- url     : https://prove2.me/theorems/c1275386-23e7-44af-9f15-741c30807fae
-- title:
--   The entangled state $\omega^*$ of Sections 11–12
-- statement:
--   Let $\rho(v)=v|\psi^-\rangle\langle\psi^-|+\frac{1-v}4 I\otimes I$ be the Werner state. On $\mathbb C^3\otimes\mathbb C^2$, with $F=|2\rangle\langle2|$, consider
--   $$\tilde\omega_{2/5}=\tfrac13\rho(2/5)+\tfrac23F\otimes\tfrac{I_2}2,$$
--   where the Werner block is supported on $\mathrm{span}\{|0\rangle,|1\rangle\}\otimes\mathbb C^2$ (Lemmas 6 and 8). The state $\omega^*$ is $\tilde\omega_{2/5}$ with constant-size pure local ancillas adjoined.
--
--   Here Alice holds $2+m_A$ qubits and Bob $1+m_B$ qubits: Alice's qutrit is her first two qubits with $|0\rangle,|1\rangle,|2\rangle\mapsto|00\rangle,|01\rangle,|10\rangle$, Bob's qubit is his first qubit, and all ancilla qubits are in $|0\rangle$.
--
--   **Formalization Note** The qutrit is embedded in two qubits; $|11\rangle$ carries no weight.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7b7dd5f4c52119a37e0ee1d00eaf20185262775b8ab7d3067a9f2fcae), §11, p.63 (Setup); Lemma 8, pp.29–30; Lemma 6, p.28

import Mathlib
import Definitions.Def_CompNonlocal_werner
import Definitions.Def_QAlgorithms_Defs_Complexity

set_option autoImplicit false

namespace CompNonlocal.Supplement

open QAlgorithms.Complexity

/-- The entangled state `ω∗` of Theorems 9 and 11. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), §11, p.63: "Let ω∗ be the entangled state
of Lemma 8 in Section 6, with fixed constant-size pure local ancillas adjoined. Its LHS model is
unchanged, and a separable comparison state τ∗ in the same local spaces can supply a uniformly random
shared label λ ∈ [Σ], where Σ = 12." Lemma 8, pp.29–30 (proof): "Apply Lemma 7 to ω_AB = ρ(2/5). The
resulting ω̃_{2/5} is entangled by Lemma 6"; Lemma 6, p.28:
ω̃_v = (1/3) ρ(v) + (2/3) F ⊗ I₂/2, F = |2⟩⟨2|, on C³ ⊗ C², "where the Werner block is supported on
S := I₃ − F".

`omegaStar m_A m_B` is `ω̃_{2/5}` with `m_A` ancilla qubits on Alice's side and `m_B` on Bob's side, all
in `|0⟩`. Alice holds `2 + m_A` qubits: her qutrit is her first two qubits, `|0⟩, |1⟩, |2⟩ ↦
|00⟩, |01⟩, |10⟩` (the Werner block is "first qubit `0`", its qubit the second one; the flag `|2⟩` is
`|10⟩`; `|11⟩` is unused). Bob holds `1 + m_B` qubits, his qubit the first one.

**Formalization Note** Entry `((a, b), (a', b'))` is `0` unless every ancilla bit of `a, a', b, b'` is
`0`; then it is `(1/3) ρ(2/5)((a₁, b₀), (a'₁, b'₀))` if `a₀ = a'₀ = 0`, `1/3` (`= (2/3)·(1/2)`) if
`a₀a₁ = a'₀a'₁ = 10` and `b₀ = b'₀`, and `0` otherwise. -/
noncomputable def omegaStar (mA mB : ℕ) :
    Matrix (Bits (2 + mA) × Bits (1 + mB)) (Bits (2 + mA) × Bits (1 + mB)) ℂ :=
  Matrix.of fun p p' =>
    if (∀ j : Fin (2 + mA), 2 ≤ (j : ℕ) → p.1 j = false) ∧
        (∀ j : Fin (2 + mA), 2 ≤ (j : ℕ) → p'.1 j = false) ∧
        (∀ j : Fin (1 + mB), 1 ≤ (j : ℕ) → p.2 j = false) ∧
        (∀ j : Fin (1 + mB), 1 ≤ (j : ℕ) → p'.2 j = false) then
      (if p.1 ⟨0, by omega⟩ = false ∧ p'.1 ⟨0, by omega⟩ = false then
        (1 / 3 : ℂ) * werner (2 / 5) (p.1 ⟨1, by omega⟩, p.2 ⟨0, by omega⟩)
          (p'.1 ⟨1, by omega⟩, p'.2 ⟨0, by omega⟩)
      else if p.1 ⟨0, by omega⟩ = true ∧ p.1 ⟨1, by omega⟩ = false ∧
          p'.1 ⟨0, by omega⟩ = true ∧ p'.1 ⟨1, by omega⟩ = false ∧
          p.2 ⟨0, by omega⟩ = p'.2 ⟨0, by omega⟩ then (1 / 3 : ℂ)
      else 0)
    else 0

end CompNonlocal.Supplement


