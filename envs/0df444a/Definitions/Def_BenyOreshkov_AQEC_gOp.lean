-- Prove2me | Definitions.Def_BenyOreshkov_AQEC_gOp
-- name    : BenyOreshkov_AQEC_gOp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:20:38.903636+00:00
-- url     : https://prove2.me/theorems/9ab47dbb-e6f9-448b-9f92-46d3a87a3d83
-- title:
--   The circuit operator of $g_\rho(U,U')$, $V_{\mathcal M}^\dagger(1\otimes C^\dagger)(W\otimes 1)V_{\mathcal N}$
-- statement:
--   Let $V_{\mathcal N}:A\to B\otimes E$ and $V_{\mathcal M}:A\to B'\otimes E'$ be the isometries of the channels $\mathcal N$ and $\mathcal M$, and let $W : B\to B'\otimes K$ and $C : E'\to E\otimes K$ be operators. The **circuit operator** is the operator on $A$
--   $$
--   G(V_{\mathcal N},V_{\mathcal M},W,C) = V_{\mathcal M}^\dagger\,\big(1_{B'}\otimes C^\dagger\big)\big(W\otimes 1_E\big)\,V_{\mathcal N}.
--   $$
--   With $W = U(\cdot\otimes|0\rangle)$ and $C = U'(\cdot\otimes|0\rangle)$, the complex number represented by the circuit of the proof of Theorem 1 is
--   $$
--   g_\rho(U,U') = \langle\psi_\rho|\,(1\otimes G)\,|\psi_\rho\rangle = \mathrm{Tr}(G\rho):
--   $$
--   the purification $|\psi_\rho\rangle$ passes through $V_{\mathcal N}$, then $U$ on $B$ and the ancilla, then $U'^\dagger$ on $E$ and the ancilla, then $V_{\mathcal M}^\dagger$, and is paired with $\langle\psi_\rho|$.
--
--   **Formalization Note** The middle factor is written entrywise, $\big((1\otimes C^\dagger)(W\otimes 1)\big)_{(b',e'),(b,e)}=\sum_k \overline{C_{(e,k),e'}}\,W_{(b',k),b}$, which matches the factor order $B'\otimes K\otimes E$ of $W\otimes 1_E$ with $B'\otimes(E\otimes K)$ of $1_{B'}\otimes C$.
-- source:
--   Bény, Oreshkov, General conditions for approximate quantum error correction and near-optimal recovery channels, arXiv:0907.5391v4, proof of Theorem 1, Eq. (4) and the circuit for g_ρ(U, U′), p. 2

import Mathlib

open Matrix

namespace BenyOreshkov.AQEC

/-- **The operator of the circuit `g_ρ(U, U′)`.** Bény, Oreshkov, arXiv:0907.5391v4, proof of
Theorem 1, Eq. (4), p. 2. The circuit sends `|ψ_ρ⟩` through `V_N : A → B ⊗ E`, then `U` on
`B ⊗ |0⟩` (output `B′ ⊗ Ẽ`), then `U′†` on `E ⊗ Ẽ` (output `E′ ⊗ |0⟩`, projected on `⟨0|`), then
`V_M†`, and pairs the result with `⟨ψ_ρ|`. With `W = U(· ⊗ |0⟩) : B → B′ ⊗ K` and
`C = U′(· ⊗ |0⟩) : E′ → E ⊗ K` this is the operator

`gOp V_N V_M W C = V_M† (1_{B′} ⊗ C†) (W ⊗ 1_E) V_N : A → A`,

and `g_ρ(U, U′) = ⟨ψ_ρ| (1 ⊗ gOp) |ψ_ρ⟩ = Tr(gOp · ρ)`.

**Formalization Note** The middle factor is written entrywise: its entry at
`((b′, e′), (b, e))` is `Σ_k conj(C_{(e, k), e′}) W_{(b′, k), b}`, i.e. the factor order
`B′ ⊗ K ⊗ E` of `W ⊗ 1_E` is matched with `B′ ⊗ (E ⊗ K)` of `1_{B′} ⊗ C`. `W` and `C` are
arbitrary matrices here (isometries, or contractions, are imposed by the statements). -/
def gOp {A B E B' E' K : Type} [Fintype A] [Fintype B] [Fintype E] [Fintype B'] [Fintype E']
    [Fintype K]
    (VN : Matrix (B × E) A ℂ) (VM : Matrix (B' × E') A ℂ) (W : Matrix (B' × K) B ℂ)
    (C : Matrix (E × K) E' ℂ) : Matrix A A ℂ :=
  VMᴴ * (Matrix.of fun (p : B' × E') (q : B × E) => ∑ k, star (C (q.2, k) p.2) * W (p.1, k) q.1)
    * VN

end BenyOreshkov.AQEC


