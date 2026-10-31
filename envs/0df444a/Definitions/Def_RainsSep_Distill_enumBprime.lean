-- Prove2me | Definitions.Def_RainsSep_Distill_enumBprime
-- name    : RainsSep_Distill_enumBprime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:58:07.846885+00:00
-- url     : https://prove2.me/theorems/70554c30-180b-4919-8f59-7990b8e5ec85
-- title:
--   $B'_S(\mathcal P)$ of a product Kraus representation
-- statement:
--   Fix a product Kraus representation $\mathcal P(\rho)=\sum_i(P_i^{(1)}\otimes P_i^{(2)})\rho(P_i^{(1)}\otimes P_i^{(2)})^\dagger$ with $P_i^{(1)},P_i^{(2)}:V\to W$, $V$ an $n$-qubit register and $\dim W=K$. For a set $S$ of subsystems (qubits of $V$, and $W$ if $0\in S$),
--
--   $$
--   B'_S(\mathcal P)=\frac{1}{2^nK}\sum_i \mathrm{Tr}\Big(\mathrm{Tr}_S\big(\overline{\rho_i^{(1)}}\big)\,\mathrm{Tr}_S\big(\rho_i^{(2)}\big)\Big),\qquad \rho_i^{(j)}=|P_i^{(j)}\rangle\langle P_i^{(j)}| .
--   $$
--
--   These are the quantum-weight-enumerator-like coefficients of the polynomial $B'$.
--
--   **Formalization Note** $B'_S$ depends on the chosen representation $(P^{(1)},P^{(2)})$, as in the paper; every statement using it quantifies over the representation. The value is the real part.
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Eq. (23), p. 2

import Mathlib
import Definitions.Def_RainsSep_Distill_krausChoi
import Definitions.Def_RainsSep_Distill_trPairS

namespace RainsSep.Distill

/-- **`B′_S(P)` of a product Kraus representation.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, Eq. (23), p. 2: "B′_S(P) = (1/(2^n K)) Σ_i Tr(Tr_S(\overline{ρ_i(1)}) Tr_S(ρ_i(2))), (23)
where Tr_S(ρ) is the partial trace of ρ with respects to the qubits of V indexed by S, as well as
W if 0 ∈ S."

For a product Kraus representation `P(ρ) = Σ_i (P₁ i ⊗ P₂ i) ρ (P₁ i ⊗ P₂ i)†` (Eq. (13)), with
`P₁ i, P₂ i : V → W`, `V` an `n`-qubit register and `dim W = K`, and a set `S` of subsystems
(`some k` = qubit `k`, `none` = `W`), `B′_S = (2ⁿK)⁻¹ Σ_i Tr(Tr_S \overline{ρ_i(1)} · Tr_S ρ_i(2))`.

**Formalization Note.** `B′_S` depends on the chosen representation `(P₁, P₂)`, as in the
paper ("to be explicit, take (13)"); every statement using it quantifies over the
representation. The value is the real part. -/
noncomputable def enumBprime {n K m : ℕ}
    (P₁ P₂ : Fin m → Matrix (Fin K) (QAlgorithms.Qubits n) ℂ) (S : Finset (Option (Fin n))) : ℝ :=
  ((((2 ^ n * K : ℕ) : ℂ))⁻¹ *
    ∑ i, trPairS S ((krausChoi (P₁ i)).map star) (krausChoi (P₂ i))).re

end RainsSep.Distill


