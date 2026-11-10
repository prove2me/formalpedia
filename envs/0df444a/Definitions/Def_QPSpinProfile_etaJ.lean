-- Prove2me | Definitions.Def_QPSpinProfile_etaJ
-- name    : QPSpinProfile_etaJ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:26:06.957249+00:00
-- url     : https://prove2.me/theorems/69d473d8-87a2-4f44-a532-cf04847c2643
-- title:
--   Conditioning construction (7) and the separable approximation $\eta_J$
-- statement:
--   Fix a one-qubit POVM $\{M_u:u\in Z\}$, an $n$-qubit state $\rho$ and $J\subseteq[n]$. Measuring every qubit of $J^c$ with outcome $z=(z_i)_{i\in J^c}$ corresponds to the product effect $M^{(J^c)}_z=\bigotimes_{i=1}^nB_i(z)$, with $B_i(z)=M_{z_i}$ for $i\in J^c$ and $B_i(z)=I$ for $i\in J$. Display (7) defines
--   $$
--   q(z)=\operatorname{Tr}(M^{(J^c)}_z\rho),\qquad \rho_{J|z}=\frac{\operatorname{Tr}_{J^c}\big[K_z\rho K_z\big]}{q(z)}\quad(q(z)>0),
--   $$
--   with $K_z=(M^{(J^c)}_z)^{1/2}$, and Lemma 2.2 builds from it
--   $$
--   \eta_J=\sum_{z:\,q(z)>0}q(z)\bigotimes_{i\in J}\rho_{i|z},\qquad \rho_{i|z}=\operatorname{Tr}_{J\setminus\{i\}}(\rho_{J|z}),
--   $$
--   a state on the qubits of $J$.
--
--   **Formalization Note** The outcome set is $\mathrm{Fin}\,t$. The conditional state is computed as $\operatorname{Tr}_{J^c}[M^{(J^c)}_z\rho]/q(z)$, which the paper notes (p.15) equals $\operatorname{Tr}_{J^c}[K_z\rho K_z]/q(z)$ by cyclicity of the partial trace over the measured qubits; zero-probability outcomes are omitted from the sum, as in the paper.
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), §2.1.1, p.14–15 (PDF p.17–18), display (7); Lemma 2.2, p.17 (PDF p.20)

import Mathlib
import Definitions.Def_QPSpinProfile_PauliString
import Definitions.Def_QPSpinProfile_marg

namespace QPSpinProfile

open Matrix

/-- The product effect `M^{(S)}_z := ⊗_{i=1}^n B_i(z)`, `B_i(z) = M_{z_i}` for `i ∈ S` and `I`
otherwise, for the measured set `S = Jᶜ` and a joint outcome `z = (z_i)_{i ∈ Jᶜ}`
(arXiv:2610.02166, held version sha256 a0a1ec89…, §2.1.1, p.14, PDF p.17). -/
def prodEffect {n t : ℕ} (M : Fin t → Matrix (Fin 2) (Fin 2) ℂ) (J : Finset (Fin n))
    (z : {i // i ∉ J} → Fin t) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun x y => ∏ i, (if h : i ∈ J then (1 : Matrix (Fin 2) (Fin 2) ℂ) else M (z ⟨i, h⟩))
    (x i) (y i)

/-- The outcome probability `q_{Jᶜ}(z) := Tr(M^{(Jᶜ)}_z ρ)` of display (7) (arXiv:2610.02166,
§2.1.1, p.14, PDF p.17). -/
noncomputable def condProb {n t : ℕ} (M : Fin t → Matrix (Fin 2) (Fin 2) ℂ) (J : Finset (Fin n))
    (ρ : Matrix (Qubits n) (Qubits n) ℂ) (z : {i // i ∉ J} → Fin t) : ℝ :=
  (Matrix.trace (prodEffect M J z * ρ)).re

/-- The conditional state `ρ_{J|z}` of the unmeasured qubits `J` after measuring `Jᶜ` with outcome
`z`, display (7) (arXiv:2610.02166, §2.1.1, p.14–15, PDF p.17–18).

**Formalization Note** Display (7) defines `ρ_{J|z} = Tr_{Jᶜ}[K_z ρ K_z] / q(z)` with
`K_z = (M_z^{(Jᶜ)})^{1/2}`; the paper notes (p.15) that `q(z) ρ_{J|z} = Tr_{Jᶜ}[M_z^{(Jᶜ)} ρ]` by
cyclicity of the partial trace over the measured qubits, and this second form is used here
(same operator). It is only used for outcomes with `q(z) > 0`. -/
noncomputable def condState {n t : ℕ} (M : Fin t → Matrix (Fin 2) (Fin 2) ℂ) (J : Finset (Fin n))
    (ρ : Matrix (Qubits n) (Qubits n) ℂ) (z : {i // i ∉ J} → Fin t) :
    Matrix (J → Fin 2) (J → Fin 2) ℂ :=
  ((condProb M J ρ z : ℂ))⁻¹ • marg (fun i => i ∈ J) (prodEffect M J z * ρ)

/-- The conditioning approximation of Lemma 2.2 (arXiv:2610.02166, §2.1.3, p.17, PDF p.20):
`η_J := ∑_{z : q(z) > 0} q(z) ⊗_{i ∈ J} ρ_{i|z}`, `ρ_{i|z} := Tr_{J∖{i}}(ρ_{J|z})`, an operator on
the qubits of `J`. -/
noncomputable def etaJ {n t : ℕ} (M : Fin t → Matrix (Fin 2) (Fin 2) ℂ) (J : Finset (Fin n))
    (ρ : Matrix (Qubits n) (Qubits n) ℂ) : Matrix (J → Fin 2) (J → Fin 2) ℂ :=
  ∑ z ∈ Finset.univ.filter (fun z => 0 < condProb M J ρ z),
    ((condProb M J ρ z : ℂ)) • Matrix.of fun x y => ∏ i : J, siteMarg i (condState M J ρ z) (x i) (y i)

end QPSpinProfile


