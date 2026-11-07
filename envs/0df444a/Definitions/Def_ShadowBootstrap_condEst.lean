-- Prove2me | Definitions.Def_ShadowBootstrap_condEst
-- name    : ShadowBootstrap_condEst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:23:01.94206+00:00
-- url     : https://prove2.me/theorems/f6c19717-0bd1-4893-bb1f-40e27c62adf4
-- title:
--   The conditional shadow estimator $\hat o$ (Definition 5.8, Eq. (20))
-- statement:
--   At level $\ell$ of the initialization, each of $N_\ell$ sampled bases $U_i$ is applied as $I_{2^\ell} \otimes U_i$ to $S_\ell$ fresh copies of $|\psi\rangle$, giving outcomes $(X_{i,a}, b_{i,a}) \in \{0,1\}^\ell \times \{0,1\}^{n-\ell}$ with probability (Eq. (18))
--   $$\Pr(x, b) = p_x\,\langle b|U\psi_xU^\dagger|b\rangle = |\langle b|U|\varphi_x\rangle|^2,\qquad \varphi_x := (\langle x|\otimes I)|\psi\rangle,\ p_x = \|\varphi_x\|_2^2 .$$
--   For a node $x$ and a suffix observable $O$, the **conditional shadow estimator** (Definition 5.8, p.19) is
--   $$\hat o := \frac{1}{N_\ell}\sum_{i=1}^{N_\ell}\frac{1}{S_\ell}\sum_{a=1}^{S_\ell}\mathbf 1\{X_{i,a} = x\}\operatorname{Tr}\big[O\,\mathcal M_\ell^{-1}(U_i^\dagger|b_{i,a}\rangle\langle b_{i,a}|U_i)\big]. \tag{20}$$
--
--   It is the estimator from which the entries of the reconstruction matrix $\hat B_x$ are formed.
--
--   **Formalization Note** The prefix comes first: the outcome string is $x \| b$ with $x$ on the first $\ell$ qubits. The estimator reads each basis's histogram $h_i(x, b)$, which gives the same value as Eq. (20). $\varphi_x = \sqrt{p_x}\,|\psi_x\rangle$ is used instead of the normalized $|\psi_x\rangle$ of Definition 5.2, which is undefined when $p_x = 0$.
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Definition 5.2, p.16; §5.2, Eq. (18), p.17; Definition 5.8, Eq. (20), p.19

import Mathlib
import Definitions.Def_ShadowBootstrap_braket
import Definitions.Def_ClassicalShadow_Linear_Setting

open ClassicalShadow.Linear

namespace ShadowBootstrap

/-- The bit string `x ‖ b ∈ {0,1}ⁿ` with prefix `x ∈ {0,1}^{n−j}` and suffix `b ∈ {0,1}^j` (§5.2,
p.17: "the first ℓ qubits are measured in the Z basis"; `ℓ = n − j`). -/
def concatBits {n j : ℕ} (x : Bits (n - j)) (b : Bits j) : Bits n :=
  fun i => if h : i.1 < n - j then x ⟨i.1, h⟩ else b ⟨i.1 - (n - j), by omega⟩

/-- The unnormalized conditional vector `φ_x := (⟨x| ⊗ I)|ψ⟩ ∈ ℂ^{2^j}` of the prefix `x`
(Definition 5.2, p.16): `φ_x = √p_x |ψ_x⟩` with `p_x = ‖φ_x‖₂²`. -/
def cond {n j : ℕ} (ψ : Bits n → ℂ) (x : Bits (n - j)) : Bits j → ℂ :=
  fun b => ψ (concatBits x b)

/-- The probability `Pr(x, b) = p_x ⟨b|U_i ψ_x U_i†|b⟩ = |⟨b|U_i|φ_x⟩|²` of the outcome `(x, b)` of
one shot in the basis `I_{2^ℓ} ⊗ U_i` (Eq. (18), p.17). -/
noncomputable def levelShotProb {n j : ℕ} {ι : Type} [Fintype ι] (E : Primitive j ι)
    (ψ : Bits n → ℂ) (i : ι) (xb : Bits (n - j) × Bits j) : ℝ :=
  (diagEntry E i (ketbra (cond ψ xb.1) (cond ψ xb.1)) xb.2).re

/-- The probability of the raw data of one level: `N` bases drawn independently from `E`, each
measured on `S` fresh copies of `|ψ⟩` (§5.2, p.17). -/
noncomputable def levelWeight {n j N S : ℕ} {ι : Type} [Fintype ι] (E : Primitive j ι)
    (ψ : Bits n → ℂ) (data : Fin N → ι × (Fin S → Bits (n - j) × Bits j)) : ℝ :=
  ∏ i, E.w.prob (data i).1 * ∏ a, levelShotProb E ψ (data i).1 ((data i).2 a)

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Definition 5.8, Eq. (20), p.19: the conditional shadow estimator of the node `x` and the suffix
observable `O`,
`ô := (1/N) Σ_i (1/S) Σ_a 1{X_{i,a} = x} Tr[O M⁻¹(U_i†|b_{i,a}⟩⟨b_{i,a}|U_i)]`.

**Formalization Note** The data of basis `i` are its label `rec i`.1 and its histogram `rec i`.2 of
the outcomes `(X, b)`; `Σ_a 1{X_{i,a} = x} g(b_{i,a}) = Σ_b h_i(x, b) g(b)`. Each basis average is
normalized by all `S` shots, as the paper notes. `O` is any complex suffix observable (the
estimator is linear in `O`); for Hermitian `O` the value is real. -/
noncomputable def condEst {n j N : ℕ} {ι : Type} [Fintype ι] (E : Primitive j ι)
    (x : Bits (n - j)) (O : Op j) (S : ℕ) (rec : Fin N → ι × (Bits (n - j) × Bits j → ℕ)) : ℂ :=
  ((1 / (N : ℝ) : ℝ) : ℂ) * ∑ i, ((1 / (S : ℝ) : ℝ) : ℂ) *
    ∑ b, (((rec i).2 (x, b) : ℕ) : ℂ) * (O * shadow E ((rec i).1, b)).trace

end ShadowBootstrap


