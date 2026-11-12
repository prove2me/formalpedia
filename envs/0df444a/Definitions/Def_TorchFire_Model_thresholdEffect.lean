-- Prove2me | Definitions.Def_TorchFire_Model_thresholdEffect
-- name    : TorchFire_Model_thresholdEffect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:33:45.931193+00:00
-- url     : https://prove2.me/theorems/1d4d266c-5bce-45fd-b5ea-a92b4fccfa34
-- title:
--   The threshold effect $T_d(Z_1,\dots,Z_N)$ (83) and reduced states
-- statement:
--   For $N$ locations with registers $H_1,\dots,H_N$ and local effects $Z_1,\dots,Z_N$, the **threshold effect** (83) is
--   $$T_d(Z_1,\dots,Z_N)=\sum_{z\in\{0,1\}^N,\ \sum_i z_i\ge d}\ \bigotimes_{i=1}^N Z_i^{z_i}(I-Z_i)^{1-z_i}.$$
--   When the local tests act on disjoint registers of a joint state $\rho$, $\Pr[\text{at least } d \text{ successes}]=\mathrm{Tr}(T_d(Z_1,\dots,Z_N)\rho)$.
--
--   The module also defines the tensor product $\bigotimes_i Z_i$ of local operators on $\bigotimes_i H_i$ and the reduced state $\rho_i=\mathrm{Tr}_{\bigotimes_{k\ne i}H_k}\rho$ at one location.
--
--   These are the joint-success probabilities of Lemma 8.2 and of the non-proliferation game.
--
--   **Formalization Note** The joint space $\bigotimes_i H_i$ is the dependent function type $(i:\mathrm{Fin}\,N)\to H_i$.
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), §8.1 step 7, (83), p.67; p.59

import Mathlib
import Definitions.Def_TorchFire_Model_traceDist

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix

namespace TorchFire.Model

/-- **The tensor product `⨂_{i=1}^N Z_i` of local operators** on the joint space `⨂_i H_i`. The
joint space is the function type `(i : Fin N) → H i`; the entry at `(x, y)` is
`∏_i (Z_i)_{x_i y_i}` (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*,
arXiv:2610.03593, held version sha256 4e43d2f2…afd593, §8.1, p.59 "`H = ⨂_{i=1}^N H_i`"). -/
def piKron {N : ℕ} {H : Fin N → Type} (Z : (i : Fin N) → Matrix (H i) (H i) ℂ) :
    Matrix ((i : Fin N) → H i) ((i : Fin N) → H i) ℂ :=
  Matrix.of fun x y => ∏ i, Z i (x i) (y i)

/-- **The threshold effect** (83), §8.1 step 7, p.67:

  `T_d(Z_1, …, Z_N) = Σ_{z ∈ {0,1}^N, Σ_i z_i ≥ d} ⨂_{i=1}^N Z_i^{z_i} (I − Z_i)^{1−z_i}`,

the effect of "at least `d` of the `N` local tests succeed" when the local tests (effects `Z_i`)
act on disjoint registers of a joint state: `Pr[at least d successes] = Tr(T_d(Z_1, …, Z_N) ρ)`. -/
def thresholdEffect {N : ℕ} {H : Fin N → Type} [∀ i, DecidableEq (H i)] (d : ℕ)
    (Z : (i : Fin N) → Matrix (H i) (H i) ℂ) :
    Matrix ((i : Fin N) → H i) ((i : Fin N) → H i) ℂ :=
  ∑ z ∈ (Finset.univ : Finset (Fin N → Bool)).filter
      (fun z => d ≤ (Finset.univ.filter fun i => z i = true).card),
    piKron fun i => if z i then Z i else 1 - Z i

/-- **The reduced state at one location**: `ρ_i = Tr_{⨂_{k≠i} H_k}(ρ)` (§8.1, p.59). -/
def reducedAt {N : ℕ} {H : Fin N → Type} [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)]
    (ρ : Matrix ((i : Fin N) → H i) ((i : Fin N) → H i) ℂ) (i : Fin N) : Matrix (H i) (H i) ℂ :=
  Matrix.of fun a b => ∑ x : (j : Fin N) → H j, if x i = a then ρ x (Function.update x i b) else 0

end TorchFire.Model


