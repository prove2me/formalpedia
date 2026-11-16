-- Prove2me | Definitions.Def_ScalablePassiveQRAM_Device_Supplement_Markov
-- name    : ScalablePassiveQRAM_Device_Supplement_Markov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:04:19.317442+00:00
-- url     : https://prove2.me/theorems/94a9c3f3-0ab4-49e3-adcf-7363b4b3065a
-- title:
--   Local time-dependent Markovian noise during QRAM queries, equations (77)–(80)
-- statement:
--   The noise model of §4.4. A noise family consists of finitely many components $\alpha$. Component $\alpha$ has an arbitrary support $S_\alpha$ among the root address record $R$, the physical ports, the auxiliaries (carriers and switches) and the memory, a time-dependent Hermitian Hamiltonian part $K_{\alpha,t}$ and finitely many time-dependent jump operators $L_{\alpha\ell,t}$, all acting as identity off $S_\alpha$. The coefficients are only required to be measurable in $t$. The device then evolves under
--
--   $$\frac{d\rho}{dt}=\mathcal L_t(\rho)=-i[K,\rho]+\sum_\alpha\mathcal N_{\alpha,t}(\rho),\qquad \mathcal N_{\alpha,t}(\rho)=-i[K_{\alpha,t},\rho]+\sum_\ell\Big(L_{\alpha\ell,t}\rho L_{\alpha\ell,t}^\dagger-\tfrac12\{L_{\alpha\ell,t}^\dagger L_{\alpha\ell,t},\rho\}\Big),$$
--
--   where $K$ is the full device Hamiltonian of the recorded interface (pinning on every memory qubit). The module defines:
--
--   1. the generator $\mathcal L_t$ and the propagator of this equation between two times, through the integral form $\rho(u)=X+\int_s^u\mathcal L_v(\rho(v))\,dv$ with integrable integrand;
--   2. the rates $\gamma_\alpha(t)=\|K_{\alpha,t}\|+\sum_\ell\|L_{\alpha\ell,t}\|^2$ (spectral norms);
--   3. with $\tau=\pi/\Omega$ and $I_j=[(j-1)\tau,j\tau]$, the exposures $G_j=\max_x\int_{I_j}\sum_{\alpha:S_\alpha\cap F_x^+\neq\varnothing}\gamma_\alpha(t)\,dt$ and $G=\max_{1\le j\le m}G_j$, where $F_x^+$ is the extended footprint of address $x$;
--   4. the incidence $\lambda_{\rm dyn}(t)=\max_q\sum_{\alpha:q\in S_\alpha}\gamma_\alpha(t)$ over every device and record qubit;
--   5. query $k$ under noise: the recorded interface of §4.3 (ideal root preparation, encoding $W_{\rm rec}$, decoding (48), ideal carrier reset), with the free evolution replaced by the noisy propagator over $I_k$, so that device time runs continuously across queries;
--   6. the noisy $m$-query algorithm, with the device prepared once with vacant auxiliaries and memory $|D\rangle$, never touched by the algorithm, and traced out at the end, and its error $\epsilon_m$, the unhalved diamond distance to the ideal algorithm querying the original database $D$.
--
--   **Formalization Note** The propagator takes the value at the final time of a solution chosen from the set of solutions of the integral equation. Existence and uniqueness of that solution are not assumed. They hold whenever the rates are integrable, which is a hypothesis of the theorem using this module. $G$ and $\lambda_{\rm dyn}$ are maxima of nonnegative quantities, written as folds of `max` starting from $0$. Zero-based query $k$ runs over $[k\tau,(k+1)\tau]$.
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), §4.3 (setting) and §4.4, equations (77)–(80), pp. 30, 32. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Static
import Mathlib

noncomputable section
open scoped BigOperators Matrix

namespace ScalablePassiveQRAM.Device.Supplement

open ScalablePassiveQRAM.Device

local instance markovDecidableEq (α : Type) : DecidableEq α := Classical.decEq α
local instance markovDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Local Markovian noise, equations (77)–(78) (p. 32). Finitely many components `α`, each with
an arbitrary support `S_α` among the record, ports, auxiliaries and memory, a time-dependent
Hermitian Hamiltonian part `K_{α,t}` and finitely many time-dependent jump operators
`L_{αℓ,t}`, all supported on `S_α` (tensored with identity elsewhere). No locality bound,
continuity or time-independence is assumed; the coefficients are only measurable in `t`. -/
structure MarkovNoise (n : ℕ) where
  count : ℕ
  support : Fin count → Finset (ExtendedQubit n)
  ham : Fin count → ℝ → Op (Recorded n)
  jumps : Fin count → ℕ
  jump : (α : Fin count) → Fin (jumps α) → ℝ → Op (Recorded n)
  hermitian : ∀ α t, (ham α t)ᴴ = ham α t
  ham_supported : ∀ α t, supportedOn n (support α) (ham α t)
  jump_supported : ∀ α ℓ t, supportedOn n (support α) (jump α ℓ t)
  ham_measurable : ∀ α i j, Measurable fun t => ham α t i j
  jump_measurable : ∀ α ℓ i j, Measurable fun t => jump α ℓ t i j

namespace MarkovNoise

variable {n : ℕ} (N : MarkovNoise n)

/-- `N_{α,t}(ρ) = −i[K_{α,t}, ρ] + ∑_ℓ (L ρ L† − ½{L†L, ρ})`, equation (78). -/
def dissipator (α : Fin N.count) (t : ℝ) (ρ : Op (Recorded n)) : Op (Recorded n) :=
  (-Complex.I) • (N.ham α t * ρ - ρ * N.ham α t) +
    ∑ ℓ, (N.jump α ℓ t * ρ * (N.jump α ℓ t)ᴴ -
      (1/2 : ℂ) • ((N.jump α ℓ t)ᴴ * N.jump α ℓ t * ρ + ρ * ((N.jump α ℓ t)ᴴ * N.jump α ℓ t)))

/-- `L_t(ρ) = −i[K, ρ] + ∑_α N_{α,t}(ρ)`, equation (77), with `K` the full recorded device
Hamiltonian (every memory qubit, the record and the ports). -/
def generator (Ω Δ t : ℝ) (ρ : Op (Recorded n)) : Op (Recorded n) :=
  (-Complex.I) • (recordedHamiltonian n Ω Δ * ρ - ρ * recordedHamiltonian n Ω Δ) +
    ∑ α, N.dissipator α t ρ

/-- `ρ` solves `dρ/dt = L_t(ρ)` on `[s, t]` with `ρ(s) = X`, in integral (Carathéodory) form;
the integrand is required to be integrable, so no junk integral is admitted. -/
def IsEvolution (Ω Δ s t : ℝ) (X : Op (Recorded n)) (ρ : ℝ → Op (Recorded n)) : Prop :=
  (∀ i j, IntervalIntegrable (fun v => N.generator Ω Δ v (ρ v) i j) MeasureTheory.volume s t) ∧
  ∀ u ∈ Set.Icc s t, ∀ i j, ρ u i j = X i j + ∫ v in s..u, N.generator Ω Δ v (ρ v) i j

/-- The propagator of the noisy evolution from time `s` to time `t`: the value at `t` of a
solution of `IsEvolution`. Existence and uniqueness of that solution are not assumed here. -/
def propagator (Ω Δ s t : ℝ) : Map (Recorded n) (Recorded n) :=
  fun X => if h : ∃ ρ, N.IsEvolution Ω Δ s t X ρ then Classical.choose h t else 0

/-- `γ_α(t) = ‖K_{α,t}‖ + ∑_ℓ ‖L_{αℓ,t}‖²`, equation (79), with spectral norms. -/
def rate (α : Fin N.count) (t : ℝ) : ℝ :=
  ScalablePassiveQRAM.Device.spectralNorm (N.ham α t) +
    ∑ ℓ, ScalablePassiveQRAM.Device.spectralNorm (N.jump α ℓ t) ^ 2

/-- `G_j = max_x ∫_{I_j} ∑_{α : S_α ∩ F⁺_x ≠ ∅} γ_α(t) dt`, equation (80), with
`I_j = [(j−1)τ, jτ]`, `τ = π/Ω`, `j` one-based. -/
def exposure (Ω : ℝ) (j : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun x : Address n =>
    ∫ t in ((j : ℝ) - 1) * (Real.pi / Ω)..(j : ℝ) * (Real.pi / Ω),
      ∑ α ∈ Finset.univ.filter (fun α => ¬ Disjoint (N.support α) (extendedFootprint n x)),
        N.rate α t

/-- `G = max_{1 ≤ j ≤ m} G_j`, equation (80) (every `G_j` is nonnegative). -/
def maxExposure (Ω : ℝ) (m : ℕ) : ℝ :=
  ((List.range m).map fun j => N.exposure Ω (j+1)).foldl max 0

/-- `λ_dyn(t) = max_q ∑_{α : q ∈ S_α} γ_α(t)`, over every record, port, auxiliary and memory
qubit (every summand is nonnegative). -/
def dynIncidence (t : ℝ) : ℝ :=
  ((Finset.univ : Finset (ExtendedQubit n)).toList.map fun q =>
    ∑ α ∈ Finset.univ.filter (fun α => q ∈ N.support α), N.rate α t).foldl max 0

/-- Query `k+1` (zero-based `k`) under noise: the §4.3 recorded interface with ideal root
controls, the free evolution replaced by the noisy propagator on the device-time interval
`I_{k+1} = [kτ, (k+1)τ]`. -/
def query (Ω Δ : ℝ) (k : ℕ) : Map (Logical n × Retained n) (Logical n × Retained n) :=
  fun X => extend (resetRetained n) (recordedDecode n
    (N.propagator Ω Δ ((k : ℝ) * (Real.pi / Ω)) (((k : ℝ) + 1) * (Real.pi / Ω))
      (conjugate (recordEncoding n) (extend (prepareRetained n) X))))

end MarkovNoise

/-- `runAlgorithm` with a query map that may depend on the (zero-based) query index. -/
def runVarying {n w m : ℕ} {r : Type} (A : Algorithm n w m)
    (Q : ℕ → Map ((Logical n × Fin w) × r) ((Logical n × Fin w) × r))
    (ρ : Op r) : Map (Logical n × Fin w) ((Logical n × Fin w) × r) :=
  fun X => (List.finRange m).foldl (fun σ k =>
    localAlgorithm A ⟨k.val+1,by omega⟩ (Q k.val σ))
    (localAlgorithm A ⟨0,by omega⟩ (tensor X ρ))

/-- The physical `m`-query algorithm under Markovian noise: device prepared once in the clean
state (vacant auxiliaries, memory `|D⟩`), never touched by the algorithm, traced out at the end. -/
def markovAlgorithm {n w m : ℕ} (A : Algorithm n w m) (N : MarkovNoise n)
    (Ω Δ : ℝ) (D : Database n) : Map (Logical n × Fin w) (Logical n × Fin w) :=
  fun X => WildeQIT.partialTraceRight
    (runVarying A (fun k => queryLift n w (N.query Ω Δ k)) (cleanRetained n D) X)

/-- `ϵ_m`: unhalved diamond distance to the ideal algorithm for the original database `D`. -/
def markovError {n w m : ℕ} (A : Algorithm n w m) (N : MarkovNoise n)
    (Ω Δ : ℝ) (D : Database n) : ℝ :=
  diamondDist (markovAlgorithm A N Ω Δ D) (idealAlgorithm A D)

end ScalablePassiveQRAM.Device.Supplement


