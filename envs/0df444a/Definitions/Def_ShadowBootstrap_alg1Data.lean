-- Prove2me | Definitions.Def_ShadowBootstrap_alg1Data
-- name    : ShadowBootstrap_alg1Data
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:25:47.494207+00:00
-- url     : https://prove2.me/theorems/c634b496-a589-40c1-a813-a00b5e407570
-- title:
--   Algorithm 1 (measurement schedule) and Algorithms 3–4 (post-processing) as data and maps
-- statement:
--   **Algorithm 1** (p.26) schedules, for a target infidelity $\epsilon$ and constants $K$ and $C$:
--
--   1. for each level $\ell = 0, \dots, n-1$: $N_\ell := \lceil Kn^2\rceil$ bases $U_{\ell,i} \sim E_\ell$, each applied as $I_{2^\ell}\otimes U_{\ell,i}$ to $S_\ell := \lceil K d^{2/3}2^{\ell/3}/N_\ell\rceil$ copies;
--   2. $J := \lceil\log_2(6/\epsilon)\rceil$ stages; at stage $t$, $N_t := \lceil 16(C+1)\rceil$ bases $U_{t,i} \sim E = E_0$, each applied to $S_t := d\,2^{t-1}$ copies.
--
--   **Algorithms 3 and 4** (p.27) compute the initialization $|\sigma_0\rangle = |\hat\psi_\emptyset\rangle$ from the level histograms and then run the $J$ bootstrapping stages from the stage histograms. The module defines the schedule with its histograms (each sampled label written as a circuit), the post-processing map, and the success probability $\Pr[1 - |\langle\psi|\hat\psi\rangle|^2 \le \epsilon]$ of the whole procedure.
--
--   **Formalization Note** $K$ and $C$ are integers, so $\lceil Kn^2\rceil = Kn^2$ and $\lceil16(C+1)\rceil = 16(C+1)$. Level settings carry tag $\ell$, stage settings tag $n + t$.
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Algorithms 1, 3 and 4, pp.26–27; proof of Theorem 5.1, p.22; proof of Corollary 4.5, p.15

import Mathlib
import Definitions.Def_ShadowBootstrap_Schedule
import Definitions.Def_ShadowBootstrap_suffixEnsemble
import Definitions.Def_ShadowBootstrap_stagesExpect
import Definitions.Def_ShadowBootstrap_recon

open ClassicalShadow.Linear ShallowShadows.ShadowNorm

namespace ShadowBootstrap

/-- Algorithm 1, line 5 (p.26), and the proof of Theorem 5.1 (p.22): `N_ℓ := ⌈K n²⌉` bases at
every level (for an integer `K`). -/
def initN (K n : ℕ) : ℕ := K * n ^ 2

/-- Algorithm 1, line 5: `S_ℓ := ⌈K d^{2/3} 2^{ℓ/3} / N_ℓ⌉` shots per basis at level `ℓ`, `d = 2ⁿ`. -/
noncomputable def initS (K n ℓ : ℕ) : ℕ :=
  ⌈(K : ℝ) * (2 : ℝ) ^ ((2 * (n : ℝ)) / 3) * (2 : ℝ) ^ ((ℓ : ℝ) / 3) / (initN K n : ℝ)⌉₊

/-- Algorithm 1, line 3: `J := ⌈log₂(6/ϵ)⌉` refinement stages (Corollary 4.5 at target `ϵ/12`). -/
noncomputable def refJ (ε : ℝ) : ℕ := (⌈Real.logb 2 (6 / ε)⌉).toNat

/-- Algorithm 1, line 12: `N_t := ⌈16(C + 1)⌉` bases per stage (for an integer `C`). -/
def refN (C : ℕ) : ℕ := 16 * (C + 1)

/-- Algorithm 1, line 12: `S_t := d 2^{t−1}` shots per basis at stage `t = t₀ + 1`. -/
def refS (n t₀ : ℕ) : ℕ := 2 ^ n * 2 ^ t₀

/-- A circuit on the last `j` qubits of an `n`-qubit register: qubit `q` of the suffix is qubit
`q + (n − j)` of the register, so the circuit implements `I_{2^{n−j}} ⊗ U` (§5.2, p.17). -/
def liftGate {n j : ℕ} (hj : j ≤ n) : Gate j → Gate n
  | .h q => .h ⟨q.1 + (n - j), by omega⟩
  | .s q => .s ⟨q.1 + (n - j), by omega⟩
  | .cx c t hct => .cx ⟨c.1 + (n - j), by omega⟩ ⟨t.1 + (n - j), by omega⟩
      (fun h => hct (Fin.ext (by have := congrArg Fin.val h; simp at this; omega)))

/-- The lift of a whole circuit to the last `j` qubits. -/
def liftCircuit {n j : ℕ} (hj : j ≤ n) (c : Circuit j) : Circuit n :=
  c.map fun L => L.map (liftGate hj)

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Algorithm 1, p.26: the measurement schedule with its histograms. Levels `ℓ = 0, …, n−1` come first
(level `ℓ` has suffix size `j = n − ℓ`, `N_ℓ` bases drawn from `E_ℓ`, each applied as
`I_{2^ℓ} ⊗ U` to `S_ℓ` copies, tag `ℓ`), then stages `t = 1, …, J` (`N_t` bases drawn from
`E = E_0`, each applied to `S_t` copies, tag `n + t`). `circ n j` turns a label of the suffix
ensemble on `j` qubits into a circuit over `{H, S, CX}`; `initL`, `refL` are the sampled labels and
`initC`, `refC` the histograms of the full `n`-bit outcomes. -/
noncomputable def alg1Data [∀ k, Fintype (CliffordLabel k)]
    (circ : (n j : ℕ) → SuffixLabel n j → Circuit j) (K C n : ℕ) (ε : ℝ)
    (initL : (j : Fin n) → Fin (initN K n) → SuffixLabel n (j.1 + 1))
    (initC : (j : Fin n) → Fin (initN K n) → Bits n → ℕ)
    (refL : Fin (refJ ε) → Fin (refN C) → SuffixLabel n n)
    (refC : Fin (refJ ε) → Fin (refN C) → Bits n → ℕ) : List (Setting n × (Bits n → ℕ)) :=
  ((List.finRange n).reverse.flatMap fun j => (List.finRange (initN K n)).map fun i =>
      (⟨n - (j.1 + 1), liftCircuit (Nat.succ_le_of_lt j.2) (circ n (j.1 + 1) (initL j i)),
        initS K n (n - (j.1 + 1))⟩, initC j i)) ++
  ((List.finRange (refJ ε)).flatMap fun t => (List.finRange (refN C)).map fun i =>
      (⟨n + 1 + t.1, circ n n (refL t i), refS n t.1⟩, refC t i))

/-- Algorithms 3 and 4 (p.27) on the data of Algorithm 1: the initialization `|σ₀⟩ := |ψ̂_∅⟩`
(Algorithm 3, with the eigenvector rule `choose`), then the `J` bootstrapping stages with the fixed
vector `|σ₀⟩` (Algorithm 4). Level `ℓ`'s histograms are read as functions of the outcome
`(x, b) ∈ {0,1}^ℓ × {0,1}^{n−ℓ}`. -/
noncomputable def postprocess [∀ k, Fintype (CliffordLabel k)]
    (choose : Matrix (Fin 2) (Fin 2) ℂ → Fin 2 → ℂ) (K C n : ℕ) (ε : ℝ)
    (initL : (j : Fin n) → Fin (initN K n) → SuffixLabel n (j.1 + 1))
    (initC : (j : Fin n) → Fin (initN K n) → Bits n → ℕ)
    (refL : Fin (refJ ε) → Fin (refN C) → SuffixLabel n n)
    (refC : Fin (refJ ε) → Fin (refN C) → Bits n → ℕ) : Bits n → ℂ :=
  let σ₀ : Bits n → ℂ :=
    initOutput (fun j => suffixEnsemble n j) choose (fun _ => initN K n) (initS K n)
      fun j i => (initL j i, fun xb => initC j i (concatBits xb.1 xb.2))
  stagesRun (suffixEnsemble n n) σ₀
    ((List.finRange (refJ ε)).map fun t => ⟨refN C, refS n t.1, fun i => (refL t i, refC t i)⟩) σ₀

/-- The success probability of Algorithms 1, 3 and 4 at target `ϵ`: initialization data and
refinement data independent, every basis drawn from its ensemble, every shot on a fresh copy of
`|ψ⟩`; the event is `1 − |⟨ψ|ψ̂⟩|² ≤ ϵ`. -/
noncomputable def alg1SuccessProb [∀ k, Fintype (CliffordLabel k)]
    (choose : Matrix (Fin 2) (Fin 2) ℂ → Fin 2 → ℂ) (K C n : ℕ) (ε : ℝ) (ψ : Bits n → ℂ) : ℝ :=
  initExpect (fun j => suffixEnsemble n j) choose (fun _ => initN K n) (initS K n) ψ fun σ₀ =>
    stagesExpect (suffixEnsemble n n) ψ σ₀ ((List.range (refJ ε)).map fun t => (refN C, refS n t))
      σ₀ fun v => if 1 - ‖braket ψ v‖ ^ 2 ≤ ε then 1 else 0

end ShadowBootstrap


