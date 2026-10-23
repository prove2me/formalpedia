-- Prove2me | Definitions.Def_KWPurify_Rate_Model
-- name    : KWPurify_Rate_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:02.570992+00:00
-- url     : https://prove2.me/theorems/f05a625e-3fba-4c0b-8832-2158e61274fc
-- title:
--   Depolarized qubit input, worst-case all-qubit fidelity $F_{\mathrm{all}}$, optimal value $F^{\max}_{\mathrm{all}}(N,M)$ and the rate function $\Phi(\mu)$ ((1), (2), (4), (10), pp. 2–5)
-- statement:
--   This file fixes the purification problem of Keyl and Werner for qubits.
--
--   1. **Noise.** For $\lambda \in \mathbb R$ the depolarizing channel acts on a one-qubit density matrix $\sigma$ by
--   $$R_*\sigma = \lambda\,\sigma + (1-\lambda)\,\frac{\mathbb 1}{2}.$$
--   2. **All-qubit fidelity.** A device taking $N$ qubits to $M$ qubits is a map $T_*$ from $2^N\times 2^N$ to $2^M\times 2^M$ complex matrices. Its all-qubit fidelity is the worst case, over all one-qubit pure states $\sigma = |\varphi\rangle\langle\varphi|$ with $\|\varphi\| = 1$, of the overlap of the output on $N$ noisy copies with $M$ perfect copies:
--   $$F_{\mathrm{all}}(T) = \inf_{\sigma}\ \operatorname{tr}\big(\sigma^{\otimes M}\, T_*\big((R_*\sigma)^{\otimes N}\big)\big).$$
--   3. **Optimal value.** $F^{\max}_{\mathrm{all}}(N,M) = \sup_T F_{\mathrm{all}}(T)$, the supremum over **all** quantum channels (trace-preserving completely positive maps) from $N$ qubits to $M$ qubits.
--   4. **Rate function.** For real $\lambda,\mu$,
--   $$\Phi(\mu) = \begin{cases} \dfrac{2\lambda^2}{2\lambda^2 + \mu(1-\lambda)} & \mu \le \lambda,\\[2mm] \dfrac{2\lambda^2}{\mu(1+\lambda)} & \mu > \lambda.\end{cases}$$
--   (The two branches agree at $\mu = \lambda$.)
--
--   These are the objects of the headline formula (10) of the paper: the optimal all-qubit fidelity at output rate $M/N \to \mu$ tends to $\Phi(\mu)$.
--
--   **Formalization Note** The $n$-qubit basis is indexed by words $x : \mathrm{Fin}\,n \to \mathrm{Fin}\,2$; tensor powers are `QAlgorithms.piKron`, $|\varphi\rangle\langle\varphi|$ is `QAlgorithms.pureDensity`, and a channel is a superoperator with a finite normalized Kraus family (`QAlgorithms.IsChannel`), which in finite dimension is exactly a CPTP map. The infimum and supremum are `sInf`/`sSup` on $\mathbb R$; for a channel and $0 \le \lambda \le 1$ the fidelity set is nonempty and contained in $[0,1]$, and the set of channel fidelities is nonempty (for instance the channel that discards its input and prepares a fixed state) and bounded by $1$, so they are the true infimum and supremum. For a superoperator that is not a channel `allFidelity` may take the junk value $0$; it is only ever evaluated inside the supremum over channels. The parameter $\lambda$ is written `lam`, since `λ` is reserved in Lean.
-- source:
--   Keyl & Werner, The Rate of Optimal Purification procedures, arXiv:quant-ph/9910124v1, pp. 2–5, eqs. (1), (2), (4), (10)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Defs_Information

namespace KWPurify.Rate

open QAlgorithms

/-- Keyl–Werner, arXiv:quant-ph/9910124v1, p. 2, eq. (1): the depolarizing channel on one qubit,
`R_* σ = λ σ + (1 − λ) 𝟙/2`. -/
noncomputable def depolarize (lam : ℝ) (σ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (lam : ℂ) • σ + (((1 - lam) / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- p. 4, eq. (2): the all-qubit fidelity of a device `T_*` from `N` qubits to `M` qubits,
`F_all(T) = inf_σ tr(σ^{⊗M} T_*((R_*σ)^{⊗N}))`, the infimum over all one-qubit pure states
`σ = |φ⟩⟨φ|`, `‖φ‖ = 1`. Words `Fin n → Fin 2` index the `n`-qubit basis; tensor powers are
`piKron`. For a channel the set is nonempty and contained in `[0, 1]`. -/
noncomputable def allFidelity (lam : ℝ) {N M : ℕ}
    (T : Superop (Fin N → Fin 2) (Fin M → Fin 2)) : ℝ :=
  sInf {r : ℝ | ∃ φ : EuclideanSpace ℂ (Fin 2), ‖φ‖ = 1 ∧
    r = (piKron M (pureDensity φ) * T (piKron N (depolarize lam (pureDensity φ)))).trace.re}

/-- p. 4, eq. (4) with `♯ = all`: the optimal all-qubit fidelity `F^max_all(N, M) = sup_T F_all(T)`,
the supremum over all quantum channels (trace-preserving completely positive maps, here in Kraus
form) from `N` qubits to `M` qubits. -/
noncomputable def maxAllFidelity (lam : ℝ) (N M : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ T : Superop (Fin N → Fin 2) (Fin M → Fin 2), IsChannel T ∧
    r = allFidelity lam T}

/-- p. 5, eq. (10): the rate function
`Φ(μ) = 2λ²/(2λ² + μ(1 − λ))` for `μ ≤ λ` and `2λ²/(μ(1 + λ))` for `μ ≥ λ`. -/
noncomputable def ratePhi (lam μ : ℝ) : ℝ :=
  if μ ≤ lam then 2 * lam ^ 2 / (2 * lam ^ 2 + μ * (1 - lam))
  else 2 * lam ^ 2 / (μ * (1 + lam))

end KWPurify.Rate


