-- Prove2me | Definitions.Def_WildeQIT_Compression_Supplement_IsAchievablePrivateRate
-- name    : WildeQIT_Compression_Supplement_IsAchievablePrivateRate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:01:09.310933+00:00
-- url     : https://prove2.me/theorems/7ed7701c-69c6-55f3-a930-8a2ed34d75bf
-- title:
--   Achievable rate of private classical communication
-- statement:
--   Let $\mathcal N_{A'\to B}$ be a quantum channel with isometric extension $U^{\mathcal N}_{A'\to BE}$ and complementary channel $\widehat{\mathcal N}_{A'\to E}(\sigma)=\operatorname{Tr}_B\{U^{\mathcal N}\sigma U^{\mathcal N\dagger}\}$. An $(n,P,\varepsilon)$ **private classical code** consists of codewords $\rho^m_{A'^n}$, $m\in\mathcal M$, and a decoding POVM $\{\Lambda_m\}$ on $B^n$ such that
--
--   1. (reliability) $p_e(m)=\operatorname{Tr}\{(I-\Lambda_m)\mathcal N^{\otimes n}(\rho^m_{A'^n})\}\le\varepsilon$ for every message $m$;
--   2. (privacy) there is one state $\sigma_{E^n}$ with $\tfrac12\|\widehat{\mathcal N}^{\otimes n}(\rho^m_{A'^n})-\sigma_{E^n}\|_1\le\varepsilon$ for every $m$;
--
--   and its rate is $P=\frac1n\log|\mathcal M|$. A rate $P$ is **achievable** if for all $\varepsilon\in(0,1)$, $\delta>0$ and all sufficiently large $n$ there is an $(n,P-\delta,\varepsilon)$ private classical code.
--
--   The privacy condition says that Eve's state is nearly independent of the message; it implies that Eve's Holevo information about the message is small (§23.1.1).
--
--   **Formalization Note** The code without the privacy clause is the published `WildeQIT.ErasureClassical.ClassicalCode` with its published error probability. A code of rate $P-\delta$ is read as one with $|\mathcal M|\ge1$ messages and $\frac1n\log_2|\mathcal M|\ge P-\delta$, as in the published classical achievable rate. Eve's channel on $n$ uses is the complementary channel of the published tensor power $\mathcal N^{\otimes n}$ for its canonical isometric extension; $\sigma_{E^n}$ is a density operator. Logarithms are base 2.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §23.1, pp. 640–641, eqs. (23.1)–(23.7)

import Mathlib
import Definitions.Def_WildeQIT_ErasureClassical_errorProb
import Definitions.Def_WildeQIT_Degradable_complementaryApply
import Definitions.Def_WildeQIT_traceNorm

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §23.1, pp. 640–641,
(23.1)–(23.7) (private classical codes and achievable private rates).
-/

namespace WildeQIT.Compression.Supplement

open Classical in
/-- **Achievable rate of private classical communication** (Wilde, *From Classical to Quantum
Shannon Theory*, arXiv:1106.1445v8, §23.1, pp. 640–641). An `(n, P, ε)` private classical code
for `N_{A′→B}` consists of codewords `ρᵐ_{A′ⁿ}`, `m ∈ M`, and a decoding POVM `{Λ_m}` on `Bⁿ` with
maximal error probability `p*_e = max_m Tr{(I − Λ_m) N^{⊗n}(ρᵐ)} ≤ ε` (23.2)–(23.3) and rate
`P = (1/n) log |M|` (23.4), satisfying the ε-privacy condition (23.7): for one constant state
`σ_{Eⁿ}`, `½ ‖ωᵐ_{Eⁿ} − σ_{Eⁿ}‖₁ ≤ ε` for every `m`, where `ωᵐ_{Eⁿ} = N̂^{⊗n}(ρᵐ)` is Eve's state
through the complementary channel `N̂_{A′→E}(σ) = Tr_B{U^N σ U^N†}` (23.5)–(23.6). "A rate `P` of
private classical communication is achievable for `N_{A′→B}` if there exists an `(n, P − δ, ε)`
private classical code for all `ε ∈ (0, 1)`, `δ > 0`, and sufficiently large `n`, where `ε`
characterizes both the reliability and the privacy of the code."

**Formalization Note.** The code without the privacy clause is the published
`WildeQIT.ErasureClassical.ClassicalCode` with the published error probability
`WildeQIT.ErasureClassical.errorProb` (messages `Fin M`, codewords arbitrary density operators on
`Fin n → a`, possibly entangled across channel uses). "An `(n, P − δ, ε)` code" is read, as in the
published `WildeQIT.ErasureClassical.IsAchievableRate`, as a code with `M ≥ 1` messages and rate
`(1/n) log₂ M ≥ P − δ` (the message number is an integer). Eve's channel on `n` uses is the
complementary channel of `N^{⊗n}` (published `WildeQIT.Degradable.tensorPower`) for its canonical
isometric extension, the tensor product of `n` copies of the canonical extension of `N`
(environment `Fin n → N.ι`); any other isometric extension changes Eve's states by a fixed
isometry, which preserves the trace distance to the correspondingly transformed `σ`. The constant
state `σ_{Eⁿ}` is a density operator; the same `ε` bounds error and privacy. Logarithms are
base 2. -/
def IsAchievablePrivateRate {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (N : QChannel a b) (P : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ →
    ∀ᶠ n : ℕ in Filter.atTop, ∃ M : ℕ, ∃ c : WildeQIT.ErasureClassical.ClassicalCode a b n M,
      0 < M ∧ P - δ ≤ Real.logb 2 M / n ∧
      (∀ m, WildeQIT.ErasureClassical.errorProb N c m ≤ ε) ∧
      ∃ σ : Matrix (WildeQIT.Degradable.tensorPower N n).ι
          (WildeQIT.Degradable.tensorPower N n).ι ℂ,
        IsDensityOperator σ ∧
        ∀ m, (1 / 2 : ℝ) * traceNorm
          (WildeQIT.Degradable.complementaryApply (WildeQIT.Degradable.tensorPower N n) (c.enc m)
            - σ) ≤ ε

end WildeQIT.Compression.Supplement


