-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_Thm614For
-- name    : QuantumKtSoI_Supplement_Thm614For
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:40:11.464419+00:00
-- url     : https://prove2.me/theorems/f8d297a1-4784-4593-b3f3-bcf2643221d4
-- title:
--   Symmetry of information with error $\theta$; Theorem 6.14, Corollary 6.15 and Proposition G.1 for a measure $\mu$
-- statement:
--   A real-valued conditional measure $\mu$ satisfies **symmetry of information with error $\theta$** (Definition 5.3) if
--   $$\mu(y|x)\le\mu(\langle x,y\rangle)-\mu(x)+\theta(|x|+|y|)\qquad\text{for all } x,y .$$
--   With $\mu$ in place of $\mathrm{qKt}$ this module states:
--
--   1. **Theorem 6.14**: there is a positive integer $c_{\mathrm{sym}}$ such that for all nondecreasing $T,\psi:\mathbb N\to\mathbb N$ with $T(n)\ge\max(n,1)$ and $\psi(n)\ge1$, if some machine estimates $\mu$ within $\psi$ in time $T$, then $\mu$ satisfies symmetry of information with error $\theta(L)=c_{\mathrm{sym}}(\lceil\log T(4L)\rceil+\psi(4L))+C\lceil\log(L+2)\rceil^3$ for a positive integer $C$ depending on the machine, $T$ and $\psi$;
--   2. **Corollary 6.15**: for every rational $\varepsilon\in(0,1)$, symmetry of information with error $\lceil a(N+1)^\varepsilon\rceil$ for a constant $a>0$ holds if and only if some machine estimates $\mu$ within $\lceil bn^\varepsilon\rceil$ in time $2^{\lceil bn^\varepsilon\rceil}$ for a constant $b>0$ (stated as its two implications);
--   3. **Proposition G.1** for a rational charge $c$: for every rational $\eta$ with $0<\eta<1-c/2$ and $\varepsilon=\eta/(40\max(c,1))$, and every gap function $g$ computable in time polynomial in the value of its argument with $g(\lambda)\le(1-c/2-\eta)\lambda$ for all large $\lambda$, no machine decides a language consistent with the gap $g$ for $\mu$ infinitely often in time $2^{\varepsilon\nu}$; in particular for the gap $\lfloor(1-c/2-\eta)\lambda\rfloor$.
--
--   Theorem F.3 asserts these for $\mu=\mathrm{qKt}^{(c)}$; at $\mu=\mathrm{qKt}$ the first two are the paper's statements.
--
--   **Formalization Note** For $\mu=\mathrm{qKt}$ the symmetry condition is $\Delta(x,y)\le\theta(|x|+|y|)$ with the published defect. Estimation, queries, consistency and deciding infinitely often are the measure-parameterized definitions of this mission.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Definition 5.3, p.52; Theorem 6.14, p.85; Corollary 6.15, p.86; Proposition G.1, p.245

import Mathlib
import Definitions.Def_QuantumKtSoI_pair
import Definitions.Def_QuantumKtSoI_CodedMachine
import Definitions.Def_QuantumKtSoI_Supplement_Estimates
import Definitions.Def_QuantumKtSoI_Supplement_query
import Definitions.Def_QuantumKtSoI_Supplement_PolyInValue

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

/-! Symmetry of information with an error function, and the results of §6.4 and Appendix G, for a
conditional measure `µ` (`µ y x` is `µ(y | x)`, `µ(y) = µ(y | ε)`; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…). With `µ = qKt` each is the
paper's statement; Theorem F.3 asserts them with `qKt^{(c)}` in place of `qKt`. -/

/-- **Definition 5.3** (Symmetry of information with error `θ`, p.52) for `µ`:
`µ(y|x) ≤ µ(⟨x,y⟩) − µ(x) + θ(|x|+|y|)` for all strings `x, y`. -/
def SoIWithError (μ : List Bool → List Bool → ℝ) (θ : ℕ → ℝ) : Prop :=
  ∀ x y : List Bool, μ y x ≤ μ (pair x y) [] - μ x [] + θ (x.length + y.length)

/-- **Theorem 6.14** (Estimation yields symmetry of information, p.85) for `µ`: there is a positive
integer `c_sym`, independent of `T`, `ψ` and the machine, such that for all nondecreasing
`T, ψ : ℕ → ℕ` with `T(n) ≥ max(n,1)` and `ψ(n) ≥ 1`, if some machine estimates `µ` within `ψ` in time
`T` (Definition 6.12), then `µ` satisfies symmetry of information with error
`θ(L) = c_sym(⌈log T(4L)⌉ + ψ(4L)) + C⌈log(L+2)⌉³` for a positive integer `C` that depends on the
machine, `T` and `ψ`. -/
def Thm614For (μ : List Bool → List Bool → ℝ) : Prop :=
  ∃ csym : ℕ, 0 < csym ∧ ∀ T ψ : ℕ → ℕ, Monotone T → Monotone ψ → (∀ n, max n 1 ≤ T n) →
    (∀ n, 1 ≤ ψ n) → ∀ A : CodedMachine, A.Valid → Estimates (fun v => μ v []) A T ψ →
      ∃ C : ℕ, 0 < C ∧ SoIWithError μ fun L =>
        ((csym * (Nat.clog 2 (T (4 * L)) + ψ (4 * L)) + C * Nat.clog 2 (L + 2) ^ 3 : ℕ) : ℝ)

/-- **Corollary 6.15** (Characterization, p.86) for `µ`: for every rational `ε ∈ (0,1)`,
(i) if `µ` satisfies symmetry of information with error `θ(N) = ⌈a(N+1)^ε⌉` for a constant
`a > 0`, then some machine estimates `µ` within `⌈bn^ε⌉` in time `2^{⌈bn^ε⌉}`, for a constant
`b > 0`;
(ii) if some machine estimates `µ` within `⌈bn^ε⌉` in time `2^{⌈bn^ε⌉}` for a constant `b > 0`, then
`µ` satisfies symmetry of information with error `⌈a(N+1)^ε⌉` for a constant `a > 0`. -/
def Cor615For (μ : List Bool → List Bool → ℝ) : Prop :=
  ∀ ε : ℚ, 0 < ε → ε < 1 →
    ((∃ a : ℝ, 0 < a ∧ SoIWithError μ fun N => (⌈a * ((N : ℝ) + 1) ^ (ε : ℝ)⌉₊ : ℝ)) →
      ∃ b : ℝ, 0 < b ∧ ∃ A : CodedMachine, A.Valid ∧
        Estimates (fun v => μ v []) A (fun n => 2 ^ ⌈b * (n : ℝ) ^ (ε : ℝ)⌉₊)
          (fun n => ⌈b * (n : ℝ) ^ (ε : ℝ)⌉₊)) ∧
    ((∃ b : ℝ, 0 < b ∧ ∃ A : CodedMachine, A.Valid ∧
        Estimates (fun v => μ v []) A (fun n => 2 ^ ⌈b * (n : ℝ) ^ (ε : ℝ)⌉₊)
          (fun n => ⌈b * (n : ℝ) ^ (ε : ℝ)⌉₊)) →
      ∃ a : ℝ, 0 < a ∧ SoIWithError μ fun N => (⌈a * ((N : ℝ) + 1) ^ (ε : ℝ)⌉₊ : ℝ))

/-- **Proposition G.1** (Other time charges, p.245), for a rational charge `c` and the measure
`µ = qKt^{(c)}` of strings: for all rational `η` with `0 < η < 1 − c/2`, with
`ε = η/(40 max(c,1))`, for every `g : ℕ → ℕ` that is computable in time polynomial in the value of
its argument and satisfies `g(λ) ≤ (1 − c/2 − η)λ` for all large `λ`, no machine decides a
language consistent with the gap `g` for `µ` infinitely often in time `2^{εν}`; in particular this
holds for the gap `⌊(1 − c/2 − η)λ⌋` (the form quoted in Theorem F.3). -/
def PropG1For (c : ℚ) (μ : List Bool → ℝ) : Prop :=
  ∀ η : ℚ, 0 < η → (η : ℝ) < 1 - (c : ℝ) / 2 →
    (∀ g : ℕ → ℕ, PolyInValue g →
      (∃ l₀ : ℕ, ∀ lam ≥ l₀, (g lam : ℝ) ≤ (1 - (c : ℝ) / 2 - η) * lam) →
      ∀ L : Set (List Bool), ConsistentGap μ g L →
        ¬∃ A : CodedMachine, A.Valid ∧ DecidesIO A L ((η : ℝ) / (40 * max (c : ℝ) 1))) ∧
    ∀ L : Set (List Bool),
      ConsistentGap μ (fun lam => ⌊(1 - (c : ℝ) / 2 - η) * lam⌋₊) L →
        ¬∃ A : CodedMachine, A.Valid ∧ DecidesIO A L ((η : ℝ) / (40 * max (c : ℝ) 1))

end QuantumKtSoI.Supplement


