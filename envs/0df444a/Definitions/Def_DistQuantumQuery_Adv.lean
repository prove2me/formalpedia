-- Prove2me | Definitions.Def_DistQuantumQuery_Adv
-- name    : DistQuantumQuery_Adv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:55.746205+00:00
-- url     : https://prove2.me/theorems/f060e20c-129f-496e-8b5c-7ad9cdc7942d
-- title:
--   $\mu$-witnesses $\mathcal W^\mu_f$, $(\varepsilon,\mu)$-targets $\mathcal G^\mu_\varepsilon(f)$ and the distributional adversary measure $\mathrm{Adv}^\mu_\varepsilon(f)$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$, $f\subseteq\Sigma\times\Omega$ a search problem and $\mu$ a distribution. A **$\mu$-witness** is $W\in\mathrm{Pos}(\Sigma)$ with a decomposition $W=\sum_{s\in\Omega}W^{(s)}$ such that
--
--   1. $W^{(s)}\succeq0$ for all $s$;
--   2. $W^{(s)}[x,x]=0$ whenever $s\notin f(x)$;
--   3. $\mathrm{Tr}[W\circ|\mu\rangle\langle\mu|]=1$.
--
--   For $\varepsilon\in[0,1)$ the **$(\varepsilon,\mu)$-targets** are
--   $$
--   \mathcal G^\mu_\varepsilon(f):=\{\Psi\in\mathrm{Pos}(\Sigma):\ \Psi\circ I=I,\ \max_{W\in\mathcal W^\mu_f}F(W\circ|\mu\rangle\langle\mu|,\Psi\circ|\mu\rangle\langle\mu|)\ge\sqrt{1-\varepsilon}\},
--   $$
--   and the **distributional adversary measure** is
--   $$
--   \mathrm{Adv}^\mu_\varepsilon(f):=\min_{\Psi\in\mathcal G^\mu_\varepsilon(f)}\bar\gamma^\mu_2(J-\Psi\mid\{\Delta_i\}).
--   $$
--   The targets are the Gram matrices of algorithms that solve $f$ under $\mu$ with error $\varepsilon$ (Theorem 3.5); the adversary measure characterizes $Q^\mu_\varepsilon(f)$ up to a change in the error.
--
--   **Formalization Note** "$\max_W F\ge\sqrt{1-\varepsilon}$" is written as the existence of a witness with $F\ge\sqrt{1-\varepsilon}$; the paper writes $\max$ (attained). $\mathrm{Adv}$ is an infimum in $[0,\infty]$. A search problem is a relation $R$ with $R(x,s)$ meaning $s\in f(x)$.
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Definition 3.2 p.23, Definition 3.3 p.23, Definition 5.1 p.43

import Mathlib
import Definitions.Def_DistQuantumQuery_gammaBar

open scoped Matrix ENNReal ComplexOrder

namespace DistQuantumQuery

/-- `W` is a **μ-witness** for the search problem `R ⊆ Σ × Ω` (Ben-David, Ebtehaj,
*Distributional Quantum Query Complexity*, arXiv:2610.06835, held version, sha256 6334ffaf…,
Definition 3.2, p.23): `W ⪰ 0` admits a decomposition `W = Σ_{s∈Ω} W^{(s)}` with
1. `W^{(s)} ⪰ 0` for every `s`;
2. `W^{(s)}[x, x] = 0` whenever `s ∉ f(x)`;
3. `Tr[W ∘ |μ⟩⟨μ|] = 1`. -/
def IsWitness {X Ω : Type*} [Fintype X] [Fintype Ω] (μ : X → ℝ) (R : X → Ω → Prop)
    (W : Matrix X X ℂ) : Prop :=
  W.PosSemidef ∧
    (∃ Ws : Ω → Matrix X X ℂ, (∀ s, (Ws s).PosSemidef) ∧ W = ∑ s, Ws s ∧
      ∀ x s, ¬ R x s → Ws s x x = 0) ∧
    Matrix.trace (W ⊙ muMat μ) = 1

/-- The set of **(ε, μ)-targets** (arXiv:2610.06835, held version, sha256 6334ffaf…,
Definition 3.3, p.23):
`G^μ_ε(f) := {Ψ ∈ Pos(Σ) : Ψ ∘ I = I; max_{W ∈ W^μ_f} F(W ∘ |μ⟩⟨μ|, Ψ ∘ |μ⟩⟨μ|) ≥ √(1 − ε)}`.

**Formalization Note** "`max_W F ≥ √(1−ε)`" is written as the existence of a witness `W` with
`F ≥ √(1−ε)`; the paper writes `max` (attained), so the two agree. -/
def Targets {X Ω : Type*} [Fintype X] [DecidableEq X] [Fintype Ω] (μ : X → ℝ)
    (R : X → Ω → Prop) (ε : ℝ) : Set (Matrix X X ℂ) :=
  {Ψ | Ψ.PosSemidef ∧ Ψ ⊙ (1 : Matrix X X ℂ) = 1 ∧
    ∃ W, IsWitness μ R W ∧ Real.sqrt (1 - ε) ≤ fidelity (W ⊙ muMat μ) (Ψ ⊙ muMat μ)}

/-- The **distributional adversary measure** (arXiv:2610.06835, held version,
sha256 6334ffaf…, Definition 5.1, p.43):
`Adv^μ_ε(f) := min_{Ψ ∈ G^μ_ε(f)} γ̄^μ₂(J − Ψ | {Δ_i})`.

**Formalization Note** Value in `ℝ≥0∞`, written as an infimum (the paper notes the minimum is
attained). -/
noncomputable def Adv {ι Ω : Type*} [Fintype ι] [Fintype Ω] (S : Finset (ι → Bool))
    (μ : S → ℝ) (R : S → Ω → Prop) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ (Ψ : Matrix S S ℂ) (_ : Ψ ∈ Targets μ R ε), gammaBar μ (allOnes S - Ψ) (qfilters S)

end DistQuantumQuery


