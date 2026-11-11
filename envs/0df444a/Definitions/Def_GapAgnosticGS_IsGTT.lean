-- Prove2me | Definitions.Def_GapAgnosticGS_IsGTT
-- name    : GapAgnosticGS_IsGTT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:31.489487+00:00
-- url     : https://prove2.me/theorems/34264dd2-7680-485d-8263-bd38786691df
-- title:
--   Gapped threshold test $\mathrm{GTT}(\eta,a;\tau)$ (the guarantee of Lemma 3.5)
-- statement:
--   Let $E$ be a hidden-basis environment, $R$ the auxiliary registers (containing the flag $C$) with zero state $|0\rangle_R$, $\eta$ a gap, $a$ an amplitude error and $\tau$ a threshold. A unitary $G$ on $I\otimes A\otimes R$ is a **gapped threshold test** $\mathrm{GTT}(\eta,a;\tau)$ for $E$ if
--
--   1. every subspace $\mathcal H_j\otimes\mathcal H_R$ is invariant under $G$;
--   2. for every arm $j$ and every unit vector $|\psi_j\rangle\in\mathcal H_j$,
--   $$p_j\ge\tau+\eta\implies\big\|(I\otimes\langle1|_C)\,G\,|\psi_j\rangle|0\rangle_R\big\|\le a,\qquad p_j\le\tau-\eta\implies\big\|(I\otimes\langle0|_C)\,G\,|\psi_j\rangle|0\rangle_R\big\|\le a .$$
--
--   $C=0$ is the high-reward outcome. Lemma 3.5 constructs such tests; Lemmas 3.6 and A.5 use them as building blocks of the variable-time test.
--
--   **Formalization Note** $|\psi_j\rangle$ is a unit vector (a state); by linearity this is equivalent to the bound $a\|\psi_j\|$ for every $\psi_j\in\mathcal H_j$.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.5, p.10 (PDF p.11)

import Definitions.Def_GapAgnosticGS_InBranch
open QAlgorithms

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.5, p.10 (PDF p.11): "There is a unitary GTT(η, a; τ) acting on the selector
register I, the arm register A, and auxiliary registers C and P … such that: (i) every subspace
H_j ⊗ H_CP is invariant; (ii) for every |ψ_j⟩_{IA} ∈ H_j,
p_j ≥ τ + η ⟹ ‖(I_{IAP} ⊗ ⟨1|_C) GTT(η, a; τ)(|ψ_j⟩_{IA}|0⟩_{CP})‖ ≤ a,
p_j ≤ τ − η ⟹ ‖(I_{IAP} ⊗ ⟨0|_C) GTT(η, a; τ)(|ψ_j⟩_{IA}|0⟩_{CP})‖ ≤ a.
Here C = 0 denotes the high-reward outcome."

`G` is a gapped threshold test with gap `η`, amplitude error `a` and threshold `τ` for `Env`, on
auxiliary registers `R` whose zero state is `r₀` and whose `C` flag is read by `cflag`: `G` is
unitary, and for every arm `j`, (i) `G` maps `H_j ⊗ ℂ^R` into itself, and (ii) for every unit
`ψ ∈ H_j`, the component of `G(ψ ⊗ |r₀⟩)` with flag `C = 1` (resp. `C = 0`) has norm at most `a`
when `p_j ≥ τ + η` (resp. `p_j ≤ τ − η`).

**Formalization Note.** "|ψ_j⟩ ∈ H_j" is read as a unit vector (a state; the overview, p.7, says
"any normalized input"); by linearity this is the same as the bound `a·‖ψ‖` for every `ψ`. The
norm of a component is the square root of the sum of squared moduli of its amplitudes. -/
def IsGTT {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] {a₀ : A} {Prj : Matrix A A ℂ}
    (Env : HidEnv n A a₀ Prj) {R : Type} [Fintype R] [DecidableEq R] (r₀ : R) (cflag : R → Bool)
    (G : Matrix ((Fin n × A) × R) ((Fin n × A) × R) ℂ) (η τ a : ℝ) : Prop :=
  G ∈ Matrix.unitaryGroup ((Fin n × A) × R) ℂ ∧
  ∀ j : Fin n,
    (∀ v, InBranch Env j v → InBranch Env j (act G v)) ∧
    ∀ ψ ∈ branchSubspace Env j, ‖ψ‖ = 1 →
      (τ + η ≤ reward Env j →
        Real.sqrt (∑ x : (Fin n × A) × R,
          if cflag x.2 = true then ‖act G (tensorVec ψ (ket r₀)) x‖ ^ 2 else 0) ≤ a) ∧
      (reward Env j ≤ τ - η →
        Real.sqrt (∑ x : (Fin n × A) × R,
          if cflag x.2 = false then ‖act G (tensorVec ψ (ket r₀)) x‖ ^ 2 else 0) ≤ a)

end GapAgnosticGS


