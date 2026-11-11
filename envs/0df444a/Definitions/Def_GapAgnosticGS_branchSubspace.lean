-- Prove2me | Definitions.Def_GapAgnosticGS_branchSubspace
-- name    : GapAgnosticGS_branchSubspace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:31:39.002718+00:00
-- url     : https://prove2.me/theorems/f9388047-8314-42a6-a836-bfd410603907
-- title:
--   Hidden branch subspace $\mathcal H_j$
-- statement:
--   For a hidden-basis environment and an arm $j$, the **branch subspace** $\mathcal H_j\subseteq I\otimes A$ is the span of
--
--   $$|\phi_j\rangle\otimes\Pi|\mathrm{arm}_j\rangle\quad\text{and}\quad|\phi_j\rangle\otimes(I-\Pi)|\mathrm{arm}_j\rangle$$
--
--   (two-dimensional when $0<p_j<1$), or the one-dimensional span of $E|\phi_j,0\rangle$ if $p_j\in\{0,1\}$. These subspaces are mutually orthogonal, and the Grover iterate and the threshold tests act inside each of them.
--
--   **Formalization Note** For $p_j\in\{0,1\}$ the two spans coincide; the case split is kept as printed.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.4, p.10 (PDF p.11)

import Definitions.Def_GapAgnosticGS_reward
open QAlgorithms

namespace GapAgnosticGS

open Classical in
/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.4, p.10 (PDF p.11): "let H_j be the two-dimensional subspace spanned by
{|ϕ_j⟩⊗Π|arm_j⟩, |ϕ_j⟩⊗(I−Π)|arm_j⟩} or the one-dimensional span of E|ϕ_j, 0⟩ if p_j ∈ {0, 1}".
The hidden branch subspace `H_j ⊆ ℂⁿ ⊗ A` of arm `j`.

**Formalization Note.** For `p_j ∈ {0, 1}` the two spanning vectors of the first case reduce to
`0` and `|ϕ_j⟩|arm_j⟩ = E|ϕ_j, 0⟩`, so both cases agree; the case split is kept as printed. -/
noncomputable def branchSubspace {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] {a₀ : A}
    {Prj : Matrix A A ℂ} (Env : HidEnv n A a₀ Prj) (j : Fin n) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n × A)) :=
  if reward Env j = 0 ∨ reward Env j = 1 then
    Submodule.span ℂ {act Env.E (tensorVec (Env.φ j) (ket a₀))}
  else
    Submodule.span ℂ {tensorVec (Env.φ j) (act Prj (Env.arm j)),
      tensorVec (Env.φ j) (act (1 - Prj) (Env.arm j))}

end GapAgnosticGS


