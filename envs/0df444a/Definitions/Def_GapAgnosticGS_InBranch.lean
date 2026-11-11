-- Prove2me | Definitions.Def_GapAgnosticGS_InBranch
-- name    : GapAgnosticGS_InBranch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:33:15.604173+00:00
-- url     : https://prove2.me/theorems/dd52d528-463b-487e-843f-a5037a289c24
-- title:
--   A vector lies in $\mathcal H_j\otimes\mathcal H_R$
-- statement:
--   Let $R$ be a finite set of auxiliary basis states. A vector $v$ on $I\otimes A\otimes\mathbb C^R$ lies in $\mathcal H_j\otimes\mathbb C^R$ when, for every auxiliary basis state $r$, its slice $\langle r|v\rangle\in I\otimes A$ lies in the branch subspace $\mathcal H_j$. Lemma 3.5 (i) says that the threshold test maps each $\mathcal H_j\otimes\mathcal H_{CP}$ into itself.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.5, p.10 (PDF p.11): "(i) every subspace H_j ⊗ H_CP is invariant"

import Definitions.Def_GapAgnosticGS_branchSubspace

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.5, p.10 (PDF p.11): "(i) every subspace H_j ⊗ H_CP is invariant". A vector on
the selector and arm registers together with auxiliary registers `R` lies in `H_j ⊗ ℂ^R`: for each
basis state `r` of the auxiliary registers, its slice on `ℂⁿ ⊗ A` lies in the branch subspace
`H_j`. -/
def InBranch {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] {a₀ : A} {Prj : Matrix A A ℂ}
    (Env : HidEnv n A a₀ Prj) (j : Fin n) {R : Type}
    (v : EuclideanSpace ℂ ((Fin n × A) × R)) : Prop :=
  ∀ r : R, (WithLp.toLp 2 fun z => v (z, r) : EuclideanSpace ℂ (Fin n × A)) ∈ branchSubspace Env j

end GapAgnosticGS


