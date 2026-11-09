-- Prove2me | Definitions.Def_DenseProdQSAT_Testing_Model
-- name    : DenseProdQSAT_Testing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:15.951237+00:00
-- url     : https://prove2.me/theorems/c92e3ee2-03a3-481f-a7cc-cf07171cb5fe
-- title:
--   Quantum instances, induced product feasibility, deletion distance and local assignments
-- statement:
--   An instance $\Phi$ has one orthogonal projector $\Pi_S$ for every nonempty $S\subseteq V$ with $|S|\le k$. Each matrix is Hermitian and idempotent; zero projectors are permitted. No rank, commutativity, density, or degree restriction is imposed.
--
--   For $C\subseteq V$, the canonical tester accepts exactly when some normalized local states satisfy
--
--   $$\Pi_S\psi_S=0\qquad(\varnothing\ne S\subseteq C,\ |S|\le k).$$
--
--   Global product satisfiability is this predicate at $C=V$. The instance is $\varepsilon$-far when every global normalized product assignment violates at least $\varepsilon n^k$ indexed supports. Violation means a nonzero projected vector, independently of its energy. A local assignment is a list of distinct labels with normalized amplitudes satisfying all constraints within its support. Amplitudes outside that support are ignored. This supplies the operational YES/NO predicates and the histories used throughout the mission.
-- source:
--   Xuhong Liu, Shuai Shao, Zicheng Han, Xiande Zhang, STOC 2027 submission #35 (October 2026), §1 and Definition 1.1; Definition 2.1 p. 5, p. 2

import Definitions.Def_DenseProdQSAT_Testing_Coordinates
set_option autoImplicit false

namespace DenseProdQSAT.Testing

abbrev Supports (n k : ℕ) := {S : Finset (Fin n) // S.Nonempty ∧ S.card ≤ k}

/-- Exactly one arbitrary orthogonal projector per nonempty support of size at most k. -/
structure Instance (n k d : ℕ) where
  projector : (S : Supports n k) → Matrix (Config d S.val) (Config d S.val) ℂ
  self_adjoint : ∀ S, (projector S).conjTranspose = projector S
  idempotent : ∀ S, projector S * projector S = projector S

def SatisfiesOn {n k d : ℕ} (Φ : Instance n k d) (C : Finset (Fin n))
    (ψ : States n d) : Prop :=
  (∀ x ∈ C, UnitState (ψ x)) ∧
  ∀ S : Supports n k, S.val ⊆ C → (Φ.projector S).mulVec (ProductVector S.val ψ) = 0

def Accepts {n k d : ℕ} (Φ : Instance n k d) (C : Finset (Fin n)) : Prop :=
  ∃ ψ : States n d, SatisfiesOn Φ C ψ

def ProductSatisfiable {n k d : ℕ} (Φ : Instance n k d) : Prop :=
  Accepts Φ Finset.univ

noncomputable def Violations {n k d : ℕ} (Φ : Instance n k d) (ψ : States n d) :
    Finset (Supports n k) := by
  classical
  exact Finset.univ.filter (fun S => (Φ.projector S).mulVec (ProductVector S.val ψ) ≠ 0)

def EpsilonFar {n k d : ℕ} (Φ : Instance n k d) (ε : ℝ) : Prop :=
  ∀ ψ : States n d, (∀ x, UnitState (ψ x)) →
    ε * (n : ℝ) ^ k ≤ (Violations Φ ψ).card

def IsLocal {n k d : ℕ} (Φ : Instance n k d) (F : List (Fin n))
    (ψ : States n d) : Prop :=
  F.Nodup ∧ SatisfiesOn Φ F.toFinset ψ

end DenseProdQSAT.Testing


