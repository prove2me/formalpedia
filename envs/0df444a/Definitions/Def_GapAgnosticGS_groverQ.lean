-- Prove2me | Definitions.Def_GapAgnosticGS_groverQ
-- name    : GapAgnosticGS_groverQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:30:39.497425+00:00
-- url     : https://prove2.me/theorems/d1bb6b34-a89e-4377-b5a5-aef37c369355
-- title:
--   Hidden-branch Grover iterate $Q$ (Eq. (1))
-- statement:
--   For a hidden-basis environment $E$ with known $|0\rangle_A$ and reward projector $\Pi$, the **hidden-branch Grover iterate** is
--
--   $$Q:=-E\big(I_{IA}-2(I_I\otimes|0\rangle\langle0|_A)\big)E^\dagger\big(I_{IA}-2(I_I\otimes\Pi_A)\big).$$
--
--   The first reflection is about the image $\mathrm{span}\{|\phi_j\rangle|\mathrm{arm}_j\rangle\}$ of the zero-arm subspace and the second is the reward reflection; unlike the reflection about a single global state, $Q$ does not mix the hidden branches (Lemma 3.4).
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §2, Eq. (1), p.7 (PDF p.8)

import Definitions.Def_GapAgnosticGS_HidEnv

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §2, Eq. (1), p.7 (PDF p.8):
"Q := −E(I_{IA} − 2(I_I ⊗ |0⟩⟨0|_A))E†(I_{IA} − 2(I_I ⊗ Π_A))". The hidden-branch Grover iterate
of an environment (the reflection about the image of the zero-arm subspace, after the reward
reflection, with the leading minus sign as printed). -/
noncomputable def groverQ {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] {a₀ : A}
    {Prj : Matrix A A ℂ} (Env : HidEnv n A a₀ Prj) : Matrix (Fin n × A) (Fin n × A) ℂ :=
  -(Env.E * (1 - (2 : ℂ) • Matrix.kronecker (1 : Matrix (Fin n) (Fin n) ℂ)
        (Matrix.single a₀ a₀ (1 : ℂ))) * Env.E.conjTranspose *
      (1 - (2 : ℂ) • Matrix.kronecker (1 : Matrix (Fin n) (Fin n) ℂ) Prj))

end GapAgnosticGS


