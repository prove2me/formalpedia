-- Prove2me | Definitions.Def_QVolTransducer_starState
-- name    : QVolTransducer_starState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:55.548457+00:00
-- url     : https://prove2.me/theorems/51b174fc-7a7f-4767-974a-c97898630e00
-- title:
--   Star state $|*_\omega\rangle$, stationary state $|\pi\rangle$ and net-flow vector $|\bar\pi\rangle$
-- statement:
--   For a transition matrix $P$ on a finite state space $\Omega$ and a state $\omega\in\Omega$, the **star state** is
--
--   $$
--   |*_\omega\rangle=\sum_{\nu\in\Omega}\sqrt{P(\omega,\nu)}\,|\nu\rangle\in\mathbb C^\Omega .
--   $$
--
--   For a distribution $\pi$ on $\Omega$ and a net-flow $\bar\pi\in\mathbb C^\Omega$ (i.e. $\sum_\omega\bar\pi(\omega)=0$),
--
--   $$
--   |\pi\rangle:=\sum_{\omega\in\Omega}\sqrt{\pi(\omega)}\,|\omega\rangle,
--   \qquad
--   |\bar\pi\rangle:=\sum_{\omega\in\Omega}\frac{\bar\pi(\omega)}{\sqrt{\pi(\omega)}}\,|\omega\rangle .
--   $$
--
--   Measuring $|*_\omega\rangle$ samples one step of the walk from $\omega$; the quantum walk reflects through $|\pi\rangle$ at a cost governed by the vectors $|\bar\pi\rangle$ orthogonal to it.
--
--   **Formalization Note** In Definition 4.1 the walk is the random walk on an electrical network with $R=1$, where $\sqrt{r_\omega/r_{\omega\nu}}=\sqrt{P(\omega,\nu)}$; the formula is the paper's star state of p.3. $|\bar\pi\rangle$ is used for distributions with positive entries.
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), p.3; Definition 4.1, p.28; Theorem 4.7, p.32 (PDF pp.5, 30, 34)

import Mathlib

namespace QVolTransducer

/-- The star state of a Markov chain at a state `ω` (Cornelissen, Apers, Gribling, *Improved
quantum volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version
of November 3, 2026, sha256 40d7b52d…), p.3 and Definition 4.1, p.28):
`|∗_ω⟩ = Σ_{ν∈Ω} √(P(ω,ν)) |ν⟩ ∈ ℂ^Ω`. (In Definition 4.1 the walk is the random walk on an
electrical network with `R = 1`, where `√(r_ω / r_{ων}) = √(P(ω,ν))`.) -/
noncomputable def starState {Ω : Type*} (P : Matrix Ω Ω ℝ) (ω : Ω) : EuclideanSpace ℂ Ω :=
  WithLp.toLp 2 (fun ν => ((Real.sqrt (P ω ν) : ℝ) : ℂ))

/-- The quantum state `|π⟩ := Σ_{ω∈Ω} √(π(ω)) |ω⟩` of a distribution `π` (arXiv:2609.40217,
Theorem 4.7, p.32). -/
noncomputable def sqrtVec {Ω : Type*} (π : Ω → ℝ) : EuclideanSpace ℂ Ω :=
  WithLp.toLp 2 (fun ω => ((Real.sqrt (π ω) : ℝ) : ℂ))

/-- The vector `|π̄⟩ := Σ_{ω∈Ω} π̄(ω)/√(π(ω)) |ω⟩` of a net-flow `π̄ ∈ ℂ^Ω` relative to a
distribution `π` (arXiv:2609.40217, Theorem 4.7, p.32; Lemma 4.2, p.29). It is used for
distributions `π` with positive entries. -/
noncomputable def flowVec {Ω : Type*} (π : Ω → ℝ) (πbar : Ω → ℂ) : EuclideanSpace ℂ Ω :=
  WithLp.toLp 2 (fun ω => πbar ω / ((Real.sqrt (π ω) : ℝ) : ℂ))

end QVolTransducer


