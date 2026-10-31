-- Prove2me | Definitions.Def_FoundationsRL_LinUCB_linearClass
-- name    : FoundationsRL_LinUCB_linearClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:12.760991+00:00
-- url     : https://prove2.me/theorems/4bf7a9eb-94fc-42b1-ae82-b1b6062beaf9
-- title:
--   The class of linear functions $\mathcal F$ (Eq. (3.21))
-- statement:
--   For a parameter set $\Theta\subseteq\mathbb R^d$ and a feature map $\phi$, the **linear class** is
--
--   $$
--   \mathcal F=\bigl\{(x,\pi)\mapsto\langle\theta,\phi(x,\pi)\rangle\ \bigm|\ \theta\in\Theta\bigr\}.
--   $$
--
--   Its cardinality enters the confidence radius of LinUCB through $\beta=8\log(|\mathcal F|/\delta)$.
--
--   **Formalization Note** $\mathcal F$ is a set of functions, so $|\mathcal F|$ counts distinct functions; the book identifies $|\Theta|=|\mathcal F|$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Eq. (3.21), p. 43

import Mathlib
import Definitions.Def_FoundationsRL_LinUCB_linearFunction

namespace FoundationsRL.LinUCB

/-- The class of linear functions `F = {(x, π) ↦ ⟨θ, ϕ(x, π)⟩ | θ ∈ Θ}` (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Eq. (3.21), p. 43).

**Formalization Note.** `F` is a set of functions, so `|F|` counts distinct functions; the book
identifies `|Θ| = |F|`. -/
def linearClass {X Act : Type*} {d : ℕ} (Θ : Set (Fin d → ℝ)) (ϕ : X → Act → Fin d → ℝ) :
    Set (X → Act → ℝ) :=
  linearFunction ϕ '' Θ

end FoundationsRL.LinUCB


