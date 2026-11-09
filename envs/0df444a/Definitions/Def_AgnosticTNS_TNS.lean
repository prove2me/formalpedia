-- Prove2me | Definitions.Def_AgnosticTNS_TNS
-- name    : AgnosticTNS_TNS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:17.322122+00:00
-- url     : https://prove2.me/theorems/02c63bec-e985-4b52-9ea0-8e0a644a9612
-- title:
--   Tensor network state class $S_d(G,w)$
-- statement:
--   For a graph $G=([n],E)$ and $w:E\to\mathbb N$, $S_d(G,w)$ is the set of normalised pure states $|\psi\rangle\in(\mathbb C^d)^{\otimes n}$, $\|\psi\|=1$, that admit a tensor network representation of the form (2.2) on $(G,w)$.
--
--   **Formalization Note** States are unit vectors; global phases are not identified, which changes no overlap.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Definition 2.1, p.12

import Mathlib
import Definitions.Def_AgnosticTNS_tnState

namespace AgnosticTNS

/-- **The class `S_d(G, w)`**, Definition 2.1, p.12 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): the normalised pure states on
`(ℂ^d)^{⊗n}` that admit a tensor network representation (2.2) on `(G, w)`.

**Formalization Note** A pure state is a unit vector `ψ : (Fin n → Fin d) → ℂ`
(`Σ_x |ψ(x)|² = 1`); global phases are not identified, which changes no overlap `⟨ψ|ρ|ψ⟩`. -/
def TNS {n : ℕ} (d : ℕ) (G : SimpleGraph (Fin n)) (w : G.edgeSet → ℕ) :
    Set ((Fin n → Fin d) → ℂ) :=
  {ψ | (∃ φ, ψ = tnState G w φ) ∧ ∑ x, ‖ψ x‖ ^ 2 = 1}

end AgnosticTNS


