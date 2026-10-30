-- Prove2me | Definitions.Def_ShorEBAdditivity_IsEntanglementBreaking
-- name    : ShorEBAdditivity_IsEntanglementBreaking
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:17:56.932385+00:00
-- url     : https://prove2.me/theorems/cecbd112-6a5b-4684-a87d-beaec76f52d1
-- title:
--   Entanglement-breaking map
-- statement:
--   Let $\Phi : M_B \to M_{B'}$ be a map from operators on a finite-dimensional space $\mathcal H_B$ to operators on $\mathcal H_{B'}$. Then $\Phi$ is **entanglement breaking** if, whenever its input is entangled with another quantum system, its output is no longer entangled with that system. Precisely: for every finite-dimensional reference system $\mathcal H_{\mathrm{ref}} = \mathbb C^a$ ($a \in \mathbb N$) and every density matrix $X$ on $\mathcal H_{\mathrm{ref}} \otimes \mathcal H_B$, the output $(I \otimes \Phi)(X)$ is separable, that is
--
--   $$
--   (I\otimes\Phi)(X) = \sum_{j} w_j\, A_j \otimes B_j
--   $$
--
--   for finitely many weights $w_j \ge 0$ and density matrices $A_j$ on $\mathcal H_{\mathrm{ref}}$ and $B_j$ on $\mathcal H_{B'}$.
--
--   This is the class of channels for which Shor proves additivity of the Holevo capacity. The paper notes that every entanglement-breaking channel can also be written in Holevo's form $\Phi(\rho) = \sum_i \operatorname{Tr}(X_i\rho)\,\theta_i$ (a result it credits to Horodecki and Ruskai); that form is not used as the definition.
--
--   **Formalization Note** The reference system is the first tensor factor, indexed by `Fin a`; $I\otimes\Phi$ applies $\Phi$ to every block. Every finite-dimensional reference space is isomorphic to some $\mathbb C^a$, so all references are covered. Separability is the published predicate `QAlgorithms.Entanglement.IsSeparablePositive` (nonnegative weights, no normalization required; for a density output the weights sum to one automatically). The map $\Phi$ is a bare function on matrices; linearity, complete positivity and trace preservation are separate hypotheses (`IsChannel`) of the theorems that use it.
-- source:
--   Shor, Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels, arXiv:quant-ph/0201149v3, p.2, "That is, when the input state is entangled between the input space Hin and another quantum system Href, the output of the channel is no longer entangled with the system Href"

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability

open QAlgorithms

namespace ShorEBAdditivity

/-- Shor, *Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels*,
arXiv:quant-ph/0201149v3, p.2, "Entanglement breaking channels are channels which destroy
entanglement with other quantum systems. That is, when the input state is entangled between the
input space Hin and another quantum system Href, the output of the channel is no longer entangled
with the system Href."

`Φ : M_B → M_{B'}` is entanglement breaking if for every finite-dimensional reference system
`Href = ℂ^a` (every `a : ℕ`) and every density matrix `X` on `Href ⊗ Hin`, the output
`(I ⊗ Φ)(X)` is separable: a nonnegative combination `Σ_j w_j A_j ⊗ B_j` of products of density
matrices (`QAlgorithms.Entanglement.IsSeparablePositive`).

**Formalization Note.** The reference system is the **first** tensor factor (`Fin a × B`), and
`I ⊗ Φ` is `QAlgorithms.idTensorSuperop Φ`, which applies `Φ` to every block. Every
finite-dimensional reference space is isomorphic to `ℂ^a` for some `a`, so quantifying over
`Fin a` covers every reference. The definition is the paper's operational one, not the Holevo
form (5), which the paper credits to Horodecki [9] and Ruskai [10]. `Φ` is a bare function;
linearity, complete positivity and trace preservation come from `QAlgorithms.IsChannel` in the
statements that use it. -/
def IsEntanglementBreaking {B B' : Type*} [Fintype B] [Fintype B'] (Φ : Superop B B') : Prop :=
  ∀ (a : ℕ) (X : Matrix (Fin a × B) (Fin a × B) ℂ), IsDensityMatrix X →
    Entanglement.IsSeparablePositive (idTensorSuperop Φ X)

end ShorEBAdditivity


