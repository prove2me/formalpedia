-- Prove2me | Definitions.Def_RamadgeWonham_Synthesis_Controllable
-- name    : RamadgeWonham_Synthesis_Controllable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:37:12.031989+00:00
-- url     : https://prove2.me/theorems/bd749ee2-96dd-4a8b-97a9-3c5e90c4cd0d
-- title:
--   L-closed, (Σ_u, L)-invariant and controllable languages; the classes C_𝒢(L), F_𝒢(L) (§5, p. 213; §7, p. 218)
-- statement:
--   Let $\mathcal G$ be a generator over the alphabet $\Sigma$, let $\Sigma_c \subseteq \Sigma$ be the controllable events and $\Sigma_u = \Sigma - \Sigma_c$ the uncontrollable ones. For languages $K, L \subseteq \Sigma^*$, $K$ is
--
--   1. **$L$-closed** if $K = \bar K \cap L$;
--   2. **$(\Sigma_u, L)$-invariant** if $\bar K \Sigma_u \cap L \subseteq \bar K$, i.e. for every prefix $s \in \bar K$ and every $\sigma \in \Sigma_u$ with $s\sigma \in L$ one has $s\sigma \in \bar K$;
--   3. **controllable** if $K \subseteq L(\mathcal G)$ and $K$ is $(\Sigma_u, L(\mathcal G))$-invariant:
--   $$K \subseteq L(\mathcal G), \qquad \bar K \Sigma_u \cap L(\mathcal G) \subseteq \bar K.$$
--
--   For a sublanguage $L \subseteq L(\mathcal G)$ define the classes
--   $$\mathbf C_{\mathcal G}(L) := \{K : K \subseteq L,\ K \text{ controllable}\}, \qquad \mathbf F_{\mathcal G}(L) := \{K : K \subseteq L,\ K = \bar K \cap L_m(\mathcal G)\}.$$
--
--   Controllability says that no physically possible uncontrollable event can take a legal prefix out of the legal prefixes; it is the exact condition under which a closed-loop behaviour can be enforced by disabling controllable events only.
--
--   **Formalization Note.** $\Sigma_c$ is `Ec : Set α`, and $\sigma \in \Sigma_u$ is written `σ ∉ Ec`. The inclusion $\bar K\Sigma_u \cap L \subseteq \bar K$ is stated pointwise. The classes are `Cset G Ec L` and `Fset G L`, of type `Set (Set (List α))`.
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, p. 213, §5, definitions (i)–(iii); p. 218, §7, definitions of C_G(L) and F_G(L)

import Mathlib
import Definitions.Def_RamadgeWonham_Shared_Generator

namespace RamadgeWonham.Synthesis

variable {α : Type}

/-- `K` is `L`-closed: `K = K̄ ∩ L` (§5, p. 213, (i)). -/
def LClosed (L K : Set (List α)) : Prop :=
  K = Shared.pre K ∩ L

/-- `K` is `(Σ_u, L)`-invariant, where `Σ_u = Σ − Σ_c` and `Σ_c = Ec`: `K̄Σ_u ∩ L ⊆ K̄`
(§5, p. 213, (ii)), written pointwise. -/
def UInvariant (Ec : Set α) (L K : Set (List α)) : Prop :=
  ∀ (s : List α) (σ : α), s ∈ Shared.pre K → σ ∉ Ec → s ++ [σ] ∈ L → s ++ [σ] ∈ Shared.pre K

/-- `K` is controllable (with respect to `𝒢` and `Σ_c = Ec`): `K ⊆ L(𝒢)` and `K` is
`(Σ_u, L(𝒢))`-invariant, i.e. `K̄Σ_u ∩ L(𝒢) ⊆ K̄` (§5, p. 213, (iii)). -/
def Controllable (G : Shared.Generator α) (Ec : Set α) (K : Set (List α)) : Prop :=
  K ⊆ G.L ∧ UInvariant Ec G.L K

/-- `C_𝒢(L) := {K : K ⊆ L and K is controllable}` (§7, p. 218). -/
def Cset (G : Shared.Generator α) (Ec : Set α) (L : Set (List α)) : Set (Set (List α)) :=
  {K | K ⊆ L ∧ Controllable G Ec K}

/-- `F_𝒢(L) := {K : K ⊆ L and K = K̄ ∩ L_m(𝒢)}` (§7, p. 218). -/
def Fset (G : Shared.Generator α) (L : Set (List α)) : Set (Set (List α)) :=
  {K | K ⊆ L ∧ K = Shared.pre K ∩ G.Lm}

end RamadgeWonham.Synthesis


