-- Prove2me | Definitions.Def_OracleStateHSP_IsStateHSPInstance
-- name    : OracleStateHSP_IsStateHSPInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:29:34.773686+00:00
-- url     : https://prove2.me/theorems/d0069ced-7254-4629-97c2-4e09f858bdc1
-- title:
--   StateHSP instance with state-preparation unitary (Definition 1.3)
-- statement:
--   Let $G$ be a finite group with a unitary representation $R$ on $\mathcal H$, let $H \le G$, and let $\varepsilon \in (0, 1]$. A unitary $U_\varphi$ preparing $|\varphi\rangle = U_\varphi |0\rangle$ is a **StateHSP instance** with hidden subgroup $H$ and parameter $\varepsilon$ if
--
--   1. $R(h)|\varphi\rangle = |\varphi\rangle$ for every $h \in H$;
--   2. $|\langle\varphi| R(g) |\varphi\rangle| \le 1 - \varepsilon$ for every $g \notin H$.
--
--   The problem is to identify $H$ from queries to $U_\varphi$, its inverse, its conjugates $U_\varphi^*$ and $U_\varphi^T$, and their controlled versions.
--
--   **Formalization Note** The group is additive and $|0\rangle$ is a designated basis vector $|z_0\rangle$. The predicate also records that $R$ is a unitary representation, that $U_\varphi$ is unitary and that $0 < \varepsilon \le 1$. The query access is the query model, not part of the predicate.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Definition 1.3, p.6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_OracleStateHSP_IsUnitaryRep

namespace OracleStateHSP

open QAlgorithms

/-- StateHSP with access to the state-preparation unitary (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, Definition 1.3, p.6): the
unitary `U` on the Hilbert space with basis `ι`, preparing `|φ⟩ = U|0⟩` from the designated basis
state `|0⟩ = |z₀⟩`, is an instance for the unitary representation `R` of the finite group `G`, with
hidden subgroup `H ≤ G` and known parameter `ε ∈ (0, 1]`, if

1. `R(h)|φ⟩ = |φ⟩` for every `h ∈ H`;
2. `|⟨φ|R(g)|φ⟩| ≤ 1 − ε` for every `g ∉ H`.

**Formalization Note.** The group is written additively. The clauses "`R` is a unitary
representation", "`U` is unitary" and "`ε ∈ (0, 1]`" of the definition are part of the predicate.
Query access to `U^{±1}`, `U^*`, `U^T` and their controlled versions is the query model
(`QueryAlgorithm`), not part of the instance. -/
def IsStateHSPInstance {G ι : Type*} [AddGroup G] [Fintype ι] [DecidableEq ι]
    (R : G → Matrix ι ι ℂ) (z₀ : ι) (U : Matrix ι ι ℂ) (H : AddSubgroup G) (ε : ℝ) : Prop :=
  IsUnitaryRep R ∧ U ∈ Matrix.unitaryGroup ι ℂ ∧ 0 < ε ∧ ε ≤ 1 ∧
    (∀ h ∈ H, act (R h) (act U (ket z₀)) = act U (ket z₀)) ∧
    ∀ g, g ∉ H → ‖inner ℂ (act U (ket z₀)) (act (R g) (act U (ket z₀)))‖ ≤ 1 - ε

end OracleStateHSP


