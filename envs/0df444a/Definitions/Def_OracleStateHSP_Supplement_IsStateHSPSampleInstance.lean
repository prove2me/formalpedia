-- Prove2me | Definitions.Def_OracleStateHSP_Supplement_IsStateHSPSampleInstance
-- name    : OracleStateHSP_Supplement_IsStateHSPSampleInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:05:15.278454+00:00
-- url     : https://prove2.me/theorems/f8e8b54c-065c-4fd8-8bdb-546435aafad0
-- title:
--   StateHSP instance in the sample model (Definition 1.2)
-- statement:
--   Let $G$ be a finite group, written additively, with a unitary representation $R : G \to U(\mathcal H)$ on a finite-dimensional Hilbert space $\mathcal H$, let $H \le G$ be a subgroup and let $\varepsilon \in (0, 1]$ be a known parameter. A state vector $|\varphi\rangle \in \mathcal H$ (a unit vector) is a **StateHSP instance in the sample model** with hidden subgroup $H$ if
--
--   1. $R(h)|\varphi\rangle = |\varphi\rangle$ for every $h \in H$;
--   2. $|\langle\varphi|R(g)|\varphi\rangle| \le 1 - \varepsilon$ for every $g \notin H$.
--
--   The problem is to identify $H$ from copies of $|\varphi\rangle$. Acting with an element of the hidden subgroup leaves the state invariant, while any element outside it perturbs the state by at least $\varepsilon$ in fidelity.
--
--   **Formalization Note** $\mathcal H$ has an orthonormal basis indexed by a finite type; "$R$ is a unitary representation" is the published predicate `IsUnitaryRep`, and $\|\varphi\| = 1$ and $0 < \varepsilon \le 1$ are part of the predicate. The query-model version (access to a preparation unitary, Definition 1.3) is the published `IsStateHSPInstance`.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Definition 1.2, pp.4–5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_OracleStateHSP_IsUnitaryRep

namespace OracleStateHSP

namespace Supplement

open QAlgorithms

/-- StateHSP in the sample model (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, Definition 1.2, pp.4–5): for a finite group `G` with a
unitary representation `R : G → U(H)` on the Hilbert space with basis `ι`, a subgroup `H ≤ G` and a
known parameter `ε ∈ (0, 1]`, the state vector `|φ⟩` (a unit vector, of which copies are given) is
an instance with hidden subgroup `H` if

1. `R(h)|φ⟩ = |φ⟩` for every `h ∈ H`;
2. `|⟨φ|R(g)|φ⟩| ≤ 1 − ε` for every `g ∉ H`.

**Formalization Note.** The group is written additively. "`R` is a unitary representation"
(the published `IsUnitaryRep`), "`|φ⟩` is a state vector" (`‖φ‖ = 1`) and "`ε ∈ (0, 1]`" are part
of the predicate. Access to copies is the sample model (`copiesState`, Definition 5.2), not part of
the instance. The query-model version (Definition 1.3) is the published `IsStateHSPInstance`. -/
def IsStateHSPSampleInstance {G ι : Type*} [AddGroup G] [Fintype ι] [DecidableEq ι]
    (R : G → Matrix ι ι ℂ) (φ : EuclideanSpace ℂ ι) (H : AddSubgroup G) (ε : ℝ) : Prop :=
  IsUnitaryRep R ∧ ‖φ‖ = 1 ∧ 0 < ε ∧ ε ≤ 1 ∧
    (∀ h ∈ H, act (R h) φ = φ) ∧
    ∀ g, g ∉ H → ‖inner ℂ φ (act (R g) φ)‖ ≤ 1 - ε

end Supplement

end OracleStateHSP


