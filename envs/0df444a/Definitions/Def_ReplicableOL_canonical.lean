-- Prove2me | Definitions.Def_ReplicableOL_canonical
-- name    : ReplicableOL_canonical
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:46.817468+00:00
-- url     : https://prove2.me/theorems/b98c87bb-95fc-4d4e-b643-106f3b0c6d8d
-- title:
--   Canonical output $z^\star_F(Q,r)$
-- statement:
--   The **canonical output** of $F$ at seed $r$ under $Q$ is the least element, in a fixed order on the finite set $Z$, among the maximizers of $z\mapsto\mathbb P_{S\sim Q}[F(S,r)=z]$. The canonical prefix $\tau^\star_{\le t}(Q,r)$ is this object for $F=\tau_{\le t}$.
--
--   **Formalization Note** The fixed order is the `LinearOrder` instance on `Z`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.3, p.8

import Mathlib
open MeasureTheory ProbabilityTheory

namespace ReplicableOL

open scoped Classical in
/-- **Canonical output $z^\star_F(Q,r)$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.3, p.8. "let z⋆_F(Q, r) be the least maximizer in a fixed order on Z".

**Formalization Note.** The fixed order is the `LinearOrder` instance on `Z`. -/
noncomputable def canonical {X Z R : Type*} [MeasurableSpace X] [Fintype Z] [Nonempty Z] [LinearOrder Z]
    (F : X → R → Z) (Q : Measure X) (r : R) : Z :=
  (Finset.univ.filter fun z => ∀ z', Q {S | F S r = z'} ≤ Q {S | F S r = z}).min' (by
    obtain ⟨z, -, hz⟩ := Finset.exists_max_image Finset.univ (fun z => Q {S | F S r = z})
      Finset.univ_nonempty
    exact ⟨z, by simpa using fun z' => hz z' (Finset.mem_univ z')⟩)

end ReplicableOL


