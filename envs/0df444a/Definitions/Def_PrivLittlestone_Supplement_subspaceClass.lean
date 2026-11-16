-- Prove2me | Definitions.Def_PrivLittlestone_Supplement_subspaceClass
-- name    : PrivLittlestone_Supplement_subspaceClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:58:10.423386+00:00
-- url     : https://prove2.me/theorems/55e702a9-9cee-43d8-8ebb-962331a06bb5
-- title:
--   The class of subspaces of dimension at most $r$ of $\mathbb F^{D_{\mathrm{amb}}}$
-- statement:
--   Let $\mathbb F$ be a field (of any cardinality) and $D_{\mathrm{amb}}, r \ge 0$ integers. The **class of subspaces of dimension at most $r$** of $\mathbb F^{D_{\mathrm{amb}}}$ is the set of binary classifiers on $\mathbb F^{D_{\mathrm{amb}}}$
--   $$
--   \{\, x \mapsto \mathbf 1\{x \in W\} \;:\; W \subseteq \mathbb F^{D_{\mathrm{amb}}} \text{ a linear subspace},\ \dim W \le r \,\}.
--   $$
--
--   These are the flats of rank at most $r$ of the vector matroid of $\mathbb F^{D_{\mathrm{amb}}}$; the class is the one of the subspace part of Theorem 1.2.
--
--   **Formalization Note** $\mathbb F^{D_{\mathrm{amb}}}$ is `Fin D → 𝕜`, subspaces are `Submodule 𝕜 (Fin D → 𝕜)`, and the dimension is `Module.finrank`, the true dimension in a finite-dimensional space.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Theorem 1.2, p.2, and §6, pp.10, 12

import Mathlib

namespace PrivLittlestone.Supplement

open Classical in
/-- The **class of subspaces of dimension at most `r`** of `𝔽^{D_amb}` (He–He, *Private Online
Learning of Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256
21480556…c562), Theorem 1.2, p.2, and §6, pp.10, 12): the indicators `x ↦ 1{x ∈ W}` of the linear
subspaces `W ⊆ 𝔽^{D_amb}` with `dim W ≤ r`, as binary classifiers on `𝔽^{D_amb}`.

**Formalization Note** `𝔽^{D_amb}` is `Fin D → 𝕜` for an arbitrary field `𝕜` (any cardinality);
subspaces are `Submodule 𝕜 (Fin D → 𝕜)` and their dimension is `Module.finrank`, which is the true
dimension since the ambient space is finite-dimensional. `{0,1}` is `Bool`. -/
def subspaceClass (𝕜 : Type*) [Field 𝕜] (D r : ℕ) : Set ((Fin D → 𝕜) → Bool) :=
  {g | ∃ W : Submodule 𝕜 (Fin D → 𝕜), Module.finrank 𝕜 W ≤ r ∧ g = fun x => decide (x ∈ W)}

end PrivLittlestone.Supplement


