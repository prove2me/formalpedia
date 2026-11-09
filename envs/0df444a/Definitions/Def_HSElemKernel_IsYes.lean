-- Prove2me | Definitions.Def_HSElemKernel_IsYes
-- name    : HSElemKernel_IsYes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:23:42.322336+00:00
-- url     : https://prove2.me/theorems/8719f833-9c47-44e2-828a-c57f7fc110da
-- title:
--   YES-instance: a hitting set of size at most $k$
-- statement:
--   An instance $(U, \mathcal S, k)$ is a **YES-instance** if there is a set $Z \subseteq U$ with
--   $$|Z| \le k \quad\text{and}\quad Z \cap A \ne \emptyset \ \text{ for every } A \in \mathcal S .$$
--   Such a $Z$ is a **hitting set**. Otherwise the instance is a NO-instance. A family containing $\emptyset$ is never a YES-instance.
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Section 3, p.6

import Mathlib
import Definitions.Def_HSElemKernel_HSInstance

namespace HSElemKernel

/-- The instance is a YES-instance: some set `Z ⊆ U` with `|Z| ≤ k` meets every input set
(Sheng–Xiao, arXiv:2609.06512, held version sha256 aca9c70e…, Section 3, p.6: "It is a
YES-instance if there exists a set Z ⊆ U such that |Z| ≤ k and Z ∩ A ≠ ∅ for every A ∈ S").

**Formalization Note** A family containing `∅` is never a YES-instance, for every `k`. -/
def IsYes (I : HSInstance) : Prop :=
  ∃ Z : Finset (Fin I.n), Z.card ≤ I.k ∧ ∀ A ∈ I.S, (Z ∩ A).Nonempty

end HSElemKernel


