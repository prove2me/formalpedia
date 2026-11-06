-- Prove2me | Definitions.Def_FracTruthSched_CoreTask
-- name    : FracTruthSched_CoreTask
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:16.622594+00:00
-- url     : https://prove2.me/theorems/a0f214f2-06b2-4930-bb23-25d2f5031d4b
-- title:
--   Core tasks of the multi-clique $MC_\ell$
-- statement:
--   For $n$ machines and an integer $\ell\ge2$, the multi-clique $MC_\ell$ consists of $\ell$ parallel tasks (**edges**) between each pair of machines, forming the class $Q_{\{u,v\}}$, and one **self-loop** $p_i$ at each machine $i$. These are the **core tasks** of the lower-bound instances.
--
--   **Formalization Note.** An edge is a pair (machine pair $(u,v)$ with $u<v$, index $k<\ell$): a machine pair is unordered and the order $u<v$ picks one representative. A self-loop is indexed by its owner. The standing assumption $\ell\ge2$ is a hypothesis of every statement about $MC_\ell$.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Definition 3, pp.8–9

import Mathlib

set_option autoImplicit false

namespace FracTruthSched

/-- The **core tasks** of `MC_ℓ` (Anastasiadis et al., arXiv:2611.06642v1, Definition 3, pp.8–9:
"For an integer ℓ ≥ 2, let MC_ℓ consist of ℓ tasks between each pair of machines and one self-loop
p_i at each machine. These are the core tasks.").

**Formalization Note.** An edge is `.inl (p, k)`, the `k`-th of the `ℓ` parallel tasks of the class
`Q{u,v}` with `p = (u, v)`, `u < v`: a machine pair is unordered, and the `<` encoding is a
convention choosing one ordered representative. The self-loop `p_i` is `.inr i`. The type is a
finite type with decidable equality (`abbrev`, so the instances are inferred). The paper's standing
`ℓ ≥ 2` is a hypothesis of every statement about `MC_ℓ`. -/
abbrev CoreTask (n ℓ : ℕ) : Type :=
  ({p : Fin n × Fin n // p.1 < p.2} × Fin ℓ) ⊕ Fin n

end FracTruthSched


