-- Prove2me | Definitions.Def_XOSMax_cliqueWrt
-- name    : XOSMax_cliqueWrt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:42.012628+00:00
-- url     : https://prove2.me/theorems/4ac93e02-8c39-4772-895b-b07b4af4fe80
-- title:
--   The clique $V^*_i$ with respect to the clause $i$
-- statement:
--   Given a ground set $V$ and a representation $w_1,\dots,w_k$ of $f$, the **clique with respect to $i$** is
--   $$
--   V^*_i:=\{\,v\in V\ :\ f_i(v)=f(v)\,\},
--   $$
--   where $f(v)$ means $f(\{v\})$. A subset of $V$ is a **clique** if it is a clique with respect to some $i$.
--
--   On $V^*_i$ the function $f$ agrees with the additive clause $f_i$, which is why cliques are the building blocks of the algorithms.
--
--   **Formalization Note** The ground set is a parameter, because the milestones work on the part of the ground type that survives the preprocessing of §2. Cliques depend on the representation, and one $f$ has many representations.
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, §2, p.3, "a clique with respect to i"

import Mathlib

namespace XOSMax

/-- The **clique with respect to `i`**, `V*ᵢ := { v ∈ V | fᵢ(v) = f(v) }`
(Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3, §2, p.3, "a clique with respect to i").
A subset of `V` is a clique if it is `cliqueWrt V w f i` for some `i`.

**Formalization Note** The ground set `V` is a parameter, because the milestones work on the part
of the ground type that survives the §2 preprocessing. A clique depends on the representation `w`,
and `f(v)` is `f {v}`. -/
noncomputable def cliqueWrt {E : Type} {k : ℕ} (V : Finset E) (w : Fin k → E → ℝ)
    (f : Finset E → ℝ) (i : Fin k) : Finset E :=
  V.filter fun v => w i v = f {v}

end XOSMax


