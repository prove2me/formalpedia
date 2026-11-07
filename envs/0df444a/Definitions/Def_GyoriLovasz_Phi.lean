-- Prove2me | Definitions.Def_GyoriLovasz_Phi
-- name    : GyoriLovasz_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:53:39.934072+00:00
-- url     : https://prove2.me/theorems/59d0272f-7c78-4df6-bb51-083560ecc2a4
-- title:
--   Criticality cost $\xi_v(t)$ and assignment potential $\Phi(\varphi)$
-- statement:
--   Fix a matching $(p_i,t_i)$ from pre-terminals to terminals and secondary edges $e_i=(p_i,q_i)$. For a vertex $v$ and a terminal $t$, the **criticality cost** $\xi_v(t)$ is the number of edges among $e_1,\dots,e_k$ that are critical for assigning $v$ to $t$ (Definition 4.10). The **potential** of an assignment $\varphi$ is
--   $$\Phi(\varphi)=\sum_{v\in V\setminus T}\xi_v(\varphi(v))\qquad\text{(Definition 4.11).}$$
--
--   **Formalization Note** $\xi_v(t)$ counts indices $s\in T$ with $\mathrm{sec}(s)$ critical. The secondary edges of a matching have distinct tails, so this is the number of edges.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Definitions 4.10 and 4.11, p.31

import Mathlib
import Definitions.Def_GyoriLovasz_IsCritical

namespace GyoriLovasz

open Classical in
/-- **Criticality cost `ξ_v(t)`.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Definition 4.10, p.31: "the number of edges among e_1, ..., e_k that
are critical for assigning v to t."

**Formalization Note.** The count runs over the indices `s ∈ T`. On a matching with secondary edges the `e_i`
have distinct tails, so the count of indices is the count of edges. -/
noncomputable def xi {V : Type*} [DecidableEq V] (G : DG V) (T : Finset V) (sec : V → V × V)
    (v t : V) : ℕ :=
  (T.filter fun s => IsCritical G T (sec s) v t).card

/-- **Assignment potential.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Definition 4.11, p.31: `Φ(φ) = ∑_{v ∈ V \ T} ξ_v(φ(v))`. -/
noncomputable def Phi {V : Type*} [DecidableEq V] (G : DG V) (T : Finset V) (sec : V → V × V)
    (φ : V → V) : ℕ :=
  ∑ v ∈ G.verts \ T, xi G T sec v (φ v)

end GyoriLovasz


