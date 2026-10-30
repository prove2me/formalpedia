-- Prove2me | Definitions.Def_GeometricDL_WL_LocalGNN_state
-- name    : GeometricDL_WL_LocalGNN_state
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:21:39.169172+00:00
-- url     : https://prove2.me/theorems/19217d5f-4738-42c9-8d6c-d2f37fc636cd
-- title:
--   Node states $h^{(\ell)}_u$ of a local GNN after $\ell$ layers
-- statement:
--   Let $\mathcal N=(H_\ell,\mathrm{enc},\Phi_\ell)$ be a local GNN and $G=(V,E)$ a finite graph with node features $x:V\to F$. The **node states** of $\mathcal N$ on $G$ are
--
--   $$h^{(0)}_u=\mathrm{enc}(x_u),\qquad h^{(\ell+1)}_u=\Phi_\ell\Big(h^{(\ell)}_u,\ \{\!\{\,(h^{(\ell)}_v,\ |N_v|):\ v\in N_u\,\}\!\}\Big).$$
--
--   The output of layer $\ell$ is the input of layer $\ell+1$, and every layer applies the same function to every node, as in eq. (13).
--
--   **Formalization Note** Layers are 0-based: $h^{(0)}$ is the encoded input. The neighbour states form a multiset.
-- source:
--   Bronstein, Bruna, Cohen & Veličković, Geometric Deep Learning, arXiv:2104.13478v2, eq. (13), printed p. 34 (PDF p. 38); §5.3, printed p. 78 (PDF p. 82)

import Mathlib
import Definitions.Def_GeometricDL_WL_nbhd
import Definitions.Def_GeometricDL_WL_LocalGNN

universe u v

namespace GeometricDL.WL

/-- **The node states of a local GNN after `ℓ` layers.**
Bronstein, Bruna, Cohen & Veličković, *Geometric Deep Learning*, arXiv:2104.13478v2, eq. (13),
printed p. 34 (PDF p. 38): "a permutation equivariant function F can be constructed by applying φ
to every node's neighbourhood in isolation: F(X, A) = [φ(x_1, X_{N_1}); …; φ(x_n, X_{N_n})]";
§5.3, printed p. 78 (PDF p. 82).

For a finite graph `(V, E)` with node features `x : V → F`:
`N.state E x 0 u = N.enc (x u)` and
`N.state E x (ℓ + 1) u = N.layer ℓ (N.state E x ℓ u) {{ (N.state E x ℓ v, |N_v|) : v ∈ N_u }}`,
with `N_u = nbhd E u` the neighbourhood (11).

**Formalization Note.** The input of layer `ℓ + 1` is the output of layer `ℓ`; layers are
0-based (`state 0` is the encoded input). Neighbour states form a multiset. -/
def LocalGNN.state {F : Type u} (N : LocalGNN.{u, v} F) {V : Type*} [Fintype V]
    (E : V → V → Prop) [DecidableRel E] (x : V → F) : (ℓ : ℕ) → V → N.H ℓ
  | 0 => fun u => N.enc (x u)
  | ℓ + 1 => fun u => N.layer ℓ (LocalGNN.state N E x ℓ u)
      ((nbhd E u).val.map (fun v => (LocalGNN.state N E x ℓ v, (nbhd E v).card)))

end GeometricDL.WL


