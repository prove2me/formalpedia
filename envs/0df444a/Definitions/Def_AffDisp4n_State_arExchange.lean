-- Prove2me | Definitions.Def_AffDisp4n_State_arExchange
-- name    : AffDisp4n_State_arExchange
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:59:30.224891+00:00
-- url     : https://prove2.me/theorems/e3bc2b66-f6b3-447b-bed9-c831aca901a4
-- title:
--   Affine reparameterisation (AR): exchanging a parameter and an auxiliary variable
-- statement:
--   Let $Q$ be an auxiliary variable whose solved form is $Q = t \cdot u + \kappa$, where $t$ is its row of $A^{-1} N$ and $\kappa = (A^{-1} c)_Q$, and let $x$ be a parameter with $t_x = 1$, so that $Q = x + \varphi(u_{-x})$. **The exchange (AR)** substitutes $x \leftarrow w + \varphi(u_{-x})$ in $\Phi$, regards $Q$ as the new parameter $w$, and regards $x$ as an auxiliary variable. Concretely:
--
--   1. the new map is $\Phi \circ \tau$, where $\tau(u')_x = t \cdot u' + \kappa$ and $\tau(u')_y = u'_y$ for $y \ne x$;
--   2. in the affine system, the column of $x$ in $N$ and the column of $Q$ in $A$ are exchanged, so every equation keeps the same terms;
--   3. in the acyclic part, the inputs $x$ and $Q$ are swapped;
--   4. the pairs are unchanged.
--
--   No equation or gate changes otherwise.
--
--   **Formalization Note** $\Phi \circ \tau$ has translation $b + \kappa L_{\cdot x}$ and linear part $L T$, where $T$ is the identity matrix with row $x$ replaced by $t$. The new parameter $w$ takes the index of $x$, and $x$ takes the index of $Q$.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.6, pp.18–19; §3.2, pp.20–21

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_Acyclic_mapInput
import Definitions.Def_AffDisp4n_State

namespace AffDisp4n

/-- **Affine reparameterisation by exchanging a parameter and an auxiliary variable** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.6
"Preserving the representation", pp.18–19, and §3.2 "AR", pp.20–21). Let the auxiliary variable `Q`
(index `j`) have the solved form `Q = t · u + κ`, where `t` is row `j` of `A⁻¹ N` and `κ = (A⁻¹ c)_j`,
and let `x` be a parameter with `t_x = 1`, so `Q = x + φ(u₋ₓ)`. The exchange substitutes
`x ← w + φ(u₋ₓ) + κ`, which is `Φ ← Φ ∘ τ` with `τ(u')_x = t · u' + κ` and `τ(u')_y = u'_y` for
`y ≠ x`. It regards `Q` as the new parameter `w` (at index `x`) and `x` as an auxiliary variable (at
index `j`). In the affine system, the column of `x` in `N` and the column of `Q` in `A` are exchanged.
In the acyclic part, the inputs `x` and `Q` are swapped. No equation or gate changes otherwise, and
the pairs are unchanged.

**Formalization Note** `Φ ∘ τ` has translation `b + κ · L_{·x}` and linear part `L T`, where `T` is the
identity with row `x` replaced by `t`. -/
noncomputable def State.arExchange {n : ℕ} (σ : State n) (j : Fin σ.r) (x : Fin σ.m) : State n where
  m := σ.m
  r := σ.r
  b := σ.b + (σ.A⁻¹.mulVec σ.c j) • (fun i => σ.L i x)
  L := σ.L * (1 : Matrix (Fin σ.m) (Fin σ.m) (ZMod 2)).updateRow x ((σ.A⁻¹ * σ.N) j)
  P := σ.P
  A := σ.A.updateCol j (fun i => σ.N i x)
  N := σ.N.updateCol x (fun i => σ.A i j)
  c := σ.c
  circ := σ.circ.mapInput (Equiv.swap (Sum.inl x) (Sum.inr j))

end AffDisp4n


